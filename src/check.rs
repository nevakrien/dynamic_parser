//! check.rs – incremental FIRST/FOLLOW checker for any LL(1) backend
//!
//! This module is **parser‑backend agnostic**: it only knows about productions
//! (lists of tokens) and never assumes a particular parsing strategy beyond the
//! LL(1) contract.  All heavy work happens *incrementally* so you can modify a
//! grammar on the fly (e.g. after a macro expansion) and re‑run just the parts
//! that became stale.
//!
//! ## Core design choices
//!
//! * **Non‑terminals** are referred to by the small, copy‑able index
//!   `NonTermId` (`usize`).  The mapping to pretty names lives entirely in the
//!   front‑end.
//! * **Terminals** are wrapped in [`ExTerm`] so that the *artificial* symbols
//!   **ε** (`Empty`) and **$** (`Eof`) travel through the same APIs as real
//!   tokens.
//! * FIRST / FOLLOW / "peek‑safety" tables are cached on demand and can be
//!   cleared via [`LLGrammar::flush`] when the grammar mutates.
//!
//! ## Full usage example
//!
//! ```rust
//! use std::rc::Rc;
//! use hashbrown::HashMap;
//! use dynamic_parser::check::{LLGrammar, Token, ExTerm};
//!
//! // Helper to build an Rc<[Token]> from a slice.
//! fn rc<T: Clone>(xs: &[Token<T>]) -> Rc<[Token<T>]> {
//!     Rc::from(xs.to_vec().into_boxed_slice())
//! }
//!
//! // Build a tiny grammar:  S → 'a' S | ε
//! let mut g: LLGrammar<char> = LLGrammar::new();
//! g.rules.entry(0).or_default().push(rc(&[Token::Term('a'), Token::NonTerm(0)]));
//! g.rules.entry(0).or_default().push(rc(&[]));
//!
//! // Seed FOLLOW(S) with end‑of‑input and compute all tables in one call.
//! g.add_start(0);
//! g.calculate();
//!
// ! // Turn the grammar into a deterministic parse table or obtain diagnosis.
// ! let table = g.get_checked_table().expect("grammar should be LL(1)");
// ! assert_eq!(table[&0][&ExTerm::Term('a')], 0); // first alternative on 'a'
//! ```
//!
//! The resulting `table` is a dense [`HashMap`] that can feed *any* LL(1)
//! interpreter or be flattened into a code generator.
//!
//! ## Dependency graph (public API)
//!
//! ```text
//!      ┌──────────┐    calculate_first_terminals
//!      │ LLGrammar  │───────────────────────────┐
//!      └──────────┘                           │
//!             │                               ▼
//!             │  calculate_first_non_terminals
//!             │                               │
//!             ▼                               │
//!       calculate_first  ◀────────────────────┘
//!             │
//!             ▼
//!     calculate_first_seqs   (needs FIRST*)
//!             │
//!             ▼
//!      calculate_follow      (needs FIRST*)
//!             │
//!             ▼
//!      get_checked_table     (needs FIRST* & FOLLOW)
//! ```
//!
//! *All* helper accessors (e.g. [`LLGrammar::get_first_set`]) rely on the caches
//! being up‑to‑date – run [`LLGrammar::calculate`] or the fine‑grained variants
//! yourself.

use crate::check::hash::Hash;
use crate::parser::Terminal;
use crate::parser::Token as PToken;
use alloc::collections::VecDeque;
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::hash;
use hashbrown::{HashMap, HashSet};

pub type NonTermId = usize;
pub type ProdId = usize;

/// Extended terminal domain used by LL(1) set algebra
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExTerm<K> {
    /// synthetic end‑of‑input symbol ($)
    Eof,
    /// ε  (empty string)  – appears only in FIRST sets
    Empty,
    /// real token coming from the user’s lexer
    Term(K),
}

impl<K> From<K> for ExTerm<K> {
    fn from(k: K) -> Self {
        ExTerm::Term(k)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token<K> {
    /// synthetic end‑of‑input symbol ($)
    Eof,
    /// real token coming from the user’s lexer
    Term(K),

    /// derived token
    NonTerm(NonTermId),
}

impl<T: Terminal, F1: Fn(&mut State, T), State> From<PToken<T, F1, State>> for Token<T::Key> {
    fn from(tok: PToken<T, F1, State>) -> Self {
        match tok {
            PToken::Term { key, .. } => Token::Term(key),
            PToken::NonTerm(id) => Token::NonTerm(id),
            PToken::Eof => Token::Eof,
        }
    }
}

pub type TokList<K> = Rc<[Token<K>]>;

#[inline(always)]
pub fn iterate_rules<K>(
    rules: &HashMap<NonTermId, Vec<TokList<K>>>,
) -> impl Iterator<Item = (NonTermId, &TokList<K>)> {
    rules.iter().flat_map(|(k, v)| v.iter().map(|x| (*k, x)))
}

/// Retrieves (or computes and memoises) the **FIRST** set of a *slice* of
/// tokens.
///
/// * `first_seq` is the global cache *per production slice*.
/// * `first`     is the cache *per non‑terminal*.
pub fn get_first_set<'a, K: Hash + Eq + Clone>(
    tokens: &[Token<K>],
    first_seq: &'a mut HashMap<TokList<K>, HashSet<ExTerm<K>>>,
    first: &HashMap<NonTermId, HashSet<ExTerm<K>>>,
) -> &'a HashSet<ExTerm<K>> {
    //Safety: we need to borrow for 'a when we get a Some but otherwise we borrow short.
    let first_seq: *mut HashMap<TokList<K>, HashSet<ExTerm<K>>> = first_seq as *mut _;
    if let Some(x) = unsafe { &*first_seq }.get(tokens) {
        return x;
    }

    //we dropped the refrence frome earlier since we got None
    make_first_set(tokens.into(), unsafe { &mut *first_seq }, first)
}

/// Same as [`get_first_set`] but takes ownership of an already shared `Rc` to
/// avoid an extra allocation during memoisation.
pub fn get_first_set_rc<'a, K: Hash + Eq + Clone>(
    tokens: TokList<K>,
    first_seq: &'a mut HashMap<TokList<K>, HashSet<ExTerm<K>>>,
    first: &HashMap<NonTermId, HashSet<ExTerm<K>>>,
) -> &'a HashSet<ExTerm<K>> {
    //Safety: we need to borrow for 'a when we get a Some but otherwise we borrow short.
    let first_seq: *mut HashMap<TokList<K>, HashSet<ExTerm<K>>> = first_seq as *mut _;
    if let Some(x) = unsafe { &*first_seq }.get(&tokens) {
        return x;
    }

    //we dropped the refrence frome earlier since we got None
    make_first_set(tokens, unsafe { &mut *first_seq }, first)
}
fn make_first_set<'a, K: Hash + Eq + Clone>(
    tokens: TokList<K>,
    first_seq: &'a mut HashMap<TokList<K>, HashSet<ExTerm<K>>>,
    first: &HashMap<NonTermId, HashSet<ExTerm<K>>>,
) -> &'a HashSet<ExTerm<K>> {
    match tokens.first() {
        None => {
            let set = first_seq.entry(tokens).or_default();
            set.insert(ExTerm::Empty);
            set
        }
        Some(Token::Eof) => {
            let set = first_seq.entry(tokens).or_default();
            set.insert(ExTerm::Eof);
            set
        }
        Some(Token::Term(k)) => {
            let k = k.clone();
            let set = first_seq.entry(tokens).or_default();
            set.insert(ExTerm::Term(k));
            set
        }

        Some(Token::NonTerm(id)) => {
            let Some(f) = first.get(id) else {
                return first_seq.entry(tokens).or_default()
            };
            if f.contains(&ExTerm::Empty) {
                let mut set = get_first_set(tokens[1..].into(), first_seq, first).clone();

                set.extend(f.iter().filter(|x| **x != ExTerm::Empty).cloned());
                first_seq.entry(tokens).or_insert(set)
            } else {
                first_seq.entry(tokens).or_insert(f.clone())
            }
        }
    }
}

#[inline(always)]
fn update_follow_con<K: Hash + Eq + Clone>(
    target: NonTermId,
    tokens: &[Token<K>],
    first: &HashMap<NonTermId, HashSet<ExTerm<K>>>,
    first_seq: &mut HashMap<TokList<K>, HashSet<ExTerm<K>>>,
    follow: &mut HashMap<NonTermId, HashSet<ExTerm<K>>>,
    follow_update: &mut HashMap<NonTermId, HashSet<NonTermId>>,
) {
    for (i, t) in tokens.iter().enumerate().rev() {
        if let Token::NonTerm(id) = t {
            let first = get_first_set(&tokens[i + 1..], first_seq, first);

            let spot = follow.entry(*id).or_default();
            for x in first.iter() {
                if *x == ExTerm::Empty {
                    continue;
                }
                spot.insert(x.clone());
            }

            if *id != target && first.contains(&ExTerm::Empty) {
                follow_update.entry(target).or_default().insert(*id);
            }
        }
    }
}

/// Dense parse table mapping `(NonTermId, lookahead)` to a **single**
/// production index.  Only available after [`LLGrammar::get_checked_table`]
/// verifies that the grammar is LL(1).
pub type ProdTable<K> = HashMap<NonTermId, HashMap<ExTerm<K>, ProdId>>;

/// Scans the *raw* table (where each cell holds **all** candidate productions)
/// and yields every FIRST/FIRST conflict.
///
/// The iterator lazily produces `(LHS, lookahead, slice_of_productions)` tuples.
pub fn get_first_first_conflicts<K: Hash + Eq>(
    table: &HashMap<NonTermId, HashMap<ExTerm<K>, Vec<ProdId>>>,
) -> impl Iterator<Item = (NonTermId, &ExTerm<K>, &[ProdId])> {
    table.iter().flat_map(|(&non_term, m)| {
        m.iter().filter_map(move |(k, vec)| {
            if vec.len() > 1 {
                Some((non_term, k, vec.as_slice()))
            } else {
                None
            }
        })
    })
}

/// Produces FIRST/FOLLOW conflicts – i.e. the intersection FIRST(A) ∩ FOLLOW(A)
/// for every non‑terminal A.
pub fn get_first_follow_conflicts<K: Hash + Eq + Clone>(
    first: &HashMap<NonTermId, HashSet<ExTerm<K>>>,
    follow: &HashMap<NonTermId, HashSet<ExTerm<K>>>,
) -> impl Iterator<Item = (NonTermId, HashSet<ExTerm<K>>)> {
    first.iter().filter_map(|(&non_term, first)| {
        if !first.contains(&ExTerm::Empty) {
            return None;
        }
        let other = follow.get(&non_term)?;
        let mut ans = HashSet::new();
        for x in first {
            if other.contains(x) {
                ans.insert(x.clone());
            };
        }

        if ans.is_empty() {
            None
        } else {
            Some((non_term, ans))
        }
    })
}

#[derive(Debug, Clone)]
pub struct GrammerErrors<K> {
    pub first_first: Vec<(NonTermId, ExTerm<K>, Vec<ProdId>)>,
    pub first_follow: Vec<(NonTermId, HashSet<ExTerm<K>>)>,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct PeekInfo {
    pub peek_update: HashMap<NonTermId, HashSet<NonTermId>>,
    /// whether or not a non terminal peek the next input
    pub peeks: HashSet<NonTermId>,
}

impl PeekInfo {
    pub fn is_valid_macro<K>(&self, toks: &[Token<K>]) -> bool {
        match toks.last() {
            None | Some(Token::Eof) => false,
            Some(Token::NonTerm(id)) => !self.peeks.contains(id),
            _ => true,
        }
    }
    pub fn add_rule<K>(&mut self, id: NonTermId, toks: &[Token<K>]) {
        self.add_rules(core::iter::once((id, toks)))
    }
    pub fn add_rules<'a, K: 'a>(
        &mut self,
        rules: impl Iterator<Item = (NonTermId, &'a [Token<K>])>,
    ) {
        let mut ids = VecDeque::new();
        for (id, toks) in rules {
            if self.add_rule_static(id, toks) {
                ids.push_back(id);
            }
        }
        self.update_loop(ids)
    }
    fn add_rule_static<K>(&mut self, target: NonTermId, toks: &[Token<K>]) -> bool {
        match toks.last() {
            None | Some(Token::Eof) => self.peeks.insert(target),
            Some(Token::NonTerm(id)) => {
                if self.peek_update.entry(target).or_default().insert(*id) {
                    self.peeks.contains(id)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn update_loop(&mut self, mut ids: VecDeque<NonTermId>) {
        while let Some(id) = ids.pop_front() {
            if self.peeks.contains(&id) {
                for other in self.peek_update.entry(id).or_default().iter() {
                    if self.peeks.insert(*other) {
                        ids.push_back(*other);
                    }
                }
            }
        }
    }
}

/// holds the rules of a grammer and some metadata
/// the metadata is only valid after a call to the correct methods is issued
#[derive(Debug, Clone, PartialEq)]
pub struct LLGrammar<K: Eq + Hash + Clone> {
    /// production rules provided by the user
    pub rules: HashMap<NonTermId, Vec<TokList<K>>>,

    /// FIRST(A)  (includes `Empty` iff A is nullable)
    pub first: HashMap<NonTermId, HashSet<ExTerm<K>>>,

    /// FIRST(A) ⊇ FIRST(B)
    pub first_update: HashMap<NonTermId, HashSet<NonTermId>>,

    /// when A turns null which rules now have a new update
    pub null_pending: HashMap<NonTermId, Vec<(NonTermId, ProdId, usize)>>,

    /// First(w) for sequnces
    pub first_seq: HashMap<TokList<K>, HashSet<ExTerm<K>>>,

    /// FOLLOW(A) (may contain `ExTerm::Eof`)
    pub follow: HashMap<NonTermId, HashSet<ExTerm<K>>>,

    /// FOLLOW(A) ⊇ FOLLOW(B)
    pub follow_update: HashMap<NonTermId, HashSet<NonTermId>>,
    // whether or not a non terminal peek the next input
    // pub peeks: HashMap<NonTermId, bool>,
}

impl<K: Eq + Hash + Clone> Default for LLGrammar<K> {
    fn default() -> Self {
        Self {
            first: HashMap::new(),
            first_seq: HashMap::new(),
            follow: HashMap::new(),
            follow_update: HashMap::new(),
            null_pending:HashMap::new(),
            first_update:HashMap::new(),
            // peeks: HashMap::new(),
            rules: HashMap::new(),
        }
    }
}

impl<K: Eq + Hash + Clone> LLGrammar<K> {
    pub fn from_rules(iter: impl Iterator<Item = (NonTermId, TokList<K>)>) -> Self {
        let mut ans = Self::new();
        ans.add_rules(iter);
        ans
    }

    pub fn add_rules(&mut self, iter: impl Iterator<Item = (NonTermId, TokList<K>)>) {
        for (k, v) in iter {
            self.rules.entry(k).or_default().push(v);
        }
    }

    pub fn new() -> Self {
        Self::default()
    }

    /// Clears all previously computed information.
    pub fn flush(&mut self) {
        self.first.values_mut().for_each(HashSet::clear);
        self.first_update.values_mut().for_each(HashSet::clear);
        self.null_pending.clear();

        self.first_seq.clear();
        self.follow.values_mut().for_each(HashSet::clear);
        self.follow_update.values_mut().for_each(HashSet::clear);
        // self.peeks.clear();
    }

    /// updates peek using the exissting rules
    pub fn update_peek(&self, p: &mut PeekInfo) {
        p.add_rules(iterate_rules(&self.rules).map(|(i, r)| (i, &**r)));
    }

    /// Inserts **$** into FOLLOW(`id`).  Must be invoked **once** on the start
    /// symbol *before* [`LLGrammar::calculate_follow`].
    pub fn add_start(&mut self, id: NonTermId) {
        self.follow.entry(id).or_default().insert(ExTerm::Eof);
    }

    /// saves rule no update
    pub fn add_rule(self: &mut LLGrammar<K>, lhs: NonTermId, rhs: Rc<[Token<K>]>){
        self.rules.entry(lhs).or_default().push(rhs)
    }

    /// saves a rule updates all relvent info
    pub fn add_rule_update(self: &mut LLGrammar<K>, lhs: NonTermId, rhs: Rc<[Token<K>]>) {
        let v = self.rules.entry(lhs).or_default();
        let prod = v.len();
        v.push(rhs.clone());

        self.add_first_of(lhs,prod,&*rhs);
        self.add_follow_of(lhs,&*rhs)
    }

    /// Gets the first set of a slice
    /// **Dependencies:** depends on a valid [`LLGrammar::first`]
    pub fn get_first_set(&mut self, tokens: &[Token<K>]) -> &HashSet<ExTerm<K>> {
        get_first_set(tokens, &mut self.first_seq, &self.first)
    }

    /// Computes anything meaningful to compute without clearing any cache
    pub fn calculate(&mut self) {
        self.calculate_first();
        self.calculate_first_seqs();
        self.calculate_follow();
    }

    /// returns an unchecked prodction table with clashes
    /// **Dependencies:** depends on a valid [`LLGrammar::first`]
    pub fn get_prod_table(&mut self) -> HashMap<NonTermId, HashMap<ExTerm<K>, Vec<ProdId>>> {
        let mut ans = HashMap::new();
        for (id, prods) in self.rules.iter() {
            let a: &mut HashMap<ExTerm<K>, Vec<ProdId>> = ans.entry(*id).or_default();
            for (i, p) in prods.iter().enumerate() {
                let first = get_first_set(p, &mut self.first_seq, &self.first);
                for k in first {
                    a.entry(k.clone()).or_default().push(i)
                }
            }
        }
        ans
    }

    /// main entry use to check all possible errors and retrive a proper prod table
    /// **Dependencies:** depends on a valid [`LLGrammar::first`] and [`LLGrammar::follow`]
    pub fn get_checked_table(&mut self) -> Result<ProdTable<K>, GrammerErrors<K>> {
        let table = self.get_prod_table();
        let first_first: Vec<_> = get_first_first_conflicts(&table)
            .map(|(i, k, s)| (i, k.clone(), s.into()))
            .collect();

        let first_follow: Vec<_> = get_first_follow_conflicts(&self.first, &self.follow).collect();
        if first_first.is_empty() && first_follow.is_empty() {
            Ok(table
                .into_iter()
                .map(|(k, m)| {
                    (
                        k,
                        m.into_iter()
                            .filter_map(|(k2, v)| Some((k2, *v.first()?)))
                            .collect(),
                    )
                })
                .collect())
        } else {
            Err(GrammerErrors {
                first_first,
                first_follow,
            })
        }
    }

    ///makes sure the [`LLGrammar::first`] set is valid
    pub fn calculate_first(&mut self) {
        self.first_seq.clear();
        let v = self.calculate_first_part1();
        self.calculate_first_nulls(v.clone());
        self.calculate_first_rest(v)
        // self.calculate_first_non_terminals()
    }

    pub fn add_first_of(&mut self,target:NonTermId,prod:ProdId,tokens:&[Token<K>]) {
        self.first_seq.clear();
        let v = self.calculate_first_single(target,prod,tokens);
        self.calculate_first_nulls(v.clone());
        self.calculate_first_rest(v)
    }

    ///caches all grammer first sets rules into [`LLGrammar::first_seq`]
    pub fn calculate_first_seqs(&mut self) {
        for (_, tokens) in iterate_rules(&self.rules) {
            get_first_set_rc(tokens.clone(), &mut self.first_seq, &self.first);
        }
    }

    fn calculate_first_part1(&mut self) -> VecDeque<NonTermId> {
        let mut ans = VecDeque::new();

        for (target, prods) in self.rules.iter() {
            ans.push_back(*target);
            let set = self.first.entry(*target).or_default();

            for (i, tokens) in prods.iter().enumerate() {
                match tokens.first() {
                    None => {
                        set.insert(ExTerm::Empty);
                    }

                    Some(Token::Term(k)) => {
                        set.insert(ExTerm::Term(k.clone()));
                    }
                    Some(Token::Eof) => {
                        set.insert(ExTerm::Eof);
                    }

                    Some(Token::NonTerm(id)) => {
                        self.first_update.entry(*id).or_default().insert(*target);
                        self.null_pending
                            .entry(*id)
                            .or_default()
                            .push((*target, i, 0));
                    }
                }
            }
        }

        ans
    }

    fn calculate_first_single(&mut self,target:NonTermId,prod:ProdId,tokens:&[Token<K>]) -> VecDeque<NonTermId> {
        let mut ans = VecDeque::new();
        ans.push_back(target);
        let set = self.first.entry(target).or_default();
        
        match tokens.first() {
            None => {
                set.insert(ExTerm::Empty);
            }

            Some(Token::Term(k)) => {
                set.insert(ExTerm::Term(k.clone()));
            }
            Some(Token::Eof) => {
                set.insert(ExTerm::Eof);
            }

            Some(Token::NonTerm(id)) => {
                self.first_update.entry(*id).or_default().insert(target);
                self.null_pending
                    .entry(*id)
                    .or_default()
                    .push((target, prod, 0));
            }
        }
        ans
    }

    fn calculate_first_nulls(&mut self, mut queue: VecDeque<NonTermId>) {
        while let Some(id) = queue.pop_front() {
            if self.first[&id].contains(&ExTerm::Empty) {
                let Some(s) = self.null_pending.get(&id) else {
                    continue;
                };
                let iter: Vec<_> =s.iter().cloned().collect();
                'outer: for (other, prodid, mut loc) in iter {
                    let toks = self.rules[&other][prodid].clone();
                    while let Some(t) = toks.get(loc){
                        match t{
                            Token::Term(k)=>{
                                self.first.entry(other).or_default().insert(ExTerm::Term(k.clone())); 
                                continue 'outer

                            },
                            Token::Eof => {
                                self.first.entry(other).or_default().insert(ExTerm::Eof); 
                                continue 'outer
                            }
                            Token::NonTerm(r) => {
                                self.first_update.entry(*r).or_default().insert(other);
                                if self.first.entry(*r).or_default().contains(&ExTerm::Empty){
                                    loc+=1;
                                    continue;
                                }

                                self.null_pending.entry(*r).or_default().push((other, prodid, loc));
                                continue 'outer

                            } 
                        }
                    }

                    self.first.entry(other).or_default().insert(ExTerm::Empty);
                    queue.push_back(other);
                }
            }
        }
    }

    fn calculate_first_rest(&mut self, mut queue: VecDeque<NonTermId>){
        let mut in_queue = HashSet::new();
        for i in queue.iter().cloned(){
            in_queue.insert(i);
        }

        while let Some(id) = queue.pop_front(){
            in_queue.remove(&id);
            let Some(targets) = self.first_update.get(&id) else{
                continue;
            };
            let Some(first) = self.first.get(&id) else{
                continue;
            };

            let first :Vec<_>= first.iter().cloned().collect();

            for other in targets {
                let set = self.first.entry(*other).or_default();
                let mut changed = false;
                for t in first.iter() {
                    if *t!=ExTerm::Empty{
                        changed|=set.insert(t.clone());
                    }
                }

                if changed && in_queue.insert(*other) {
                    queue.push_back(*other);
                }
            }
        }
    }

    ///makes sure the [`LLGrammar::follow`] set is valid
    ///**Dependencies:** depends on a valid [`LLGrammar::first`]
    pub fn calculate_follow(&mut self) {
        self.calculate_follow_pass1();

        let queue: VecDeque<NonTermId> = self.follow.keys().copied().collect();
        self.calculate_follow_pass2(queue)
    }

    ///add a specific productions follow set
    ///**Dependencies:** depends on a valid [`LLGrammar::first`] that has the new first tokens
    /// as well as [`LLGrammar::follow`] with previous tokens
    pub fn add_follow_of(&mut self, id: NonTermId, tokens: &[Token<K>]) {
        self.follow.entry(id).or_default();
        update_follow_con(
            id,
            tokens,
            &self.first,
            &mut self.first_seq,
            &mut self.follow,
            &mut self.follow_update,
        );

        let queue: VecDeque<NonTermId> = core::iter::once(id).collect();
        self.calculate_follow_pass2(queue)
    }

    fn calculate_follow_pass1(&mut self) {
        self.follow_update.clear();
        for (target, tokens) in iterate_rules(&self.rules) {
            update_follow_con(
                target,
                tokens,
                &self.first,
                &mut self.first_seq,
                &mut self.follow,
                &mut self.follow_update,
            );
        }
    }

    fn calculate_follow_pass2(&mut self, mut queue: VecDeque<NonTermId>) {
        let mut in_queue: HashSet<NonTermId> = queue.iter().copied().collect();

        while let Some(u) = queue.pop_front() {
            in_queue.remove(&u);

            // clone is cheap: just the pointers & hashes, not the Sym values
            let src: Vec<ExTerm<K>> = self.follow[&u].iter().cloned().collect();

            // for every edge  u → v
            if let Some(dests) = self.follow_update.get(&u) {
                for &v in dests {
                    let dest = self.follow.entry(v).or_default();

                    // merge src into dest, remember whether dest changed
                    let mut grew = false;
                    for sym in &src {
                        if dest.insert(sym.clone()) {
                            grew = true;
                        }
                    }

                    // if FOLLOW(v) grew, (re)-enqueue v exactly once
                    if grew && in_queue.insert(v) {
                        queue.push_back(v);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{ExTerm, LLGrammar, NonTermId, TokList, Token};
    use crate::check::PeekInfo;
    use alloc::rc::Rc;
    use hashbrown::HashSet;

    /// Convenience: turn a slice into the `Rc<[Token<K>]>` expected by `LLGrammar`
    fn rc<K: Clone>(v: &[Token<K>]) -> TokList<K> {
        Rc::from(v.to_vec().into_boxed_slice())
    }

    /// Helper to insert a single-production rule
    fn add_rule<K: Eq + core::hash::Hash + Clone>(
        g: &mut LLGrammar<K>,
        lhs: NonTermId,
        rhs: &[Token<K>],
    ) {
        // g.rules.entry(lhs).or_default().push(rc(rhs));
        g.add_rule(lhs,rc(rhs))
    }

    fn set<T: Eq + core::hash::Hash>(xs: &[T]) -> HashSet<T>
    where
        T: Clone,
    {
        xs.iter().cloned().collect()
    }

    #[test]
    fn macro_safety_edge_cases() {
        // Grammar 0: S → 'a'
        let mut g0: PeekInfo = PeekInfo::default();
        g0.add_rule(0, &[Token::Term('a')]);
        assert!(
            g0.is_valid_macro(&[Token::Term('a')]),
            "terminal tail should be macro‑safe"
        );

        // Grammar 1: S → A; A → ε | 'a'
        let mut g1: PeekInfo = PeekInfo::default();
        g1.add_rule(0, &[Token::<char>::NonTerm(1)]); // S → A
        g1.add_rule::<char>(1, &[]); // A → ε
        g1.add_rule(1, &[Token::Term('a')]); // A → 'a'
        assert!(
            !g1.is_valid_macro(&[Token::<char>::NonTerm(1)]),
            "nullable tail must be rejected for macro safety"
        );

        // Grammar 2: A → 'a' A | 'a'  (right recursion)
        let mut g2: PeekInfo = PeekInfo::default();
        g2.add_rule(0, &[Token::Term('a'), Token::NonTerm(0)]);
        g2.add_rule(0, &[Token::Term('a')]);
        assert!(
            g2.is_valid_macro(&[Token::Term('a'), Token::NonTerm(0)]),
            "recursive production should be macro‑safe"
        );
        assert!(
            g2.is_valid_macro(&[Token::Term('a'), Token::NonTerm(0)]),
            "base production should be macro‑safe"
        );

        // Grammar 3: A → B; B → C; C → 'c'  (multi-hop chain)
        let mut g3: PeekInfo = PeekInfo::default();
        g3.add_rule(0, &[Token::<char>::NonTerm(1)]); // A → B
        g3.add_rule(1, &[Token::<char>::NonTerm(2)]); // B → C
        g3.add_rule(2, &[Token::Term('c')]); // C → 'c'
        assert!(
            g3.is_valid_macro(&[Token::<char>::NonTerm(1)]),
            "A’s production should be macro‑safe via B→C→'c'"
        );
        assert!(
            g3.is_valid_macro(&[Token::<char>::NonTerm(2)]),
            "B’s production should be macro‑safe via C→'c'"
        );
        assert!(
            g3.is_valid_macro(&[Token::Term('c')]),
            "C’s production is trivially macro‑safe"
        );
    }

    /// JSON‑like grammar exercising nullable tails, deep recursion,
    /// multi‑hop chains, and token‑ending alternatives.
    ///
    /// Non‑terminal numbering
    ///  0 VALUE        5 PAIR
    ///  1 OBJECT       6 ARRAY
    ///  2 OPTMEMBERS   7 OPTVALUES
    ///  3 MEMBERS      8 VALUES
    ///  4 RESTMEMBERS  9 RESTVALUES
    ///
    /// Terminals (as chars):
    ///  '{' '}' '[' ']' ',' ':' 's' (string) 'n' (number)
    #[test]
    fn macro_safety_json_like() {
        let mut peek = PeekInfo::default();

        // VALUE → OBJECT | ARRAY | 's' | 'n'
        peek.add_rule(0, &[Token::<char>::NonTerm(1)]);
        peek.add_rule(0, &[Token::<char>::NonTerm(6)]);
        peek.add_rule(0, &[Token::Term('s')]);
        peek.add_rule(0, &[Token::Term('n')]);

        // OBJECT → '{' OPTMEMBERS '}'
        peek.add_rule(1, &[Token::Term('{'), Token::NonTerm(2), Token::Term('}')]);

        // OPTMEMBERS → MEMBERS | ε
        peek.add_rule(2, &[Token::<char>::NonTerm(3)]);
        peek.add_rule::<u32>(2, &[]);

        // MEMBERS → PAIR RESTMEMBERS
        peek.add_rule(3, &[Token::<char>::NonTerm(5), Token::<char>::NonTerm(4)]);

        // RESTMEMBERS → ',' PAIR RESTMEMBERS | ε
        peek.add_rule(
            4,
            &[
                Token::Term(','),
                Token::<char>::NonTerm(5),
                Token::<char>::NonTerm(4),
            ],
        );
        peek.add_rule::<i8>(4, &[]);

        // PAIR → 's' ':' VALUE
        peek.add_rule(
            5,
            &[
                Token::Term('s'),
                Token::Term(':'),
                Token::<char>::NonTerm(0),
            ],
        );

        // ARRAY → '[' OPTVALUES ']'
        peek.add_rule(
            6,
            &[
                Token::Term('['),
                Token::<char>::NonTerm(7),
                Token::Term(']'),
            ],
        );

        // OPTVALUES → VALUES | ε
        peek.add_rule(7, &[Token::<char>::NonTerm(8)]);
        peek.add_rule::<char>(7, &[]);

        // VALUES → VALUE RESTVALUES
        peek.add_rule(8, &[Token::<char>::NonTerm(0), Token::<char>::NonTerm(9)]);

        // RESTVALUES → ',' VALUE RESTVALUES | ε
        peek.add_rule(
            9,
            &[
                Token::Term(','),
                Token::<char>::NonTerm(0),
                Token::<char>::NonTerm(9),
            ],
        );
        peek.add_rule::<char>(9, &[]);

        // ------------------------------------------------------------------
        // EXPECTED MACRO‑SAFETY RESULTS
        // ------------------------------------------------------------------

        // SAFE productions (pass the actual token arrays directly)
        assert!(peek.is_valid_macro(&[
            Token::Term('{'),
            Token::<char>::NonTerm(2),
            Token::Term('}')
        ])); // OBJECT → … '}'

        assert!(peek.is_valid_macro(&[
            Token::Term('['),
            Token::<char>::NonTerm(7),
            Token::Term(']')
        ])); // ARRAY  → … ']'

        assert!(peek.is_valid_macro(&[
            Token::Term('s'),
            Token::Term(':'),
            Token::<char>::NonTerm(0)
        ])); // PAIR   → … VALUE

        // VALUE alternatives ending in terminals are SAFE
        assert!(peek.is_valid_macro(&[Token::Term('s')])); // VALUE → 's'
        assert!(peek.is_valid_macro(&[Token::Term('n')])); // VALUE → 'n'

        // UNSAFE: tails are nullable chains
        assert!(!peek.is_valid_macro(&[Token::<char>::NonTerm(3)])); // OPTMEMBERS → MEMBERS
        assert!(!peek.is_valid_macro(&[
            Token::Term(','),
            Token::<char>::NonTerm(5),
            Token::<char>::NonTerm(4)
        ])); // RESTMEMBERS recursive
        assert!(!peek.is_valid_macro::<char>(&[])); // RESTMEMBERS → ε
    }

    // --------------------------------------------------------------------------

    #[test]
    fn first_and_nullable_propagation() {
        // Non‑terminal indices for readability
        const S: usize = 0;
        const A: usize = 1;
        const B: usize = 2;
        const C: usize = 3;
        const Z: usize = 4;

        // Build grammar (same structure as before, just easier to read)
        //
        //   S → A B
        //   A → ε | 'a'
        //   B → C | 'b'
        //   C → ε
        //   Z → $
        //
        let mut g: LLGrammar<char> = LLGrammar::new();

        // S
        add_rule(&mut g, S, &[Token::NonTerm(A), Token::NonTerm(B)]);

        // A
        add_rule(&mut g, A, &[]); // ε
        add_rule(&mut g, A, &[Token::Term('a')]); // 'a'

        // B
        add_rule(&mut g, B, &[Token::NonTerm(C)]); // C
        add_rule(&mut g, B, &[Token::Term('b')]); // 'b'

        // C
        add_rule(&mut g, C, &[]); // ε

        // Z
        add_rule(&mut g, Z, &[Token::Eof]); // $

        g.calculate_first();
        g.calculate_first_seqs();

        // ---------------- EXPECTED RESULTS ------------------------------------

        // FIRST(A) = { ε, 'a' }
        assert_eq!(
            &g.first[&A],
            &set(&[ExTerm::Empty, ExTerm::Term('a')]),
            "FIRST(A)"
        );

        // FIRST(B) = { ε, 'b' }
        assert_eq!(
            &g.first[&B],
            &set(&[ExTerm::Empty, ExTerm::Term('b')]),
            "FIRST(B)"
        );

        // FIRST(S) = { 'a', 'b' }   (A may ε so ε dropped, then B contributes)
        assert_eq!(
            &g.first[&S],
            &set(&[ExTerm::Term('a'), ExTerm::Term('b'), ExTerm::Empty]),
            "FIRST(S)"
        );

        // FIRST(Z) = { $ }
        assert_eq!(&g.first[&Z], &set(&[ExTerm::Eof]), "FIRST(Z)");
    }

    // -------------------------------------------------------------------------

    #[test]
    fn follow_various_cases() {
        // Index constants so the rules stay readable
        const S: usize = 0;
        const A: usize = 1;
        const B: usize = 2;
        const C: usize = 3;

        // ---------------------------------------------------------------------
        // Grammar under test
        //
        //   S  →  A B           (nullable A, nullable B => ε in FOLLOW propagation)
        //   A  →  ε  | 'a'
        //   B  →  C  | 'b'
        //   C  →  ε
        //
        // ---------------------------------------------------------------------
        let mut g: LLGrammar<char> = LLGrammar::new();

        // S rules
        add_rule(&mut g, S, &[Token::NonTerm(A), Token::NonTerm(B)]);

        // A rules
        add_rule(&mut g, A, &[]);
        add_rule(&mut g, A, &[Token::Term('a')]);

        // B rules
        add_rule(&mut g, B, &[Token::NonTerm(C)]);
        add_rule(&mut g, B, &[Token::Term('b')]);

        // C rules
        add_rule(&mut g, C, &[]);

        //----------------------------------------------------------------------
        // 1.  FIRST + nullable (required before FOLLOW)
        //----------------------------------------------------------------------
        g.calculate_first();
        g.calculate_first_seqs();

        //----------------------------------------------------------------------
        // 2.  FOLLOW
        //----------------------------------------------------------------------
        g.add_start(S);
        g.calculate_follow();

        // FOLLOW(S) = { '$', $ }  ($ from seed, '$' from Z‑rule terminal)
        assert_eq!(g.follow[&S], set(&[ExTerm::Eof]));

        // FOLLOW(A) = { 'b', '$', $ }
        //   - 'b' : from S → A B  (terminal immediately after A)
        //   - '$' + $ : because A nullable, B nullable, so FOLLOW(S) propagates
        assert_eq!(g.follow[&A], set(&[ExTerm::Term('b'), ExTerm::Eof]));

        // FOLLOW(B) = { '$', $ }  (terminal after S, plus EOF via S)
        assert_eq!(g.follow[&B], set(&[ExTerm::Eof]));

        // FOLLOW(C) = { '$', $ }  (B → C •, then FOLLOW(B))
        assert_eq!(g.follow[&C], set(&[ExTerm::Eof]));

        // 3.  Sanity: No FOLLOW set contains ε
        for (nt, fset) in &g.follow {
            assert!(
                !fset.contains(&ExTerm::Empty),
                "FOLLOW({nt}) unexpectedly contains ε"
            );
        }
    }

    /// FIRST/FIRST:  S → 'a' A  |  'a' B   (same look‑ahead in two alternatives)
    #[test]
    fn detects_first_first_conflict() {
        const S: usize = 0;
        const A: usize = 1;
        const B: usize = 2;

        let mut g: LLGrammar<char> = LLGrammar::new();
        add_rule(&mut g, S, &[Token::Term('a'), Token::NonTerm(A)]);
        add_rule(&mut g, S, &[Token::Term('a'), Token::NonTerm(B)]);
        add_rule(&mut g, A, &[Token::Term('x')]);
        add_rule(&mut g, B, &[Token::Term('y')]);

        g.add_start(S);
        g.calculate();

        let err = g
            .get_checked_table()
            .expect_err("should hit FIRST/FIRST clash");
        assert!(
            err.first_first
                .iter()
                .any(|(nt, sym, _)| *nt == S && *sym == ExTerm::Term('a')),
            "expected FIRST/FIRST conflict on 'a' in S"
        );
        // No FIRST/FOLLOW problems in this grammar
        assert!(err.first_follow.is_empty());
    }

    /// FIRST/FOLLOW:  A derives 'x', and ‘x’ also follows A in S → A 'x'
    #[test]
    fn first_follow_false_conflict() {
        const S: usize = 0;
        const A: usize = 1;

        let mut g: LLGrammar<char> = LLGrammar::new();
        
        // A rule
        g.add_rule_update(A, [Token::Term('x')].into());

        // S rules
        g.add_start(S);
        g.add_rule_update(S, [Token::NonTerm(A), Token::Term('x')].into());
        g.add_rule_update(S, [Token::Term('y')].into());
        

        g.get_checked_table().unwrap();
    }

    /// FIRST/FOLLOW:  A derives 'x' and ε, and ‘x’ also follows A in S → A 'x'
    #[test]
    fn detects_first_follow_conflict() {
        const S: usize = 0;
        const A: usize = 1;

        let mut g: LLGrammar<char> = LLGrammar::new();

        // S rules
        g.add_start(S);
        g.add_rule_update(S, [Token::NonTerm(A), Token::Term('x')].into());
        g.add_rule_update(S, [Token::Term('y')].into());

        // A rule
        g.add_rule_update(A, [Token::Term('x')].into());
        g.add_rule_update(A, [].into());

        let err = g
            .get_checked_table()
            .expect_err("should hit FIRST/FOLLOW clash");
        assert!(
            err.first_follow
                .iter()
                .any(|(nt, overlap)| *nt == A && overlap.contains(&ExTerm::Term('x'))),
            "expected FIRST/FOLLOW conflict on 'x' for A"
        );
        // No FIRST/FIRST problems in this grammar
        assert!(err.first_first.is_empty());
    }
}
