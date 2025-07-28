//! ll1_check.rs  –  incremental FIRST/FOLLOW checker for any LL(1) backend
//!
//!  •No assumptions about the concrete parser implementation
//!  •All non‑terminals are addressed by `NonTermId` (usize alias)
//!  •Terminals travel through `ExTerm<K>` so EOF / ε are represented
//!

use crate::check::hash::Hash;
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::hash;
use hashbrown::hash_map::Entry;
use hashbrown::hash_table::OccupiedEntry;
use hashbrown::{HashMap, HashSet};

pub type NonTermId = usize;

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token<K> {
    /// synthetic end‑of‑input symbol ($)
    Eof,
    /// real token coming from the user’s lexer
    Term(K),

    /// derived token
    NonTerm(NonTermId),
}

pub type TokList<K> = Rc<[Token<K>]>;

#[inline(always)]
pub fn iterate_rules<K>(
    rules: &HashMap<NonTermId, Vec<TokList<K>>>,
) -> impl Iterator<Item = (NonTermId, &TokList<K>)> {
    rules
        .iter()
        .map(|(k, v)| v.iter().map(|x| (*k, x)))
        .flatten()
}

fn calculate_peeks<K>(
    toks: &[Token<K>],
    rules: &HashMap<NonTermId, Vec<TokList<K>>>,
    peeks: &mut HashMap<NonTermId, bool>,
    visited: &mut HashSet<NonTermId>,
) -> bool {
    let Some(t) = toks.last() else {
        return false;
    };

    let id = match t {
        Token::Eof => return false,
        Token::Term(_) => return true,
        Token::NonTerm(id) => id,
    };

    if !visited.insert(*id) {
        //be optimistic to avoid cycles
        //however for the outer call this is valid
        return true;
    }

    if let Some(ans) = peeks.get(id) {
        return *ans;
    }

    for toks in rules[id].iter() {
        if !calculate_peeks(toks, rules, peeks, visited) {
            peeks.insert(*id, false);
            return false;
        }
    }

    //we cant update since we have false positives
    //final result should be good though
    true
}

/// holds the rules of a grammer and some metadata
/// the metadata is only valid after a call to the correct methods is issued
#[derive(Debug, Clone, PartialEq)]
pub struct IncSets<K: Eq + Hash + Clone> {
    /// production rules provided by the user
    pub rules: HashMap<NonTermId, Vec<TokList<K>>>,

    /// FIRST(A)  (includes `Empty` iff A is nullable)
    pub first: HashMap<NonTermId, HashSet<ExTerm<K>>>,

    /// FOLLOW(A) (may contain `ExTerm::Eof`)
    pub follow: HashMap<NonTermId, HashSet<ExTerm<K>>>,

    /// whether or not a non terminal does not peek the next input
    pub peeks: HashMap<NonTermId, bool>,
}

impl<K: Eq + Hash + Clone> Default for IncSets<K> {
    fn default() -> Self {
        Self {
            first: HashMap::new(),
            follow: HashMap::new(),
            peeks: HashMap::new(),
            rules: HashMap::new(),
        }
    }
}

impl<K: Eq + Hash + Clone> IncSets<K> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Clears all previously computed information.
    pub fn flush(&mut self) {
        self.first.values_mut().for_each(HashSet::clear);
        self.follow.values_mut().for_each(HashSet::clear);
        self.peeks.clear();
    }

    pub fn add_start(&mut self,id:NonTermId){
        self.follow.entry(id).or_default().insert(ExTerm::Eof);
    }

    /// Checks if a rule is valid to be used as a macro (ie changing the input)
    pub fn is_valid_macro(&mut self, toks: &[Token<K>]) -> bool {
        let Some(t) = toks.last() else {
            return false;
        };

        let id = match t {
            Token::Eof => return false,
            Token::Term(_) => return true,
            Token::NonTerm(id) => id,
        };

        if let Some(ans) = self.peeks.get(id) {
            return *ans;
        }

        let mut visited = HashSet::new();
        let ans = calculate_peeks(toks, &self.rules, &mut self.peeks, &mut visited);
        if ans {
            //now we have checked all last extended terminals are not empty
            //this means that all visited non terminals are also non empty
            for id in visited {
                self.peeks.insert(id, true);
            }
        }

        ans
    }

    pub fn first_set_of(&self, tokens: &[Token<K>]) -> HashSet<ExTerm<K>> {
        let mut ans = HashSet::new();
        for t in tokens {
            match t {
                Token::Eof => {
                    ans.insert(ExTerm::Eof);
                    return ans;
                }
                Token::Term(k) => {
                    ans.insert(ExTerm::Term(k.clone()));
                    return ans;
                }
                Token::NonTerm(id) => {
                    let first = &self.first[id];
                    if !first.contains(&ExTerm::Empty) {
                        ans.extend(first.iter().cloned());
                        return ans;
                    }

                    ans.extend(first.iter().filter(|x| **x != ExTerm::Empty).cloned());
                }
            };
        }

        ans.insert(ExTerm::Empty);
        ans
    }

    pub fn calculate(&mut self) {
        self.calculate_first();
        self.calculate_follow();
    }

    pub fn calculate_first(&mut self) {
        self.calculate_first_terminals();
        self.calculate_first_non_terminals()
    }

    pub fn calculate_first_terminals(&mut self) {
        for (target, prods) in self.rules.iter() {
            let set = self.first.entry(*target).or_default();

            for tokens in prods {
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

                    Some(Token::NonTerm(_)) => {}
                }
            }
        }
    }

    pub fn calculate_first_non_terminals(&mut self) {
        let mut changed = false;

        //we need all these entries there already
        // for id in self.rules.keys() {
        //     self.first.entry(*id).or_default();
        // }

        for (target, tokens) in iterate_rules(&self.rules) {
            //skip terminals since they were done already
            let Some(Token::NonTerm(id)) = tokens.first() else {
                continue;
            };

            //loop empty A style rules untill we get term A style
            let mut id = id;
            let mut loc = 0;
            loop {
                match self.first[id].contains(&ExTerm::Empty) {
                    false => {
                        let [Some(other), Some(me)] = self.first.get_many_mut([id, &target]) else {
                            break;
                        };

                        for item in other.iter().cloned() {
                            changed |= me.insert(item);
                        }

                        break;
                    }
                    true => {
                        if let [Some(other), Some(me)] = self.first.get_many_mut([id, &target]) {
                            for item in other.iter().cloned() {
                                if item != ExTerm::Empty {
                                    changed |= me.insert(item);
                                }
                            }
                        };

                        loc += 1;
                        match tokens.get(loc) {
                            None => {
                                changed |=
                                    self.first.get_mut(&target).unwrap().insert(ExTerm::Empty);
                                break;
                            }
                            Some(Token::NonTerm(new_id)) => {
                                id = new_id;
                            }
                            Some(Token::Eof) => {
                                changed |= self.first.get_mut(&target).unwrap().insert(ExTerm::Eof);
                                break;
                            }
                            Some(Token::Term(k)) => {
                                changed |= self
                                    .first
                                    .get_mut(&target)
                                    .unwrap()
                                    .insert(ExTerm::Term(k.clone()));
                                break;
                            }
                        }
                    }
                }
            }
        }

        if changed == true {
            self.calculate_first_non_terminals()
        }
    }

    pub fn calculate_follow(&mut self){
        for id in self.rules.keys() {
            self.follow.entry(*id).or_default();
        }

        self._calculate_follow()
    }
    fn _calculate_follow(&mut self) {
        let mut changed = false;

        for (target, tokens) in iterate_rules(&self.rules) {
            let mut first = HashSet::new();
            first.insert(ExTerm::Empty);

            for t in tokens.iter().rev() {
                match t {
                    Token::Term(k) => {
                        first.clear();
                        first.insert(ExTerm::Term(k.clone()));
                    }
                    Token::Eof => {
                        first.clear();
                        first.insert(ExTerm::Eof);
                    }
                    Token::NonTerm(id) => {
                        let spot = self.follow.get_mut(id).unwrap();
                        for x in first.iter(){
                            if *x == ExTerm::Empty {
                                continue;
                            }
                            changed|=spot.insert(x.clone());
                        }

                        if first.contains(&ExTerm::Empty){
                            if let [Some(prod),Some(tgt)] = self.follow.get_many_mut([id,&target]) {
                                for x in tgt.iter() {
                                    changed|=prod.insert(x.clone());
                                }
                            }
                        }

                        //maintain an accurate first
                        let other_first = &self.first[id]; 
                        if other_first.contains(&ExTerm::Empty){
                            first.extend(other_first.iter().filter(|x| **x!=ExTerm::Empty).cloned())
                        }else{
                            first.clone_from(other_first);
                        }
                        
                    },
                }
            }


        }

        if changed == true {
            self._calculate_follow()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{IncSets, NonTermId, TokList, Token};
    use alloc::rc::Rc;

    /// Convenience: turn a slice into the `Rc<[Token<K>]>` expected by `IncSets`
    fn rc<K: Clone>(v: &[Token<K>]) -> TokList<K> {
        Rc::from(v.to_vec().into_boxed_slice())
    }

    /// Helper to insert a single-production rule
    fn add_rule<K: Eq + core::hash::Hash + Clone>(
        g: &mut IncSets<K>,
        lhs: NonTermId,
        rhs: &[Token<K>],
    ) {
        g.rules.entry(lhs).or_default().push(rc(rhs));
    }

    #[test]
    fn macro_safety_edge_cases() {
        // Grammar 0: S → 'a'
        let mut g0: IncSets<char> = IncSets::new();
        add_rule(&mut g0, 0, &[Token::Term('a')]);
        assert!(
            g0.is_valid_macro(&g0.rules[&0][0].clone()),
            "terminal tail should be macro‑safe"
        );

        // Grammar 1: S → A; A → ε | 'a'
        let mut g1: IncSets<char> = IncSets::new();
        add_rule(&mut g1, 0, &[Token::NonTerm(1)]); // S → A
        add_rule(&mut g1, 1, &[]); // A → ε
        add_rule(&mut g1, 1, &[Token::Term('a')]); // A → 'a'
        assert!(
            !g1.is_valid_macro(&g1.rules[&0][0].clone()),
            "nullable tail must be rejected for macro safety"
        );

        // Grammar 2: A → 'a' A | 'a'  (right recursion)
        let mut g2: IncSets<char> = IncSets::new();
        add_rule(&mut g2, 0, &[Token::Term('a'), Token::NonTerm(0)]);
        add_rule(&mut g2, 0, &[Token::Term('a')]);
        assert!(
            g2.is_valid_macro(&g2.rules[&0][0].clone()),
            "recursive production should be macro‑safe"
        );
        assert!(
            g2.is_valid_macro(&g2.rules[&0][1].clone()),
            "base production should be macro‑safe"
        );

        // Grammar 3: A → B; B → C; C → 'c'  (multi-hop chain)
        let mut g3: IncSets<char> = IncSets::new();
        add_rule(&mut g3, 0, &[Token::NonTerm(1)]); // A → B
        add_rule(&mut g3, 1, &[Token::NonTerm(2)]); // B → C
        add_rule(&mut g3, 2, &[Token::Term('c')]); // C → 'c'
        assert!(
            g3.is_valid_macro(&g3.rules[&0][0].clone()),
            "A’s production should be macro‑safe via B→C→'c'"
        );
        assert!(
            g3.is_valid_macro(&g3.rules[&1][0].clone()),
            "B’s production should be macro‑safe via C→'c'"
        );
        assert!(
            g3.is_valid_macro(&g3.rules[&2][0].clone()),
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
        let mut g: IncSets<char> = IncSets::new();

        // VALUE → OBJECT | ARRAY | 's' | 'n'
        add_rule(&mut g, 0, &[Token::NonTerm(1)]);
        add_rule(&mut g, 0, &[Token::NonTerm(6)]);
        add_rule(&mut g, 0, &[Token::Term('s')]);
        add_rule(&mut g, 0, &[Token::Term('n')]);

        // OBJECT → '{' OPTMEMBERS '}'
        add_rule(
            &mut g,
            1,
            &[Token::Term('{'), Token::NonTerm(2), Token::Term('}')],
        );

        // OPTMEMBERS → MEMBERS | ε
        add_rule(&mut g, 2, &[Token::NonTerm(3)]);
        add_rule(&mut g, 2, &[]);

        // MEMBERS → PAIR RESTMEMBERS
        add_rule(&mut g, 3, &[Token::NonTerm(5), Token::NonTerm(4)]);

        // RESTMEMBERS → ',' PAIR RESTMEMBERS | ε
        add_rule(
            &mut g,
            4,
            &[Token::Term(','), Token::NonTerm(5), Token::NonTerm(4)],
        );
        add_rule(&mut g, 4, &[]);

        // PAIR → 's' ':' VALUE
        add_rule(
            &mut g,
            5,
            &[Token::Term('s'), Token::Term(':'), Token::NonTerm(0)],
        );

        // ARRAY → '[' OPTVALUES ']'
        add_rule(
            &mut g,
            6,
            &[Token::Term('['), Token::NonTerm(7), Token::Term(']')],
        );

        // OPTVALUES → VALUES | ε
        add_rule(&mut g, 7, &[Token::NonTerm(8)]);
        add_rule(&mut g, 7, &[]);

        // VALUES → VALUE RESTVALUES
        add_rule(&mut g, 8, &[Token::NonTerm(0), Token::NonTerm(9)]);

        // RESTVALUES → ',' VALUE RESTVALUES | ε
        add_rule(
            &mut g,
            9,
            &[Token::Term(','), Token::NonTerm(0), Token::NonTerm(9)],
        );
        add_rule(&mut g, 9, &[]);

        // ------------------------------------------------------------------
        // EXPECTED MACRO‑SAFETY RESULTS
        // ------------------------------------------------------------------

        // Definitively SAFE productions
        assert!(g.is_valid_macro(&g.rules[&1][0].clone())); // OBJECT → … '}'      (tail is '}')
        assert!(g.is_valid_macro(&g.rules[&6][0].clone())); // ARRAY  → … ']'      (tail is ']')
        assert!(g.is_valid_macro(&g.rules[&5][0].clone())); // PAIR   → … VALUE    (VALUE always consumes)

        // VALUE alternatives ending in terminals are SAFE
        assert!(g.is_valid_macro(&g.rules[&0][2].clone())); // VALUE → 's'
        assert!(g.is_valid_macro(&g.rules[&0][3].clone())); // VALUE → 'n'

        // UNSAFE: tails are nullable chains
        assert!(!g.is_valid_macro(&g.rules[&2][0].clone())); // OPTMEMBERS → MEMBERS  (MEMBERS tail may ε)
        assert!(!g.is_valid_macro(&g.rules[&4][0].clone())); // RESTMEMBERS recursive alternative
        assert!(!g.is_valid_macro(&g.rules[&4][1].clone())); // RESTMEMBERS → ε
    }
}

#[cfg(test)]
mod first_sets {
    use super::{ExTerm, IncSets, Token};
    use alloc::rc::Rc;
    use hashbrown::HashSet; // shorter spelling

    // -------- helper utilities ------------------------------------------------
    fn rc<K: Clone>(v: &[Token<K>]) -> Rc<[Token<K>]> {
        Rc::from(v.to_vec().into_boxed_slice())
    }
    fn add_rule<K: Eq + core::hash::Hash + Clone>(
        g: &mut IncSets<K>,
        lhs: usize,
        rhs: &[Token<K>],
    ) {
        g.rules.entry(lhs).or_default().push(rc(rhs));
    }
    fn set<T: Eq + core::hash::Hash>(xs: &[T]) -> HashSet<T>
    where
        T: Clone,
    {
        xs.iter().cloned().collect()
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
        let mut g: IncSets<char> = IncSets::new();

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
}

#[cfg(test)]
mod follow_sets {
    use super::{IncSets, ExTerm, Token};
    use alloc::rc::Rc;
    use hashbrown::HashSet;

    // -------------------------------- helpers ---------------------------------
    fn rc<K: Clone>(v: &[Token<K>]) -> Rc<[Token<K>]> {
        Rc::from(v.to_vec().into_boxed_slice())
    }
    fn add_rule<K: Eq + core::hash::Hash + Clone>(
        g: &mut IncSets<K>,
        lhs: usize,
        rhs: &[Token<K>],
    ) {
        g.rules.entry(lhs).or_default().push(rc(rhs));
    }
    fn set<T: Eq + core::hash::Hash>(xs: &[T]) -> HashSet<T>
    where
        T: Clone,
    {
        xs.iter().cloned().collect()
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
        let mut g: IncSets<char> = IncSets::new();

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

        //----------------------------------------------------------------------
        // 2.  FOLLOW
        //----------------------------------------------------------------------
        g.add_start(S);
        g.calculate_follow();

        // FOLLOW(S) = { '$', $ }  ($ from seed, '$' from Z‑rule terminal)
        assert_eq!(
            g.follow[&S],
            set(&[ExTerm::Eof])
        );

        // FOLLOW(A) = { 'b', '$', $ }
        //   - 'b' : from S → A B  (terminal immediately after A)
        //   - '$' + $ : because A nullable, B nullable, so FOLLOW(S) propagates
        assert_eq!(
            g.follow[&A],
            set(&[ExTerm::Term('b'), ExTerm::Eof])
        );

        // FOLLOW(B) = { '$', $ }  (terminal after S, plus EOF via S)
        assert_eq!(
            g.follow[&B],
            set(&[ ExTerm::Eof])
        );

        // FOLLOW(C) = { '$', $ }  (B → C •, then FOLLOW(B))
        assert_eq!(
            g.follow[&C],
            set(&[ ExTerm::Eof])
        );


        // 3.  Sanity: No FOLLOW set contains ε
        for (nt, fset) in &g.follow {
            assert!(
                !fset.contains(&ExTerm::Empty),
                "FOLLOW({nt}) unexpectedly contains ε"
            );
        }
    }
}
