use crate::parser::Terminal;
use core::hash::Hash;
use crate::parser::Token as PToken;
use alloc::rc::Rc;
use alloc::vec::Vec;
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



impl<T: Terminal, F1: Fn(&mut State, T), State> From<PToken<T,F1, State>> for Token<T::Key> {
    fn from(tok:PToken<T,F1, State>) -> Self {
        match tok {
            PToken::Term { key, ..}=>Token::Term(key),
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

pub struct ProdMeta<K>{
    pub tokens: TokList<K>,
    pub last_idx: usize,//we need overflow to be fine
    pub first_idx: usize,
}

pub struct UpdateInfo {
    pub first_updates: Vec<NonTermId>,
    pub first_null_updates: Vec<(NonTermId,usize)>,
    pub follow_updates: Vec<NonTermId>,
    pub follow_null_updates: Vec<(NonTermId,usize)>,
}

/// holds the rules of a grammer and some metadata
/// the metadata is only valid after a call to the correct methods is issued
#[derive(Debug, Clone, PartialEq)]
pub struct LLGrammar<K: Eq + Hash + Clone> {
    /// production rules provided by the user
    pub rules: HashMap<NonTermId, Vec<TokList<K>>>,

    /// FIRST(A)  (includes `Empty` iff A is nullable)
    pub first: HashMap<NonTermId, HashSet<ExTerm<K>>>,

    pub first_seq: HashMap<TokList<K>, HashSet<ExTerm<K>>>,

    /// FOLLOW(A) (may contain `ExTerm::Eof`)
    pub follow: HashMap<NonTermId, HashSet<ExTerm<K>>>,

    /// whether or not a non terminal does not peek the next input
    pub peeks: HashMap<NonTermId, bool>,
}

impl<K: Eq + Hash + Clone> Default for LLGrammar<K> {
    fn default() -> Self {
        Self {
            first: HashMap::new(),
            first_seq: HashMap::new(),
            follow: HashMap::new(),
            peeks: HashMap::new(),
            rules: HashMap::new(),
        }
    }
}

impl<K: Eq + Hash + Clone> LLGrammar<K> {
    pub fn from_rules(iter:impl Iterator<Item = (NonTermId,TokList<K>)>)->Self{
        let mut ans = Self::new();
        ans.add_rules(iter);
        ans
    }

    pub fn add_rules(&mut self, iter:impl Iterator<Item = (NonTermId,TokList<K>)>){
        for (k,v) in iter {
            self.rules.entry(k).or_default().push(v);
        }
    }

    pub fn new() -> Self {
        Self::default()
    }

    /// Clears all previously computed information.
    pub fn flush(&mut self) {
        self.first.values_mut().for_each(HashSet::clear);
        self.first_seq.clear();
        self.follow.values_mut().for_each(HashSet::clear);
        self.peeks.clear();
    }

    /// Checks if a rule is valid to be used as a macro (ie changing the input)
    /// **Dependencies:** caches results to peeks
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
}