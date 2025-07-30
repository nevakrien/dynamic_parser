use crate::check::ExTerm;
use crate::check::GrammerErrors;
use crate::check::LLGrammar;
use crate::check::ProdTable;
use crate::check::Token as CToken;
use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt::Debug;
use core::hash::Hash;
use core::iter::Peekable;
use core::marker::PhantomData;
use hashbrown::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub struct ParseError<Term: Terminal> {
    pub found: Option<Term>,
    pub expected: Vec<Option<Term::Key>>,
}

pub trait Terminal {
    type Key: Eq + Hash + Clone + Debug;
    fn get_key(&self) -> Self::Key;
}

impl Terminal for u8 {
    type Key = u8;
    fn get_key(&self) -> u8 {
        *self
    }
}

impl Terminal for char {
    type Key = u32;
    fn get_key(&self) -> u32 {
        *self as u32
    }
}

pub type NonTermId = usize;

#[derive(Debug, PartialEq)]
pub enum Token<T: Terminal, F: Fn(&mut State, T), State> {
    Eof,
    Term {
        key: <T as Terminal>::Key,
        callback: Option<F>,
        _ph: PhantomData<State>,
    },
    NonTerm(NonTermId),
}

impl<T, F, State> Clone for Token<T, F, State>
where
    T: Terminal,
    F: Fn(&mut State, T) + Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::NonTerm(id) => Self::NonTerm(*id),
            Token::Eof => Token::Eof,
            Self::Term { key, callback, _ph } => Self::Term {
                key: key.clone(),
                callback: callback.clone(),
                _ph: *_ph,
            },
        }
    }
}
pub trait CallBack<Term, State, F2>: Clone
where
    Term: Terminal,
    F2: Fn(&mut State, Term),
{
    fn call(&self, state: &mut State, parser: &mut Parser<Term, State, Self, F2>);
}

#[derive(Debug, PartialEq)]
pub struct Prod<Term, State, F1, F2>
where
    Term: Terminal,
    F1: CallBack<Term, State, F2>,
    F2: Fn(&mut State, Term),
{
    elements: Rc<[Token<Term, F2, State>]>,
    callback: Option<F1>,
    _ph: PhantomData<dyn Fn(&mut State)>,
}

impl<Term, State, F1, F2> Prod<Term, State, F1, F2>
where
    Term: Terminal,
    F1: CallBack<Term, State, F2>,
    F2: Fn(&mut State, Term),
{
    pub fn into_grammar(&self) -> Rc<[CToken<Term::Key>]> {
        self.elements
            .iter()
            .map(|e| match e {
                Token::Term { key, .. } => CToken::Term(key.clone()),
                Token::NonTerm(id) => CToken::NonTerm(*id),
                Token::Eof => CToken::Eof,
            })
            .collect()
    }
}

impl<Term, State, F1, F2> Clone for Prod<Term, State, F1, F2>
where
    Term: Terminal,
    F1: CallBack<Term, State, F2>,
    F2: Fn(&mut State, Term) + Clone,
{
    fn clone(&self) -> Self {
        Self {
            elements: self.elements.clone(),
            callback: self.callback.clone(),
            _ph: self._ph,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParseTable<Term, State, F1, F2>
where
    Term: Terminal,
    F1: CallBack<Term, State, F2>,
    F2: Fn(&mut State, Term),
{
    explicit: HashMap<<Term as Terminal>::Key, Prod<Term, State, F1, F2>>,
    empty: Option<Prod<Term, State, F1, F2>>,
    eof: Option<Prod<Term, State, F1, F2>>,
}

impl<Term, State, F1, F2> Default for ParseTable<Term, State, F1, F2>
where
    Term: Terminal,
    F1: CallBack<Term, State, F2>,
    F2: Fn(&mut State, Term),
{
    fn default() -> Self {
        Self {
            explicit: HashMap::new(),
            empty: None,
            eof: None,
        }
    }
}

impl<Term, State, F1, F2> ParseTable<Term, State, F1, F2>
where
    Term: Terminal,
    F1: CallBack<Term, State, F2>,
    F2: Fn(&mut State, Term),
{
    pub fn get_prod(&self, key: Option<&Term::Key>) -> Option<&Prod<Term, State, F1, F2>> {
        match key {
            None => self.eof.as_ref().or(self.empty.as_ref()),
            // None => self.empty.as_ref(),
            Some(t) => self.explicit.get(t).or(self.empty.as_ref()),
        }
    }
}

pub type ProdMap<T, State, F1, F2> = HashMap<NonTermId, ParseTable<T, State, F1, F2>>;

#[derive(Debug, Clone, PartialEq)]
pub struct Parser<Term, State, F1, F2>
where
    Term: Terminal,
    F1: CallBack<Term, State, F2>,
    F2: Fn(&mut State, Term),
{
    pub productions: ProdMap<Term, State, F1, F2>,
}

impl<Term, State, F1, F2> Parser<Term, State, F1, F2>
where
    Term: Terminal,
    F1: CallBack<Term, State, F2> + Clone,
    F2: Fn(&mut State, Term),
{
    pub fn parse(
        &mut self,
        target: NonTermId,
        state: &mut State,
        input: &mut impl Iterator<Item = Term>,
    ) -> Result<(), ParseError<Term>> {
        let mut input = input.peekable();
        // self.partial_parse(target, state, &mut input)
        self.partial_parse(target, state, &mut input)?;

        //on a proper grammar this never happens
        //however if someone forgot EOF on the target this does happen
        //note that in that case we also have potential infinite loops
        match input.next() {
            None => Ok(()),
            Some(found) => Err(ParseError {
                found: Some(found),
                expected: vec![None],
            }),
        }
    }

    pub fn partial_parse(
        &mut self,
        target: NonTermId,
        state: &mut State,
        input: &mut Peekable<impl Iterator<Item = Term>>,
    ) -> Result<(), ParseError<Term>> {
        let table = &self.productions[&target];
        let key = input.peek().map(|x| x.get_key());

        let Some(prod) = table.get_prod(key.as_ref()) else {
            let expected: Vec<_> = table.explicit.keys().map(|x| Some(x.clone())).collect();

            return Err(ParseError {
                found: input.next(),
                expected,
            });
        };
        let callback = prod.callback.clone();

        for e in prod.elements.clone().iter() {
            match e {
                Token::Eof => {
                    if let Some(found) = input.next() {
                        return Err(ParseError {
                            found: Some(found),
                            expected: vec![None],
                        });
                    }
                }
                Token::Term { key, callback, .. } => {
                    let Some(found) = input.next() else {
                        return Err(ParseError {
                            found: None,
                            expected: vec![Some(key.clone())],
                        });
                    };
                    if found.get_key() != *key {
                        return Err(ParseError {
                            found: Some(found),
                            expected: vec![Some(key.clone())],
                        });
                    }
                    if let Some(f) = callback.as_ref() {
                        f(state, found)
                    }
                }
                Token::NonTerm(id) => self.partial_parse(*id, state, input)?,
            }
        }

        if let Some(f) = callback {
            f.call(state, self);
        }

        Ok(())
    }
}

/// super generic dynamic parser capable of just about anything
/// for most cases this is absolutely overkill but it does cover the best this libarary has to offer
/// rules and start tokens need to be inserted the rest is figured out later
/// see [`DynamicParser::generate_parser`]
#[derive(Debug, Clone, PartialEq)]
pub struct DynamicParser<Term, State, F1, F2>
where
    Term: Terminal,
    F1: CallBack<Term, State, F2>,
    F2: Fn(&mut State, Term),
{
    ///main entry point to the grammar
    pub start: NonTermId,
    ///a list of production rules in no paticular order
    pub rules: HashMap<NonTermId, Vec<Prod<Term, State, F1, F2>>>,

    ///type checking info generated automatically
    pub grammar: LLGrammar<Term::Key>,

    ///dynamic parser generated automatically
    pub parser: Parser<Term, State, F1, F2>,
}

impl<Term, State, F1, F2> DynamicParser<Term, State, F1, F2>
where
    Term: Terminal,
    F1: CallBack<Term, State, F2>,
    F2: Fn(&mut State, Term) + Clone,
{
    pub fn new(start: NonTermId, rules_v: Vec<(NonTermId, Prod<Term, State, F1, F2>)>) -> Self {
        let grammar = LLGrammar::from_rules(rules_v.iter().map(|(id, p)| (*id, p.into_grammar())));
        let mut rules: hashbrown::HashMap<_, Vec<_>> = HashMap::new();
        for (id, p) in rules_v.into_iter() {
            rules.entry(id).or_default().push(p)
        }
        let parser = Parser {
            productions: HashMap::new(),
        };
        Self {
            start,
            rules,
            grammar,
            parser,
        }
    }

    pub fn add_rule(&mut self, id: NonTermId, prod: Prod<Term, State, F1, F2>) {
        self.grammar.add_rule(id, prod.into_grammar());
        self.rules.entry(id).or_default().push(prod);
    }

    pub fn is_valid_macro(&mut self, non_term: NonTermId, prod: usize) -> bool {
        self.grammar
            .is_valid_macro(&self.rules[&non_term][prod].into_grammar())
    }

    /// verifys the grammar is LL1 using the cached grammar
    /// then updates the internal parser to agree with the current table
    pub fn generate_parser(&mut self) -> Result<(), GrammerErrors<Term::Key>> {
        self.grammar.add_start(self.start);
        self.grammar.calculate();
        let table = self.grammar.get_checked_table()?;

        self.parser.productions.clear();

        for (k, m) in table.into_iter() {
            let spot = self.parser.productions.entry(k).or_default();
            let rules = &self.rules[&k];

            for (ex, id) in m.into_iter() {
                match ex {
                    ExTerm::Eof => spot.eof = Some(rules[id].clone()),
                    ExTerm::Empty => {
                        spot.empty = Some(rules[id].clone());
                    }
                    ExTerm::Term(k) => {
                        spot.explicit.insert(k, rules[id].clone());
                    }
                };
            }
        }
        Ok(())
    }

    /// generally used for debuging
    /// gives an explicit copy of the grammar for refrence
    pub fn get_parse_table(&mut self) -> Result<ProdTable<Term::Key>, GrammerErrors<Term::Key>> {
        self.grammar.add_start(self.start);
        self.grammar.calculate();
        self.grammar.get_checked_table()
    }

    pub fn clear_grammar_cach(&mut self) {
        self.grammar.flush();
        self.grammar.add_rules(
            self.rules
                .iter()
                .flat_map(|(id, v)| v.iter().map(|p| (*id, p.into_grammar()))),
        );
    }

    pub fn parse(
        &mut self,
        target: NonTermId,
        state: &mut State,
        input: &mut impl Iterator<Item = Term>,
    ) -> Result<(), ParseError<Term>> {
        self.parser.parse(target, state, input)
    }

    pub fn partial_parse(
        &mut self,
        target: NonTermId,
        state: &mut State,
        input: &mut Peekable<impl Iterator<Item = Term>>,
    ) -> Result<(), ParseError<Term>> {
        self.parser.partial_parse(target, state, input)
    }
}

// -----------------------------------------------------------------------------
// 🧪 Unit‑tests for the LL(1) arithmetic parser (CallBack version)
// -----------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;
    use alloc::rc::Rc;
    use alloc::vec::Vec;
    use core::marker::PhantomData;
    use hashbrown::HashMap;

    // ---------- Lexer ---------------------------------------------------------
    #[derive(Clone, Debug, Eq, Hash, PartialEq)]
    enum Key {
        Int,
        Plus,
        Star,
    }

    #[derive(Clone, Debug)]
    enum Tok {
        Int(i32),
        Plus,
        Star,
    }

    impl Terminal for Tok {
        type Key = Key;
        fn get_key(&self) -> Key {
            match self {
                Tok::Int(_) => Key::Int,
                Tok::Plus => Key::Plus,
                Tok::Star => Key::Star,
            }
        }
    }

    fn lex(src: &str) -> Vec<Tok> {
        let mut out = Vec::new();
        let mut it = src.chars().peekable();
        while let Some(&c) = it.peek() {
            match c {
                '0'..='9' => {
                    let mut n = 0i32;
                    while let Some(d @ '0'..='9') = it.peek().copied() {
                        n = n * 10 + (d as i32 - '0' as i32);
                        it.next();
                    }
                    out.push(Tok::Int(n));
                }
                '+' => {
                    it.next();
                    out.push(Tok::Plus);
                }
                '*' => {
                    it.next();
                    out.push(Tok::Star);
                }
                ' ' | '\t' | '\n' | '\r' => {
                    it.next();
                } // skip ws
                _ => panic!("unexpected char '{}'", c),
            }
        }
        out
    }

    // ---------- Semantic state & term‑token callback --------------------------
    #[derive(Default, Clone)]
    struct EvalState {
        stack: Vec<i32>,
    }

    fn on_int(st: &mut EvalState, tok: Tok) {
        if let Tok::Int(v) = tok {
            st.stack.push(v);
        }
    }

    // ---------- prod‑callback implementation via ZST enum --------------------
    #[derive(Clone)]
    enum ProdCb {
        Add(&'static str),
        Mul(&'static str),
        Report(&'static str),
    }

    impl ProdCb {
        fn get_s(&self) -> &'static str {
            match self {
                ProdCb::Add(s) => s,
                ProdCb::Mul(s) => s,
                ProdCb::Report(s) => s,
            }
        }
    }

    impl<Term, F2> CallBack<Term, EvalState, F2> for ProdCb
    where
        Term: Terminal,
        F2: Fn(&mut EvalState, Term),
    {
        fn call(&self, state: &mut EvalState, _parser: &mut Parser<Term, EvalState, Self, F2>) {
            extern crate std;

            std::println!("{}", self.get_s());
            use std::io::Write;
            std::io::stdout().flush().unwrap();

            if let ProdCb::Report(_) = self {
                return;
            }

            let b = state.stack.pop().expect("stack underflow");
            let a = state.stack.pop().expect("stack underflow");

            match self {
                ProdCb::Add(_) => state.stack.push(a + b),
                ProdCb::Mul(_) => state.stack.push(a * b),
                ProdCb::Report(_) => {}
            }
        }
    }

    // shorthand type aliases
    type TermCb = fn(&mut EvalState, Tok);
    type P = Parser<Tok, EvalState, ProdCb, TermCb>;

    const FACTOR: usize = 0;
    const TERM_TAIL: usize = 1;
    const TERM: usize = 2;
    const EXPR_TAIL: usize = 3;
    const EXPR: usize = 4;

    fn prod(
        elts: Vec<Token<Tok, TermCb, EvalState>>,
        cb: ProdCb,
    ) -> Prod<Tok, EvalState, ProdCb, TermCb> {
        Prod {
            elements: Rc::from(elts.into_boxed_slice()),
            callback: Some(cb),
            _ph: PhantomData,
        }
    }

    fn build_parser() -> P {
        use Token::{NonTerm, Term};

        // --- token constructors -------------------------------------------------
        let tm_plus = Term {
            key: Key::Plus,
            callback: None,
            _ph: PhantomData,
        };
        let tm_star = Term {
            key: Key::Star,
            callback: None,
            _ph: PhantomData,
        };
        let tm_int = Term {
            key: Key::Int,
            callback: Some(on_int as TermCb),
            _ph: PhantomData,
        };

        // --- FACTOR → INT -------------------------------------------------------
        let mut factor = ParseTable {
            explicit: HashMap::new(),
            empty: None,
            eof: None,
        };
        factor.explicit.insert(
            Key::Int,
            prod(vec![tm_int], ProdCb::Report("factor -> int")),
        );

        // --- TERM_TAIL ----------------------------------------------------------
        // '*' Factor TermTail   | ε
        // ε is legal on look‑ahead
        let mut term_tail = ParseTable {
            explicit: HashMap::new(),
            empty: Some(prod(vec![], ProdCb::Report("term_trail -> e"))),
            eof: None,
        };
        // '*' branch
        term_tail.explicit.insert(
            Key::Star,
            prod(
                vec![tm_star.clone(), NonTerm(FACTOR), NonTerm(TERM_TAIL)],
                ProdCb::Mul("term_trail -> * factor term_trail"),
            ),
        );

        // --- TERM → Factor TermTail --------------------------------------------
        let mut term = ParseTable {
            explicit: HashMap::new(),
            empty: None,
            eof: None,
        };
        term.explicit.insert(
            Key::Int,
            prod(
                vec![NonTerm(FACTOR), NonTerm(TERM_TAIL)],
                ProdCb::Report("term -> factor term_trail"),
            ),
        );

        // --- EXPR_TAIL ----------------------------------------------------------
        // '+' Term ExprTail     | ε
        let mut expr_tail = ParseTable {
            explicit: HashMap::new(),
            empty: Some(prod(vec![], ProdCb::Report("expr_trail -> e"))),
            eof: None,
        };
        expr_tail.explicit.insert(
            Key::Plus,
            prod(
                vec![tm_plus.clone(), NonTerm(TERM), NonTerm(EXPR_TAIL)],
                ProdCb::Add("expr_trail -> + term expr_trail"),
            ),
        );

        // --- EXPR → Term ExprTail Eof----------------------------------------------
        //  (top‑level cannot derive ε)
        let mut expr = ParseTable {
            explicit: HashMap::new(),
            empty: None,
            eof: None,
        };
        expr.explicit.insert(
            Key::Int,
            prod(
                vec![NonTerm(TERM), NonTerm(EXPR_TAIL), Token::Eof],
                ProdCb::Report("expr -> term expr_trail"),
            ),
        );

        // --- assemble -----------------------------------------------------------
        let mut prods = HashMap::new();
        prods.insert(FACTOR, factor);
        prods.insert(TERM_TAIL, term_tail);
        prods.insert(TERM, term);
        prods.insert(EXPR_TAIL, expr_tail);
        prods.insert(EXPR, expr);

        Parser { productions: prods }
    }

    fn eval(src: &str) -> i32 {
        extern crate std;

        let mut parser = build_parser();
        let mut st = EvalState::default();
        let mut toks = lex(src).into_iter().map(|x| {
            std::println!("reading {:?}", x);
            x
        });
        parser.parse(EXPR, &mut st, &mut toks).expect("parse error");
        assert!(toks.next().is_none(), "lexer left‑over tokens");
        st.stack.pop().unwrap()
    }

    // ---------- actual tests --------------------------------------------------
    #[test]
    fn single_number() {
        assert_eq!(eval("42"), 42);
    }

    #[test]
    fn mixed_precedence() {
        assert_eq!(eval("2+3*3"), 11); // 2 + (3*3)
    }

    #[test]
    fn longer_expression() {
        assert_eq!(eval("1+2+3*4*5+6"), 69);
    }

    #[test]
    fn unexpected_token() {
        // "+3" cannot start an expression
        let mut parser = build_parser();
        let mut st = EvalState::default();
        let mut it = lex("+3").into_iter();
        parser.parse(EXPR, &mut st, &mut it).unwrap_err();
    }

    #[test]
    fn missing_operand() {
        // "2+" ends after '+'
        let mut parser = build_parser();
        let mut it = lex("2+").into_iter();
        let mut st = EvalState::default();
        parser.parse(EXPR, &mut st, &mut it).unwrap_err();
    }

    #[test]
    fn trailing_garbage() {
        extern crate std;
        // "2 2" is invalid: second INT must be preceded by '+'
        let mut parser = build_parser();
        let mut st = EvalState::default();
        let mut it = lex("2 2").into_iter().map(|x| {
            std::println!("reading {:?}", x);
            x
        });
        parser.parse(EXPR, &mut st, &mut it).unwrap_err();
    }

    #[test]
    fn complex_trailing_garbage() {
        extern crate std;
        let mut parser = build_parser();
        let mut st = EvalState::default();
        let mut it = lex("1+2+3*4*5+6 2+3+2").into_iter().map(|x| {
            std::println!("reading {:?}", x);
            x
        });
        parser.parse(EXPR, &mut st, &mut it).unwrap_err();
    }

    #[test]
    fn empty_input() {
        let mut parser = build_parser();
        let mut st = EvalState::default();
        let mut it = lex("").into_iter();
        parser.parse(EXPR, &mut st, &mut it).unwrap_err();
    }
}

#[cfg(test)]
mod dynamic_parser_tests {
    use super::*;
    use alloc::rc::Rc;
    use alloc::vec::Vec;
    use core::marker::PhantomData;
    extern crate std;

    // ----- Tokens/keys identical in spirit to the existing tests --------------
    #[derive(Clone, Debug, Eq, Hash, PartialEq)]
    enum Key {
        Int,
        Plus,
        Star,
    }

    #[derive(Clone, Debug)]
    enum Tok {
        Int(i32),
        Plus,
        Star,
    }

    impl Terminal for Tok {
        type Key = Key;
        fn get_key(&self) -> Key {
            match self {
                Tok::Int(_) => Key::Int,
                Tok::Plus => Key::Plus,
                Tok::Star => Key::Star,
            }
        }
    }

    // ----- Tiny lexer just for these tests -----------------------------------
    fn lex(src: &str) -> Vec<Tok> {
        let mut out = Vec::new();
        let mut it = src.chars().peekable();
        while let Some(&c) = it.peek() {
            match c {
                '0'..='9' => {
                    let mut n = 0i32;
                    while let Some(d @ '0'..='9') = it.peek().copied() {
                        n = n * 10 + (d as i32 - '0' as i32);
                        it.next();
                    }
                    out.push(Tok::Int(n));
                }
                '+' => {
                    it.next();
                    out.push(Tok::Plus);
                }
                '*' => {
                    it.next();
                    out.push(Tok::Star);
                }
                ' ' | '\t' | '\n' | '\r' => {
                    it.next();
                }
                _ => panic!("unexpected char '{c}'"),
            }
        }
        out
    }

    // ----- Eval state & production/term callbacks (same behavior as before) ---
    #[derive(Default, Clone)]
    struct EvalState {
        stack: Vec<i32>,
    }

    fn on_int(st: &mut EvalState, tok: Tok) {
        if let Tok::Int(v) = tok {
            st.stack.push(v)
        }
    }

    #[derive(Clone)]
    enum ProdCb {
        Add,
        Mul,
        Report,
    }

    impl<Term, F2> CallBack<Term, EvalState, F2> for ProdCb
    where
        Term: Terminal,
        F2: Fn(&mut EvalState, Term),
    {
        fn call(&self, st: &mut EvalState, _p: &mut Parser<Term, EvalState, Self, F2>) {
            match self {
                ProdCb::Report => {}
                ProdCb::Add => {
                    let b = st.stack.pop().expect("stack underflow");
                    let a = st.stack.pop().expect("stack underflow");
                    st.stack.push(a + b);
                }
                ProdCb::Mul => {
                    let b = st.stack.pop().expect("stack underflow");
                    let a = st.stack.pop().expect("stack underflow");
                    st.stack.push(a * b);
                }
            }
        }
    }

    type TermCb = fn(&mut EvalState, Tok);
    type P = DynamicParser<Tok, EvalState, ProdCb, TermCb>;

    const FACTOR: usize = 0;
    const TERM_TAIL: usize = 1;
    const TERM: usize = 2;
    const EXPR_TAIL: usize = 3;
    const EXPR: usize = 4;

    fn tm(key: Key, cb: Option<TermCb>) -> Token<Tok, TermCb, EvalState> {
        Token::Term {
            key,
            callback: cb,
            _ph: PhantomData,
        }
    }
    fn nt(id: usize) -> Token<Tok, TermCb, EvalState> {
        Token::NonTerm(id)
    }

    fn prod(
        elts: Vec<Token<Tok, TermCb, EvalState>>,
        cb: ProdCb,
    ) -> Prod<Tok, EvalState, ProdCb, TermCb> {
        Prod {
            elements: Rc::from(elts.into_boxed_slice()),
            callback: Some(cb),
            _ph: PhantomData,
        }
    }

    // -------------------------------------------------------------------------
    // ✅ Green path: same arithmetic grammar, but built via DynamicParser::new
    // -------------------------------------------------------------------------
    #[test]
    fn generate_parser_ok() {
        // tokens
        let t_plus = tm(Key::Plus, None);
        let t_star = tm(Key::Star, None);
        let t_int = tm(Key::Int, Some(on_int as TermCb));

        // rules: identical structure to your hand-wired tables
        let mut rules: Vec<(NonTermId, Prod<Tok, EvalState, ProdCb, TermCb>)> = Vec::new();

        // FACTOR → INT
        rules.push((FACTOR, prod(vec![t_int.clone()], ProdCb::Report)));

        // TERM_TAIL → "*" FACTOR TERM_TAIL | ε
        rules.push((
            TERM_TAIL,
            prod(vec![t_star.clone(), nt(FACTOR), nt(TERM_TAIL)], ProdCb::Mul),
        ));
        rules.push((TERM_TAIL, prod(vec![], ProdCb::Report)));

        // TERM → FACTOR TERM_TAIL
        rules.push((TERM, prod(vec![nt(FACTOR), nt(TERM_TAIL)], ProdCb::Report)));

        // EXPR_TAIL → "+" TERM EXPR_TAIL | ε
        rules.push((
            EXPR_TAIL,
            prod(vec![t_plus.clone(), nt(TERM), nt(EXPR_TAIL)], ProdCb::Add),
        ));
        rules.push((EXPR_TAIL, prod(vec![], ProdCb::Report)));

        // EXPR → TERM EXPR_TAIL EOF   (start)
        rules.push((
            EXPR,
            prod(vec![nt(TERM), nt(EXPR_TAIL), Token::Eof], ProdCb::Report),
        ));

        // Build dynamic parser from rules and materialize parse tables
        let mut dp: P = DynamicParser::new(EXPR, rules);
        dp.generate_parser()
            .expect("LL(1) arithmetic grammar should pass");
        std::println!("{:?}", dp.grammar);

        // Now parse and evaluate like before
        let mut st = EvalState::default();
        let mut it = lex("2+3*3").into_iter();
        dp.parse(EXPR, &mut st, &mut it).expect("parse failed");
        assert_eq!(st.stack.pop(), Some(11));
        assert!(it.next().is_none(), "no trailing garbage expected");
    }

    // -------------------------------------------------------------------------
    // ❌ Red path: FIRST/FIRST conflict (S → INT | INT) => generate_parser() errs
    // -------------------------------------------------------------------------
    #[test]
    fn generate_parser_conflict() {
        // One nonterminal S with two alternatives that both start with INT.
        const S: usize = 0;
        let t_int = tm(Key::Int, Some(on_int as TermCb));

        let mut rules: Vec<(NonTermId, Prod<Tok, EvalState, ProdCb, TermCb>)> = Vec::new();
        rules.push((S, prod(vec![t_int.clone()], ProdCb::Report)));
        rules.push((S, prod(vec![t_int.clone()], ProdCb::Report)));

        let mut dp: P = DynamicParser::new(S, rules);
        let err = dp
            .generate_parser()
            .expect_err("should detect FIRST/FIRST conflict");
        // Optional: if your error type carries per‑nonterminal conflicts,
        // you can assert specifics here. For now, existence of Err is enough.
        let _ = err; // silence unused warning if not asserting more
    }
}

#[cfg(test)]
mod c_funptr_ambiguity {
    use super::*;
    use alloc::string::String;
    use alloc::{rc::Rc, vec::Vec};
    use core::cell::RefCell;
    use core::marker::PhantomData;
    use hashbrown::HashSet;

    // ---------------------------------------------------------------------
    // 🔑  Token keys (tiny subset)
    // ---------------------------------------------------------------------
    #[derive(Clone, Debug, Eq, Hash, PartialEq)]
    enum Key {
        TypedefKw, // "typedef"
        TypeKw,    // builtin type keyword (“int” only here)
        TypeName,  // identifier in typedef set
        Id,        // plain identifier
        Lp,
        Rp,
        Star,
        Semi,
        Comma,
    }

    // ---------------------------------------------------------------------
    // 🏷️  Concrete tokens
    // ---------------------------------------------------------------------
    #[derive(Clone, Debug)]
    enum Tok {
        KwTypedef,
        KwInt,
        TypeName(String),
        Id(String),
        Lp,
        Rp,
        Star,
        Semi,
        Comma,
    }

    impl Terminal for Tok {
        type Key = Key;
        fn get_key(&self) -> Key {
            match self {
                Tok::KwTypedef => Key::TypedefKw,
                Tok::KwInt => Key::TypeKw,
                Tok::TypeName(_) => Key::TypeName,
                Tok::Id(_) => Key::Id,
                Tok::Lp => Key::Lp,
                Tok::Rp => Key::Rp,
                Tok::Star => Key::Star,
                Tok::Semi => Key::Semi,
                Tok::Comma => Key::Comma,
            }
        }
    }

    // ---------------------------------------------------------------------
    // 🧠  Parser state
    // ---------------------------------------------------------------------
    #[derive(Default)]
    struct CState {
        lexer: Rc<RefCell<LexerCore>>,
        armed_typedef: bool,
        pending_typedef: Option<String>,
    }

    // ---------------------------------------------------------------------
    // 🖋️  Lexer with typedef set
    // ---------------------------------------------------------------------
    #[derive(Default)]
    struct LexerCore {
        src: Vec<char>,
        i: usize,
        typedefs: HashSet<String>,
    }

    impl LexerCore {
        fn new(s: &str) -> Self {
            Self {
                src: s.chars().collect(),
                i: 0,
                typedefs: HashSet::new(),
            }
        }
        fn insert_typedef(&mut self, name: String) {
            self.typedefs.insert(name);
        }

        fn bump(&mut self) -> Option<char> {
            let ch = self.src.get(self.i).copied();
            if ch.is_some() {
                self.i += 1
            }
            ch
        }
        fn peek(&self) -> Option<char> {
            self.src.get(self.i).copied()
        }
        fn skip_ws(&mut self) {
            while matches!(self.peek(), Some(c) if c.is_whitespace()) {
                self.i += 1;
            }
        }

        fn ident(&mut self) -> String {
            let start = self.i;
            while let Some(c) = self.peek() {
                if c.is_ascii_alphanumeric() || c == '_' {
                    self.i += 1;
                } else {
                    break;
                }
            }
            self.src[start..self.i].iter().collect()
        }

        fn next_token(&mut self) -> Option<Tok> {
            self.skip_ws();
            let ch = self.peek()?;
            Some(match ch {
                '(' => {
                    self.bump();
                    Tok::Lp
                }
                ')' => {
                    self.bump();
                    Tok::Rp
                }
                '*' => {
                    self.bump();
                    Tok::Star
                }
                ';' => {
                    self.bump();
                    Tok::Semi
                }
                ',' => {
                    self.bump();
                    Tok::Comma
                }
                c if c.is_ascii_alphabetic() || c == '_' => {
                    let w = self.ident();
                    match w.as_str() {
                        "typedef" => Tok::KwTypedef,
                        "int" => Tok::KwInt,
                        _ if self.typedefs.contains(&w) => Tok::TypeName(w),
                        _ => Tok::Id(w),
                    }
                }
                _ => {
                    panic!("unexpected char {:?}", ch)
                }
            })
        }
    }

    // iterator wrapper
    struct LexStream {
        core: Rc<RefCell<LexerCore>>,
    }
    impl LexStream {
        fn new(c: Rc<RefCell<LexerCore>>) -> Self {
            Self { core: c }
        }
    }
    impl Iterator for LexStream {
        type Item = Tok;
        fn next(&mut self) -> Option<Tok> {
            self.core.borrow_mut().next_token()
        }
    }

    // ---------------------------------------------------------------------
    // 📎  Callbacks
    // ---------------------------------------------------------------------
    type TermCb = fn(&mut CState, Tok);

    fn on_typedef_kw(st: &mut CState, _t: Tok) {
        st.armed_typedef = true;
    }

    fn on_decl_id(st: &mut CState, t: Tok) {
        if st.armed_typedef {
            match t {
                Tok::Id(s) | Tok::TypeName(s) => st.pending_typedef = Some(s),
                _ => {}
            }
        }
    }

    #[derive(Clone)]
    enum ProdCb {
        CommitTypedef,
    }

    impl<T, F2> CallBack<T, CState, F2> for ProdCb
    where
        T: Terminal,
        F2: Fn(&mut CState, T),
    {
        fn call(&self, st: &mut CState, _p: &mut Parser<T, CState, Self, F2>) {
            match self {
                ProdCb::CommitTypedef => {
                    if let Some(name) = st.pending_typedef.take() {
                        st.lexer.borrow_mut().insert_typedef(name);
                    }
                    st.armed_typedef = false;
                }
            }
        }
    }

    // helpers
    fn tm(key: Key, cb: Option<TermCb>) -> Token<Tok, TermCb, CState> {
        Token::Term {
            key,
            callback: cb,
            _ph: PhantomData,
        }
    }
    fn nt(id: usize) -> Token<Tok, TermCb, CState> {
        Token::NonTerm(id)
    }
    fn eof<T>() -> Vec<T> {
        Vec::new()
    }
    fn prod(
        elts: Vec<Token<Tok, TermCb, CState>>,
        cb: Option<ProdCb>,
    ) -> Prod<Tok, CState, ProdCb, TermCb> {
        Prod {
            elements: Rc::from(elts.into_boxed_slice()),
            callback: cb,
            _ph: PhantomData,
        }
    }

    // ---------------------------------------------------------------------
    // 📜  Mini grammar
    // ---------------------------------------------------------------------
    const TRANS_UNIT: usize = 0;
    const DECL_LIST: usize = 1;
    const DECL: usize = 2;
    const TYPEDEF_DECL: usize = 3;
    const TYPE_SPEC: usize = 4;
    const DECLARATOR: usize = 5;
    const DIR_DECL: usize = 6;
    const VAR_DECL: usize = 7;

    fn build_parser() -> DynamicParser<Tok, CState, ProdCb, TermCb> {
        // ------------------------------------------------------------------
        // 🏗️  assemble rules
        // ------------------------------------------------------------------
        let mut rules: Vec<(NonTermId, Prod<Tok, CState, ProdCb, TermCb>)> = Vec::new();

        // translation-unit → decl-list EOF
        rules.push((TRANS_UNIT, prod(vec![nt(DECL_LIST), Token::Eof], None)));

        // decl-list → decl decl-list | ε
        rules.push((DECL_LIST, prod(vec![nt(DECL), nt(DECL_LIST)], None)));
        rules.push((DECL_LIST, prod(eof(), None)));

        // decl → typedef-decl | var-decl
        rules.push((DECL, prod(vec![nt(TYPEDEF_DECL)], None)));
        rules.push((DECL, prod(vec![nt(VAR_DECL)], None)));

        // typedef-decl → 'typedef' type-spec declarator ';'   {commit}
        rules.push((
            TYPEDEF_DECL,
            prod(
                vec![
                    tm(Key::TypedefKw, Some(on_typedef_kw)),
                    nt(TYPE_SPEC),
                    nt(DECLARATOR),
                    tm(Key::Semi, None),
                ],
                Some(ProdCb::CommitTypedef),
            ),
        ));

        // type-spec → TypeKw | TypeName
        rules.push((TYPE_SPEC, prod(vec![tm(Key::TypeKw, None)], None)));
        rules.push((TYPE_SPEC, prod(vec![tm(Key::TypeName, None)], None)));

        // declarator → dir-decl
        rules.push((DECLARATOR, prod(vec![nt(DIR_DECL)], None)));

        // dir-decl → Id
        rules.push((DIR_DECL, prod(vec![tm(Key::Id, Some(on_decl_id))], None)));

        // dir-decl → '(' '*' Id ')' '(' type-spec ')'
        rules.push((
            DIR_DECL,
            prod(
                vec![
                    tm(Key::Lp, None),
                    tm(Key::Star, None),
                    tm(Key::Id, Some(on_decl_id)), // typedef name
                    tm(Key::Rp, None),
                    tm(Key::Lp, None),
                    nt(TYPE_SPEC),
                    tm(Key::Rp, None),
                ],
                None,
            ),
        ));

        // -------------------------  ❗ key change ❗ -------------------------
        // var-decl → type-spec declarator ';'   (covers simple & fp vars)
        rules.push((
            VAR_DECL,
            prod(
                vec![nt(TYPE_SPEC), nt(DECLARATOR), tm(Key::Semi, None)],
                None,
            ),
        ));

        // ------------------------------------------------------------------
        // 🛠️  build & validate parser
        // ------------------------------------------------------------------
        let mut dp = DynamicParser::<Tok, CState, ProdCb, TermCb>::new(TRANS_UNIT, rules);

        // generate LL(1) tables – will Err on any remaining conflicts
        dp.generate_parser().unwrap();

        // assert that the typedef production (index 0 under TYPEDEF_DECL) is macro-safe
        assert!(
            dp.is_valid_macro(TYPEDEF_DECL, 0),
            "typedef-decl production must be macro-safe"
        );

        dp
    }

    fn make_state_stream(src: &str) -> (CState, LexStream) {
        let core = Rc::new(RefCell::new(LexerCore::new(src)));
        (
            CState {
                lexer: core.clone(),
                ..Default::default()
            },
            LexStream::new(core),
        )
    }

    // -------------------------------------------------------------------------
    // ✅ 1. typedef a base type, then function pointer using that typedef
    // -------------------------------------------------------------------------
    #[test]
    fn typedef_then_funptr_ok() {
        let src = "typedef int my_int; my_int (*fp)(my_int);";
        let mut parser = build_parser();
        let (mut st, mut it) = make_state_stream(src);

        parser.parse(TRANS_UNIT, &mut st, &mut it).unwrap();
        assert!(st.lexer.borrow().typedefs.contains("my_int"));
    }

    // -------------------------------------------------------------------------
    // ❌ 2. ordinary variable, then try to use its name as a type  → error
    // -------------------------------------------------------------------------
    #[test]
    fn variable_then_funptr_err() {
        let src = "int my_int; my_int (*fp)(int);";
        let mut parser = build_parser();
        let (mut st, mut it) = make_state_stream(src);

        let err = parser.parse(TRANS_UNIT, &mut st, &mut it).unwrap_err();
        extern crate std;
        std::println!("expected failure (variable-name as type): {:?}", err);
    }

    // -------------------------------------------------------------------------
    // ✅ 3. two-level typedef, then a variable of the final alias
    // -------------------------------------------------------------------------
    #[test]
    fn two_level_typedef_then_var_ok() {
        // typedef int base_t;   typedef base_t alias_t;   alias_t y;
        let src = "typedef int base_t; typedef base_t alias_t; alias_t y;";
        let mut parser = build_parser();
        let (mut st, mut it) = make_state_stream(src);

        parser.parse(TRANS_UNIT, &mut st, &mut it).unwrap();
        let td = &st.lexer.borrow().typedefs;
        assert!(td.contains("base_t") && td.contains("alias_t"));
    }

    // -------------------------------------------------------------------------
    // ✅ 4. same typedef used in *two* function-pointer declarations
    // -------------------------------------------------------------------------
    #[test]
    fn multiple_funptr_decls_ok() {
        let src = "typedef int my_int; \
                   my_int (*fp1)(my_int); \
                   my_int (*fp2)(my_int);";
        let mut parser = build_parser();
        let (mut st, mut it) = make_state_stream(src);

        parser.parse(TRANS_UNIT, &mut st, &mut it).unwrap();
        assert!(st.lexer.borrow().typedefs.contains("my_int"));
    }

    // -------------------------------------------------------------------------
    // ❌ 5. unknown parameter type inside the function-pointer declarator
    // -------------------------------------------------------------------------
    #[test]
    fn invalid_funptr_unknown_param() {
        // ‘unknown_t’ is *not* a typedef →
        // TYPE_SPEC inside “…)(TYPE_SPEC)” must be TypeKw or TypeName.
        let src = "typedef int my_int; my_int (*fp)(unknown_t);";
        let mut parser = build_parser();
        let (mut st, mut it) = make_state_stream(src);

        let err = parser.parse(TRANS_UNIT, &mut st, &mut it).unwrap_err();
        extern crate std;
        std::println!("expected failure (unknown param type): {:?}", err);
    }

    // -------------------------------------------------------------------------
    // ❌ 6. missing parentheses around ‘*’ in function-pointer declarator
    // -------------------------------------------------------------------------
    #[test]
    fn invalid_funptr_missing_paren() {
        // grammar requires “TypeName (*id)(type-spec)”
        let src = "typedef int my_int; my_int *fp(my_int);";
        let mut parser = build_parser();
        let (mut st, mut it) = make_state_stream(src);

        let err = parser.parse(TRANS_UNIT, &mut st, &mut it).unwrap_err();
        extern crate std;
        std::println!("expected failure (missing parentheses): {:?}", err);
    }

    // -----------------------------------------------------------------------------
// 🧨 extra negative-tests to stress the LL(1) + macro checker
// (append them to c_funptr_ambiguity after the earlier tests)
// -----------------------------------------------------------------------------

// helper: clone build_parser’s rules, then splice in extra broken ones
fn rebuild_with(mut more: Vec<(NonTermId,
                               Prod<Tok, CState, ProdCb, TermCb>)>)
    -> DynamicParser<Tok, CState, ProdCb, TermCb>
{
    // start with the canonical good grammar
    let base = build_parser();

    // pull out its rule list
    let mut rules: Vec<_> =
        base.rules.into_iter().flat_map(|(nt, v)| v.into_iter().map(move |p| (nt, p))).collect();

    // extend
    rules.append(&mut more);

    let mut dp = DynamicParser::<Tok, CState, ProdCb, TermCb>::new(TRANS_UNIT, rules);
    dp.clear_grammar_cach();            // sync rules → grammar cache
    dp
}

	// -------------------------------------------------------------------------
	// 1️⃣  FIRST/FIRST conflict hidden by shared prefix TYPE_SPEC
	// -------------------------------------------------------------------------
	#[test]
	fn hidden_first_first_detected() {
	    const BROKEN: usize = 100;

	    // BROKEN → type-spec Id ';'  |  TypeName Id ';'
	    let mut extra = Vec::new();
	    extra.push((BROKEN,
	        prod(vec![nt(TYPE_SPEC), tm(Key::Id, None), tm(Key::Semi, None)], None)));
	    extra.push((BROKEN,
	        prod(vec![tm(Key::TypeName, None), tm(Key::Id, None), tm(Key::Semi, None)], None)));

	    // attach BROKEN as new top-level
	    extra.push((TRANS_UNIT, prod(vec![nt(BROKEN), Token::Eof], None)));

	    let mut dp = rebuild_with(extra);
	    assert!(dp.generate_parser().is_err(),
	            "FIRST/FIRST overlap through TYPE_SPEC was *not* caught");
	}

	// -------------------------------------------------------------------------
	// 2️⃣  FIRST/FOLLOW ε-nullable conflict
	// -------------------------------------------------------------------------
	#[test]
	fn nullable_first_follow_detected() {
	    const A: usize = 101;
	    const S: usize = 102;

	    let mut extra = Vec::new();

	    // S → A Id ';'
	    extra.push((S, prod(vec![nt(A), tm(Key::Id, None), tm(Key::Semi, None)], None)));
	    // A → ε   |  Id
	    extra.push((A, prod(Vec::new(), None)));                   // ε
	    extra.push((A, prod(vec![tm(Key::Id, None)], None)));

	    // make S the new start
	    extra.push((TRANS_UNIT, prod(vec![nt(S), Token::Eof], None)));

	    let mut dp = rebuild_with(extra);
	    assert!(dp.generate_parser().is_err(),
	            "nullable FIRST/FOLLOW conflict slipped through");
	}
}