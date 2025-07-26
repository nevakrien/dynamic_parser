use crate::error::ParseError;
use crate::terminal::Terminal;
use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;
use core::iter::Peekable;
use core::marker::PhantomData;
use hashbrown::HashMap;

pub type NonTermId = usize;

pub enum Token<T: Terminal, F: Fn(&mut State, T), State> {
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

#[derive(Clone)]
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

pub struct ParseTable<Term, State, F1, F2>
where
    Term: Terminal,
    F1: CallBack<Term, State, F2>,
    F2: Fn(&mut State, Term),
{
    explicit: HashMap<<Term as Terminal>::Key, Prod<Term, State, F1, F2>>,
    empty: Option<Prod<Term, State, F1, F2>>,
}

impl<Term, State, F1, F2> ParseTable<Term, State, F1, F2>
where
    Term: Terminal,
    F1: CallBack<Term, State, F2>,
    F2: Fn(&mut State, Term),
{
    pub fn get_prod(&self, key: Option<&Term::Key>) -> Option<&Prod<Term, State, F1, F2>> {
        match key {
            None => self.empty.as_ref(),
            Some(t) => self.explicit.get(t).or(self.empty.as_ref()),
        }
    }
}

pub type ProdMap<T, State, F1, F2> = HashMap<NonTermId, ParseTable<T, State, F1, F2>>;

pub struct Parser<Term, State, F1, F2>
where
    Term: Terminal,
    F1: CallBack<Term, State, F2>,
    F2: Fn(&mut State, Term),
{
    productions: ProdMap<Term, State, F1, F2>,
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

        self.partial_parse(target, state, &mut input)?;
        
        match input.next(){
        	None=>Ok(()),
        	Some(found)=>Err(ParseError {
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
    	fn get_s(&self) -> &'static str{
    		match self{
    			ProdCb::Add(s)=>s,
    			ProdCb::Mul(s)=>s,
    			ProdCb::Report(s)=>s,
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
            
            std::println!("{}",self.get_s());	
            use std::io::Write;
            std::io::stdout().flush().unwrap();

            if let ProdCb::Report(_) = self{
            	return;
            }

            let b = state.stack.pop().expect("stack underflow");
            let a = state.stack.pop().expect("stack underflow");
            
            match self {
                ProdCb::Add(_) => state.stack.push(a + b),
                ProdCb::Mul(_) => state.stack.push(a * b),
                ProdCb::Report(_) => {},
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
	    let tm_plus = Term { key: Key::Plus, callback: None, _ph: PhantomData };
	    let tm_star = Term { key: Key::Star, callback: None, _ph: PhantomData };
	    let tm_int  = Term { key: Key::Int,  callback:Some(on_int as TermCb), _ph: PhantomData };

	    // --- FACTOR → INT -------------------------------------------------------
	    let mut factor = ParseTable { explicit: HashMap::new(), empty: None };
	    factor.explicit.insert(
	        Key::Int,
	        prod(vec![tm_int], ProdCb::Report("factor -> int"))
	    );

	    // --- TERM_TAIL ----------------------------------------------------------
	    // '*' Factor TermTail   | ε
	    // ε is legal on look‑ahead
	    let mut term_tail = ParseTable {
	        explicit: HashMap::new(),
	        empty:    Some(prod(vec![], ProdCb::Report("term_trail -> e"))),
	    };
	    // '*' branch
	    term_tail.explicit.insert(
	        Key::Star,
	        prod(vec![tm_star.clone(), NonTerm(FACTOR), NonTerm(TERM_TAIL)],
	             ProdCb::Mul("term_trail -> * factor term_trail"))
	    );

	    // --- TERM → Factor TermTail --------------------------------------------
	    let mut term = ParseTable { explicit: HashMap::new(), empty: None };
	    term.explicit.insert(
	        Key::Int,
	        prod(vec![NonTerm(FACTOR), NonTerm(TERM_TAIL)], ProdCb::Report("term -> factor term_trail"))
	    );

	    // --- EXPR_TAIL ----------------------------------------------------------
	    // '+' Term ExprTail     | ε
	    let mut expr_tail = ParseTable {
	        explicit: HashMap::new(),
	        empty:    Some(prod(vec![], ProdCb::Report("expr_trail -> e"))),
	    };
	    expr_tail.explicit.insert(
	        Key::Plus,
	        prod(vec![tm_plus.clone(), NonTerm(TERM), NonTerm(EXPR_TAIL)],
	             ProdCb::Add("expr_trail -> + term expr_trail"))
	    );

	    // --- EXPR → Term ExprTail ----------------------------------------------
	    //  (top‑level cannot derive ε)
	    let mut expr = ParseTable { explicit: HashMap::new(), empty: None };
	    expr.explicit.insert(
	        Key::Int,
	        prod(vec![NonTerm(TERM), NonTerm(EXPR_TAIL)], ProdCb::Report("expr -> term expr_trail"))
	    );

	    // --- assemble -----------------------------------------------------------
	    let mut prods = HashMap::new();
	    prods.insert(FACTOR,    factor);
	    prods.insert(TERM_TAIL, term_tail);
	    prods.insert(TERM,      term);
	    prods.insert(EXPR_TAIL, expr_tail);
	    prods.insert(EXPR,      expr);

	    Parser { productions: prods }
	}


    fn eval(src: &str) -> i32 {
    	extern crate std;

        let mut parser = build_parser();
        let mut st = EvalState::default();
        let mut toks = lex(src).into_iter().map(|x| { std::println!("reading {:?}",x); x});
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
        let mut it = lex("2 2").into_iter().map(|x| { std::println!("reading {:?}",x); x});
        parser.parse(EXPR, &mut st, &mut it).unwrap_err();
    }

    #[test]
    fn complex_trailing_garbage() {
    	extern crate std;
        let mut parser = build_parser();
        let mut st = EvalState::default();
        let mut it = lex("1+2+3*4*5+6 2+3+2").into_iter().map(|x| { std::println!("reading {:?}",x); x});
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
