use alloc::vec;
use crate::error::ParseError;
use crate::terminal::Terminal;
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::iter::Peekable;
use core::marker::PhantomData;
use hashbrown::HashMap;

pub type NonTermId = usize;

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
            Self::Eof => Self::Eof,
            Self::NonTerm(id) => Self::NonTerm(*id),
            Self::Term { key, callback, _ph } => Self::Term {
                key: key.clone(),
                callback: callback.clone(),
                _ph: *_ph,
            },
        }
    }
}

pub trait CallBack<Term, State, F2> : Clone
where
    Term: Terminal,
    F2: Fn(&mut State, Term),
{
	fn call(&self,state:&mut State,parser:&mut Parser<Term,State,Self,F2>);
}

#[derive(Clone)]
pub struct Rule<Term, State, F1, F2>
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
    explicit: HashMap<<Term as Terminal>::Key, Rule<Term, State, F1, F2>>,
    default: Option<Rule<Term, State, F1, F2>>, // ← ε here
    eof: Option<Rule<Term, State, F1, F2>>,     // distinct EOF rule
}

impl<Term, State, F1, F2> ParseTable<Term, State, F1, F2>
where
    Term: Terminal,
   F1: CallBack<Term, State, F2>,
    F2: Fn(&mut State, Term),
{
    pub fn get_rule(&self, key: Option<&Term::Key>) -> Option<&Rule<Term, State, F1, F2>> {
        match key {
            None => self.eof.as_ref(),
            Some(t) => self.explicit.get(t).or(self.default.as_ref()),
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
        self.parse_threaded(target, state, &mut input.peekable())
    }

    pub fn parse_threaded(
        &mut self,
        target: NonTermId,
        state: &mut State,
        input: &mut Peekable<impl Iterator<Item = Term>>,
    ) -> Result<(), ParseError<Term>> {
        let table = &self.productions[&target];
        let key = input.peek().map(|x| x.get_key());

        let Some(rule) = table.get_rule(key.as_ref()) else {
            let mut expected: Vec<_> = table.explicit.keys().map(|x| Some(x.clone())).collect();
            if table.eof.is_some() {
                expected.push(None);
            }

            return Err(ParseError {
                found: input.next(),
                expected,
            });
        };
        let callback = rule.callback.clone();

        for e in rule.elements.clone().iter() {
            match e {
                Token::Eof => {
                    if let Some(x) = input.next() {
                        return Err(ParseError{
                    		found:Some(x),
                    		expected:vec![None]
                    	})
                    }
                }
                Token::Term { key, callback, .. } => {
                    let Some(found) = input.next() else{
                    	return Err(ParseError{
                    		found:None,
                    		expected:vec![Some(key.clone())]
                    	})
                    };
                    if found.get_key() != *key {
                        return Err(ParseError{
                    		found:Some(found),
                    		expected:vec![Some(key.clone())]
                    	})
                    }
                    if let Some(f) = callback.as_ref() {
                        f(state, found)
                    }
                }
                Token::NonTerm(id) => self.parse_threaded(*id, state, input)?,
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
    use alloc::vec::Vec;
    use alloc::rc::Rc;
    use core::marker::PhantomData;
    use hashbrown::HashMap;

    // ---------- Lexer ---------------------------------------------------------
    #[derive(Clone, Debug, Eq, Hash, PartialEq)]
    enum Key { Int, Plus, Star }

    #[derive(Clone, Debug)]
    enum Tok { Int(i32), Plus, Star }

    impl Terminal for Tok {
        type Key = Key;
        fn get_key(&self) -> Key {
            match self {
                Tok::Int(_) => Key::Int,
                Tok::Plus   => Key::Plus,
                Tok::Star   => Key::Star,
            }
        }
    }

    fn lex(src: &str) -> Vec<Tok> {
        let mut out = Vec::new();
        let mut it  = src.chars().peekable();
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
                '+' => { it.next(); out.push(Tok::Plus); }
                '*' => { it.next(); out.push(Tok::Star); }
                ' ' | '\t' | '\n' | '\r' => { it.next(); } // skip ws
                _ => panic!("unexpected char '{}'", c),
            }
        }
        out
    }

    // ---------- Semantic state & term‑token callback --------------------------
    #[derive(Default,Clone)]
    struct EvalState { stack: Vec<i32> }

    fn on_int(st: &mut EvalState, tok: Tok) {
        if let Tok::Int(v) = tok { st.stack.push(v); }
    }

    // ---------- Rule‑callback implementation via ZST enum --------------------
    #[derive(Clone)]
    enum RuleCb { Add, Mul }

    impl<Term, F2> CallBack<Term, EvalState, F2> for RuleCb
    where
        Term: Terminal,
        F2: Fn(&mut EvalState, Term),
    {
        fn call(&self,
                state: &mut EvalState,
                _parser: &mut Parser<Term, EvalState, Self, F2>) {
            let b = state.stack.pop().expect("stack underflow");
            let a = state.stack.pop().expect("stack underflow");
            match self {
                RuleCb::Add => state.stack.push(a + b),
                RuleCb::Mul => state.stack.push(a * b),
            }
        }
    }

    // shorthand type aliases
    type TermCb = fn(&mut EvalState, Tok);
    type P      = Parser<Tok, EvalState, RuleCb, TermCb>;

    const FACTOR: usize    = 0;
    const TERM_TAIL: usize = 1;
    const TERM: usize      = 2;
    const EXPR_TAIL: usize = 3;
    const EXPR: usize      = 4;

    fn rule(elts: Vec<Token<Tok, TermCb, EvalState>>,
            cb: Option<RuleCb>) -> Rule<Tok, EvalState, RuleCb, TermCb> {
        Rule {
            elements: Rc::from(elts.into_boxed_slice()),
            callback: cb,
            _ph: PhantomData,
        }
    }

    fn build_parser() -> P {
	    use Token::{NonTerm, Term};

	    let tm_plus = Term { key: Key::Plus, callback: None, _ph: PhantomData };
	    let tm_star = Term { key: Key::Star, callback: None, _ph: PhantomData };
	    let tm_int  = |cb| Term { key: Key::Int, callback: cb, _ph: PhantomData };

	    // FACTOR → INT
	    let mut factor = ParseTable { explicit: HashMap::new(), default: None, eof: None };
	    factor.explicit.insert(Key::Int,
	        rule(vec![tm_int(Some(on_int as TermCb))], None));

	    // reusable ε‑rule
	    let empty = rule(vec![], None);

	    // TERM_TAIL
	    //  '*' Factor TermTail
	    //  ε     (allowed look‑ahead: '+'  or EOF)
	    let mut term_tail = ParseTable {
	        explicit: HashMap::new(),
	        default: None,                 // ← no blanket default!
	        eof:     Some(empty.clone()),  // ε when stream really ends
	    };
	    // explicit multiplication branch
	    term_tail.explicit.insert(
	        Key::Star,
	        rule(vec![tm_star.clone(), NonTerm(FACTOR), NonTerm(TERM_TAIL)],
	             Some(RuleCb::Mul))
	    );
	    // explicit ε when the next token is '+'
	    term_tail.explicit.insert(Key::Plus, empty.clone());

	    // TERM → Factor TermTail
	    let mut term = ParseTable { explicit: HashMap::new(), default: None, eof: None };
	    term.explicit.insert(
	        Key::Int,
	        rule(vec![NonTerm(FACTOR), NonTerm(TERM_TAIL)], None)
	    );

	    // EXPR_TAIL
	    //  '+' Term ExprTail
	    //  ε     (look‑ahead EOF only)
	    let mut expr_tail = ParseTable {
	        explicit: HashMap::new(),
	        default: None,                 // ← no blanket default!
	        eof:     Some(empty.clone()),  // ε at EOF
	    };
	    expr_tail.explicit.insert(
	        Key::Plus,
	        rule(vec![tm_plus.clone(), NonTerm(TERM), NonTerm(EXPR_TAIL)],
	             Some(RuleCb::Add))
	    );

	    // EXPR → Term ExprTail
	    let mut expr = ParseTable {
	        explicit: HashMap::new(),
	        default: None,
	        eof:     None,
	    };
	    expr.explicit.insert(
	        Key::Int,
	        rule(vec![NonTerm(TERM), NonTerm(EXPR_TAIL)], None)
	    );

	    let mut prods = HashMap::new();
	    prods.insert(FACTOR,    factor);
	    prods.insert(TERM_TAIL, term_tail);
	    prods.insert(TERM,      term);
	    prods.insert(EXPR_TAIL, expr_tail);
	    prods.insert(EXPR,      expr);

	    Parser { productions: prods }
	}



    fn eval(src: &str) -> i32 {
        let mut parser = build_parser();
        let mut st     = EvalState::default();
        let mut toks   = lex(src).into_iter();
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
        assert_eq!(eval("2+3*3"), 11);   // 2 + (3*3)
    }

    #[test]
    fn longer_expression() {
        assert_eq!(eval("1+2+3*4*5+6"), 69);
    }


    #[test]
    fn unexpected_token() {
        // "+3" cannot start an expression
        let mut parser = build_parser();
        let mut st  = EvalState::default();
        let mut it  = lex("+3").into_iter();
        assert!(parser.parse(EXPR, &mut st, &mut it).is_err());
    }

    #[test]
    fn missing_operand() {
        // "2+" ends after '+'
        let mut parser = build_parser();
        let mut it  = lex("2+").into_iter();
        let mut st  = EvalState::default();
        assert!(parser.parse(EXPR, &mut st, &mut it).is_err());
    }

    #[test]
    fn trailing_garbage() {
        // "2 2" is invalid: second INT must be preceded by '+'
        let mut parser = build_parser();
        let mut st  = EvalState::default();
        let mut it  = lex("2 2").into_iter();
        assert!(parser.parse(EXPR, &mut st, &mut it).is_err());
    }

    #[test]
    fn empty_input() {
        let mut parser = build_parser();
        let mut st = EvalState::default();
        let mut it = lex("").into_iter();
        assert!(parser.parse(EXPR, &mut st, &mut it).is_err());
    }


}
