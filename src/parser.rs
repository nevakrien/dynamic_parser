use alloc::rc::Rc;
use crate::terminal::Terminal;
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

// #[derive(Clone)]
// pub enum ExToken<Term, State, F1, F2>
// where
//     Term: Terminal,
//     F1: Fn(&mut State),
//     F2: Fn(&mut State, Term),
// {
//     Regular(Token<Term, F2, State>),
//     Callback(F1),
// }

pub struct Rule<Term, State, F1, F2>
where
    Term: Terminal,
    F1: Fn(&mut State,&mut Parser<Term,State,F1,F2>),
    F2: Fn(&mut State, Term),
{
    elements: Rc<[Token<Term, F2, State>]>,
    callback: Option<F1>,
    _ph: PhantomData<dyn Fn(&mut State)>,
}

pub struct ParseTable<Term, State, F1, F2>
where
    Term: Terminal,
    F1: Fn(&mut State,&mut Parser<Term,State,F1,F2>),
    F2: Fn(&mut State, Term),
{
    explicit: HashMap<<Term as Terminal>::Key, Rule<Term, State, F1, F2>>,
    default: Option<Rule<Term, State, F1, F2>>, // ← ε here
    eof: Option<Rule<Term, State, F1, F2>>,     // distinct EOF rule
}

impl<Term, State, F1, F2> ParseTable<Term, State, F1, F2>
where
    Term: Terminal,
    F1: Fn(&mut State,&mut Parser<Term,State,F1,F2>),
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
    F1: Fn(&mut State,&mut Parser<Term,State,F1,F2>)+Clone,
    F2: Fn(&mut State, Term),
 {
    productions: ProdMap<Term, State, F1, F2>,
}

impl<Term, State, F1, F2> Parser<Term, State, F1, F2>
where
    Term: Terminal,
    F1: Fn(&mut State,&mut Parser<Term,State,F1,F2>)+Clone,
    F2: Fn(&mut State, Term),
{
    pub fn parse(
        &mut self,
        target: NonTermId,
        state: &mut State,
        input: &mut impl Iterator<Item = Term>,
    ) {
        self.parse_threaded(target, state, &mut input.peekable())
    }

    pub fn parse_threaded(
        &mut self,
        target: NonTermId,
        state: &mut State,
        input: &mut Peekable<impl Iterator<Item = Term>>,
    ) {
        let table = &self.productions[&target];
        let key = input.peek().map(|x| x.get_key());
        let rule = table.get_rule(key.as_ref()).expect("syntax error");
        let callback = rule.callback.clone();

        for e in rule.elements.clone().iter() {
            match e {
                Token::Eof => {
                    if let Some(_x) = input.next() {
                        todo!()
                    }
                }
                Token::Term { key, callback, .. } => {
                    let found = input.next().expect("TODO");
                    if found.get_key() != *key {
                        todo!()
                    }
                    if let Some(f) = callback.as_ref() {
                        f(state, found)
                    }
                }
                Token::NonTerm(id) => self.parse_threaded(*id, state, input),
            }
        }

        if let Some(f) = callback {
            f(state,self)
        }
    }

    // pub fn parse_step(
    //     &self,
    //     parse_stack: &mut Vec<ExToken<Term, State, F1, F2>>,
    //     state: &mut State,
    //     input: &mut Peekable<impl Iterator<Item = Term>>,
    // ) -> Option<()>
    // where
    //     F1: Clone,
    //     F2: Clone,
    // {

    //     match parse_stack.pop()? {
    //         ExToken::Regular(Token::Eof) => {
    //             if let Some(_x) = input.next() {
    //                 todo!()
    //             }
    //         }
    //         ExToken::Regular(Token::Term { key, callback, .. }) => {
    //             let found = input.next().expect("TODO");
    //             if found.get_key() != key {
    //                 todo!()
    //             }
    //             if let Some(f) = callback.as_ref() {
    //                 f(state, found)
    //             }
    //         }
    //         ExToken::Regular(Token::NonTerm(id)) => {
    //             let table = &self.productions[&id];
    //             let key = input.peek().map(|x| x.get_key());
    //             let rule = table.get_rule(key.as_ref()).expect("syntax error");

    //             if let Some(f) = &rule.callback {
    //             	parse_stack.push(ExToken::Callback(f.clone()));
    //             }
    //             for e in rule.elements.iter().rev() {
    //                 parse_stack.push(ExToken::Regular(e.clone()));
    //             }
    //         }
    //         ExToken::Callback(f) => f(state),
    //     }

    //     Some(())
    // }
}
