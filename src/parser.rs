use crate::terminal::Terminal;
use alloc::boxed::Box;
use core::iter::Peekable;
use core::marker::PhantomData;
use hashbrown::HashMap;

pub type NonTermId = usize;

pub enum Token<T: Terminal, F: Fn(&mut State, T),State> {
    Eof,
    Term(<T as Terminal>::Key, F,PhantomData<State>),
    NonTerm(NonTermId),
}

pub struct Rule<Term, State, F1, F2>
where
    Term: Terminal,
    F1: Fn(&mut State),
    F2: Fn(&mut State, Term),
{
    elements: Box<[Token<Term, F2,State>]>,
    callback: Option<F1>,
    _ph: PhantomData<dyn Fn(&mut State)>,
}

pub struct ParseTable<Term, State, F1, F2>
where
    Term: Terminal,
    F1: Fn(&mut State),
    F2: Fn(&mut State, Term),
{
    explicit: HashMap<<Term as Terminal>::Key, Rule<Term, State, F1, F2>>,
    default: Option<Rule<Term, State, F1, F2>>, // ← ε here
    eof: Option<Rule<Term, State, F1, F2>>,     // distinct EOF rule
}

impl<Term, State, F1, F2> ParseTable<Term, State, F1, F2>
where
    Term: Terminal,
    F1: Fn(&mut State),
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

pub struct Parser<Term: Terminal, State, F1: Fn(&mut State), F2: Fn(&mut State, Term)> {
    productions: ProdMap<Term, State, F1, F2>,
}

impl<Term, State, F1, F2> Parser<Term, State, F1, F2>
where
    Term: Terminal,
    F1: Fn(&mut State),
    F2: Fn(&mut State, Term),
{
    pub fn parse(
        &self,
        target: NonTermId,
        state: &mut State,
        input: &mut impl Iterator<Item = Term>,
    ) {
        self.parse_threaded(target, state, &mut input.peekable())
    }

    pub fn parse_threaded(
        &self,
        target: NonTermId,
        state: &mut State,
        input: &mut Peekable<impl Iterator<Item = Term>>,
    ) {
        let table = &self.productions[&target];
        let key = input.peek().map(|x| x.get_key());
        let rule = table.get_rule(key.as_ref()).expect("syntax error");

        for e in rule.elements.iter() {
            match e {
                Token::Eof => {
                    if let Some(_x) = input.next() {
                        todo!()
                    }
                }
                Token::Term(k, f, _) => {
                    let found = input.next().expect("TODO");
                    if found.get_key() != *k {
                        todo!()
                    }
                    f(state,found);
                }
                Token::NonTerm(id) => self.parse_threaded(*id, state, input),
            }
        }

        if let Some(f) = rule.callback.as_ref() {
            f(state)
        }
    }

    // pub fn parse_step(
    //     &self,
    //     parse_stack: Vec<NonTermId>,
    //     state: &mut State,
    //     input: &mut Peekable<impl Iterator<Item = Term>>,
    // ) -> Option<()>{
    // 	let target = parse_stack.pop()?;
    // }
}