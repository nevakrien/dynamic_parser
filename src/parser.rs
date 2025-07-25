use core::iter::Peekable;
use crate::terminal::Terminal;
use alloc::boxed::Box;
use core::marker::PhantomData;
use hashbrown::HashMap;

pub type NonTermId = usize;

pub enum Token<T:Terminal> {
    Eof,
    Term(<T as Terminal>::Key),
    NonTerm(NonTermId),
}

pub struct Rule<Term:Terminal, State, F: Fn(&mut State)> {
    elements: Box<[Token<Term>]>,
    callback: Option<F>,
    _ph: PhantomData<dyn Fn(&mut State)>,
}

//TODO: add a way to handle the empty string (distinct from EOF)
pub type ParseTable<T, State, F> =
    HashMap<Option<<T as Terminal>::Key>, Rule<T, State, F>>;
pub type ProdMap<T, State, F> = HashMap<NonTermId, ParseTable<T, State, F>>;

pub struct Parser<Term: Terminal, State, F: Fn(&mut State)> {
    productions: ProdMap<Term, State, F>,
}

impl<Term, State, F> Parser<Term, State, F>
where
    Term: Terminal,
    F: Fn(&mut State),
{

	pub fn parse(&self,target:NonTermId,state:&mut State,input:&mut impl Iterator<Item=Term>){
		self.parse_threaded(target,state,&mut input.peekable())
	}

	pub fn parse_threaded(&self,target:NonTermId,state:&mut State,input:&mut Peekable<impl Iterator<Item=Term>>){
		let table = &self.productions[&target];
		let key = input.peek().map(|t| t.get_key());

		let rule = table.get(&key).expect("TODO");
		for e in rule.elements.iter(){
			match e{
				Token::Eof=> if let Some(_x) = input.next(){
					todo!()
				}
				Token::Term(k)=> {
					let found = input.next().expect("TODO");
					if found.get_key()!=*k{
						todo!()
					}
				},
				Token::NonTerm(id) => self.parse_threaded(*id,state,input)
			}
		}

		rule.callback.as_ref().map(|f| f(state));
	}
}
