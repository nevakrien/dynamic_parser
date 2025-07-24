#![no_std]
extern crate alloc;


use alloc::boxed::Box;
use alloc::vec::Vec;

pub type Action = dyn Fn(&mut ParseState);
pub type ActionId = usize;

#[derive(Debug,Clone,Copy,PartialEq,Eq,Hash)]
pub struct RuleId(pub usize);
pub const NO_RULE: RuleId = RuleId(usize::MAX);

impl RuleId{
	pub fn as_option(self)->Option<usize>{
		if self == NO_RULE {
			None
		}else{
			Some(self.0)
		}
	}
}

#[derive(Clone)]
pub enum Token{
	Eof,
	Literal(u8),
	NonTerminal(RuleId)
}

///all states we can get to given the next byte
///256 values + eof
pub type ParseTable =[RuleId;257];
pub struct Rule {
	pub table:ParseTable,
	pub action:ActionId,
}

pub struct ParseState {
	rule:usize,
	pub stack:Vec<Token>
}

pub struct Parser {
	actions:Vec<Box<Action>>,
	states:Vec<Rule>,
}


impl Parser {
	pub fn add_action(&mut self,action:Box<Action>)->ActionId{
		self.actions.push(action);
		self.actions.len()-1
	}

	pub fn get_action(&self,id:ActionId)->&Action{
		&self.actions[id]
	}

	pub fn get_action_mut(&mut self,id:ActionId)->&mut Action{
		&mut self.actions[id]
	}

	pub fn parse_iteration(&mut self,state:&mut ParseState,input:&mut impl Iterator<Item=u8>)->Option<()>{
		let rule = &self.states[state.rule];

		let id = match input.next(){
			None=>rule.table[256],
			Some(id)=>rule.table[id as usize],
		}.as_option()?;

		self.actions[rule.action](state);

		state.rule=id;

		Some(())
	}
}