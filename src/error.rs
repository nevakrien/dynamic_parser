use crate::terminal::Terminal;
use alloc::vec::Vec;

#[derive(Debug, Clone, PartialEq)]
pub struct ParseError<Term: Terminal> {
    pub found: Option<Term>,
    pub expected: Vec<Option<Term::Key>>,
}
