use core::hash::Hash;

pub trait Terminal {
    type Key: Eq + Hash;
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
