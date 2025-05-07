use super::GenericId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GenericRange {
    // start might not be a valid GenericId
    pub start: GenericId,
    pub len: u32, // Is there any benefit to this being a u16?
}

impl GenericRange {
    pub const EMPTY: Self = Self { start: GenericId { _raw: 0 }, len: 0 };

    pub fn iter(self) -> GenericRangeIter {
        self.into_iter()
    }
}

impl IntoIterator for GenericRange {
    type Item = GenericId;
    type IntoIter = GenericRangeIter;
    fn into_iter(self) -> Self::IntoIter {
        GenericRangeIter { start: self.start, len: self.len }
    }
}

pub struct GenericRangeIter {
    start: GenericId,
    len: u32,
}

impl Iterator for GenericRangeIter {
    type Item = GenericId;
    fn next(&mut self) -> Option<Self::Item> {
        self.len = self.len.checked_sub(1)?;
        Some(self.start.incr())
    }
}
