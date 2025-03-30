use std::{
    fmt,
    ops::{Index, Range},
};

use super::SourceId;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    start: u32,
    len: u16,
    source: SourceId,
}

const _: () = assert!(size_of::<Span>() == size_of::<usize>());

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.into_range().fmt(f)
    }
}

impl Span {
    pub const ZERO: Self = Self { start: 0, len: 0, source: SourceId::NULL };

    #[expect(clippy::cast_possible_truncation)]
    pub fn new(range: Range<usize>, source: SourceId) -> Self {
        let len = (range.end - range.start).min(u16::MAX as _) as _;
        Self { start: range.start as _, len, source }
    }

    pub fn start(self) -> u32 {
        self.start
    }
    pub fn end(self) -> u32 {
        self.start + self.len()
    }
    pub fn len(self) -> u32 {
        u32::from(self.len)
    }
    pub fn shrink(self, n: u32) -> Self {
        (self.start + n..self.end() - n).into()
    }
    pub fn into_range(self) -> Range<u32> {
        self.start..self.end()
    }
    pub fn into_range_usize(self) -> Range<usize> {
        self.start as usize..self.end() as usize
    }
}

impl From<Range<u32>> for Span {
    fn from(Range { start, end }: Range<u32>) -> Self {
        Self::new(start as usize..end as usize, SourceId::NULL)
    }
}

impl Index<Span> for str {
    type Output = Self;
    fn index(&self, index: Span) -> &Self::Output {
        &self[index.into_range_usize()]
    }
}
