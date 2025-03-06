use std::{
    fmt,
    ops::{Index, Range},
};

#[derive(Clone, Copy)]
pub struct Span {
    start: u32,
    end: u32,
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.into_range().fmt(f)
    }
}

impl Span {
    pub fn into_range(self) -> Range<u32> {
        self.start..self.end
    }
    pub fn into_range_usize(self) -> Range<usize> {
        self.start as usize..self.end as usize
    }
}

impl From<Range<u32>> for Span {
    fn from(Range { start, end }: Range<u32>) -> Self {
        Self { start, end }
    }
}

impl Index<Span> for str {
    type Output = str;
    fn index(&self, index: Span) -> &Self::Output {
        &self[index.into_range_usize()]
    }
}

impl From<Span> for miette::SourceSpan {
    fn from(span: Span) -> Self {
        miette::SourceSpan::from(span.into_range_usize())
    }
}
