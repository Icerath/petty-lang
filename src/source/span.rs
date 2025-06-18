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

    #[cfg_attr(debug_assertions, track_caller)]
    #[expect(clippy::cast_possible_truncation)]
    pub fn new(range: Range<usize>, source: SourceId) -> Self {
        let len = (range.end - range.start).min(u16::MAX as _) as _;
        Self { start: range.start as _, len, source }
    }

    pub fn start(self) -> usize {
        self.start as _
    }
    pub fn end(self) -> usize {
        self.start() + self.len()
    }
    pub fn len(self) -> usize {
        self.len.into()
    }
    pub fn shrink(self, n: usize) -> Self {
        Self::new(self.start() + n..self.end() - n, self.source())
    }
    pub fn into_range(self) -> Range<usize> {
        self.start()..self.end()
    }
    pub fn join(spans: impl IntoIterator<Item = Self>) -> Self {
        let mut spans = spans.into_iter();
        let Some(first) = spans.next() else { return Self::ZERO };

        let mut start = first.start();
        let mut end = first.end();
        spans.for_each(|span| {
            debug_assert_eq!(span.source(), first.source);
            start = start.min(span.start());
            end = start.max(span.end());
        });
        Self::new(start..end, first.source())
    }
    pub fn source(self) -> SourceId {
        self.source
    }
    pub fn with_end(self, end: usize) -> Self {
        Self::new(self.start()..end, self.source)
    }
    pub fn from_start_len(start: usize, len: usize, source: SourceId) -> Self {
        Self { start: start.try_into().unwrap(), len: len.try_into().unwrap(), source }
    }
}

impl Index<Span> for str {
    type Output = Self;
    fn index(&self, index: Span) -> &Self::Output {
        &self[index.into_range()]
    }
}
