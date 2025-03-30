#![expect(dead_code)]

pub mod span;

use std::path::PathBuf;

use index_vec::IndexVec;

#[derive(Default)]
pub struct Source {
    inner: IndexVec<SourceId, SourceInfo>,
}

impl Source {
    pub fn push(&mut self, src: SourceInfo) -> SourceId {
        self.inner.push(src)
    }
}

pub struct SourceInfo {
    path: PathBuf,
    src: String,
}

crate::define_id! {
    pub SourceId = u16
}

impl SourceId {
    pub const NULL: Self = Self { _raw: 0 };
}
