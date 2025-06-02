#![expect(dead_code)]

pub mod span;

use std::{
    io,
    path::{Path, PathBuf},
    sync::{Mutex, OnceLock},
};

use index_vec::IndexVec;

use crate::HashMap;

#[derive(Default)]
pub struct Source {
    path_ids: HashMap<PathBuf, SourceId>,
    source_data: IndexVec<SourceId, (PathBuf, String)>,
}

static GLOBAL: OnceLock<Mutex<Source>> = OnceLock::new();

impl Source {
    pub fn with_global<T>(f: impl FnOnce(&mut Self) -> T) -> T {
        f(&mut GLOBAL.get_or_init(Mutex::default).lock().unwrap())
    }
    pub fn init(&mut self, path: impl Into<PathBuf>) -> io::Result<SourceId> {
        let path = path.into();
        if let Some(existing) = self.path_ids.get(&path) {
            return Ok(*existing);
        }
        let contents = std::fs::read_to_string(&path)?;
        let id = self.source_data.push((path.clone(), contents));
        self.path_ids.insert(path, id);
        Ok(id)
    }
    pub fn get_id(&self, path: impl AsRef<Path>) -> SourceId {
        *self.path_ids.get(path.as_ref()).unwrap_or_else(|| panic!("{}", path.as_ref().display()))
    }
    fn get_path(&self, id: SourceId) -> &Path {
        &self.source_data[id].0
    }
    fn get(&self, id: SourceId) -> (&Path, &str) {
        let raw = &self.source_data[id];
        (&raw.0, &raw.1)
    }
}

impl SourceId {
    pub fn path(self) -> PathBuf {
        self.get().0
    }
    pub fn contents(self) -> String {
        self.get().1
    }
    pub fn get(self) -> (PathBuf, String) {
        GLOBAL.get_or_init(Mutex::default).lock().unwrap().source_data[self].clone()
    }
}

crate::define_id! {
    pub SourceId = u16
}

impl SourceId {
    pub const NULL: Self = Self { _raw: 0 };
}
