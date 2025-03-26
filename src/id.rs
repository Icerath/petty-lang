#[macro_export]
macro_rules! define_id {
    ($vis:vis $name:ident) => { $crate::define_id!($vis $name = u32); };
    ($vis:vis $name:ident = $repr:ident) => { index_vec::define_index_type! {
        $vis struct $name = $repr;
        DISABLE_MAX_INDEX_CHECK = cfg!(not(debug_assertions));
    } }
}
