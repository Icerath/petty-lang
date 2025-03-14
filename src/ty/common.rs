use std::fmt;

use super::{Ty, TyCtx, TyKind};

macro_rules! common {
    [$($name: ident : $kind: ident),* $(,)?] => {
        pub struct CommonTypes {
            $($name: Ty),*
        }

        impl Default for CommonTypes {
            fn default() -> Self {
                Self {
                    $($name: Ty::from(TyKind::$kind)),*
                }
            }
        }
        impl TyCtx {
            $(pub fn $name(&self) -> &Ty {
                &self.common.$name
            })*
        }
    };
}

common![
    unit: Unit,
    bool: Bool,
    int: Int,
    char: Char,
    str: Str,
    never: Never,
];

impl fmt::Debug for CommonTypes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CommonTypes").finish_non_exhaustive()
    }
}
