use crate::compile::compile_test;

macro_rules! test {
    {$name: ident} => {
        #[test]
        fn $name() {
            compile_test(concat!("tests/", stringify!($name), ".pebble")).unwrap();
        }
    };
    {$fails:literal $name: ident} => {
        #[test]
        #[should_panic = $fails]
        fn $name() {
            compile_test(concat!("tests/", stringify!($name), ".pebble")).unwrap();
        }
    };
}

test! { inference }
test! { never }
test! { arrays }
test! { generics }
test! { if_expr }
test! { functions }
test! { structs }
test! { ref_assignment }
test! { precedence }
test! { chars }
test! { strings }
test! { format }
test! { recursion }
test! { refs }

test! { "expected `!`, found `int`" fail_never }
test! { "expected `int`, found `str`" fail_variables }
test! { "expected `int`, found `str`" fail_return }
test! { "assertion failed" fail_assert }
