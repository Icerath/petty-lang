use crate::compile::compile_test;

macro_rules! test {
    {$name: ident} => {
        #[test]
        fn $name() {
            compile_test(concat!("tests/", stringify!($name), ".pty")).unwrap();
        }
    };
    {$fails:literal $name: ident} => {
        #[test]
        #[should_panic = $fails]
        fn $name() {
            compile_test(concat!("tests/", stringify!($name), ".pty")).unwrap();
        }
    };
    {$($name:ident)*  $($fails:literal $fail_name: ident)*} => {
        $(test!($name);)*
        $(test!($fails $fail_name);)*
    };
}

test! {
    inference
    never
    arrays
    generics
    if_expr
    functions
    structs
    ref_assignment
    precedence
    chars
    strings
    format
    recursion
    refs
    variables
    logical
    // should panic
    "expected `!`, found `int`" fail_never
    "expected `int`, found `str`" fail_variables
    "expected `int`, found `str`" fail_return
    "assertion failed" fail_assert
}
