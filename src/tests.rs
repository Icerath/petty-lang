use crate::compile::compile_test;

#[test]
fn inference() {
    compile_test(include_str!("tests/inference.pebble")).unwrap();
}

#[test]
fn never() {
    compile_test(include_str!("tests/never.pebble")).unwrap();
}

#[test]
fn arrays() {
    compile_test(include_str!("tests/arrays.pebble")).unwrap();
}

#[test]
#[should_panic = "expected `!`, found `int`"]
fn fail_never() {
    compile_test(include_str!("tests/fail_never.pebble")).unwrap();
}

#[test]
#[should_panic = "expected `int`, found `str`"]
fn fail_variables() {
    compile_test(include_str!("tests/fail_variables.pebble")).unwrap();
}

#[test]
#[should_panic = "expected `int`, found `str`"]
fn fail_return() {
    compile_test(include_str!("tests/fail_return.pebble")).unwrap();
}
