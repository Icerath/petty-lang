use crate::compile::compile;

#[test]
fn test_inference() {
    compile(include_str!("tests/inference.pebble")).unwrap();
}

#[test]
fn test_never() {
    compile(include_str!("tests/never.pebble")).unwrap();
}

#[test]
#[should_panic = "expected `!`, found `int`"]
fn never_subtype() {
    compile(include_str!("tests/fail_never.pebble")).unwrap();
}

#[test]
#[should_panic = "expected `int`, found `str`"]
fn fail_variables() {
    compile(include_str!("tests/fail_variables.pebble")).unwrap();
}
