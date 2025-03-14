use crate::compile::compile;

#[test]
fn test_inference() {
    compile(include_str!("tests/inference.pebble")).unwrap();
}

#[test]
fn test_never() {
    compile(include_str!("tests/never.pebble")).unwrap();
}
