use crate::compile::compile_test;

macro_rules! include_test {
    ($name:literal) => {
        include_str!(concat!("../tests/", $name, ".pebble"))
    };
}

#[test]
fn inference() {
    compile_test(include_test!("inference")).unwrap();
}

#[test]
fn never() {
    compile_test(include_test!("never")).unwrap();
}

#[test]
fn arrays() {
    compile_test(include_test!("arrays")).unwrap();
}

#[test]
#[should_panic = "expected `!`, found `int`"]
fn fail_never() {
    compile_test(include_test!("fail_never")).unwrap();
}

#[test]
#[should_panic = "expected `int`, found `str`"]
fn fail_variables() {
    compile_test(include_test!("fail_variables")).unwrap();
}

#[test]
#[should_panic = "expected `int`, found `str`"]
fn fail_return() {
    compile_test(include_test!("fail_return")).unwrap();
}
