use trybuild::TestCases;

#[test]
fn parsing() {
    let t = TestCases::new();
    t.pass("tests/parsing/pass/*.rs");
    t.compile_fail("tests/parsing/fail/*.rs");
}

#[test]
fn typing() {
    let t = TestCases::new();
    t.pass("tests/typing/pass/*.rs");
    t.compile_fail("tests/parsing/fail/*.rs");
}

#[test]
fn scheduling() {
    let t = TestCases::new();
    t.pass("tests/scheduling/pass/*.rs");
    t.compile_fail("tests/scheduling/fail/*.rs");
}

#[test]
fn codegen() {
    let t = TestCases::new();
    t.pass("tests/codegen/pass/*.rs");
    t.compile_fail("tests/codegen/fail/*.rs");
}
