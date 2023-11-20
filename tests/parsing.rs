use trybuild::TestCases;

#[test]
fn parsing() {
    let t = TestCases::new();
    t.pass("tests/parsing/pass/*.rs");
    t.compile_fail("tests/parsiing/fail/*.rs");
}
