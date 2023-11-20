use trybuild::TestCases;

#[test]
fn typing() {
    let t = TestCases::new();
    t.pass("tests/typing/pass/*.rs");
    t.compile_fail("tests/typing/fail/*.rs");
}
