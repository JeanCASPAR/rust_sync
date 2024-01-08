use trybuild::TestCases;

#[test]
fn codegen() {
    let t = TestCases::new();
    t.pass("tests/codegen/pass/*.rs");
    t.compile_fail("tests/codegen/fail/*.rs");
}
