use trybuild::TestCases;

#[test]
fn scheduling() {
    let t = TestCases::new();
    t.pass("tests/scheduling/pass/*.rs");
    t.compile_fail("tests/scheduling/fail/*.rs");
}
