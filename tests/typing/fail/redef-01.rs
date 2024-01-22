use rustre::sync;

sync! {
    #![pass(1)]

    node oui(hello: int) = (hello)
    where
        hello : int = hello;
}

fn main() {}
