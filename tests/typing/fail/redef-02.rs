use rustre::sync;

sync! {
    #![pass(1)]

    node oui() = (hello)
    where
        hello : int = hello,
        hello : int = hello;
}

fn main() {}
