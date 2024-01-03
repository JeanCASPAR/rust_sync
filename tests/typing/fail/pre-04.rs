use rustre::sync;

sync! {
    #![pass(1)]

    node oui() = ()
    where
        x : bool = false -> y,
        y : bool = pre (!x);
}

fn main() {}
