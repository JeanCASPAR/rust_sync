use rustre::sync;

sync! {
    #![pass(1)]

    node oui() = (a)
    where
        a : int = false -> 3;
}

fn main() {}
