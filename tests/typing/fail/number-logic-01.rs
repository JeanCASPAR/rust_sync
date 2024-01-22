use rustre::sync;

sync! {
    #![pass(1)]

    node oui() = (a)
    where
        a : bool = !3;
}

fn main() {}
