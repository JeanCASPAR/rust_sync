use rustre::sync;

sync! {
    #![pass(1)]

    node oui() = (hello)
    where
        bye : int = 3;
}

fn main() {}
