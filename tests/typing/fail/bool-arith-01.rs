use rustre::sync;

sync! {
    #![pass(1)]

    node oui() = (a)
    where
        a : int = -false;
}

fn main() {}
