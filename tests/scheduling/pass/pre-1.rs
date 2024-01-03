use rustre::sync;

sync! {
    #![pass(2)]

    node oui() = ()
    where
        a : int = 0 -> pre a;
}

fn main() {}
