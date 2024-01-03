use rustre::sync;

sync! {
    #![pass(1)]

    node oui() = (a)
    where
        a : int = 0 -> (1+pre a);
}

fn main() {}
