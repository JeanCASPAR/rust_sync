use rustre::sync;

sync! {
    #![pass(1)]

    node oui() = (a)
    where
        a : int = 0 -> pre (1-a);
}

fn main() {}
