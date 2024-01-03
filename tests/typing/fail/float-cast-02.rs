use rustre::sync;

sync! {
    #![pass(1)]

    node oui() = (a)
    where
        a : float = 3.0 as float;
}

fn main() {}
