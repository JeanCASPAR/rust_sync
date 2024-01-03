use rustre::sync;

sync! {
    #![pass(1)]

    node oui() = (a, a)
    where
        a : int = 3 + oui();
}

fn main() {}
