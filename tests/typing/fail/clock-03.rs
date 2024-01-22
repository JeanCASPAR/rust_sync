use rustre::sync;

sync! {
    #![pass(1)]

    node oui() = ()
    where
        a : float = 3.0 whennot c;
}

fn main() {}
