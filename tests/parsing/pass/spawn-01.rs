use rustre::sync;

sync! {
    #![pass(0)]
    node non() = ();

    node oui() = ()
    where
        a : int = spawn non();
}

fn main() {}
