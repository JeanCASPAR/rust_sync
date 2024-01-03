use rustre::sync;

sync! {
    #![pass(0)]

    node oui() = ()
    where
        () = ();
}

fn main() {}
