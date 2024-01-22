use rustre::sync;

sync! {
    #![pass(2)]

    node oui() = ()
    where
        () = oui();
}

fn main() {}
