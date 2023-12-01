use rust_sync::sync;

sync! {
    #![pass(2)]

    node oui() = ()
    where
        () = non();

    node non() = ();
}

fn main() {}
