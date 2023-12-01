use rust_sync::sync;

sync! {
    #![pass(2)]

    node oui() = ()
    where
        () = oui();
}

fn main() {}
