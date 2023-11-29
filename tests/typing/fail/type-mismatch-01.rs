use rust_sync::sync;

sync! {
    #![pass(1)]

    node oui() = ()
    where
        o : int = 3.0;
}

fn main() {}
