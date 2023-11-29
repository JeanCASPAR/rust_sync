use rust_sync::sync;

sync! {
    #![pass(2)]

    node oui() = ()
    where
        a : int = a;
}

fn main() {}
