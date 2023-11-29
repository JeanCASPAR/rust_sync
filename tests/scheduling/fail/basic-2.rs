use rust_sync::sync;

sync! {
    #![pass(2)]

    node oui() = ()
    where
        a : int = b,
        b : int = a;
}

fn main() {}
