use rust_sync::sync;

sync! {
    #![pass(1)]

    node oui() = (a)
    where
        a : int = pre 0;
}

fn main() {}
