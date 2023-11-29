use rust_sync::sync;

sync! {
    #![pass(1)]

    node oui() = (a)
    where
        a : int = 0 -> 1 -> pre pre pre 0;
}

fn main() {}
