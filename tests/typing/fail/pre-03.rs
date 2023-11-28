use rust_sync::sync;

sync! {
    node oui() = (a)
    where
        a : int = 0 -> 1 -> pre pre pre 0;
}

fn main() {}
