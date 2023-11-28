use rust_sync::sync;

sync! {
    node oui() = (a)
    where
        a : int = pre 0 -> 1;
}

fn main() {}
