use rust_sync::sync;

sync! {
    node oui() = ()
    where
        x : int = 0 -> pre y,
        y : int = 1 -> pre x;
}

fn main() {}
