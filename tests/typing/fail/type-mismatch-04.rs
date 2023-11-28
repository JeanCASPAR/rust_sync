use rust_sync::sync;

sync! {
    node oui() = (a)
    where
        a : int = false -> 3;
}

fn main() {}
