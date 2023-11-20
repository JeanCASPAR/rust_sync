use rust_sync::sync;

sync! {
    node oui() = (hello)
    where
        bye : int = 3;
}

fn main() {}
