use rust_sync::sync;

sync! {
    node oui() = (a)
    where
        a : bool = !3;
}

fn main() {}
