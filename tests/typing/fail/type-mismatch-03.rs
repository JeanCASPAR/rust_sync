use rust_sync::sync;

sync! {
    node oui() = (a)
    where
        a : int = false -> !(pre a);
}

fn main() {}
