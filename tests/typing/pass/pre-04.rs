use rust_sync::sync;

sync! {
    node oui() = (a)
    where
        a : bool = false -> !(pre a);
}

fn main() {}
