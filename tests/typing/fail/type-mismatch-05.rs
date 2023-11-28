use rust_sync::sync;

sync! {
    node oui() = ()
    where
        a : int = 3 + false;
}

fn main() {}
