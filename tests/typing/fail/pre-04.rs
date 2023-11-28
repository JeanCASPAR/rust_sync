use rust_sync::sync;

sync! {
    node oui() = ()
    where
        x : bool = false -> y,
        y : bool = pre (!x);
}

fn main() {}
