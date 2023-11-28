use rust_sync::sync;

sync! {
    node oui() = (a, a)
    where
        a : int = 3 + oui();
}

fn main() {}
