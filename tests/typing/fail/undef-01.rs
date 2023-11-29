use rust_sync::sync;

sync! {
    #![pass(1)]

    node oui() = (hello)
    where
        bye : int = 3;
}

fn main() {}
