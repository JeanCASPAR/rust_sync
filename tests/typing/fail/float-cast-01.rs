use rust_sync::sync;

sync! {
    #![pass(1)]

    node oui() = (a)
    where
        a : float = false as float;
}

fn main() {}
