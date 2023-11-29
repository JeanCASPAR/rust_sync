use rust_sync::sync;

sync! {
    #![pass(2)]

    node oui() = ()
    where
        a : int = 0 -> 1 -> pre (pre a);
}

fn main() {}
