use rust_sync::sync;

sync! {
    node oui() = ()
    where
        a : float = merge c {
            true => 3.0,
            false => 2.0,
        };
}

fn main() {}
