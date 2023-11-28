use rust_sync::sync;

sync! {
    node oui() = ()
    where
        a : float = 3.0 whennot a;
}

fn main() {}
