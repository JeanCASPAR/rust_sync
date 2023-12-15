use rust_sync::sync;

sync! {
    #![pass(1)]

    node oui(a : int) = ()
    where
        b : int = spawn non(a, 0),
}

fn main() {}
