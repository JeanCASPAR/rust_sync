use rust_sync::sync;

sync! {
    #![pass(0)]

    node oui(c : bool) = ()
    where
        a : int = spawn c;
}

fn main() {}
