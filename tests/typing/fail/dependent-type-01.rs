use rustre::sync;

sync! {
    #[pass(1)]

    node oui(c : bool, x : int on bool) = ();
}

fn main() {}
