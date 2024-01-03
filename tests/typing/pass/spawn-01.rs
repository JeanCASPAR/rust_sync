use rustre::sync;

sync! {
    #![pass(1)]

    node non(x : int, y : int) = (z)
    where
        z : int = x + y;

    node oui(a : int) = ()
    where
        b : int = 0 -> spawn non(a, pre b);
}

fn main() {}
