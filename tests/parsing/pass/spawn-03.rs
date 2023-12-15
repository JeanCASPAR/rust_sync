use rust_sync::sync;

sync! {
    #![pass(0)]
    node non(x : int, y : int) = (x, y, z)
    where
        z : int = x + y;

    node oui(a : int) = ()
    where
        b : int = 0 -> 3 * spawn non(a, pre b);
}

fn main() {}
