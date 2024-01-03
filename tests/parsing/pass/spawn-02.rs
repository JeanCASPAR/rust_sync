use rustre::sync;

sync! {
    #![pass(0)]
    node non(x : int, y : int) = (x, y, z)
    where
        z : int = x + y;

    node oui(a : int) = ()
    where
        b : int = spawn non(a, 2);
}

fn main() {}
