use rustre::sync;

sync! {
    node f(x : int) = ()
    where
        o : bool = x;
}

fn main() {}
