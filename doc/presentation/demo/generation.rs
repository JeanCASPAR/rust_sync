use rustre::sync;

sync! {
    node f(x : int) = (o)
    where
        o : int = 2*x;
}

fn main() {}
