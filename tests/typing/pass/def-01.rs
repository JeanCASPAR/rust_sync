use rustre::sync;

sync! {
    #![pass(1)]

    node a(x : int) = (x);
}

fn main() {}
