use rust_sync::sync;

sync! {
    #![pass(1)]

    node a(x : int) = (x);
}

fn main() {}
