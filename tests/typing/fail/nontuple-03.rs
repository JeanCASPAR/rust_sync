use rustre::sync;

sync! {
    #![pass(1)]

    node non(a : int, b : int) = (a, b);

    node oui() = ()
    where
        (a : int, b : int) = non(2, 1) as float;
}

fn main() {}
