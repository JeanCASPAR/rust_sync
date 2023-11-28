use rust_sync::sync;

sync! {
    node non(a : int, b : int) = (a, b);
    
    node oui() = ()
    where
        (a : int, b : int) = if true {
            non(1, 2)
        } else {
            non(2, 1)
        };
}

fn main() {}
