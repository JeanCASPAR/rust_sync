use rustre::sync;

sync! {
    #![pass(1)]
    
    node f() = (x)
    where
        x : int = 3;

    node g() = ()
    where
        () = f();
}

fn main() {}
