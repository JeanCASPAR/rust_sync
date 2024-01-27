use rustre::sync;

fn f(x: i64) -> i64 {
    x
}

sync! {
    #![pass(1)]
    
    node oui(b: bool) = ()
    where
        a : int = f(0 when b);
}

fn main() {}
