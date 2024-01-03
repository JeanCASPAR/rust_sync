use rustre::sync;

sync! {
    #![pass(1)]
    
    node oui(a : int) = (a);

    node non(b : bool) = ()
    where
        o : int = oui(b);
}

fn main() {}
