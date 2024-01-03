use rustre::sync;

sync! {
    #![pass(1)]
    
    node oui(a : int) = (a);

    node non() = ()
    where
        o : int = oui();
}

fn main() {}
