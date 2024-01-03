use rustre::sync;

sync! {
    #![pass(0)]
    
    node oui() = ()
    where
        x : bool = !pre x;
}

fn main() {}
