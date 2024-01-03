use rustre::sync;

sync! {
    #![pass(0)]
    
    node oui() = ()
    where
        x : bool = !!true;
}

fn main() {}
