use rustre::sync;

sync! {
    #![pass(0)]
    
    node oui() = ()
    where
        x : bool = 3 >= -y;
}

fn main() {}
