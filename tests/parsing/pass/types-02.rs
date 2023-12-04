use rust_sync::sync;

sync! {
    #![pass(0)]
    
    node oui() = ()
    where
        a : float = 3.0;
}

fn main() {}
