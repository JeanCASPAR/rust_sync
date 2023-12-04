use rust_sync::sync;

sync! {
    #![pass(0)]
    
    node oui() = ()
    where
        a : int = 3;
}

fn main() {}
