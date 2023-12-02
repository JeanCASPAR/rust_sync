use rust_sync::sync;

sync! {
    #![pass(1)]
    
    node oui() = ()
    where
        a : int = 3 + false;
}

fn main() {}
