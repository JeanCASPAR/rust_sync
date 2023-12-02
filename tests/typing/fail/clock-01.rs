use rust_sync::sync;

sync! {
    #![pass(1)]
    
    node oui() = ()
    where
        a : float = 3.0 when c;
}

fn main() {}
