use rust_sync::sync;

sync! {
    #![pass(0)]
    
    node oui() = ()
    where
        a : unit = ();
}

fn main() {}
