use rust_sync::sync;

sync! {
    #![pass(1)]
    
    node oui() = (a)
    where
        a : bool = false -> !(pre a);
}

fn main() {}
