use rust_sync::sync;

sync! {
    #![pass(1)]
    
    node oui(hello : int, bye : bool) = (oh)
    where
        oh : int = if bye { hello } else { 3.0 };
}

fn main() {}
