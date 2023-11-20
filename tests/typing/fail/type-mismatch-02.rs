use rust_sync::sync;

sync! {
    node oui(hello : int, bye : bool) = (oh)
    where
        oh : int = if bye { hello } else { 3.0 };
}

fn main() {}
