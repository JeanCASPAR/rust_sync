use rust_sync::sync;

sync! {
    node min_max() = (min, max)
    where
        min : int = 0,
        max : float = x -> 0.2 + 3 * (false) * min * if 0 { 0 + 1 } else { pre (0 -> 1) };
    node abcd() = (a)
    where
        a : float = 0 -> 1 as float + f(x, y);
}

fn main() {
    println!("Test!");
}
