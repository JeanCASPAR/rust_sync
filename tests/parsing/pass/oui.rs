use rust_sync::sync;

sync! {
    node min_max() = (min, max)
    where
        min : int = 0,
        max : float = x -> 0.2 + 3 * (false) * min * if 0 { 0 + 1 } else { pre (0 -> 1) };
    node abcd(foo: int, bar: bool) = (d)
    where
        a : float = 0 -> 1 as float + f(x, y),
        x: int, y:float = 0,
        () = 0,
        (a: int, y:float) = 3,
        () = f();
}

fn main() {}
