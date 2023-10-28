use rust_sync::sync;

sync! {
    node min_max() = (min, max)
    where
        min : int = 0,
        // TODO -> ne marche pas
        /* les commentaires marchent, eux */
        max : float = 0.2 + 3 * (false) * min * if 0 { 0 + 1 } else { pre 0 - 1 };
    node abcd(a: int, b: bool, y: float) = (a,  ui, ret)
    where
        azfzefd : float = true;
}

fn main() {
    println!("Test!");
}
