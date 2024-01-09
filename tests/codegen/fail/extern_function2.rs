use rust_sync::sync;

fn f(x: f64) -> f64 {
    x * 2.0
}

sync! {
    #![pass(3)]

    node non(c : bool) = (a,)
    where
        a : float = merge c {
            true => 3.0 when c,
            false => 2.0 whennot c,
        };

    #[export]
    node oui(c : bool) = (d)
    where
        b : float = 0.0 -> pre spawn non(c),
        d : int = f(b);
}

fn main() {
    let mut oui = sync::Nodeoui::new();
    let mut v = Vec::with_capacity(10);
    for b in [true, false, true, false, true] {
        v.push(oui.step((b,)).0);
    }
    oui.reset();
    for b in [false, true, false, true, true] {
        v.push(oui.step((b,)).0);
    }
    assert_eq!(v, [0, 6, 4, 6, 4, 0, 4, 6, 4, 6]);
}
