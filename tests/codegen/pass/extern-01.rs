use rustre::sync;

fn f(x: f64) -> f64 {
    x * 2.
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
        b : float = 0.0 -> spawn non(c),
        d : float = f(b);
}

fn main() {
    assert_eq!(
        sync::oui([true, false, true, false, true].into_iter().map(|x| (x,)))
            .map(|(d,)| d)
            .collect::<Vec<_>>(),
        [0.0, 6.0, 4.0, 6.0, 4.0],
    )
}
