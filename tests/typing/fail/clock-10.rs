use rust_sync::sync;

sync! {
    #![pass(1)]

    node oui(c1 : bool, c2 : bool) = ()
    where
        a : float = merge c1 {
            true => 3.0 when c1,
            false => 2.0 whennot c2,
        };
}

fn main() {}
