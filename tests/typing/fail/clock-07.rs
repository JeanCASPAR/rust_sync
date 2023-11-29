use rust_sync::sync;

sync! {
    #![pass(1)]

    node oui(c : bool) = ()
    where
        a : float = merge c {
            true => (3.0 when c) when c,
            false => (2.0 when c) whennot c,
        };
}

fn main() {}
