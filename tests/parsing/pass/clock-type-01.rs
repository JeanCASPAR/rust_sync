use rust_sync::sync;

sync! {
    #![pass(0)]

    node oui(c : bool) = ()
    where
        y : bool on c = (false when c) -> pre (!y),
        a : float on c = merge y {
            true => (3.0 when c) when y,
            false => (2.0 when c) whennot y,
        };
}

fn main() {}
