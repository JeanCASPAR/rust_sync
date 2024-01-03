use rustre::sync;

sync! {
    #![pass(1)]

    node oui(c : bool) = ()
    where
        a : float = merge c {
            true => 3.0,
            false => 2.0,
        };
}

fn main() {}
