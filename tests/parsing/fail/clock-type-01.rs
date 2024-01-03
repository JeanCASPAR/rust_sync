use rustre::sync;

sync! {
    #![pass(0)]

    node oui(c : bool) = ()
    where
        a : float = a when c when c;
}

fn main() {}
