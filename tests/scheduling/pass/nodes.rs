use rustre::sync;

sync! {
    #![pass(2)]

    node oui(a:bool) = (b)
    where
        b : bool = non(a);

    node non(c : bool) = (c);
}

fn main() {}
