use rustre::sync;

sync! {
    node oui() = (a)
    where
        c : bool = false,
        a : int on c = 3 when c;

    node non() = ()
    where
        c : bool = true,
        a : int on c = oui(),
        l : int = merge c {
            true => a,
            false => 1 whennot c,
        };
}

fn main() {}
