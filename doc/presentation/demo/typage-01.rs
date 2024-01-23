use rustre::sync;

sync! {
    node f(c : bool, d : int on c) = (x)
    where
        x : int on c = d;

    #[export]
    node g(c : bool) = (o)
    where
        a : int on c = f(c, 3 when c),
        o : int = merge c {
            true => a,
            false => 2 whennot c
        };
}

fn main() {
    for (o,) in g([true, false, false, true].into_iter().map(|x| (x,))) {
        println!("{o}");
    }
}
