use rustre::sync;

sync! {
    #![pass(3)]
    
    node oui(c: bool) = (b)
    where
        b : int = merge c {
            true => (1 when c) -> (2 when c),
            false => 0 whennot c,
        };
}

trait IteratorExt: Sized {
    fn on<T>(self, f: impl FnOnce(Self) -> T) -> T {
        f(self)
    }
}

impl<T: Iterator> IteratorExt for T {}

fn main() {
    for ((res,), expected) in [(false,), (true,), (true,)]
        .into_iter()
        .on(sync::oui)
        .zip([0, 2, 2])
    {
        assert_eq!(res, expected)
    }
}
