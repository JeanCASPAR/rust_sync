use rust_sync::sync;

sync! {
    #![pass(1)]
    
    node oui(c1 : bool, c2 : bool) = ()
    where
        a : float = merge c2 {
            true => merge c1 when c2 {
                true => (3.0 when c2) when c1,
                false => (2.0 when c2) whennot c1,
            },
            false => merge c1 {
                true => 1.0 when c1,
                false => 0.0 whennot c1,
            } whennot c2,
        };
}

fn main() {}
