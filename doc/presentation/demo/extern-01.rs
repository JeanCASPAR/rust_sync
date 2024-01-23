use rustre::sync;
use std::fmt::Display;

fn print_newline<T: Display>(x: T) {
    println!("{x}");
}

sync! {
    #[export]
    node f(x : int, y : int) = ()
    where
        o : bool = true -> !(pre o),
        () = print_newline(o),
        () = print_newline(x+y);
}

fn main() {
    sync::f((0..5).zip(5..10)).for_each(|()| {});
}
