use std::time::Duration;

use rust_sync::sync;

fn f() -> bool {
    for i in 0..5 {
        std::thread::sleep(Duration::from_millis(200));
        println!("sleep 1: {}", i);
    }
    true
}

fn g() -> bool {
    std::thread::sleep(Duration::from_millis(1000));
    println!("sleep 2");
    true
}

sync! {
    #![pass(3)]

    node sleep1() = (a1)
    where
        a1 : bool = f();

    node sleep2() = (a2)
    where
        a2 : bool = g();

    #[export]
    node main(b: bool) = ()
    where
        a : bool = true -> merge b {
            true => pre spawn sleep1() when b,
            false => pre spawn sleep2() whennot b,
        }
}

fn main() {}
