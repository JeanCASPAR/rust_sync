use std::{time::{Duration, Instant}, iter::repeat};

use rustre::sync;

fn f() -> bool {
    for i in 0..6 {
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

    node sleep1() = (a)
    where
        a : bool = f();

    node sleep2() = (b)
    where
        b : bool = g();

    #[export]
    node main() = ()
    where
        a : bool = true -> spawn sleep1(),
        b : bool = false -> spawn sleep2();
}

fn main() {
    let mut now = Instant::now();
    // `repeat(x)` renvoie le stream `x x x...`
    // `s.take(n)` renvoie le stream `s` tronqué à ses `n` premières valeurs
    for _ in sync::main(repeat(())).take(3) {
        println!("It took {:?}", now.elapsed());
        now = Instant::now();
    }
}
