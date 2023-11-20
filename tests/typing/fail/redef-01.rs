use rust_sync::sync;

sync! {
    node oui(hello: int) = (hello)
    where
        hello : int = hello;
}

fn main() {}
