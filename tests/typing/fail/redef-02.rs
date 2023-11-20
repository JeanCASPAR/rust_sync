use rust_sync::sync;

sync! {
    node oui() = (hello)
    where
        hello : int = hello,
        hello : int = hello;
}

fn main() {}
