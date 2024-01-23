use rustre::sync;

sync! {
    node f(x : int) = x; // ajouter des parenthèses autour du `x`
}

fn main() {}
