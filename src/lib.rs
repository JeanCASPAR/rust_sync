use proc_macro_error::proc_macro_error;
use syn::parse_macro_input;

extern crate proc_macro;

mod error;
mod parser;
#[allow(dead_code, unused_variables)]
mod scheduler;
#[allow(dead_code, unused_variables)]
mod typing;

#[proc_macro_error]
#[proc_macro]
pub fn sync(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let nodes = parse_macro_input!(input as parser::Module);
    let mut pass = nodes.pass;

    if pass > 0 {
        pass -= 1;
        let _typed_nodes = match typing::Ast::try_from(nodes) {
            Ok(x) => x,
            Err(err) => err.raise(),
        };
    }

    if pass != 0 {
        // Ok...
    }

    proc_macro::TokenStream::new()
}
