use syn::parse_macro_input;

extern crate proc_macro;

mod parser;

#[proc_macro]
pub fn sync(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let _nodes = parse_macro_input!(input as parser::Nodes);

    proc_macro::TokenStream::new()
}
