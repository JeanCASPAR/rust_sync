#![deny(missing_debug_implementations)]

use proc_macro_error::proc_macro_error;
use quote::quote;
use syn::parse_macro_input;

extern crate proc_macro;

mod codegen;
mod error;
mod parser;
mod scheduler;
mod typing;

#[proc_macro_error]
#[proc_macro]
pub fn sync(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let nodes = parse_macro_input!(input as parser::Module);
    let typed_nodes;
    let mut pass = nodes.pass;

    if pass > 0 {
        pass -= 1;
        typed_nodes = match typing::Ast::try_from(nodes) {
            Ok(x) => x,
            Err(err) => err.raise(),
        };
    } else {
        return proc_macro::TokenStream::new();
    }

    let scheduled_nodes;
    if pass > 0 {
        pass -= 1;
        scheduled_nodes = match scheduler::Ast::try_from(typed_nodes) {
            Ok(x) => x,
            Err(err) => err.raise(),
        };
    } else {
        return proc_macro::TokenStream::new();
    }

    let codegen = if pass > 0 {
        pass -= 1;
        quote! {
            #scheduled_nodes
        }
    } else {
        proc_macro2::TokenStream::new()
    };

    let s = codegen.to_string();
    let res = syn::parse_file(&s);
    if let Ok(file) = &res {
        println!("{}", prettyplease::unparse(&file));
    } else {
        println!("pretty print failed");
        println!("{}", s);
        res.unwrap();
    }

    if pass != 0 {
        // Ok...
    }

    codegen.into()
}
