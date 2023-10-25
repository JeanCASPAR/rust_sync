extern crate proc_macro;

#[proc_macro]
pub fn sync(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = proc_macro2::TokenStream::from(input);

    let output: proc_macro2::TokenStream = {
        input /* transform input */
    };

    proc_macro::TokenStream::from(output)
}
