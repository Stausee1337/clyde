use proc_macro::TokenStream;

mod codegen;

#[proc_macro_derive(Internable, attributes(alias))]
pub fn derive_internable(item: TokenStream) -> TokenStream {
    codegen::generate_internable(item.into())
        .unwrap_or_else(|err| syn::Error::to_compile_error(&err))
        .into()
}
