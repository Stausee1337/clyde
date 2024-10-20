use proc_macro::TokenStream;

mod codegen;

#[proc_macro_derive(Internable, attributes(alias))]
pub fn derive_internable(item: TokenStream) -> TokenStream {
    codegen::generate_internable(item.into())
        .unwrap_or_else(|err| syn::Error::to_compile_error(&err))
        .into()
}

#[proc_macro_derive(Operator, attributes(op, token, precedence))]
pub fn derive_operator(_item: TokenStream) -> TokenStream {
    /*codegen::generate_internable(item.into())
        .unwrap_or_else(|err| syn::Error::to_compile_error(&err))
        .into()*/
    TokenStream::default()
}

#[proc_macro_derive(LexFromString, attributes(str))]
pub fn derive_lex_from_string(_item: TokenStream) -> TokenStream {
    /*codegen::generate_internable(item.into())
        .unwrap_or_else(|err| syn::Error::to_compile_error(&err))
        .into()*/
    TokenStream::default()
}
