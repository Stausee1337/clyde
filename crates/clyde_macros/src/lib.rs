use proc_macro::TokenStream;

mod codegen;

#[proc_macro_derive(Operator, attributes(op, token, precedence))]
pub fn derive_operator(item: TokenStream) -> TokenStream {
    codegen::generate_operator(item.into())
        .unwrap_or_else(|err| syn::Error::to_compile_error(&err))
        .into()
}

#[proc_macro_derive(LexFromString, attributes(str))]
pub fn derive_lex_from_string(item: TokenStream) -> TokenStream {
    codegen::generate_lex_from_string(item.into())
        .unwrap_or_else(|err| syn::Error::to_compile_error(&err))
        .into()
}

#[proc_macro]
pub fn base_case_handler(item: TokenStream) -> TokenStream {
    codegen::generate_base_case_handler(item.into())
        .unwrap_or_else(|err| syn::Error::to_compile_error(&err))
        .into()
}
