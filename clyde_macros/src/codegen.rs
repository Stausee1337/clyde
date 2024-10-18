use proc_macro2::{TokenStream, Ident, Span};
use quote::{quote, ToTokens, quote_spanned, TokenStreamExt};
use syn::{ItemStruct, Meta, GenericParam, punctuated::Punctuated, Token, Generics, Item, Attribute};

fn ident(item: &Item) -> Result<&Ident, syn::Error> {
    match item {
        Item::Struct(s) => Ok(&s.ident),
        Item::Enum(e) => Ok(&e.ident),
        _ => Err(syn::Error::new(Span::call_site(), format!("expected `enum` or `struct`")))
    }
}

fn attrs(item: &Item) -> Result<&Vec<Attribute>, syn::Error> {
    match item {
        Item::Struct(s) => Ok(&s.attrs),
        Item::Enum(e) => Ok(&e.attrs),
        _ => Err(syn::Error::new(Span::call_site(), format!("expected `enum` or `struct`")))
    }
}

fn generics(item: &Item) -> Result<&Generics, syn::Error> {
    match item {
        Item::Struct(s) => Ok(&s.generics),
        Item::Enum(e) => Ok(&e.generics),
        _ => Err(syn::Error::new(Span::call_site(), format!("expected `enum` or `struct`")))
    }
}

pub fn generate_internable(token_stream: TokenStream) -> Result<TokenStream, syn::Error> {
    let item: Item = syn::parse2(token_stream)?;
    let ident = ident(&item)?;
    let name = ident.to_string();

    let marker_ident = Ident::new(&format!("MarkerFor{name}"), Span::call_site());
    let mut alias = None;
    for attr in attrs(&item)? {
        let Meta::List(list) = &attr.meta else {
            continue;
        };
        let Some(ident) = list.path.get_ident() else {
            continue;
        };
        if !ident.eq("alias") {
            continue;
        }
        alias = Some(list.tokens.clone());
    }

    let alias = alias.ok_or_else(
        || syn::Error::new(Span::call_site(), format!("Expected #[alias(...)] for internable {name}")))?;

    // let mut lifetimes = Punctuated::<GenericParam, Token![,]>::new();
    let mut new_generics = Generics::default();
    let lifetimes = &mut new_generics.params;
    for generic in  &generics(&item)?.params {
        if let GenericParam::Lifetime(..) = generic {
            lifetimes.push(generic.clone());
        }
    }

    Ok(quote! {
        #[doc(hidden)]
        pub struct #marker_ident;

        impl<'tcx> crate::context::Internable<'tcx> for #ident #new_generics {
            type Marker = #marker_ident;
            type Interned<'a> = #alias<'a>;

            fn intern(self, tcx: crate::context::TyCtxt<'tcx>) -> Self::Interned<'tcx> {
                #alias(tcx.interner.intern(self, tcx))
            }
        }
    })
}
