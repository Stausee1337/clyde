use std::collections::HashMap;

use proc_macro2::{TokenStream, Ident, Span, Punct};
use quote::{quote, ToTokens, TokenStreamExt};
use syn::{Meta, GenericParam, Generics, Item, Attribute, ItemEnum, Fields, spanned::Spanned, Lit, parse::{Parse, ParseStream}};

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

fn map_enum_attributes(enm: &ItemEnum, names: &'static [&'static str]) -> Result<HashMap<Ident, Vec<(&'static str, Lit)>>, syn::Error> {
    let mut map = HashMap::new();
    for variant in &enm.variants {
        let Fields::Unit = variant.fields else {
            return Err(syn::Error::new(variant.span(), "proc macro is only supported on unit variants"));
        };

        let mut attrs = Vec::new();
        for attr in &variant.attrs {
            let Meta::NameValue(name_value) = &attr.meta else {
                continue;
            };
            let Some(ident) = name_value.path.get_ident() else {
                continue;
            };

            for name in names {
                if ident.eq(name) {
                    let literal: Lit = syn::parse2(name_value.value.to_token_stream())?;
                    attrs.push((*name, literal));
                }
            }
        }

        if !attrs.is_empty() {
            map.insert(variant.ident.clone(), attrs);
        }
    }

    Ok(map)
}

struct MultiPunct {
    puncts: Vec<Punct>
}

impl Parse for MultiPunct {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut puncts = Vec::new();
        puncts.push(input.parse()?); 
        while input.cursor().punct().is_some() {
            puncts.push(input.parse()?); 
        }
        Ok(MultiPunct { puncts })
    }
}

impl ToTokens for MultiPunct {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append_all(self.puncts.iter());
    }
}

pub fn generate_operator(token_stream: TokenStream) -> Result<TokenStream, syn::Error> {
    let enm: ItemEnum = syn::parse2(token_stream)?;
    let enm_ident = &enm.ident;

    let map = map_enum_attributes(&enm, &["precedence", "token"])?;

    let mut from_punct = TokenStream::new();
    let mut precedence = TokenStream::new();
    let mut display = TokenStream::new();
    for mapping in map {
        let (ident, attrs) = mapping;
        for (attr, lit) in attrs {
            match attr {
                "precedence" => {
                    let Lit::Int(lit) = lit else {
                        return Err(syn::Error::new(lit.span(), "expected int"))
                    };
                    precedence.extend(quote! { #enm_ident::#ident => #lit, })
                }
                "token" => {
                    let Lit::Str(lit) = lit else {
                        return Err(syn::Error::new(lit.span(), "expected string"));
                    };
                    let punct = lit.parse::<MultiPunct>()?;
                    from_punct.extend(quote! { Token![#punct] => #enm_ident::#ident, });
                    display.extend(quote! { #enm_ident::#ident => #lit, });
                }
                _ => unreachable!()
            }
        }
    }

    let converter = quote! {
        impl Operator for #enm_ident {
            fn from_punct(punct: Punctuator) -> Option<Self> {
                Some(match punct {
                    #from_punct
                    _ => return None
                })
            }
        }
    };

    let precedence = if !precedence.is_empty() {
        Some(quote! {
            impl #enm_ident {
                pub fn precedence(self) -> i32 {
                    match self {
                        #precedence
                    }
                }
            }
        })
    } else {
        None
    };

    let display = quote! {
        impl std::fmt::Display for #enm_ident {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let dis = match self {
                    #display
                };
                f.write_str(dis)
            }
        }
    };

    Ok(quote! {
        #converter
        #precedence
        #display
    })
}

pub fn generate_lex_from_string(token_stream: TokenStream) -> Result<TokenStream, syn::Error> {
    let enm: ItemEnum = syn::parse2(token_stream)?;
    let enm_ident = &enm.ident;

    // let xxx = Token![->](12);
    
    let map = map_enum_attributes(&enm, &["str"])?;

    // let mut structs = TokenStream::new();
    let mut mappings = TokenStream::new();
    for mapping in map {
        let (ident, attrs) = mapping;
        let (_, lit) = attrs.first().unwrap();
        let Lit::Str(lit) = lit else {
            return Err(syn::Error::new(lit.span(), "expected string"));
        };
        mappings.extend(quote! { #lit => #enm_ident::#ident, });
        /*structs.extend(quote! {
            pub struct #ident;
            impl #ident {
                pub const TOKEN: #enm_ident = #enm_ident::#ident;
            }
        });*/
    }

    /*let mod_ident = Ident::new(
        &format!("{}s", enm_ident.to_string().to_lowercase()),
        Span::call_site());*/

    Ok(quote! {
        impl LexFromString for #enm_ident {
            fn try_from_string(str: &str) -> Option<Self> {
                const MAP: phf::Map<&'static str, #enm_ident> = phf::phf_map! {
                    #mappings
                };
                MAP.get(str).map(|r| *r)
            }
        }

        /*mod #mod_ident {
            use super::#enm_ident;
            #structs
        }*/
    })
}
