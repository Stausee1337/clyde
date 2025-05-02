use std::{collections::HashMap, ops::Deref};

use proc_macro2::{extra::DelimSpan, Span, Ident, Punct, TokenStream, TokenTree, Delimiter};
use quote::{quote, ToTokens, TokenStreamExt};
use syn::{parse::{Parse, ParseStream}, spanned::Spanned, Expr, ExprLit, ExprMatch, Fields, ItemEnum, Lit, LitByteStr, LitStr, Meta, Token};

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
                pub fn precedence(self) -> u32 {
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
    let mut display = TokenStream::new();
    for mapping in map {
        let (ident, attrs) = mapping;
        let (_, lit) = attrs.first().unwrap();
        let Lit::Str(lit) = lit else {
            return Err(syn::Error::new(lit.span(), "expected string"));
        };
        display.extend(quote! { #enm_ident::#ident => #lit, });
        let lit = LitByteStr::new(lit.value().as_bytes(), lit.span());
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
            fn try_from_string(str: &[u8]) -> Option<Self> {
                const MAP: phf::Map<&'static [u8], #enm_ident> = phf::phf_map! {
                    #mappings
                };
                MAP.get(str).map(|r| *r)
            }
        }

        impl std::fmt::Display for #enm_ident {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let dis = match self {
                    #display
                };
                f.write_str(dis)
            }
        }
    })
}

struct BaseCaseHandler {
    start: LitStr,
    chain: Vec<ExprMatch>,
    resolution: TokenStream
}

fn parse_delimiter(input: ParseStream) -> syn::Result<(DelimSpan, TokenStream)> {
    input.step(|cursor| {
        if let Some((TokenTree::Group(g), rest)) = cursor.token_tree() {
            let span = g.delim_span();
            let delimiter = match g.delimiter() {
                Delimiter::Brace => span,
                _ => {
                    return Err(cursor.error("expected brace delimiter"));
                }
            };
            Ok(((delimiter, g.stream()), rest))
        } else {
            Err(cursor.error("expected delimiter"))
        }
    })
}

impl Parse for BaseCaseHandler {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let start: LitStr = input.parse()?;
        let mut chain: Vec<ExprMatch> = vec![];
        while input.peek(Token![>>]) {
            input.parse::<Token![>>]>().unwrap();
            chain.push(input.parse()?);
        }
        input.parse::<Token![=>]>()?;
        let (_, resolution) = parse_delimiter(input)?;

        Ok(Self {
            start,
            chain,
            resolution
        })
    }
}

fn ident_from_str(str: &LitStr) -> Option<Ident> {
    let value = str.value();
    if value.len() > 0 {
        return Some(Ident::new(&value, Span::call_site()))
    }
    None
}

fn join_ident_and_str(ident: &Ident, str: &LitStr) -> Ident {
    Ident::new(&format!("{}{}", ident.to_string(), str.value()), Span::call_site())
}

fn generate_handler_recursively(
    current_ident: Option<Ident>,
    remaining_chain: &[ExprMatch],
) -> TokenStream {
    if remaining_chain.is_empty() {
        return quote! { inner!(#current_ident) };
    }
    let mut mtch = remaining_chain[0].clone();

    for arm in &mut mtch.arms {
        if let Expr::Lit(ExprLit { lit: Lit::Str(str), .. }) = arm.body.deref() {
            let joined_ident = if let Some(ref current_ident) = current_ident {
                Some(join_ident_and_str(current_ident, str))
            } else {
                ident_from_str(str)
            };
            arm.body = Box::new(syn::parse2(
                generate_handler_recursively(joined_ident, &remaining_chain[1..])
            ).unwrap());
        }
    }

    quote! { #mtch }
}

pub fn generate_base_case_handler(token_stream: TokenStream) -> Result<TokenStream, syn::Error> {
    let base_case: BaseCaseHandler = syn::parse2(token_stream)?;
    let delim = base_case.resolution;

    let ident = ident_from_str(&base_case.start);
    let recusive_matches = generate_handler_recursively(
        ident, &base_case.chain);

    Ok(quote! {
        {
            macro_rules! inner {
                ($token:tt) => {{ #delim }}
            }
            #recusive_matches
        }
    })
}
