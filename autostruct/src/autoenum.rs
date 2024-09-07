
use std::path;

use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::spanned::Spanned;
use syn::{parse_quote, Attribute, Error, Item, ItemEnum, LitInt, LitStr, Path, Token};
use syn::parse::Parse;

use crate::find_item::find_item;
use crate::util::{get_passthrough_attrs, take_attrs_by_name};

static SPECIAL_ATTR_NAMES: [&'static str; 2] = ["attr_first", "attr"];

struct AutoEnum {
    pub _enum_item: ItemEnum,
    pub _attrs: Vec<Attribute>,
    pub _extends_token: Token![..],
    pub _file_path: LitStr,
    pub _path: Path,
    pub _semi: Token![;],
}
impl Parse for AutoEnum {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let enum_item = input.parse()?;
        let attrs: Vec<Attribute> = input.call(Attribute::parse_outer)?;
        let _extends_token: Token![..] = input.parse()?;
        let file_path = input.parse()?;
        let path: Path = input.parse()?;
        let _semi = input.parse()?;
        Ok(AutoEnum { _enum_item: enum_item, _attrs: attrs, _extends_token, _file_path: file_path, _path: path, _semi })
    }
}

#[allow(dead_code)]
pub fn macro_main(input: TokenStream, workspace_path: impl AsRef<path::Path>, relative_file_path: impl AsRef<path::Path>) -> syn::Result<TokenStream> {
    let mut input: AutoEnum = syn::parse2(input)?;
    let mut enum_item = input._enum_item;
    let remote_enum = find_item(&workspace_path, &relative_file_path, &input._file_path, &input._path)?;
    let Item::Enum(remote_enum) = remote_enum else {
        return Err(Error::new(input._file_path.span(), format!("found {:?} is not an enum", input._path.segments.last().map(|s| &s.ident))));
    };
    let attrs_by_name = take_attrs_by_name(&mut input._attrs, &SPECIAL_ATTR_NAMES);
    // attributes for all variants
    let variant_attrs = match attrs_by_name.get("attr") {
        Some(v) => get_passthrough_attrs(v),
        None => Vec::new(),
    };

    let mut i: i128 = 0;
    // make all discriminants explicit
    let mut first = true;
    for variant in &remote_enum.variants {
        let mut variant = variant.clone();
        // Don't copy attrs from the original struct
        variant.attrs.clear();
        if let Some(discriminant) = &variant.discriminant {
            // Take explicit discriminants from remote enum if present
            let lit: LitInt = syn::parse2(discriminant.1.to_token_stream())?;
            i = lit.base10_digits().parse().unwrap();
        } else {
            // If variant on remote enum has no explicit discriminant,
            // just count up from the last
            i = i + 1;
        }
        // Set the explicit discriminant
        let int = LitInt::new(&i.to_string(), input._path.span());
        variant.discriminant = Some((Token![=](input._path.span()), parse_quote!(#int)));

        if first {
            // Apply attrs in #[attr_first(...)] to the first enum variant
            if let Some(v) = attrs_by_name.get("attr_first") {
                for attr in get_passthrough_attrs(v) {
                    variant.attrs.push(attr);
                }
            }
        }
        // Apply attrs in #[attr(...)] to each enum variant
        for attr in &variant_attrs {
            variant.attrs.push(attr.clone());
        }

        enum_item.variants.push(variant);
        first = false;
    }
    let mut token_stream = TokenStream::new();
    enum_item.to_tokens(&mut token_stream);
    let enum_name = enum_item.ident;
    let remote_name = input._path;

    // Implement conversion traits
    let mut match_tokens = TokenStream::new();
    let mut reverse_match_tokens = TokenStream::new();
    for variant in &remote_enum.variants {
        let ident = &variant.ident;
        quote!(#remote_name::#ident => #enum_name::#ident,).to_tokens(&mut match_tokens);
        quote!(#enum_name::#ident => #remote_name::#ident,).to_tokens(&mut reverse_match_tokens);
    }
    quote! {
        impl From<&#remote_name> for #enum_name {
            fn from(value: &#remote_name) -> Self {
                match value {
                    #match_tokens
                }
            }
        }
        impl From<#remote_name> for #enum_name {
            fn from(value: #remote_name) -> Self {
                match value {
                    #match_tokens
                }
            }
        }
        impl From<&#enum_name> for #remote_name {
            fn from(value: &#enum_name) -> Self {
                match value {
                    #reverse_match_tokens
                }
            }
        }
        impl From<#enum_name> for #remote_name {
            fn from(value: #enum_name) -> Self {
                match value {
                    #reverse_match_tokens
                }
            }
        }
    }.to_tokens(&mut token_stream);
    Ok(token_stream)
}
