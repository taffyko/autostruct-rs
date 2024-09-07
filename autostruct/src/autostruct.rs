use crate::util::{take_attrs_by_name};
use proc_macro2::{Span, TokenStream, TokenTree, Group};
use quote::{ToTokens, quote_spanned};
use syn::ext::IdentExt;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::visit_mut::VisitMut;
use syn::{braced, parse2, parse_quote, parse_quote_spanned, token, AngleBracketedGenericArguments, AttrStyle, Attribute, Block, Error, Expr, ExprStruct, Field, FieldValue, Fields, FieldsNamed, GenericArgument, Ident, Item, ItemImpl, ItemStruct, LitStr, Macro, Meta, MetaList, Path, PathArguments, Stmt, Token, Type, Visibility};
use syn::parse::{Parse, ParseStream, Parser};
use std::collections::{HashSet, HashMap};
use std::hash::Hash;
use std::path;

use super::find_item::find_item;

pub struct AutoStructBody {
    pub struct_item: ItemStruct,
    pub mixins: Vec<AutoStructMixin>,
    pub impls: Vec<ItemImpl>,
}
#[derive(Clone)]
pub struct AutoStructExplicitField {
    pub attrs: Vec<Attribute>,
    pub vis: Visibility,
    pub ident: Ident,
    pub colon_token: Option<Token![:]>,
    pub ty: Option<Type>,
}
impl ToTokens for AutoStructExplicitField {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for attr in &self.attrs {
            attr.to_tokens(tokens);
        }
        self.vis.to_tokens(tokens);
        self.ident.to_tokens(tokens);
        self.colon_token.to_tokens(tokens);
        self.ty.to_tokens(tokens);
    }
}

/// Recurses through the `TokenTree`s in a stream and overwrites all tokens to have the same span
pub fn overwrite_token_spans(stream: TokenStream, span: Span) -> TokenStream {
    let mut new_token_stream = TokenStream::new();
    for mut token in stream {
        match &mut token {
            TokenTree::Group(tt) => {
                *tt = Group::new(tt.delimiter(), overwrite_token_spans(tt.stream(), span));
                tt.set_span(span);
            }
            _ => { token.set_span(span); }
        };
        token.to_tokens(&mut new_token_stream)
    }
    new_token_stream
}


pub struct AutoStructMixin {
    pub attrs: Vec<Attribute>,
    pub vis: Visibility,
    pub extends_token: Token![..],
    pub file_path: LitStr,
    pub path: Path,
    pub _brace_token: token::Brace,
    pub explicit_fields: Punctuated<AutoStructExplicitField, Token![,]>,
}
impl Parse for AutoStructMixin {
    fn parse(input: ParseStream) -> Result<Self, syn::Error> {
        let attrs: Vec<Attribute> = input.call(Attribute::parse_outer)?;
        let vis: Visibility = input.parse()?;
        let extends_token: Token![..] = input.parse()?;
        let file_path = input.parse()?;
        let path: Path = input.parse()?;
        let content;
        let brace_token = braced!(content in input);
        let explicit_fields = content.parse_terminated(AutoStructExplicitField::parse, Token![,])?;
        Ok(AutoStructMixin { attrs, vis, extends_token, file_path, path, _brace_token: brace_token, explicit_fields })
    }
}
impl Parse for AutoStructBody {
    fn parse(input: ParseStream) -> Result<Self, syn::Error> {
        let mut struct_item: Option<ItemStruct> = None;
        let mut mixins = Vec::new();
        let mut impls = Vec::new();
        while !input.is_empty() {
            let forked = input.fork();
            let _ = forked.call(Attribute::parse_outer)?;
            if forked.peek(Token![..]) || forked.peek2(Token![..]) {
                mixins.push(input.parse::<AutoStructMixin>()?);
            } else if forked.peek(Token![impl]) {
                impls.push(input.parse::<ItemImpl>()?);
            } else if forked.peek(Token![struct]) || forked.peek2(Token![struct]) {
                if struct_item.is_some() {
                    let struct_item: ItemStruct = input.parse()?;
                    Err(Error::new(struct_item.span(), "expected no more than one `struct` item"))?;
                }
                struct_item = Some(input.parse()?);
            } else {
                forked.span();
                Err(Error::new(forked.span(), "expected one of `..`, `struct` `impl`, `pub struct`, `pub ..`"))?;
            }
        }
        let Some(struct_item) = struct_item else { Err(Error::new(input.span(), "expected at least one `struct` item"))? };
        Ok(AutoStructBody { struct_item, mixins, impls })
    }
}
impl Parse for AutoStructExplicitField {
    fn parse(input: ParseStream) -> Result<Self, syn::Error> {
        let attrs: Vec<Attribute> = input.call(Attribute::parse_outer)?;
        let vis: Visibility = input.parse()?;
        let ident = input.call(Ident::parse_any)?;
        let mut colon_token: Option<Token![:]> = None;
        let mut ty: Option<Type> = None;
        if input.peek(Token![:]) {
            colon_token = Some(input.parse()?);
            ty = Some(input.parse()?);
        }
        Ok(AutoStructExplicitField {
            attrs,
            vis,
            ident,
            colon_token,
            ty,
        })
    }
}

#[derive(Clone)]
pub struct MappingAttributeFunction {
    // Hints that the value should not be passed into the mapping function by reference
    move_token: Option<Token![move]>,
    // Hints that the mapping function is fallible
    question_token: Option<Token![?]>,
    map_fn: Expr,
}
impl Parse for MappingAttributeFunction {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut move_token = None;
        let mut question_token = None;
        if input.peek(Token![move]) {
            move_token = Some(input.parse()?);
        }
        if input.peek(Token![?]) {
            question_token = Some(input.parse()?);
        }
        let map_fn = input.parse()?;
        Ok(MappingAttributeFunction {
            move_token,
            map_fn,
            question_token,
        })
    }
}

pub struct FieldMappingAttributeContent {
    /// Hints that the two types are actually the same, just written differently. The field should simply be assigned.
    pub as_token: Option<Token![as]>,
    // Callable expression, such as a closure or function name
    pub map_fn: Option<MappingAttributeFunction>,
    pub reverse_map_fn: Option<MappingAttributeFunction>,
}
impl Parse for FieldMappingAttributeContent {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut as_token = None;
        let mut map_fn = None;
        let mut reverse_map_fn = None;
        'opt: {
            if input.is_empty() { break 'opt }
            if input.peek(Token![as]) {
                as_token = input.parse()?;
                if input.is_empty() { break 'opt }
                input.parse::<Token![,]>()?;
            }
            if input.is_empty() { break 'opt }
            if !input.peek(Token![_]) {
                map_fn = Some(input.parse()?);
            } else {
                input.parse::<Token![_]>()?;
            }
            if input.is_empty() { break 'opt }
            input.parse::<Token![,]>()?;
            if input.is_empty() { break 'opt }
            if !input.peek(Token![_]) {
                reverse_map_fn = Some(input.parse()?);
            } else {
                input.parse::<Token![_]>()?;
            }
            if input.is_empty() { break 'opt }
            input.parse::<Token![,]>()?;
        }
        Ok(FieldMappingAttributeContent { as_token, map_fn, reverse_map_fn })
    }
}
/// Mixin-level `#[map(ty1, ty2)]` attribute.
/// <br> NOTE: The source type in a mapping must be written
/// the same way it is written in the source struct declaration
pub struct TypeMappingAttributeContent {
    pub from_ty: Type,
    /// Hints that the two types are actually the same, just written differently
    pub as_token: Option<Token![as]>,
    pub to_ty: Type,
    pub map_fn: Option<MappingAttributeFunction>,
    pub reverse_map_fn: Option<MappingAttributeFunction>,
}
impl Parse for TypeMappingAttributeContent {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut as_token = None;
        let from_ty = input.parse().map_err(|e| Error::new(e.span(), "expected a type"))?;
        if input.peek(Token![as]) {
            as_token = Some(input.parse()?);
        } else {
            input.parse::<Token![,]>().map_err(|e| Error::new(e.span(), "expected `,` or `as`"))?;
        }
        let to_ty = input.parse().map_err(|e| Error::new(e.span(), "expected a type"))?;
        let mut map_fn = None;
        let mut reverse_map_fn = None;
        'opt: {
            if input.is_empty() { break 'opt }
            input.parse::<Token![,]>()?;
            if input.is_empty() { break 'opt }
            if !input.peek(Token![_]) {
                map_fn = Some(input.parse()?);
            } else {
                input.parse::<Token![_]>()?;
            }
            if input.is_empty() { break 'opt }
            input.parse::<Token![,]>()?;
            if input.is_empty() { break 'opt }
            if !input.peek(Token![_]) {
                reverse_map_fn = Some(input.parse()?);
            } else {
                input.parse::<Token![_]>()?;
            }
            if input.is_empty() { break 'opt }
            input.parse::<Token![,]>()?;
        }
        Ok(TypeMappingAttributeContent { from_ty, as_token, to_ty, map_fn, reverse_map_fn })
    }
}

#[allow(dead_code)]
struct InitMacro {
    pub path: Path,
    pub comma_token: Option<Token![,]>,
    pub prefix: Option<Ident>,
}
impl Parse for InitMacro {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let path = input.parse()?;
        let mut comma_token = None;
        let mut prefix = None;
        if !input.is_empty() {
            comma_token = input.parse()?;
            prefix = input.parse()?;
        }
        Ok(InitMacro { path, comma_token, prefix })
    }
}

#[allow(dead_code)]
struct FieldsMacro {
    pub target_struct_path: Path,
    pub comma_token_1: Option<Token![,]>,
    /// Variable to access the fields from
    pub ident: Ident,
    pub colon_token: Token![:],
    pub src_struct_path: Path,
    pub comma_token_2: Option<Token![,]>,
    pub prefix: Option<Ident>,
}
impl Parse for FieldsMacro {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let target_struct_path = input.parse()?;
        let comma_token_1 = input.parse()?;
        let ident = input.call(Ident::parse_any)?;
        let colon_token = input.parse()?;
        let src_struct_path = input.parse()?;
        let mut comma_token_2 = None;
        let mut prefix = None;
        if !input.is_empty() {
            comma_token_2 = input.parse()?;
            prefix = input.parse()?;
        }
        Ok(FieldsMacro { target_struct_path, comma_token_1, ident, colon_token, src_struct_path, comma_token_2, prefix })
    }
}

/// Version of syn::Type that hashes based on its tokenized String
/// (only considers two types the same when they are written identically)
#[allow(dead_code)]
struct TypeStringComparable(Type, String);
impl Hash for TypeStringComparable {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.1.hash(state);
    }
}
impl From<Type> for TypeStringComparable {
    fn from(value: Type) -> Self {
        let s = value.to_token_stream().to_string();
        TypeStringComparable(value, s)
    }
}
impl From<&Type> for TypeStringComparable {
    fn from(value: &Type) -> Self {
        let s = value.to_token_stream().to_string();
        TypeStringComparable(value.clone(), s)
    }
}
impl std::cmp::Eq for TypeStringComparable { }
impl PartialEq for TypeStringComparable {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1
    }
}
impl PartialEq<Type> for TypeStringComparable {
    fn eq(&self, other: &Type) -> bool {
        self.1 == other.clone().to_token_stream().to_string()
    }
}

/// Represents data for fields to be produced in a generated struct
struct AutoStructMacroField {
    field: Field,
    map_fn: Option<MappingAttributeFunction>,
    from_struct_path: Option<Path>,
}

static SPECIAL_ATTR_NAMES: [&'static str; 4] = ["map", "mapgeneric", "exclude", "attr"];

#[allow(dead_code)]
pub fn macro_main(input: TokenStream, workspace_path: impl AsRef<path::Path>, relative_file_path: impl AsRef<path::Path>) -> syn::Result<TokenStream> {
    // Parse the input tokens into a syntax tree.
    let mut input: AutoStructBody = syn::parse2(input)?;
    let mut new_struct = input.struct_item.clone();

    fn get_passthrough_attrs(attrs_by_name: &HashMap<String, Vec<MetaList>>) -> Vec<Attribute> {
        // parse #[attrs(...)]
        let mut field_attrs = Vec::new();
        if let Some(attrs) = attrs_by_name.get("attr") {
            for attr in attrs {
                field_attrs.extend(attr.parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated).unwrap().into_iter().map(|meta| {
                    Attribute {
                        pound_token: token::Pound::default(),
                        style: AttrStyle::Outer,
                        bracket_token: token::Bracket::default(),
                        meta: meta.clone(),
                    }
                }));
            }
        }
        field_attrs
    }

    let struct_name = new_struct.ident.to_string();
    let mut fields_by_struct: HashMap<String, Vec<AutoStructMacroField>> = HashMap::new();
    fields_by_struct.insert(struct_name.clone(), Vec::new());
    // Add explicit struct fields
    for field in &new_struct.fields {
        fields_by_struct.get_mut(&struct_name).unwrap().push(AutoStructMacroField {
            field: field.clone(),
            map_fn: None,
            from_struct_path: None,
        })
    }

    let Fields::Named(new_struct_fields) = &mut new_struct.fields else { return Err(Error::new(new_struct.ident.span(), "only c-style structs allowed")) };

    for mixin in &input.mixins {
        let mixin_struct = find_item(&workspace_path, &relative_file_path, &mixin.file_path, &mixin.path)?;
        let Item::Struct(mixin_struct) = mixin_struct else {
            return Err(Error::new(mixin.file_path.span(), format!("found {:?} is not a struct", mixin.path.segments.last().map(|s| &s.ident))));
        };
        let Fields::Named(mixin_struct_fields) = &mixin_struct.fields else { return Err(Error::new(mixin_struct.ident.span(), "only c-style structs allowed")) };

        let mut mixin_level_attrs = mixin.attrs.clone();
        let attrs_by_name = take_attrs_by_name(&mut mixin_level_attrs, &SPECIAL_ATTR_NAMES);
        mixin_level_attrs.extend(get_passthrough_attrs(&attrs_by_name));

        let mixin_struct_path_string = mixin.path.to_token_stream().to_string();
        fields_by_struct.insert(mixin_struct_path_string.clone(), Vec::new());

        // parse #[exclude(...)]
        let mut excluded_fields = HashSet::new();
        if let Some(attrs) = attrs_by_name.get("exclude") {
            for attr in attrs {
                excluded_fields.extend(attr.parse_args_with(Punctuated::<Ident, Token![,]>::parse_terminated).unwrap());
            }
        }
        // parse #[map(ty1, ty2, )]
        let mut type_mappings = HashMap::<TypeStringComparable, TypeMappingAttributeContent>::new();
        if let Some(attrs) = attrs_by_name.get("map") {
            for meta_list in attrs {
                let type_mapping: TypeMappingAttributeContent = syn::parse2(meta_list.tokens.clone())
                    .map_err(|e| {
                        if meta_list.tokens.is_empty() { Error::new(meta_list.span(), e.to_string()) }
                        else { e }
                    })?;
                type_mappings.insert(type_mapping.from_ty.clone().into(), type_mapping);
            }
        }

        // parse #[mapgeneric(ty1, ty2, )]
        let mut generic_type_mappings = HashMap::<TypeStringComparable, TypeMappingAttributeContent>::new();
        if let Some(attrs) = attrs_by_name.get("mapgeneric") {
            for meta_list in attrs {
                let type_mapping: TypeMappingAttributeContent = syn::parse2(meta_list.tokens.clone())
                    .map_err(|e| {
                        if meta_list.tokens.is_empty() { Error::new(meta_list.span(), e.to_string()) }
                        else { e }
                    })?;
                generic_type_mappings.insert(type_mapping.from_ty.clone().into(), type_mapping);
            }
        }

        let mut explicit_fields: Vec<_> = mixin.explicit_fields.iter().collect();

        // copy fields from base struct
        for field in &mixin_struct_fields.named {
            // overwrite spans of imported fields
            let mut field = Field::parse_named.parse2(overwrite_token_spans(field.to_token_stream(), mixin.extends_token.span()))?;
            let ident = field.ident.as_ref().unwrap();
            if let Some(_) = new_struct_fields.named.iter().find(|f| f.ident.as_ref().unwrap() == ident) {
                continue;
            }

            // skip private fields on the mixin struct
            let Visibility::Public(_) = field.vis else { continue };

            // skip excluded fields from being generated on the resulting struct
            // but still record them for inclusion in the INIT! macro expansion of the mixin type
            if excluded_fields.contains(field.ident.as_ref().unwrap()) { 
                fields_by_struct.get_mut(&mixin_struct_path_string).unwrap().push(AutoStructMacroField {
                    field: field.clone(),
                    map_fn: None,
                    from_struct_path: None,
                });
                continue;
            }

            let mut map_fn = None;
            let mut reverse_map_fn = None;

            let mixin_field = field.clone();
            let mut explicit_ty = false;
            let mut aliased_ty = false;

            if let Some(explicit_field_idx) = explicit_fields.iter().position(|f| &f.ident == ident) {
                let explicit_field = explicit_fields.remove(explicit_field_idx);
                // overrides from fields named explicitly in mixin body

                // field visibility
                field.vis = explicit_field.vis.clone();

                let mut field_attrs = explicit_field.attrs.clone();
                let attrs_by_name = take_attrs_by_name(&mut field_attrs, &SPECIAL_ATTR_NAMES);

                // field-level #[map] attribute
                if let Some(Some(meta_list)) = attrs_by_name.get("map").map(|v| v.iter().next()) {
                    let mapping_attr: FieldMappingAttributeContent = syn::parse2(meta_list.tokens.clone())?;
                    map_fn = mapping_attr.map_fn;
                    reverse_map_fn = mapping_attr.reverse_map_fn;
                    aliased_ty = mapping_attr.as_token.is_some();
                };

                // field-level type mapping
                if let Some(ty) = &explicit_field.ty {
                    field.ty = ty.clone();
                    explicit_ty = true;
                }
                // attribute passthroughs
                let passthrough_attrs = get_passthrough_attrs(&attrs_by_name);
                field_attrs.extend(passthrough_attrs);
                field.attrs = field_attrs;
            } else {
                // apply mixin-level defaults for fields not named explicitly
                field.attrs = mixin_level_attrs.clone();
                field.vis = mixin.vis.clone();
            }

            // mixin-level #[map] attribute
            if let Some((_, type_mapping)) = type_mappings.iter().find(|t| t.0 == &mixin_field.ty.clone()) {
                // Apply mixin-level type mapping if no explicit type mapping was applied
                if !explicit_ty {
                    field.ty = type_mapping.to_ty.clone();
                    aliased_ty = type_mapping.as_token.is_some();
                }
                
                // Use mixin-level mapping functions if none were were provided at the field-level
                // (unless a field-level type mapping set the field to a different target type than the mixin-level type mapping)
                if TypeStringComparable::from(field.ty.clone()) == type_mapping.to_ty {
                    if map_fn.is_none() {
                        map_fn = type_mapping.map_fn.clone();
                    }
                    if reverse_map_fn.is_none() {
                        reverse_map_fn = type_mapping.reverse_map_fn.clone();
                    }
                }
            }
            
            let mut has_type_mapping = !aliased_ty && TypeStringComparable::from(field.ty.clone()) != mixin_field.ty;
            let has_explicit_type = aliased_ty || explicit_ty || has_type_mapping;

            // Check if from_ty and to_ty are both generic types
            fn get_bare_generic_type(ty: &Type) -> (Option<Type>, Option<Type>) {
                let mut ty = ty.clone();
                match &mut ty {
                    Type::Path(p) => 'a: {
                        if let Some(last_segment) = p.path.segments.last_mut() {
                            if let PathArguments::AngleBracketed(AngleBracketedGenericArguments { args, .. }) = &last_segment.arguments {
                                let mut inner_ty = None;
                                if let Some(GenericArgument::Type(ty)) = args.first() {
                                    inner_ty = Some(ty.clone());
                                }
                                last_segment.arguments = PathArguments::None;
                                break 'a (Some(ty), inner_ty);
                            } 
                        }
                        (None, None)
                    },
                    _ => (None, None)
                }
            }

            fn set_first_generic_arg(ty: &mut Type, new_inner_ty: Type) {
                match ty {
                    Type::Path(p) => {
                        if let Some(last_segment) = p.path.segments.last_mut() {
                            let new_args: AngleBracketedGenericArguments = parse_quote!(<#new_inner_ty>);
                            last_segment.arguments = PathArguments::AngleBracketed(new_args);
                            // if let PathArguments::AngleBracketed(AngleBracketedGenericArguments { args, .. }) = &last_segment.arguments {
                            //     if let Some(GenericArgument::Type(inner_ty)) = args.first_mut() {
                            //         *inner_ty = new_inner_ty.clone();
                            //     }
                            // } 
                        }
                    },
                    _ => {}
                }
            }
            
            // Handle generic type mappings

            if !has_explicit_type || (map_fn.is_none() || reverse_map_fn.is_none()) {
                // Get the bare type name (without type args) of each type
                // Extract the inner type of the first generic argument from each
                let (generic_from_ty, inner_from_ty) = get_bare_generic_type(&mixin_field.ty);
                let (generic_to_ty, inner_to_ty) = get_bare_generic_type(&field.ty);
                
                if let (Some(generic_from_ty), Some(mut generic_to_ty), Some(inner_from_ty), Some(mut inner_to_ty)) = (generic_from_ty, generic_to_ty, inner_from_ty, inner_to_ty) {
                    // See if a generic type mapping exists that matches the bare generic types involved
                    let generic_type_mapping = generic_type_mappings.get(&TypeStringComparable::from(generic_from_ty));
                    // Check if mapping functions exist for those inner types
                    let inner_type_mapping = type_mappings.get(&TypeStringComparable::from(inner_from_ty));
                    
                    if !has_explicit_type {
                        // No mapping: e.g. Option<i32> to Option<i32>
                        // Update the outer types if #[mapgeneric(Option, Result)] exists.
                        if let Some(generic_type_mapping) = &generic_type_mapping {
                            generic_to_ty = generic_type_mapping.to_ty.clone();
                            has_type_mapping = true;
                        }
                        // Update the inner types if #[map(i32, i64)] exists.
                        if let Some(inner_type_mapping) = &inner_type_mapping {
                            inner_to_ty = inner_type_mapping.to_ty.clone();
                            has_type_mapping = true;
                        }
                    } 
                    
                    let from_ty = &mixin_field.ty;

                    let mut to_ty = generic_to_ty.clone();
                    set_first_generic_arg(&mut to_ty, inner_to_ty.clone());
                    
                    'i: {
                        if !(map_fn.is_none() || reverse_map_fn.is_none()) { break 'i }
                        let Some(generic_type_mapping) = generic_type_mapping else { break 'i };
                        if TypeStringComparable::from(&generic_type_mapping.to_ty) != generic_to_ty { break 'i }
                        
                        'j: {
                            let Some(inner_type_mapping) = inner_type_mapping else { break 'j };
                            if TypeStringComparable::from(&inner_type_mapping.to_ty) != inner_to_ty { break 'j }
                                
                            // Mixin or field-level mapping: Option<i32> to Option<i64>, no mapping functions
                            // Provide one if #[mapgeneric(Option, Option)] and #[map(i32, i64)] exist.

                            let span = Span::call_site(); // will be overwritten

                            // Final mapping function is generic_map_fn(obj, inner_map_fn)
                            if map_fn.is_none() {
                                if let (
                                    Some(MappingAttributeFunction { map_fn: generic_map_fn, question_token, move_token }),
                                    Some(inner_map_fn),
                                ) = (&generic_type_mapping.map_fn, &inner_type_mapping.map_fn) {
                                    let v: Expr = parse_quote!(v);
                                    let fn_call = expand_map_fn(inner_map_fn.clone(), span.clone(), v.clone(), move_token.is_none())?;
                                    map_fn = Some(MappingAttributeFunction {
                                        question_token: question_token.clone(),
                                        move_token: move_token.clone(),
                                        map_fn: parse_quote!(|obj: #from_ty| (#generic_map_fn)(obj, |#v| #fn_call)),
                                    });
                                }
                            }
                            if reverse_map_fn.is_none() {
                                if let (
                                    Some(MappingAttributeFunction { map_fn: generic_map_fn, question_token, move_token }),
                                    Some(inner_map_fn),
                                ) = (&generic_type_mapping.reverse_map_fn, &inner_type_mapping.reverse_map_fn) {
                                    let v: Expr = parse_quote!(v);
                                    let fn_call = expand_map_fn(inner_map_fn.clone(), span.clone(), v.clone(), move_token.is_none())?;
                                    reverse_map_fn = Some(MappingAttributeFunction {
                                        question_token: question_token.clone(),
                                        move_token: move_token.clone(),
                                        map_fn: parse_quote!(|obj: #to_ty| (#generic_map_fn)(obj, |#v| #fn_call)),
                                    });
                                }
                            }
                        }
                        
                        // Mixin or field-level mapping: Option<i32> to Result<i64>, no mapping function
                        // Provide one if #[mapgeneric(Option, Result)] exists
                        if map_fn.is_none() {
                            if let Some(MappingAttributeFunction { map_fn: generic_map_fn, question_token, move_token }) = &generic_type_mapping.map_fn {
                                map_fn = Some(MappingAttributeFunction {
                                    question_token: question_token.clone(),
                                    move_token: move_token.clone(),
                                    map_fn: parse_quote!(|obj: #from_ty| (#generic_map_fn)(obj, |item| item)),
                                });
                            }
                        }
                        if reverse_map_fn.is_none() {
                            if let Some(MappingAttributeFunction { map_fn: generic_map_fn, question_token, move_token }) = &generic_type_mapping.reverse_map_fn {
                                reverse_map_fn = Some(MappingAttributeFunction {
                                    question_token: question_token.clone(),
                                    move_token: move_token.clone(),
                                    map_fn: parse_quote!(|obj: #to_ty| (#generic_map_fn)(obj, |item| item)),
                                });
                            }
                        }
                    }
                    
                    if !has_explicit_type {
                        field.ty = to_ty;
                    }
                }
            }
            // If there are type mappings but no mapping function to handle this, set `from_struct_path` to `None` so that mapping code is never generated
            let from_struct_path = if has_type_mapping && map_fn.is_none() { None } else { Some(mixin.path.clone()) };
            fields_by_struct.get_mut(&struct_name).unwrap().push(AutoStructMacroField {
                field: field,
                map_fn,
                from_struct_path,
            });
            let from_struct_path = if has_type_mapping && reverse_map_fn.is_none() { None } else { Some(new_struct.ident.clone().into()) };
            fields_by_struct.get_mut(&mixin_struct_path_string).unwrap().push(AutoStructMacroField {
                field: mixin_field,
                map_fn: reverse_map_fn,
                from_struct_path,
            })
        }
        for explicit_field in explicit_fields {
            Err(Error::new(explicit_field.span(), format!("{:?} is not a public field of struct {:?}", explicit_field.ident.to_string(), mixin_struct_path_string)))?
        }
    }

    *new_struct_fields = FieldsNamed {
        brace_token: token::Brace::default(),
        named: fields_by_struct.get(&struct_name).unwrap().iter().map(|field| {
            field.field.clone()
        }).collect(),
    };

    let mut replacer = SubMacroReplacer { fields_by_struct };
    let mut output = new_struct.to_token_stream();
    for item_impl in input.impls.iter_mut() {
        replacer.visit_item_impl_mut(item_impl);
        item_impl.to_tokens(&mut output);
    }
    // add useless items that reference the mixin struct name in the expansion (using the same span as the one that was given in the macro input)
    // so that jump-to-definition works on the given mixin name
    for (i, mixin) in input.mixins.iter().enumerate() {
        let throwaway_ident = Ident::new(&format!("_{struct_name}AutoMixinInternal{i}"), Span::mixed_site());
        let mixin_path = &mixin.path;
        quote_spanned! {Span::mixed_site()=>
            type #throwaway_ident = #mixin_path;
        }.to_tokens(&mut output)
    }
    Ok(output)
}

/// Expands the `FIELDS!` and `INIT!` sub-macros of the `AUTOSTRUCT!` macro.
struct SubMacroReplacer {
    fields_by_struct: HashMap<String, Vec<AutoStructMacroField>>,
}

fn expand_map_fn(map_fn: MappingAttributeFunction, span: Span, input: Expr, input_is_reference: bool) -> Result<Expr, Error> {
    let MappingAttributeFunction { map_fn, question_token, move_token, .. } = map_fn;
    // intentionally allow unhygienic interactions in mapping expressions
    let span = map_fn.span().resolved_at(span);
    let question_token = question_token.map(|tk| { Token![?](tk.span.resolved_at(span)) });
    let ref_token = if !input_is_reference && move_token.is_none() { Some(Token![&](span)) } else { None };
    let map_fn: Expr = syn::parse2(overwrite_token_spans(map_fn.to_token_stream(), span))?;
    Ok(parse_quote_spanned!(span=> (#map_fn)(#ref_token #input)#question_token ))
}

impl SubMacroReplacer {

    /// e.g. expand `FIELDS!(Bar, self: Foo, pfx_)` to
    /// <br> `let pfx_a = self.a;`
    /// <br> `let pfx_b = mapfn(self.b);`
    /// <br> `let pfx_c = self.c;`
    fn expand_fields_macro_stmt(&mut self, mac: &Macro) -> Result<Vec<Stmt>, Error> {
        let tokens = mac.tokens.clone();
        if tokens.is_empty() { return Err(Error::new(mac.span(), "expected identifier")); }
        let macro_params: FieldsMacro = parse2(tokens)?;
        // name of the variable to access fields from
        let base_name = macro_params.ident;
        let mut new_stmts: Vec<Stmt> = Vec::new();
        let src_struct_path = &macro_params.src_struct_path;
        let src_struct_path_string = src_struct_path.to_token_stream().to_string();
        let target_struct_path = &macro_params.target_struct_path;
        let target_struct_path_string = target_struct_path.to_token_stream().to_string();

        if !self.fields_by_struct.contains_key(&src_struct_path_string) {
            Err(Error::new(src_struct_path.span(), format!("{src_struct_path_string:?} not one of {:?}", self.fields_by_struct.keys())))?;
        }
        if !self.fields_by_struct.contains_key(&target_struct_path_string) {
            Err(Error::new(target_struct_path.span(), format!("{target_struct_path_string:?} not one of {:?}", self.fields_by_struct.keys())))?;
        }

        let fields = &self.fields_by_struct[&target_struct_path_string];
        for field in fields {
            if field.from_struct_path.to_token_stream().to_string() == src_struct_path_string {
                let mut name = field.field.ident.clone().unwrap();
                name.set_span(mac.span());
                let mut var_name = name.clone();
                if let Some(pfx) = macro_params.prefix.clone() {
                    var_name = Ident::new(&(pfx.to_string() + &var_name.to_string()), mac.span())
                }
                if let Some(map_fn) = field.map_fn.clone() {
                    // don't want to use span of the original tokens, otherwise errors involving both emitted tokens here
                    // and the `&` / `?` originating elsewhere
                    // will result in a huge continuous span between both points being underlined as the source of the error
                    let field_access: TokenStream = quote::quote!(#base_name.#name);
                    let field_access_span = field_access.span();
                    let field_access: Expr = syn::parse2(overwrite_token_spans(field_access, field_access_span.located_at(map_fn.map_fn.span())))?;
                    let fn_call = expand_map_fn(map_fn, mac.span(), field_access, false)?;
                    new_stmts.push(parse_quote_spanned!(mac.span()=> let #var_name = #fn_call; ));
                } else {
                    new_stmts.push(parse_quote_spanned!(mac.span()=> let #var_name = #base_name.#name; ));
                }
            }
        }
        Ok(new_stmts)
    }
    
    /// e.g. expand `INIT!(Foo, pfx_)` to `Foo { a: pfx_a, b: pfx_a, c: pfx_a }`
    fn expand_init_macro_expr(&mut self, mac: &Macro) -> Result<Expr, Error> {
        let tokens = mac.tokens.clone();
        if tokens.is_empty() { return Err(Error::new(mac.span(), "expected identifier")); }
        let macro_params: InitMacro = parse2(mac.tokens.clone())?;
        let target_struct_path = macro_params.path.to_token_stream().to_string();
        let fields = &self.fields_by_struct.get(&target_struct_path)
            .ok_or(Error::new(macro_params.path.span(), format!("{target_struct_path:?} not one of {:?}", self.fields_by_struct.keys())))?;
        let fields = fields.iter().map(|field| {
            let mut ident = field.field.ident.as_ref().unwrap().clone();
            ident.set_span(mac.span());
            let mut var_name = ident.clone();
            if let Some(pfx) = macro_params.prefix.clone() {
                var_name = Ident::new(&(pfx.to_string() + &ident.to_string()), mac.span());
            }
            FieldValue {
                attrs: Vec::new(),
                member: syn::Member::Named(ident.clone()),
                colon_token: Some(token::Colon::default()),
                expr: parse_quote!(#var_name),
            }
        }).collect();
        Ok(Expr::Struct(ExprStruct {
            attrs: Vec::new(),
            qself: None,
            path: macro_params.path.clone(),
            brace_token: token::Brace::default(),
            fields: fields,
            dot2_token: None,
            rest: None,
        }))
    }
}
impl VisitMut for SubMacroReplacer {
    fn visit_block_mut(&mut self, block: &mut Block) {
        let mut i = 0;
        while i < block.stmts.len() {
            if let Stmt::Macro(m) = &block.stmts[i] {
                if let Some(ident) = m.mac.path.get_ident() {
                    if ident == &Ident::new("FIELDS", Span::call_site()) {
                        let result = self.expand_fields_macro_stmt(&m.mac);
                        match result {
                            Ok(new_stmts) => {
                                let len = new_stmts.len();
                                // Replace the original statement with the new statements
                                block.stmts.splice(i..=i, new_stmts);
                                i += len; // Skip past the newly inserted statements
                                continue;
                            }
                            Err(e) => {
                                let err_stmt: Stmt = syn::parse2(e.into_compile_error()).unwrap();
                                block.stmts.splice(i..=i, [err_stmt]);
                                i += 1;
                                continue;
                            }
                        }
                    }
                    if ident == &Ident::new("INIT", Span::call_site()) {
                        match self.expand_init_macro_expr(&m.mac) {
                            Ok(expr) => {
                                block.stmts[i] = Stmt::Expr(expr, Some(token::Semi::default()));
                            }
                            Err(e) => {
                                block.stmts[i] = syn::parse2(e.into_compile_error()).unwrap();
                            }
                        };

                    }
                }
            }
            i += 1;
        }
        
        // Continue visiting the rest of the block tree
        syn::visit_mut::visit_block_mut(self, block);
    }

    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        if let Expr::Macro(m) = expr {
            if let Some(ident) = m.mac.path.get_ident() {
                if ident == &Ident::new("INIT", Span::call_site()) {
                    match self.expand_init_macro_expr(&m.mac) {
                        Ok(e) => {
                            *expr = e;
                        }
                        Err(e) => {
                            *expr = syn::parse2(e.into_compile_error()).unwrap();
                        }
                    };
                    return;
                }
            }
        }
        syn::visit_mut::visit_expr_mut(self, expr);
    }
}
