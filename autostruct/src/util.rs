use std::{cell::RefCell, collections::HashMap};

use syn::{punctuated::Punctuated, token, AttrStyle, Attribute, Meta, MetaList, Token};

thread_local! {
    pub static MACRO_ID: RefCell<i32> = RefCell::new(0);
}

pub fn mylog(message: &str) {
    MACRO_ID.with_borrow(|id| {
        let thread_id = std::thread::current().id().as_u64();
        let name = format!("rustmacro {}.{}.{}", std::process::id(), thread_id, id);
        let message = message.to_owned();
        std::thread::spawn(move || {
            #[cfg(debug_assertions)]
            #[cfg(target_os="windows")]
            let _ = std::process::Command::new("mylog.exe")
                .args([name, message])
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .stdin(std::process::Stdio::null())
                .spawn();
            #[cfg(debug_assertions)]
            #[cfg(not(target_os="windows"))]
            let _ = std::process::Command::new("mylog")
                .args([name, message])
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .stdin(std::process::Stdio::null())
                .spawn();
        })
    });
}

/// Arranges special attrs into a HashMap and removes them from the input list
pub fn take_attrs_by_name(attrs: &mut Vec<Attribute>, names: &[&str]) -> HashMap<String, Vec<MetaList>> {
    let mut attrs_by_name = HashMap::<String, Vec<MetaList>>::new();
    attrs.retain(|attr| {
        let Some(ident) = attr.path().get_ident() else { return true };
        let Meta::List(meta_list) = &attr.meta else { return true; };
        let attr_name = ident.to_string();
        if !names.contains(&&*attr_name) { return true; }
        let attrs_by_name_list = attrs_by_name.entry(ident.to_string()).or_insert_with(|| Vec::new());
        attrs_by_name_list.push(meta_list.clone());
        false
    });
    attrs_by_name
}

/// Used to convert `#[attr(a, b ,c)]` into `#[a] #[b] #[c]`
pub fn get_passthrough_attrs(attrs: &[MetaList]) -> Vec<Attribute> {
    let mut field_attrs = Vec::new();
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
    field_attrs
}
