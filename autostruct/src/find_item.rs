use lazy_static::lazy_static;
use crate::mylog;
use syn::LitStr;
use syn::{parse_file, Item, Error, spanned::Spanned};
use std::fs;
use std::path;
use std::collections::HashMap;
use std::sync::RwLock;


lazy_static! {
    static ref FILE_CACHE: RwLock<HashMap<path::PathBuf, String>> = RwLock::new(HashMap::new());
}


pub fn find_item(
    workspace_path: impl AsRef<path::Path>,
    relative_file_path: impl AsRef<path::Path>,
    given_file_path_lit: &LitStr,
    item_path: &syn::Path,
) -> Result<Item, Error> {
    // Check if path begins with a dot
    let given_file_path = given_file_path_lit.value();
    let begins_with_dot = given_file_path.chars().nth(0) == Some('.');
    let given_file_path: &path::Path = given_file_path.as_ref();
    let file_path: path::PathBuf;
    if begins_with_dot {
        // Evaluate relative to directory of the source file where the macro is invoked
        file_path = [workspace_path.as_ref(), relative_file_path.as_ref().parent().unwrap(), given_file_path.as_ref()].iter().collect();
    } else {
        // Evaluate relative to workspace dir
        file_path = [workspace_path.as_ref(), given_file_path.as_ref()].iter().collect();
    }
    
    let result: Option<String> = (*FILE_CACHE).read().unwrap().get(&file_path).map(|s| s.clone());
    let content = match result {
        Some(s) => {
            // Cache hit
            mylog(&format!("cache HIT for {:?}", file_path));
            let file_path = file_path.clone();
            std::thread::spawn(move || {
                if let Ok(s) = fs::read_to_string(&file_path) {
                    let mut file_cache = (*FILE_CACHE).write().unwrap();
                    file_cache.insert(file_path.clone(), s.clone());
                };
            });
            s
        }
        None => {
            match fs::read_to_string(&file_path) {
                Ok(s) => {
                    let mut file_cache = (*FILE_CACHE).write().unwrap();
                    mylog(&format!("cache MISS for {:?}", file_path));
                    file_cache.insert(file_path.clone(), s.clone());
                    s
                },
                Err(_) => { return Err(Error::new(given_file_path_lit.span(), format!("couldn't read {file_path:?}"))) }
            }
        }
    };
    
    // can't cache parsed file as it is not Sync
    let file = parse_file(&content)?;

    let ident = &item_path.segments.last().unwrap().ident;
    for item in file.items {
        if let Item::Struct(item) = item {
            if &item.ident == ident {
                return Ok(Item::Struct(item));
            }
        } else if let Item::Enum(item) = item {
            if &item.ident == ident {
                return Ok(Item::Enum(item));
            }
        }
    }
    Err(Error::new(item_path.span(), format!("couldn't find {ident:?} in {file_path:?}")))
}
