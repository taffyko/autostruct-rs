#![feature(try_blocks)]
#![allow(unused_braces)]
#![feature(proc_macro_span)]
#![feature(thread_id_value)]
#![allow(unused_braces)]

use std::fs;

use proc_macro2;
use autostruct::{macro_main};

mod util;
use syn::{parse_file, Item};
pub use util::mylog;
mod find_item;
mod autostruct;
mod autoenum;
use proc_macro2::{TokenStream, Span, Ident};
use quote::{ToTokens};
use std::process::Command;
use anyhow::{bail};


/// May only appear in Item position
fn find_autostruct_macro_invocations(items: &[Item]) -> Vec<(usize, TokenStream)> {
    // find invocation of AUTOSTRUCT! macro
    let invocations: Vec<_> = items.iter().enumerate().filter_map(|(i, item)| {
        if let Item::Macro(item) = item {
            if item.mac.path.get_ident() == Some(&Ident::new("AUTOSTRUCT", Span::call_site())) {
                return Some((i, item.mac.tokens.clone()))
            }
        }
        None
    }).collect();
    invocations
}

fn main() -> anyhow::Result<()> {
    let Some(workspace_path) = std::env::args().nth(1) else { bail!("workspace path arg missing"); };
    let Some(file_path) = std::env::args().nth(2) else { bail!("file path arg missing"); };
    let content = fs::read_to_string(&file_path)?;
    let mut file = parse_file(&content)?;

    let invocations = find_autostruct_macro_invocations(&file.items);

    for (i, tokens) in invocations {
        file.items.remove(i);
        let start_time = std::time::Instant::now();
        let tokens = macro_main(tokens, &workspace_path, &file_path)?;
        println!("expansion in {:?}", start_time.elapsed());
        file.items.insert(i, syn::Item::Verbatim(tokens));
    }

    let dest_file_path = file_path.replace(".rs", ".output.rs");
    fs::write(&dest_file_path, file.into_token_stream().to_string())?;
    Command::new("rustfmt")
        .arg(&dest_file_path)
        .spawn()?;
    Ok(())
}
