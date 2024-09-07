#![feature(proc_macro_span)]
#![feature(try_blocks)]
#![feature(thread_id_value)]
#![allow(unused_braces)]

use std::path;

use proc_macro::{Span, TokenStream};
mod autostruct;
mod autoenum;
mod find_item;
mod util;

pub(self) use util::mylog;

fn get_paths() -> (path::PathBuf, path::PathBuf) {
    let span = Span::call_site();
    let source = span.source_file();
    // empty when invoked by vscode rust-analyzer
    let source_path = source.path();
    // when invoked by cargo, this is the workspace of the crate where the macro was invoked
    // when invoked by rust-analyzer, this is the dir of the crate where the macro was invoked
    let mut cwd = std::env::current_dir().unwrap();
    
    // if source_path is empty, assume rust-analyzer is executing and cwd is a package inside a workspace, bump up the path
    if source_path.to_str().unwrap() == "" {
        cwd.push("..");
    }
    (cwd, source_path)
}

#[allow(non_snake_case)]
#[proc_macro]
pub fn AUTOSTRUCT(input: TokenStream) -> TokenStream {
    util::MACRO_ID.with_borrow_mut(|i| {
        *i = *i + 1;
    });
    let (cwd, source_path) = get_paths();
    let start_time = std::time::Instant::now();
    mylog(&format!("beginning AUTOSTRUCT, cwd {cwd:?}, source_path: {source_path:?}"));
    let tokens = match autostruct::macro_main(input.into(), &cwd, &source_path) {
        Ok(t) => t,
        Err(e) => { 
            e.into_compile_error()
        },
    }.into();
    let elapsed = start_time.elapsed();
    mylog(&format!("finished AUTOSTRUCT in {elapsed:?}, cwd {cwd:?}, source_path: {source_path:?}"));
    tokens
}

/// Currently just used to copy discriminant-only enums
#[allow(non_snake_case)]
#[proc_macro]
pub fn AUTOENUM(input: TokenStream) -> TokenStream {
    let start_time = std::time::Instant::now();
    let (cwd, source_path) = get_paths();
    mylog(&format!("beginning AUTOENUM, cwd {cwd:?}, source_path: {source_path:?}"));
    let tokens = match autoenum::macro_main(input.into(), &cwd, &source_path) {
        Ok(t) => t,
        Err(e) => { 
            e.into_compile_error()
        },
    }.into();
    let elapsed = start_time.elapsed();
    mylog(&format!("finished AUTOENUM in {elapsed:?}, cwd {cwd:?}, source_path: {source_path:?}"));
    tokens
}

#[proc_macro]
pub fn passthrough(mut input: TokenStream) -> TokenStream {
    <TokenStream as Extend<TokenStream>>::extend(&mut input, "fn hello(i: i32) -> i32 {i}".parse());
    input
}
