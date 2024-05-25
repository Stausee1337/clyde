
use std::{env, process::ExitCode};

use interface::build_compiler;

use crate::context::GlobalCtxt;

mod ast;
mod lexer;
mod parser;
mod symbol;
mod node_visitor;
mod diagnostics;
mod interface;
mod resolve;
mod types;
mod normalization;
mod context;

fn main() -> ExitCode {
    let options = match interface::parse_argv_options(env::args()) {
        Err(code) =>
            return code,
        Ok(options) => options
    };
    let sess = options.create_compile_session();
    
    build_compiler(sess, |compiler| {
        let gcx = GlobalCtxt::new();
        let mut ast = compiler.parse(&gcx)?;
    
        resolve::run_resolve(&gcx, &mut ast);
        println!("{:#?}", ast);

        if gcx.has_fatal_errors() {
            gcx.all_diagnostics().for_each(|diag| diag.print_diagnostics());
            return Ok::<ExitCode, ()>(ExitCode::FAILURE);
        }

        // lower()

        // type collection
        // type checking

        // IR generation

        gcx.all_diagnostics().for_each(|diag| diag.print_diagnostics());

        Ok::<ExitCode, ()>(ExitCode::SUCCESS)
    }).unwrap_or(ExitCode::FAILURE)
}

