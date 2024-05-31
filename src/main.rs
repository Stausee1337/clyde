
use std::{env, process::ExitCode};

use interface::build_compiler;

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
mod queries;

fn main() -> ExitCode {
    let options = match interface::parse_argv_options(env::args()) {
        Err(code) =>
            return code,
        Ok(options) => options
    };
    let sess = options.create_compile_session();
    
    build_compiler(sess, |compiler| {
        let gcx = compiler.global_ctxt();

        gcx.enter(|tcx| {
            let ast = resolve::run_resolve(tcx);

            println!("{:#?}", ast);
        }); 

        if gcx.has_fatal_errors() {
            gcx.all_diagnostics(|diag| diag.print_diagnostics());
            return Ok::<ExitCode, ()>(ExitCode::FAILURE);
        }

        // lower()

        // type collection
        // type checking

        // IR generation

        gcx.all_diagnostics(|diag| diag.print_diagnostics());

        Ok::<ExitCode, ()>(ExitCode::SUCCESS)
    }).unwrap_or(ExitCode::FAILURE)
}

