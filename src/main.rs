
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

fn main() -> ExitCode {
    let options = match interface::parse_argv_options(env::args()) {
        Err(code) =>
            return code,
        Ok(options) => options
    };
    let sess = options.create_compile_session();
    
    build_compiler(sess, |compiler| {
        let mut ast = compiler.parse().map_err(|diagnostics| {
            diagnostics.print_diagnostics();
            ()
        })?;
    
        resolve::run_resolve(&mut ast);
        println!("{:#?}", ast);

        if ast.diagnostics.has_fatal() {
            ast.diagnostics.print_diagnostics();
            return Ok::<ExitCode, ()>(ExitCode::FAILURE);
        }

        // lower()

        // type collection
        // type checking

        // IR generation

        ast.diagnostics.print_diagnostics();

        Ok::<ExitCode, ()>(ExitCode::SUCCESS)
    }).unwrap_or(ExitCode::FAILURE)
}

