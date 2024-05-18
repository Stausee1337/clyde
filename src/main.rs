
use std::{env, process::ExitCode};

use interface::build_compiler;

mod ast;
mod lexer;
mod parser;
mod symbol;
mod node_visitor;
mod diagnostics;
mod interface;


fn main() -> ExitCode {
    let options = match interface::parse_argv_options(env::args()) {
        Err(code) =>
            return code,
        Ok(options) => options
    };
    let sess = options.create_compile_session();
    
    build_compiler(sess, |compiler| {
        let ast = compiler.parse()?;
        println!("{ast:#?}");
    
        interface::fully_resolve_unit(ast);
        // lower()

        // type collection
        // type checking

        // IR generation

        Ok::<ExitCode, ()>(ExitCode::SUCCESS)
    }).unwrap_or(ExitCode::FAILURE)
}
