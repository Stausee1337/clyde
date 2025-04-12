
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
mod context;
mod typecheck;
mod string_internals;

fn main() -> ExitCode {
    let options = match interface::parse_argv_options(env::args()) {
        Err(code) =>
            return code,
        Ok(options) => options
    };
    let sess = options.create_compile_session();
    
    build_compiler(sess, |compiler| {

        let gcx = compiler.global_ctxt()?; 

        if gcx.diagnostics().has_fatal() {
            gcx.diagnostics().render();
            return Err(());
        }

        gcx.enter(|tcx| {
            tcx.resolutions.items.iter().for_each(|&def_id| {
                if let Some(..) = tcx.node_by_def_id(def_id).body() {
                    tcx.typecheck(def_id);
                }
            });

            Ok(())
        })?;


        // lower()

        // type collection
        // type checking

        // IR generation
        
        let diagnostics = gcx.diagnostics();
        diagnostics.render();

        Ok::<ExitCode, ()>(if !diagnostics.has_error() { ExitCode::SUCCESS } else { ExitCode::FAILURE })
    }).unwrap_or(ExitCode::FAILURE)
}

