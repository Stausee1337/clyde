
use std::{env, process::ExitCode};

use interface::build_compiler;

mod ast;
mod lexer;
mod parser;
mod symbol;
mod mut_visitor;
mod node_visitor;
mod diagnostics;
mod interface;
mod resolve;
mod types;
mod context;
mod queries;
mod typecheck;

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
            let resolutions = resolve::run_resolve(tcx, compiler.parse()?);

            if gcx.has_fatal_errors() {
                gcx.all_diagnostics(|diag| diag.print_diagnostics());
                return Err(());
            }

            // println!("{:#?}", tcx.file_ast(interface::INPUT_FILE_IDX));
            resolutions.items.iter().for_each(|&def_id| {
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

        gcx.all_diagnostics(|diag| diag.print_diagnostics());

        Ok::<ExitCode, ()>(if !gcx.has_errors() { ExitCode::SUCCESS } else { ExitCode::FAILURE })
    }).unwrap_or(ExitCode::FAILURE)
}

