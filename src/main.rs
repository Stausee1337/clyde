
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
mod intermediate;

fn main() -> ExitCode {
    let options = match interface::parse_argv_options(env::args()) {
        Err(code) =>
            return code,
        Ok(options) => options
    };
    let sess = options.create_compile_session();
    
    build_compiler(sess, |compiler| {

        let Ok(gcx) = compiler.global_ctxt() else {
            compiler.sess.diagnostics().render();
            return Err(());
        };

        if gcx.diagnostics().has_fatal() {
            gcx.diagnostics().render();
            return Err(());
        }

        gcx.enter(|tcx| {

            tcx.resolutions.items.iter().for_each(|&def_id| {
                if let Some(..) = tcx.node_by_def_id(def_id).body() {
                    let body = tcx.build_ir(def_id);
                    let mut buffer = String::new();
                    intermediate::display_ir_body(tcx, body, &mut buffer)
                        .unwrap();
                    println!("{buffer}");
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

