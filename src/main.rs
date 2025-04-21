#![feature(dropck_eyepatch)]
#![feature(let_chains)]
#![feature(if_let_guard)]

use std::{env, process::ExitCode};

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

    let res = sess.global_ctxt(|tcx| {
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
    });

    sess.diagnostics().render();
    
    let Result::Ok(..) = res else {
        return ExitCode::FAILURE;
    };

    ExitCode::SUCCESS
}

