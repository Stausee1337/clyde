#![feature(dropck_eyepatch)]
#![feature(let_chains)]
#![feature(if_let_guard)]

use std::{env, process::ExitCode};

mod syntax;
mod analysis;

mod diagnostics;
mod session;
mod target;
mod type_ir;
mod files;
mod context;
mod string_internals;

fn main() -> ExitCode {
    let options = match session::parse_argv_options(env::args()) {
        Err(code) =>
            return code,
        Ok(options) => options
    };
    let sess = match options.create_compile_session() {
        Ok(sess) => sess,
        Err(()) => return ExitCode::FAILURE
    };

    let res = sess.global_ctxt(|tcx| {
        tcx.resolutions.items.iter().for_each(|&def_id| {
            if let Some(..) = tcx.node_by_def_id(def_id).body() {
                let body = tcx.build_ir(def_id);
                let mut buffer = String::new();
                analysis::intermediate::display_ir_body(tcx, body, &mut buffer)
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

