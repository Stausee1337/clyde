#![feature(dropck_eyepatch)]
#![feature(let_chains)]
#![feature(if_let_guard)]
#![feature(ptr_metadata)]
#![feature(unsize)]
#![feature(never_type)]
#![feature(iter_chain)]

use std::{env, process::ExitCode};

mod syntax;
mod analysis;

mod diagnostics;
mod session;
mod target;
mod type_ir;
mod files;
mod context;
// mod codegen;
mod mapping;
mod string_internals;
mod pretty_print;

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
        analysis::run_analylsis(tcx)?;
        // Ok(codegen::run_codegen(tcx))
        Ok(())
    });

    sess.diagnostics().render();
    
    let Result::Ok(..) = res else {
        return ExitCode::FAILURE;
    };

    ExitCode::SUCCESS
}


