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
        run_analylsis(tcx)?;

        Ok(())
    });

    sess.diagnostics().render();
    
    let Result::Ok(..) = res else {
        return ExitCode::FAILURE;
    };

    ExitCode::SUCCESS
}

fn run_analylsis(tcx: context::TyCtxt) -> Result<(), ()> {
    use syntax::ast::{Node, Item, ItemKind};

    let mut has_errors = false;
    for def in &tcx.resolutions.items {
        let node = tcx.node_by_def_id(*def);
        match node {
            _ if node.body().is_some() =>
                has_errors |= tcx.build_ir(*def).is_err(),
            Node::Item(Item { kind: ItemKind::Function(..), .. }) =>
                // check if signature is well-formed for bodyless (external) fns
                has_errors |= tcx.fn_sig(*def).has_errors,
            Node::Item(..) =>
                has_errors |= tcx.layout_of(tcx.type_of(*def)).is_err(),
            _ => ()
        }
    }

    if has_errors {
        return Err(());
    }

    Ok(())
}

