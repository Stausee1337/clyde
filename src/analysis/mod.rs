use crate::{context::TyCtxt, diagnostics::Message, pretty_print::{PrettyPrinter, Print}, syntax::{ast::{Item, ItemKind, Node}, lexer}};

pub mod resolve;
pub mod node_visitor;
pub mod typecheck;
pub mod intermediate;

pub fn run_analylsis(tcx: TyCtxt) -> Result<(), ()> {
    let mut has_errors = tcx.resolutions.ast_info.tainted_with_errors.get().is_some();

    for def in &tcx.resolutions.items {
        let node = tcx.node_by_def_id(*def);
        match node {
            _ if node.body().is_some() => {
                let body = tcx.build_ir(*def);
                if let Ok(body) = body && tcx.session.config.print_ir {
                    let string = PrettyPrinter::print_into_string(tcx, |p| body.print(p)).unwrap();
                    eprintln!("{string}");
                }
                has_errors |= body.is_err();
            }
            Node::Item(Item { kind: ItemKind::Function(..), .. }) =>
                // check if signature is well-formed for bodyless (external) fns
                has_errors |= tcx.fn_sig(*def).has_errors,
            Node::Item(..) =>
                // FIXME: this should be replaced with an actual and percice well fromed check,
                // also including a check for recusrive type aliases, which currently will just
                // cause a silent Err without any explanation
                has_errors |= tcx.layout_of(tcx.type_of(*def)).is_err(),
            _ => ()
        }
    }

    if tcx.resolutions.entry.is_none() {
        Message::error("file doesn't have an entry point")
            .at(lexer::Span::new(0, 1)) // emit an error at the first char in the input file
            .note("consider adding `void main()`")
            .push(tcx.diagnostics());
        has_errors = true;
    }

    if has_errors {
        return Err(());
    }

    Ok(())
}

