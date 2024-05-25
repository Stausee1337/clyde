use std::{path::Path, fs::File, io::{Read, self}};

use crate::{lexer::{Token, self}, ast, diagnostics::Diagnostics, interface::path_to_string, context::GlobalCtxt};

struct ParseContext<'tcx> {
    pub diagnostics: Diagnostics<'tcx>,
    pub current_node_id: u32
}

impl<'tcx> ParseContext<'tcx> {
    pub fn make_node_id(&mut self) -> ast::NodeId {
        let new_node_id = self.current_node_id + 1;
        ast::NodeId(std::mem::replace(&mut self.current_node_id, new_node_id))
    }
}

fn read_entire_file(filename: &Path) -> io::Result<String> {
    let mut result = String::new();
    File::open(filename)?
        .read_to_string(&mut result)?;
    Ok(result)
}

pub fn parse_file<'a, 'tcx>(gcx: &'tcx GlobalCtxt<'tcx>, file: &Path) -> Result<ast::TopLevel, ()> {
    let contents = read_entire_file(file)
        .map_err(|err| {
            let file = unsafe { path_to_string(file) };
            eprintln!("ERROR: couldn't read {file}: {err}");
        })?;

    let file = unsafe { path_to_string(file) };
    let diagnostics = gcx.diagnostics_for(file, contents.clone());

    let tokens = lexer::lex_input_string(&contents).map_err(|err| {
        diagnostics.error(err.1).with_span(err.0);
    })?;

    Ok(parse(tokens, &mut ParseContext { diagnostics, current_node_id: 0 }))
}

fn parse<'a, 'tcx>(tokens: Vec<Token>, ctxt: &'a mut ParseContext<'tcx>) -> ast::TopLevel {
    clyde::TopLevelParser::new()
        .parse(ctxt, tokens
            .into_iter()
            .map(|tok| (tok.1.start, tok.0, tok.1.end)))
    .unwrap()
}

mod clyde {
    include!(concat!(env!("OUT_DIR"), "/clyde.rs"));
}
