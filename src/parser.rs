use std::path::Path;

use crate::{lexer::{Token, self}, ast, diagnostics::DiagnosticsCtxt, interface::Session};

struct ParseContext<'sess> {
    pub diagnostics: &'sess DiagnosticsCtxt,
    pub current_node_id: u32
}

impl<'tcx> ParseContext<'tcx> {
    pub fn make_node_id(&mut self) -> ast::NodeId {
        let new_node_id = self.current_node_id + 1;
        ast::NodeId(std::mem::replace(&mut self.current_node_id, new_node_id))
    }
}

pub fn parse_file<'a, 'sess>(session: &'sess Session, path: &Path) -> Result<ast::SourceFile, ()> {
    let diagnostics = session.diagnostics();
    let source = session.file_cacher().load_file(path)?;

    let (tokens, errors) = lexer::lex_input_string(source);
    for err in errors {
        diagnostics.error(err.1).with_span(err.0);
    }

    let source_file = parse(tokens, &mut ParseContext { diagnostics, current_node_id: 0 });
    Ok(source_file)
}

fn parse<'a, 'tcx>(tokens: Vec<Token>, ctxt: &'a mut ParseContext<'tcx>) -> ast::SourceFile {
    clyde::SourceFileParser::new()
        .parse(ctxt, tokens
            .into_iter()
            .map(|tok| (tok.1.start, tok.0, tok.1.end)))
    .unwrap()
}

mod clyde {
    include!(concat!(env!("OUT_DIR"), "/clyde.rs"));
}
