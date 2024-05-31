use crate::{lexer::{Token, self}, ast, diagnostics::Diagnostics, interface::{FileIdx, Steal}, context::TyCtxt};

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

pub fn parse_file<'a, 'tcx>(tcx: TyCtxt<'tcx>, file: FileIdx) -> &'tcx Steal<ast::SourceFile> {
    let source = tcx.file_path_and_source(file).1;
    let diagnostics = tcx.diagnostics_for_file(file);

    let (tokens, errors) = lexer::lex_input_string(source);
    for err in errors {
        diagnostics.error(err.1).with_span(err.0);
    }

    let source_file = parse(tokens, &mut ParseContext { diagnostics, current_node_id: 0 });
    tcx.alloc(Steal::new(source_file))
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
