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

    todo!()
}

/*mod clyde {
    include!(concat!(env!("OUT_DIR"), "/clyde.rs"));
}*/
