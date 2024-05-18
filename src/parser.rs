use std::{path::Path, fs::File, io::{Read, self}};

use crate::{lexer::{Token, self}, ast, diagnostics::Diagnostics, interface::{self, path_to_string}};

struct ParseContext {
    pub diagnostics: Diagnostics,
    pub current_node_id: u32
}

impl ParseContext {
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

pub fn parse_file<'a>(file: &Path, sess: &interface::Session) -> Result<ast::TopLevel, ()> {
    let contents = read_entire_file(file)
        .map_err(|err| {
            let file = unsafe { path_to_string(file) };
            eprintln!("ERROR: couldn't read {file}: {err}");
        })?;

    let file = unsafe { path_to_string(file) };
    let tokens = lexer::lex_input_string(&contents).map_err(|err| {
        let diagnostics = sess.create_diagnostics_for_file(&file, &contents);
        diagnostics.error(err.1).with_span(err.0);
    })?;

    let diagnostics = sess.create_diagnostics_for_file(&file, &contents);

    Ok(parse(tokens, ParseContext { diagnostics, current_node_id: 0 }))
}

fn parse(tokens: Vec<Token>, mut ctxt: ParseContext) -> ast::TopLevel {
    wpascal::TopLevelParser::new()
        .parse(
            &mut ctxt,
            tokens
            .into_iter()
            .map(|tok| (tok.1.start, tok.0, tok.1.end)))
    .unwrap()
}

mod wpascal {
    include!(concat!(env!("OUT_DIR"), "/wpascal.rs"));
}
