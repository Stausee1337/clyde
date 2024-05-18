use std::{path::Path, fs::File, io::{Read, self}};

use crate::{lexer::{Token, self}, ast, diagnostics::Diagnostics, interface::{self, path_to_string}};

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

    Ok(parse(tokens, diagnostics))
}

fn parse(tokens: Vec<Token>, diagnostics: Diagnostics) -> ast::TopLevel {
    wpascal::TopLevelParser::new()
        .parse(
            diagnostics,
            tokens
            .into_iter()
            .map(|tok| (tok.1.start, tok.0, tok.1.end)))
    .unwrap()
}

mod wpascal {
    include!(concat!(env!("OUT_DIR"), "/wpascal.rs"));
}
