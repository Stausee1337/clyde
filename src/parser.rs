use std::{path::Path, marker::PhantomData};

use crate::{interface::Session, ast, lexer::{Punctuator, Keyword, Token, TokenKind, Span}, symbol::Symbol};

pub struct Cursor<'a> {
    current: *const Token<'a>,
    end: *const Token<'a>,
    _phantom: PhantomData<&'a ()>
}

impl<'a> Clone for Cursor<'a> {
    fn clone(&self) -> Self {
        Self {
            current: self.current,
            end: self.current,
            _phantom: PhantomData::default()
        }
    }
}

impl<'a> Cursor<'a> {
    pub fn punct(&self) -> Option<Punctuator> {
        if let TokenKind::Punctuator(punctuator) = self.current().kind {
            return Some(punctuator);
        }
        None
    }

    pub fn keyword(&self) -> Option<Keyword> {
        if let TokenKind::Keyword(keyword) = self.current().kind {
            return Some(keyword);
        }
        None
    }

    pub fn symbol(&self) -> Option<Symbol> {
        if let TokenKind::Symbol(symbol) = self.current().kind {
            return Some(symbol);
        }
        None
    }

    pub fn literal(&self) -> Option<&'a str> {
        if let TokenKind::Literal(literal) = self.current().kind {
            return Some(literal);
        }
        None
    }

    pub fn current(&self) -> &'a Token<'a> {
        unsafe { &* self.current }
    }

    pub fn span(&self) -> Span {
        self.current().span
    }

    pub fn advance(&mut self) {
        if self.end <= self.current {
            panic!("Cursor is at EOS");
        }
        unsafe {
            self.current = self.current.add(1);
        }
    }
}

pub struct Parser<'a> {
    cursor: Cursor<'a>
}

pub fn parse_file<'a, 'sess>(session: &'sess Session, path: &Path) -> Result<ast::SourceFile, ()> {
    let _diagnostics = session.diagnostics();
    let _source = session.file_cacher().load_file(path)?;

    todo!()
}

/*mod clyde {
    include!(concat!(env!("OUT_DIR"), "/clyde.rs"));
}*/
