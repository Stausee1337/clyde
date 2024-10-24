use std::{path::Path, marker::PhantomData};

use crate::{interface::Session, ast, lexer::{Punctuator, Keyword, Token, TokenKind, Span, self, LiteralKind}, symbol::Symbol};

pub struct TokenCursor<'a> {
    current: *const Token<'a>,
    end: *const Token<'a>,
    _phantom: PhantomData<&'a ()>
}

impl<'a> Clone for TokenCursor<'a> {
    fn clone(&self) -> Self {
        Self {
            current: self.current,
            end: self.current,
            _phantom: PhantomData::default()
        }
    }
}

impl<'a> TokenCursor<'a> {
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

    pub fn literal(&self) -> Option<(&'a str, LiteralKind)> {
        if let TokenKind::Literal(literal, kind) = self.current().kind {
            return Some((literal, kind));
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
    cursor: TokenCursor<'a>
}

pub trait ParseToken {
    fn peek(cursor: TokenCursor) -> bool;
}

pub fn parse_file<'a, 'sess>(session: &'sess Session, path: &Path) -> Result<ast::SourceFile, ()> {
    let _diagnostics = session.diagnostics();
    let source = session.file_cacher().load_file(path)?;

    lexer::tokenize(&source);

    todo!()
}

/*mod clyde {
    include!(concat!(env!("OUT_DIR"), "/clyde.rs"));
}*/
