use std::path::Path;

use crate::{
    ast::{self, Constant, Stmt, StmtKind},
    interface::Session,
    lexer::{self, Keyword, LiteralKind, NumberMode, Operator, Span, StringKind, StringParser, Token, TokenKind, TokenStream, Tokenish},
    symbol::Symbol,
    Token
};

pub struct TokenCursor<'a> {
    stream: TokenStream<'a>,
    current: usize
}

impl<'a> TokenCursor<'a> {
    fn current(&self) -> Token<'a> {
        self.stream.tokens[self.current]
    }

    fn span(&self) -> Span {
        self.current().span
    }

    fn advance(&mut self) {
        if self.stream.tokens.len() <= self.current {
            panic!("TokenCursor is at EOS");
        }
        self.current += 1;
    }
}

trait Parsable: Sized {
    fn from_token<'a>(token: Token<'a>) -> Option<Self>;
}

impl<T: Operator> Parsable for T {
    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        if let TokenKind::Punctuator(punct) = token.kind {
            return T::from_punct(punct);
        }
        None
    }
}

impl Parsable for Keyword {
    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        if let TokenKind::Keyword(keyword) = token.kind {
            return Some(keyword);
        }
        None
    }
}

impl Parsable for Symbol {
    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        if let TokenKind::Symbol(sym) = token.kind {
            return Some(sym);
        }
        return None;
    }
}

impl Parsable for String {
    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        if let TokenKind::Literal(repr, LiteralKind::String) = token.kind {
            let mut parser = StringParser::new(StringKind::String);
            let mut buffer = String::new();
            for char in repr.chars() {
                match parser.feed(char) {
                    Ok(out) => {
                        if let Some(out) = out {
                            buffer.push(out);
                        }
                        if parser.ended() {
                            break;
                        }
                    }
                    Err(string_error) => 
                        unreachable!("unreachable string error in parser: {string_error:?} (should have been handled at lexing stage)"),
                }
            }
            return Some(buffer);
        }
        None
    }
}

impl Parsable for Constant {
    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        match token.kind {
            TokenKind::Literal(repr, LiteralKind::Char) => {
                let mut parser = StringParser::new(StringKind::Char);
                let mut res = None;
                for char in repr.chars() {
                    match parser.feed(char) {
                        Ok(Some(out)) => {
                            res = Some(out);
                        }
                        Err(string_error) => 
                            unreachable!("unreachable string error in parser: {string_error:?} (should have been handled at lexing stage)"),
                        _ => ()
                    }
                }

                Some(Constant::Char(res.unwrap()))
            }
            TokenKind::Literal(repr, LiteralKind::FloatingPoint) =>
                Some(Constant::Floating(repr.parse().expect("unexpected invalid float at parsing stage"))),
            TokenKind::Literal(repr, LiteralKind::IntNumber(mode)) => {
                let radix = match mode {
                    NumberMode::Binary => 2,
                    NumberMode::Octal => 8,
                    NumberMode::Decimal => 10,
                    NumberMode::Hex => 16
                };

                let int = u64::from_str_radix(repr, radix).expect("unexpected invalid int at parsing stage");
                Some(Constant::Integer(int))
            }
            TokenKind::Keyword(Token![null]) => Some(Constant::Null),
            _ => None
        }
    }
}

pub struct Parser<'a> {
    cursor: TokenCursor<'a>
}

impl<'a> Parser<'a> {
    fn matches(&self, token: impl Tokenish) -> bool {
        token.matches(self.cursor.current())
    }

    fn skip_if(&mut self, token: impl Tokenish) -> Option<Token> {
        let current = self.cursor.current();
        if token.matches(current) {
            self.cursor.advance();
            return Some(current);
        }
        None
    }

    fn parse<P: Parsable>(&mut self) -> Option<P> {
        let current = self.cursor.current();
        if let Some(p) = P::from_token(current) {
            self.cursor.advance();
            return Some(p);
        }
        return None;
    }

    fn parse_statement(&mut self) -> Stmt {
        let start = self.cursor.pos();

        if let Some(keyword) = self.parse::<Keyword>() {
            let kind = match keyword {
                Token![var] =>
                    self.parse_variable_declaration(None),
                Token![if] =>
                    self.parse_if_statement(),
                Token![for] => 
                    self.parse_for_loop(),
                Token![while] => 
                    self.parse_while_loop(),
                Token![break] | Token![continue] => 
                    self.parse_control_flow(keyword),
                _ => StmtKind::Err
            };
            return Stmt {
                kind,
                span: self.cursor.spanned(start),
                node_id: self.make_id()
            };
        }

        let result = self.try_parse_ty_expr();
        match result {
            ParseTy::TyExpr(expr) =>
                return self.parse_variable_declartion(Some(expr)),
            ParseTy::Doubt(ty_expr) => {
                if let Some(stmt) = self.maybe_parse_variable_declaration(Some(ty_expr)) {
                    return stmt;
                }
            }
            ParseTy::None => ()
        }

        StmtKind::Expr(self.parse_expression(Restrictions::NO_MULTIPLICATION))
    }
}

pub fn parse_file<'a, 'sess>(session: &'sess Session, path: &Path) -> Result<ast::SourceFile, ()> {
    let _diagnostics = session.diagnostics();
    let source = session.file_cacher().load_file(path)?;


    println!("Tokenization ...");
    let (stream, errors) = lexer::tokenize(&source);
    for err in errors {
        println!("{:?}", err);
    }

    for tok in stream.tokens {
        println!("{:?}", tok);
    }

    todo!()
}

