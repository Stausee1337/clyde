use std::path::Path;

use crate::{
    ast::{self, Constant, NodeId, Stmt, StmtKind},
    interface::Session,
    lexer::{self, AssociotiveOp, Keyword, LiteralKind, NumberMode, Operator, Punctuator, Span, StringKind, StringParser, Token, TokenKind, TokenStream, Tokenish},
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

    fn replace(&mut self, new: Token<'static>) {
        self.stream.tokens[self.current] = new;
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

impl Parsable for Punctuator {
    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        if let TokenKind::Punctuator(punct) = token.kind {
            return Some(punct);
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
            _ => None
        }
    }
}

impl Parsable for AssociotiveOp {
    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        if let TokenKind::Punctuator(punct) = token.kind {
            if let Some(binop) = lexer::BinaryOp::from_punct(punct) {
                return Some(Self::BinaryOp(binop));
            }
            if let Some(assignop) = lexer::AssignmentOp::from_punct(punct) {
                return Some(Self::AssignOp(assignop));
            }
        }
        None
    }
}

pub struct Parser<'src, 'ast> {
    cursor: TokenCursor<'src>,
    arena: &'ast bumpalo::Bump
}

impl<'src, 'ast> Parser<'src, 'ast> {
    fn matches(&self, token: impl Tokenish) -> bool {
        token.matches(self.cursor.current())
    }

    fn bump_if(&mut self, token: impl Tokenish) -> Option<Token> {
        let current = self.cursor.current();
        if token.matches(current) {
            self.cursor.advance();
            return Some(current);
        }
        None
    }

    fn bump_on<P: Parsable>(&mut self) -> Option<P> {
        let current = self.cursor.current();
        if let Some(p) = P::from_token(current) {
            self.cursor.advance();
            return Some(p);
        }
        return None;
    }

    fn bump(&mut self) {
        self.cursor.advance();
    }

    fn match_on<P: Parsable>(&mut self) -> Option<P> {
        let current = self.cursor.current();
        if let Some(p) = P::from_token(current) {
            return Some(p);
        }
        return None;
    }

    fn alloc<T>(&self, object: T) -> &'ast T {
        self.arena.alloc(object)
    }

    fn alloc_slice<T: Clone>(&self, slice: &[T]) -> &'ast [T] {
        self.arena.alloc_slice_clone(slice)
    }
    
    fn make_id(&mut self) -> NodeId {
        // FIXME: actually advance ids
        NodeId(0)
    }

    fn parse_primary(&mut self) -> &'ast ast::Expr<'ast> {
        let token = self.cursor.current();
        if let Some(keyword) = self.bump_on::<Keyword>() {
            let kind = match keyword {
                Token![null] =>
                    ast::ExprKind::Constant(ast::Constant::Null),
                Token![true] =>
                    ast::ExprKind::Constant(ast::Constant::Boolean(true)),
                Token![false] =>
                    ast::ExprKind::Constant(ast::Constant::Boolean(false)),
                _ =>
                    ast::ExprKind::Err
            };
            let expr = ast::Expr {
                kind,
                span: token.span,
                node_id: self.make_id()
            };
            return self.alloc(expr);
        } else if let Some(literal) = self.bump_on::<Constant>() {
            let expr = ast::Expr {
                kind: ast::ExprKind::Constant(literal),
                span: token.span,
                node_id: self.make_id()
            };
            return self.alloc(expr);
        } else if let Some(stringlit) = self.bump_on::<String>() {
            let expr = ast::Expr {
                kind: ast::ExprKind::String(stringlit),
                span: token.span,
                node_id: self.make_id()
            };
            return self.alloc(expr);
        } else if let Some(symbol) = self.bump_on::<Symbol>() {
            let name = ast::Name::from_ident(ast::Ident {
                symbol,
                span: token.span
            });
            // maybe this could be a discrete type init like: 
            // `MyType { a: b }`
            let expr = if self.matches(lexer::Punctuator::LCurly) {
                self.parse_type_init_body()
            } else {
                let expr = ast::Expr {
                    kind: ast::ExprKind::Name(name),
                    span: token.span,
                    node_id: self.make_id()
                };
                self.alloc(expr)
            };
            return expr;
        }

        let Some(punct) = self.bump_on::<Punctuator>() else {
            let expr = ast::Expr {
                kind: ast::ExprKind::Err,
                span: token.span,
                node_id: self.make_id()
            };
            return self.alloc(expr);
        };

        // Tuple (or nomral Expr resetting precedence), TypeInit or Block
        let end = None;
        let kind = match punct {
            Punctuator::LParen => {
                todo!()
            },
            _ => ast::ExprKind::Err
        };

        let end = end.unwrap_or(token.span);

        let expr = ast::Expr {
            kind,
            span: Span::interpolate(token.span, end),
            node_id: self.make_id()
        };
        self.alloc(expr)
    }

    fn parse_expr_prefix(&mut self) -> &'ast ast::Expr<'ast> {
        let start = self.cursor.span();
        if let Some(op) = self.bump_on::<lexer::UnaryOp>() {
            let expr = self.parse_expr_prefix();
            let expr = ast::Expr {
                kind: ast::ExprKind::UnaryOp(ast::UnaryOp {
                    expr,
                    operator: op
                }),
                span: Span::interpolate(start, expr.span),
                node_id: self.make_id()
            };
            return self.alloc(expr);
        } else if let Some(..) = self.bump_if(Token![*]) {
            let expr = self.parse_expr_prefix();
            let expr = ast::Expr {
                kind: ast::ExprKind::Deref(expr),
                span: Span::interpolate(start, expr.span),
                node_id: self.make_id()
            };
            return self.alloc(expr);
        } else if self.matches(Token![&&]) {
            // parse double refrence
            let tok = self.cursor.current();
            self.cursor.replace(Token {
                kind: TokenKind::Punctuator(Token![&]),
                span: Span {
                    start: tok.span.start + 1,
                    end: tok.span.end
                }
            });
            let expr = self.parse_expr_prefix();

            let expr = ast::Expr {
                kind: ast::ExprKind::UnaryOp(ast::UnaryOp {
                    expr,
                    operator: lexer::UnaryOp::Ref
                }),
                span: Span::interpolate(start, expr.span),
                node_id: self.make_id()
            };
            return self.alloc(expr);
        } else if self.matches(Token![cast]) || self.matches(Token![transmute]) {
            let _token = self.cursor.current();
            self.cursor.advance();
            todo!("self.parse_ty_expr()")
        }
        let expr = self.parse_primary();
        /*
        FIXME: These are postfix expressions they will need to be parsed here
        (or rahter in seperate method)
        FunctionCall(FunctionCall<'ast>),
        Subscript(Subscript<'ast>),
        Field(Field<'ast>),
        */
        expr
    }

    fn parse_expr_assoc(&mut self, min_precendence: u32) -> &'ast ast::Expr<'ast> {
        let mut lhs = self.parse_expr_prefix();

        while let Some(op) = self.match_on::<AssociotiveOp>() {
            let prec = op.precedence();
            if prec < min_precendence {
                break;
            }
            self.bump();

            let rhs = self.parse_expr_assoc(prec + op.associotivity() as u32);

            let span = Span::interpolate(lhs.span, rhs.span);

            let kind = match op {
                AssociotiveOp::BinaryOp(op) =>
                    ast::ExprKind::BinaryOp(ast::BinaryOp {
                        lhs,
                        rhs,
                        operator: op
                    }),
                AssociotiveOp::AssignOp(op) =>
                    ast::ExprKind::AssignOp(ast::AssignOp {
                        lhs,
                        rhs,
                        operator: op
                    })
            };

            let expr = ast::Expr {
                kind,
                span,
                node_id: self.make_id()
            };
            lhs = self.alloc(expr);
        }
        lhs
    }

    /*fn parse_statement(&mut self) -> Stmt {
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

        let lhs = self.parse_expression(Restrictions::NO_MULTIPLICATION);
        if self.skip_if(Token![=]).is_none() {
            return Stmt {
                kind: StmtKind::Expr(lhs),
                span: self.cursor.spanned(start),
                node_id: self.make_id()
            };
        }

        let rhs = self.parse_expression(Restrictions::empty());
        
        return Stmt {
            kind: StmtKind::Assign(lhs, rhs),
            span: self.cursor.spanned(start),
            node_id: self.make_id()
        };
    }*/
}

pub fn parse_file<'a, 'sess>(session: &'sess Session, path: &Path) -> Result<ast::SourceFile<'sess>, ()> {
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

