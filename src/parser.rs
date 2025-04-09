use std::{cell::OnceCell, path::Path};

use crate::{
    ast::{self, Constant, NodeId},
    interface::Session,
    lexer::{self, AssociotiveOp, Keyword, LiteralKind, NumberMode, Operator, Punctuator, Span, StringKind, StringParser, Token, TokenKind, TokenStream, Tokenish},
    symbol::Symbol,
    Token
};

enum ParseTry<'src, T> {
    Sure(T),
    Doubt(T, TokenCursor<'src>),
    Never,
}

pub struct TokenCursor<'src> {
    current: *mut Token<'src>,
    end: *mut Token<'src>
}

impl<'src> TokenCursor<'src> {
    fn fork(&mut self) -> TokenCursor<'src> {
        // FIXME: this is the only source of unsafeity in TokenCursor since it clones 
        // it, while leagally it shouldn't be cloneable. Maybe there is a way to keep
        // similar behaviour while not compromising memory saftey
        TokenCursor {
            current: self.current,
            end: self.end
        }
    }

    fn sync(&mut self, other: TokenCursor<'src>) -> Option<TokenCursor<'src>> {
        if other.end == self.end {
            return Some(std::mem::replace(self, other));
        }
        None
    }

    fn current(&self) -> Token<'src> {
        unsafe { *self.current }
    }

    fn replace(&mut self, new: Token<'static>) {
        unsafe { *self.current = new }
    }

    fn span(&self) -> Span {
        self.current().span
    }

    fn is_eos(&self) -> bool {
        self.current == self.end
    }

    fn advance(&mut self) {
        if self.end <= self.current {
            panic!("TokenCursor is at EOS");
        }
        unsafe { self.current = self.current.add(1) };
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

impl Parsable for u64 {
    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        if let TokenKind::Literal(repr, LiteralKind::IntNumber(mode)) = token.kind {
            let radix = match mode {
                NumberMode::Binary => 2,
                NumberMode::Octal => 8,
                NumberMode::Decimal => 10,
                NumberMode::Hex => 16
            };

            let int = u64::from_str_radix(repr, radix).expect("unexpected invalid int at parsing stage");
            return Some(int);
        }
        None
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
    _tokens: Box<[Token<'src>]>,
    cursor: TokenCursor<'src>,
    arena: &'ast bumpalo::Bump
}

impl<'src, 'ast> Parser<'src, 'ast> {
    fn new(stream: TokenStream<'src>, arena: &'ast bumpalo::Bump) -> Self {
        let mut tokens = stream.into_boxed_slice();
        let start = tokens.as_mut_ptr();
        let cursor = TokenCursor {
            current: start,
            end: unsafe { start.add(tokens.len() - 1) }
        };
        Self {
            _tokens: tokens,
            cursor,
            arena
        }
    }

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

    fn enter_speculative_block<'a, R, F: FnOnce(&mut Self) -> R>(
        &mut self, do_work: F) -> (R, TokenCursor<'src>) {
        let cursor = self.cursor.fork();
        let result = do_work(self);
        let cursor = self.cursor.sync(cursor);
        (result, cursor.unwrap())
    }

    fn maybe_parse_ty_expr(&mut self) -> ParseTry<'src, &'ast ast::TypeExpr<'ast>> {
        ParseTry::Never
    }

    fn parse_tuple_ty(&mut self) -> &'ast ast::TypeExpr<'ast> {
        let start = self.cursor.span();
        self.cursor.advance();

        let mut args = vec![];
        while !self.matches(Punctuator::RParen) {
            args.push(self.parse_ty_expr());
            
            if self.bump_if(Token![,]).is_none() && !self.matches(Punctuator::RParen){
                let expr = ast::TypeExpr {
                    kind: ast::TypeExprKind::Err,
                    span: Span::interpolate(start, self.cursor.span()),
                    node_id: self.make_id()
                };
                return self.alloc(expr);
            }
        }
        let end = self.cursor.span();
        self.cursor.advance();

        let args = self.alloc_slice(&args);

        let expr = ast::TypeExpr {
            kind: ast::TypeExprKind::Tuple(args),
            span: Span::interpolate(start, end),
            node_id: self.make_id()
        };
        self.alloc(expr)
    }

    fn parse_array_or_slice(&mut self, ty: &'ast ast::TypeExpr<'ast>) -> &'ast ast::TypeExpr<'ast> {
        self.cursor.advance();

        if let Some(tok) = self.bump_if(Punctuator::RBracket) {
            let expr = ast::TypeExpr {
                kind: ast::TypeExprKind::Slice(ty),
                span: Span::interpolate(ty.span, tok.span),
                node_id: self.make_id()
            };
            return self.alloc(expr);
        }

        let cap = match self.match_on::<Punctuator>() {
            Some(Token![_]) => {
                self.cursor.advance();
                ast::ArrayCapacity::Infer
            }
            Some(Token![..]) => {
                self.cursor.advance();
                ast::ArrayCapacity::Dynamic
            }
            _ => {
                let expr = self.parse_expr_assoc(0);
                let expr = ast::NestedConst {
                    span: expr.span,
                    expr,
                    node_id: self.make_id(),
                    def_id: OnceCell::new() 
                };
                ast::ArrayCapacity::Discrete(expr)
            }
        };

        let end = self.cursor.span();
        if self.bump_if(Punctuator::RBracket).is_none() {
            let expr = ast::TypeExpr {
                kind: ast::TypeExprKind::Err,
                span: self.cursor.span(),
                node_id: self.make_id()
            };
            return self.alloc(expr);
        }

        let expr = ast::TypeExpr {
            kind: ast::TypeExprKind::Array(ast::Array { ty, cap }),
            span: Span::interpolate(ty.span, end),
            node_id: self.make_id()
        };
        self.alloc(expr)
    }

    fn parse_ty_expr(&mut self) -> &'ast ast::TypeExpr<'ast> {
        let start = self.cursor.span();
        let mut ty_expr;
        if self.matches(Punctuator::LParen) {
            ty_expr = self.parse_tuple_ty();
        } else if let Some(symbol) = self.bump_on::<Symbol>() {
            let name = ast::Name::from_ident(ast::Ident {
                symbol,
                span: start
            });
            ty_expr = if self.matches(Token![<]) {
                let generic_args = match self.maybe_parse_generic_args() {
                    ParseTry::Sure(generic_args) =>
                        generic_args,
                        ParseTry::Doubt(generic_args, cursor) => {
                            self.cursor.sync(cursor); // there is no doubt in forced ype expression
                            generic_args
                        }
                    ParseTry::Never => {
                        let expr = ast::TypeExpr {
                            kind: ast::TypeExprKind::Err,
                            span: self.cursor.span(),
                            node_id: self.make_id()
                        };
                        return self.alloc(expr);
                    }
                };

                let expr = ast::TypeExpr {
                    kind: ast::TypeExprKind::Generic(ast::Generic {
                        name,
                        args: generic_args
                    }),
                    span: self.cursor.span(),
                    node_id: self.make_id()
                };
                self.alloc(expr)
            } else {
                let expr = ast::TypeExpr {
                    span: name.ident.span,
                    kind: ast::TypeExprKind::Name(name),
                    node_id: self.make_id()
                };
                self.alloc(expr)
            };
        } else {
            let expr = ast::TypeExpr {
                kind: ast::TypeExprKind::Err,
                span: self.cursor.span(),
                node_id: self.make_id()
            };
            return self.alloc(expr);
        }

        while let Some(punct) = self.match_on::<Punctuator>() {
            match punct {
                Punctuator::LBracket =>
                    ty_expr = self.parse_array_or_slice(ty_expr),
                Token![*] => {
                    let expr = ast::TypeExpr {
                        kind: ast::TypeExprKind::Ref(ty_expr),
                        span: self.cursor.span(),
                        node_id: self.make_id()
                    };
                    ty_expr = self.alloc(expr);
                }
                _ => break
            }
        }
        
        // Name(Name),                             = int
        // Generic(Generic<'ast>),                 = HashMap<string, int>
        // Array(Array<'ast>),                     = string[5], string[..]
        // Slice(&'ast TypeExpr<'ast>),            = string[]
        // Tuple(&'ast  [&'ast TypeExpr<'ast>]),   = (int, bool, char)

        // Ref(&'ast TypeExpr<'ast>),              = int*
        //
        ty_expr
    }

    fn maybe_parse_generic_args(&mut self) -> ParseTry<'src, &'ast [ast::GenericArgument<'ast>]> {
        todo!()
    }

    fn parse_type_init_body(
        &mut self,
        ty_expr: Option<&'ast ast::TypeExpr<'ast>>) -> &'ast ast::Expr<'ast> {
        todo!()
    }

    fn try_parse_block(&mut self) -> Option<ast::Block<'ast>> {
        let (block, cursor) = self.enter_speculative_block(|this| {
            let Some(start) = this.bump_if(Punctuator::LCurly) else {
                return None;
            };
            let start = start.span;

            let Some(stmt) = this.try_parse_stmt() else {
                return None;
            };

            let mut stmts = vec![stmt];

            while !this.matches(Punctuator::RCurly) {
                stmts.push(this.parse_stmt());
            }

            let end = this.cursor.current();
            this.cursor.advance();

            let stmts = this.alloc_slice(&stmts);

            Some(ast::Block {
                stmts,
                span: Span::interpolate(start, end.span),
                node_id: this.make_id()
            })
        });

        if let Some(block) = block {
            self.cursor.sync(cursor);
            return Some(block);
        }

        None
    }

    fn parse_expr_primary(&mut self) -> &'ast ast::Expr<'ast> {
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
        } else if let Some(symbol) = self.match_on::<Symbol>() {
            // maybe this could be a discrete type init like: 
            // `Simple { a }`, `Wrapper<int> { inner: 42 }` or `int[_] { 1, 2, 3 }`
            let try_ty = self.maybe_parse_ty_expr();
            let mut ty_expr = None;
            match try_ty {
                ParseTry::Sure(expr) => {
                    ty_expr = Some(expr);
                    if !self.matches(Punctuator::LCurly) {
                        let expr = ast::Expr {
                            kind: ast::ExprKind::Err,
                            span: token.span,
                            node_id: self.make_id()
                        };
                        return self.alloc(expr);
                    }
                }
                ParseTry::Doubt(expr, cursor) => {
                    if let TokenKind::Punctuator(
                        Punctuator::LCurly) = cursor.current().kind {
                        self.cursor.sync(cursor);
                        self.cursor.advance();
                        ty_expr = Some(expr);
                    }
                }
                ParseTry::Never => (),
            }

            let expr = if let Some(ty_expr) = ty_expr {
                self.parse_type_init_body(Some(ty_expr))
            } else {
                let name = ast::Name::from_ident(ast::Ident {
                    symbol,
                    span: token.span
                });
                self.cursor.advance(); // advance past the Symbol we matched
                let expr = ast::Expr {
                    kind: ast::ExprKind::Name(name),
                    span: token.span,
                    node_id: self.make_id()
                };
                self.alloc(expr)
            };
            return expr;
        }

        let Some(punct) = self.match_on::<Punctuator>() else {
            let expr = ast::Expr {
                kind: ast::ExprKind::Err,
                span: token.span,
                node_id: self.make_id()
            };
            return self.alloc(expr);
        };

        // Tuple (or nomral Expr resetting precedence), TypeInit or Block
        let mut end = None;
        let kind = match punct {
            Punctuator::LParen => {
                self.cursor.advance();
                if let Some(rparen) = self.bump_if(Punctuator::RParen) {
                    let expr = ast::Expr {
                        kind: ast::ExprKind::Tuple(&[]),
                        span: Span::interpolate(token.span, rparen.span),
                        node_id: self.make_id()
                    };
                    return self.alloc(expr);
                }

                let mut expr = self.parse_expr_assoc(0);

                let mut tuple_args = vec![];
                let mut flushed = false;
                while let Some(..) = self.bump_if(Token![,]) {
                    tuple_args.push(expr);

                    if self.matches(Punctuator::RParen) {
                        flushed = true;
                        break;
                    }

                    expr = self.parse_expr_assoc(0);
                }
                if !flushed {
                    tuple_args.push(expr);
                }
                if let Some(rparen) = self.bump_if(Punctuator::RParen) {
                    if tuple_args.is_empty() {
                        // FIXME: we currently don't take into account the added
                        // span changes from the parens, this can only be solved
                        // using new ExprKind::Paren
                        return expr;
                    }
                    end = Some(rparen.span);
                    ast::ExprKind::Tuple(self.alloc_slice(&tuple_args))
                } else {
                    end = Some(self.cursor.span());
                    ast::ExprKind::Err
                }
            },
            Punctuator::LCurly => {
                let Some(block) = self.try_parse_block() else {
                    return self.parse_type_init_body(None);
                };
                end = Some(block.span);
                ast::ExprKind::Block(block)
            }
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

    fn parse_call_expr(&mut self, expr: &'ast ast::Expr<'ast>, generic_args: &'ast [ast::GenericArgument<'ast>]) -> &'ast ast::Expr<'ast> {
        self.cursor.advance();

        let mut args = vec![];
        while !self.matches(Punctuator::RParen) {
            // TODO: implement lookahead
            let keyword: Option<ast::Ident> = None;
            /*if let Some(symbol) = self.match_on::<Symbol>() {
                if self.lookahead().matches(Token![:]).is_some() {
                    self.cursor.advance();
                    self.cursor.advance();
                    keyword = Some(symbol);
                }
            }*/

            let expr = self.parse_expr_assoc(0);
            let argument = if let Some(keyword) = keyword {
                ast::FunctionArgument::Keyword(keyword, expr)
            } else {
                ast::FunctionArgument::Direct(expr)
            };

            args.push(argument);
            
            if self.bump_if(Token![,]).is_none() && !self.matches(Punctuator::RParen) {
                let expr = ast::Expr {
                    kind: ast::ExprKind::Err,
                    span: Span::interpolate(expr.span, self.cursor.span()),
                    node_id: self.make_id()
                };
                return self.alloc(expr);
            }
        }
        let end = self.cursor.span();
        self.cursor.advance();

        let args = self.alloc_slice(&args);

        let expr = ast::Expr {
            kind: ast::ExprKind::FunctionCall(ast::FunctionCall {
                callable: expr,
                args,
                generic_args
            }),
            span: Span::interpolate(expr.span, end),
            node_id: self.make_id()
        };
        self.alloc(expr)
    }

    fn parse_subscript_expr(
        &mut self, expr: &'ast ast::Expr<'ast>) -> &'ast ast::Expr<'ast> {
        self.cursor.advance();

        let mut args = vec![];
        while !self.matches(Punctuator::RBracket) {
            args.push(self.parse_expr_assoc(0));
            
            if self.bump_if(Token![,]).is_none() && !self.matches(Punctuator::RBracket) {
                let expr = ast::Expr {
                    kind: ast::ExprKind::Err,
                    span: Span::interpolate(expr.span, self.cursor.span()),
                    node_id: self.make_id()
                };
                return self.alloc(expr);
            }
        }
        let end = self.cursor.span();
        self.cursor.advance();

        let args = self.alloc_slice(&args);

        let expr = ast::Expr {
            kind: ast::ExprKind::Subscript(ast::Subscript {
                expr,
                args,
            }),
            span: Span::interpolate(expr.span, end),
            node_id: self.make_id()
        };
        self.alloc(expr)
    }

    fn parse_field_expr(
        &mut self, expr: &'ast ast::Expr<'ast>) -> &'ast ast::Expr<'ast> {
        let start = self.cursor.current();
        self.cursor.advance();
        
        let ident; 
        if let Some(symbol) = self.bump_on::<Symbol>() {
            ident = ast::FieldIdent::Named(ast::Ident {
                symbol,
                span: start.span
            })
        } else if let Some(index) = self.bump_on::<u64>() {
            ident = ast::FieldIdent::Tuple {
                value: index,
                span: start.span
            }
        } else {
            let expr = ast::Expr {
                kind: ast::ExprKind::Err,
                span: self.cursor.span(),
                node_id: self.make_id()
            };
            return self.alloc(expr);
        }

        let expr = ast::Expr {
            kind: ast::ExprKind::Field(ast::Field {
                expr,
                field: ident
            }),
            span: Span::interpolate(expr.span, start.span),
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
        let mut expr = self.parse_expr_primary();
        while let Some(punct) = self.match_on::<Punctuator>() {
            expr = match punct {
                Punctuator::LParen =>
                    self.parse_call_expr(expr, &[]),
                Punctuator::LBracket =>
                    self.parse_subscript_expr(expr),
                Token![.] =>
                    self.parse_field_expr(expr),
                Token![<] if matches!(expr.kind, ast::ExprKind::Name(..)) => {
                    match self.maybe_parse_generic_args() {
                        ParseTry::Sure(generic_args) =>
                            self.parse_call_expr(expr, generic_args),
                        ParseTry::Doubt(generic_args, cursor) => {
                            if let TokenKind::Punctuator(Punctuator::LParen) = cursor.current().kind {
                                self.cursor.sync(cursor);
                                self.parse_call_expr(expr, generic_args)
                            } else {
                                break;
                            }
                        }
                        ParseTry::Never => break
                    }
                }
                _ => break,
            };
        }
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

    fn try_parse_variable_declaration(&mut self, ty_expr: &'ast ast::TypeExpr<'ast>, cursor: TokenCursor<'src>) -> Option<&'ast ast::Stmt<'ast>> {
        todo!()
    }

    fn parse_variable_declaration(&mut self, ty_expr: Option<&'ast ast::TypeExpr<'ast>>) -> &'ast ast::Stmt<'ast> {
        todo!()
    }

    fn parse_if_stmt(&mut self) -> &'ast ast::Stmt<'ast> {
        todo!()
    }

    fn parse_return_stmt(&mut self) -> &'ast ast::Stmt<'ast> {
        todo!()
    }

    fn parse_for_loop(&mut self) -> &'ast ast::Stmt<'ast> {
        todo!()
    }

    fn parse_while_loop(&mut self) -> &'ast ast::Stmt<'ast> {
        todo!()
    }

    fn parse_control_flow(&mut self, keyword: Keyword) -> &'ast ast::Stmt<'ast> {
        todo!()
    }

    fn try_parse_stmt(&mut self) -> Option<&'ast ast::Stmt<'ast>> {
        todo!()
    }

    fn parse_stmt(&mut self) -> &'ast ast::Stmt<'ast> {
        let start = self.cursor.span();

        if let Some(keyword) = self.match_on::<Keyword>() {
            return match keyword {
                Token![var] =>
                    self.parse_variable_declaration(None),
                Token![if] =>
                    self.parse_if_stmt(),
                Token![return] => 
                    self.parse_return_stmt(),
                Token![for] => 
                    self.parse_for_loop(),
                Token![while] => 
                    self.parse_while_loop(),
                Token![break] | Token![continue] => 
                    self.parse_control_flow(keyword),
                _ => {
                    let stmt = ast::Stmt {
                        kind: ast::StmtKind::Err,
                        span: start,
                        node_id: self.make_id()
                    };
                    self.alloc(stmt)
                }
            };
        }

        let ty_try = self.maybe_parse_ty_expr();
        let expr;
        match ty_try {
            ParseTry::Sure(ty_expr) =>
                return self.parse_variable_declaration(Some(ty_expr)),
            ParseTry::Doubt(ty_expr, cursor) => {
                if let Some(stmt) = self.try_parse_variable_declaration(ty_expr, cursor) {
                    return stmt;
                }
                expr = self.parse_expr_assoc(0);
            }
            ParseTry::Never => {
                expr = self.parse_expr_assoc(0);
            }
        }

        if self.bump_if(Token![;]).is_none() {
            let stmt = ast::Stmt {
                kind: ast::StmtKind::Err,
                span: self.cursor.span(),
                node_id: self.make_id()
            };
            return self.alloc(stmt);
        }

        let stmt = ast::Stmt {
            kind: ast::StmtKind::Expr(expr),
            span: expr.span,
            node_id: self.make_id()
        };
        self.alloc(stmt)
    }
}

pub fn parse_file<'a, 'sess>(session: &'sess Session, path: &Path) -> Result<ast::SourceFile<'sess>, ()> {
    let _diagnostics = session.diagnostics();
    let source = session.file_cacher().load_file(path)?;


    println!("Tokenization ...");
    let (stream, errors) = lexer::tokenize(&source);
    for err in errors {
        println!("{:?}", err);
    }

    /*let xxx = stream.into_boxed_slice();
    for x in xxx {
        println!("{:?}", x);
    }*/
    
    let tmp = bumpalo::Bump::new();

    let mut parser = Parser::new(stream, &tmp);
    let xxx = parser.parse_ty_expr();
    println!("{xxx:#?}");

    todo!()
}

