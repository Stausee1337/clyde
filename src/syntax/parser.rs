use std::{cell::OnceCell, fmt::Write, ops::ControlFlow, path::Path};

use index_vec::IndexVec;

use super::{
    ast::{self, IntoNode, Literal, LocalId, NodeId, OwnerId}, lexer::{self, AssociotiveOp, Keyword, LiteralKind, NumberMode, Operator, Punctuator, Span, StringKind, StringParser, Token, TokenKind, TokenStream, Tokenish}, symbol::Symbol
};

use crate::{diagnostics::{DiagnosticsCtxt, Message}, session::Session, Token};

enum ParseTry<'src, T> {
    Sure(T),
    Doubt(T, TokenCursor<'src>),
    Never,
}

bitflags::bitflags! {
#[derive(Clone, Copy)]
struct Restrictions: u32 {
    const NO_CURLY_BLOCKS = 0x1;
}
}

pub struct TokenCursor<'src> {
    current: *mut Token<'src>,
    end: *mut Token<'src>
}

impl<'src> TokenCursor<'src> {
    fn substream<R, F: FnMut(Token<'src>) -> ControlFlow<R>>(&self, mut do_work: F) -> Option<(R, TokenCursor<'src>)> {
        let start = self.current;
        let mut current = self.current;
        while current < self.end {
            let flow = do_work(unsafe { *current });

            match flow {
                ControlFlow::Break(result) => {
                    let cursor = TokenCursor {
                        current: start,
                        end: current
                    };
                    return Some((result, cursor));
                },
                ControlFlow::Continue(_) =>
                    current = unsafe { current.add(1) }
            }
        }

        None
    }

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

    fn lookahead(&self) -> Token<'src> {
        if self.end <= self.current {
            return unsafe { *self.current };
        }
        unsafe { *self.current.add(1) }
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

    fn try_error_advance(&mut self) {
        if self.end <= self.current {
            return;
        }
        if let TokenKind::Punctuator(
            Punctuator::LParen | Punctuator::LBracket | Punctuator::LCurly |
            Punctuator::RParen | Punctuator::RBracket | Punctuator::RCurly
        ) = self.current().kind {
            return; // never adanvce over delimiter
        }
        unsafe { self.current = self.current.add(1) };
    }

    fn advance_to(&mut self, pos: &Token<'src>) {
        let pos = (&raw const *pos) as *mut _;
        if (self.current..=self.end).contains(&pos) {
            self.current = pos;
        }
    }

    fn pos(&self) -> &Token<'src> {
        unsafe { &*self.current }
    }
}

trait Parsable: Sized {
    const CLASSNAME: Option<&'static str>;

    fn from_token<'a>(token: Token<'a>) -> Option<Self>;
}

impl<T: Operator> Parsable for T {
    const CLASSNAME: Option<&'static str> = Some("<operator>");

    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        if let TokenKind::Punctuator(punct) = token.kind {
            return T::from_punct(punct);
        }
        None
    }
}

impl Parsable for Keyword {
    const CLASSNAME: Option<&'static str> = None;

    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        if let TokenKind::Keyword(keyword) = token.kind {
            return Some(keyword);
        }
        None
    }
}

impl Parsable for Punctuator {
    const CLASSNAME: Option<&'static str> = Some("<punct>");

    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        if let TokenKind::Punctuator(punct) = token.kind {
            return Some(punct);
        }
        None
    }
}

impl Parsable for ast::Ident {
    const CLASSNAME: Option<&'static str> = Some("<ident>");

    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        if let TokenKind::Symbol(symbol) = token.kind {
            return Some(ast::Ident { symbol, span: token.span });
        }
        if let TokenKind::Punctuator(Token![_]) = token.kind {
            return Some(ast::Ident { symbol: Symbol::intern("_"), span: token.span });
        }
        return None;
    }
}

impl Parsable for Literal {
    const CLASSNAME: Option<&'static str> = Some("<lit>");

    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        match token.kind {
            TokenKind::Literal(repr, LiteralKind::Char) => {
                let mut parser = StringParser::new(StringKind::Char);
                let mut res = None;
                let mut chars = repr.chars();
                chars.next();
                for char in chars {
                    match parser.feed(char) {
                        Ok(Some(out)) => {
                            res = Some(out);
                        }
                        Err(string_error) => 
                            unreachable!("unreachable string error in parser: {string_error:?} (should have been handled at lexing stage)"),
                        _ => ()
                    }
                }

                Some(Literal::Char(res.unwrap()))
            }
            TokenKind::Literal(repr, LiteralKind::FloatingPoint) =>
                Some(Literal::Floating(repr.parse().expect("unexpected invalid float at parsing stage"))),
            TokenKind::Literal(repr, LiteralKind::IntNumber(mode)) => {
                let radix = match mode {
                    NumberMode::Binary => 2,
                    NumberMode::Octal => 8,
                    NumberMode::Decimal => 10,
                    NumberMode::Hex => 16
                };

                // FIXME: the lexer finds underscores to be valid in number literals, while
                // this rust function does not
                let value = u64::from_str_radix(repr, radix).expect("unexpected invalid int at parsing stage");
                Some(Literal::Integer(ast::Integer { value, signed: false }))
            }
            TokenKind::Literal(repr, LiteralKind::String) => {
                let mut parser = StringParser::new(StringKind::String);
                let mut buffer = String::new();
                for char in repr[1..].chars() {
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
                return Some(Literal::String(buffer));
            }
            _ => None
        }
    }
}

impl Parsable for u64 {
    const CLASSNAME: Option<&'static str> = Some("<intnumber>");

    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        if let TokenKind::Literal(repr, LiteralKind::IntNumber(mode)) = token.kind {
            let radix = match mode {
                NumberMode::Binary => 2,
                NumberMode::Octal => 8,
                NumberMode::Decimal => 10,
                NumberMode::Hex => 16
            };

            // FIXME: the lexer finds underscores to be valid in number literals, while
            // this rust function does not
            let int = u64::from_str_radix(repr, radix).expect("unexpected invalid int at parsing stage");
            return Some(int);
        }
        None
    }
}

impl Parsable for AssociotiveOp {
    const CLASSNAME: Option<&'static str> = Some("<op>");

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

enum NumberLiteral {
    Integer(ast::Integer),
    Floating(f64),
}

impl NumberLiteral {
    fn neg(self) -> NumberLiteral {
        match self {
            NumberLiteral::Integer(ast::Integer { value, signed }) =>
                NumberLiteral::Integer(ast::Integer { value, signed: !signed }),
            NumberLiteral::Floating(f) =>
                NumberLiteral::Floating(-f)
        }
    }

    fn as_literal(self) -> Literal {
        match self {
            NumberLiteral::Integer(i) =>
                Literal::Integer(i),
            NumberLiteral::Floating(f) =>
                Literal::Floating(-f)
        }
    }
}

impl Parsable for NumberLiteral {
    const CLASSNAME: Option<&'static str> = None;

    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        match token.kind {
            TokenKind::Literal(repr, LiteralKind::FloatingPoint) =>
                Some(NumberLiteral::Floating(repr.parse().expect("unexpected invalid float at parsing stage"))),
            TokenKind::Literal(repr, LiteralKind::IntNumber(mode)) => {
                let radix = match mode {
                    NumberMode::Binary => 2,
                    NumberMode::Octal => 8,
                    NumberMode::Decimal => 10,
                    NumberMode::Hex => 16
                };

                // FIXME: the lexer finds underscores to be valid in number literals, while
                // this rust function does not
                let value = u64::from_str_radix(repr, radix).expect("unexpected invalid int at parsing stage");
                Some(NumberLiteral::Integer(ast::Integer { value, signed: false }))
            }
            _ => None
        }
    }
}

type PRes<T> = Result<T, Span>;

pub struct Parser<'src, 'ast> {
    _tokens: Box<[Token<'src>]>,
    cursor: TokenCursor<'src>,
    arena: &'ast bumpalo::Bump,
    owners: &'src mut IndexVec<OwnerId, ast::Owner<'ast>>,
    owner_stack: Vec<OwnerId>,
    local_ids: IndexVec<LocalId, ast::Node<'ast>>,
    diagnostics: &'ast DiagnosticsCtxt
}

struct TokenJoiner<'a, T: Tokenish>(&'a [T]);

impl<'a, T: Tokenish> TokenJoiner<'a, T> {
    fn one(t: &'a T, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('`')?;
        std::fmt::Display::fmt(t, f)?;
        f.write_char('`')
    }
}

impl<'a, T: Tokenish> std::fmt::Display for TokenJoiner<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.len() == 1 {
            return Self::one(&self.0[0], f);
        }

        let last = self.0.len() - 1;
        for (i, tok) in self.0.iter().enumerate() {
            if i == last {
                f.write_str(" or ")?;
            } else if i > 0 {
                f.write_str(", ")?;
            }
            Self::one(tok, f)?;
        }
        Ok(())
    }
}

impl<'src, 'ast> Parser<'src, 'ast> {
    fn new(
        stream: TokenStream<'src>,
        arena: &'ast bumpalo::Bump,
        owners: &'src mut IndexVec<OwnerId, ast::Owner<'ast>>,
        diagnostics: &'ast DiagnosticsCtxt) -> Self {
        let mut tokens = stream.into_boxed_slice();
        let start = tokens.as_mut_ptr();
        let cursor = TokenCursor {
            current: start,
            end: unsafe { start.add(tokens.len() - 1) }
        };
        Self {
            _tokens: tokens,
            cursor,
            arena,
            diagnostics,
            owners,
            owner_stack: vec![],
            local_ids: IndexVec::new(),
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

    fn create_node_id<N: ast::IntoNode<'ast>>(&mut self, f: impl FnOnce(&Self, NodeId) -> &'ast N) -> &'ast N {
        let owner_id = *self.owner_stack.last().unwrap();
        let node_id = NodeId {
            owner: owner_id,
            local: self.local_ids.len_idx(),
        };
        let res = f(self, node_id);
        let node = res;
        let node = node.into_node();
        self.local_ids.insert(
            node_id.local,
            node
        );
        res
    }

    fn make_stmt(&mut self, kind: ast::StmtKind<'ast>, span: Span) -> &'ast ast::Stmt<'ast> {
        self.create_node_id(|this, node_id| this.alloc(ast::Stmt {
            kind,
            span,
            node_id
        }))
    }

    fn make_expr(&mut self, kind: ast::ExprKind<'ast>, span: Span) -> &'ast ast::Expr<'ast> {
        self.create_node_id(|this, node_id| this.alloc(ast::Expr {
            kind,
            span,
            node_id
        }))
    }

    fn make_item(&mut self, kind: ast::ItemKind<'ast>, span: Span) -> &'ast ast::Item<'ast> {
        self.create_node_id(|this, node_id| this.alloc(ast::Item {
            kind,
            span,
            node_id
        }))
    }

    fn make_generic_param(&mut self, kind: ast::GenericParamKind<'ast>, span: Span) -> &'ast ast::GenericParam<'ast> {
        self.create_node_id(|this, node_id| this.alloc(ast::GenericParam {
            kind,
            span,
            node_id
        }))
    }

    fn make_param(&mut self, ident: ast::Ident, ty: &'ast ast::TypeExpr<'ast>, span: Span) -> &'ast ast::Param<'ast> {
        self.create_node_id(|this, node_id| this.alloc(ast::Param {
            ident,
            ty,
            span,
            node_id
        }))
    }

    fn make_nested_const(&mut self, expr: &'ast ast::Expr<'ast>) -> &'ast ast::NestedConst<'ast> {
        self.create_node_id(|this, node_id| this.alloc(ast::NestedConst {
            span: expr.span,
            expr,
            node_id,
            def_id: OnceCell::new(),
        }))
    }

    fn make_field_def(&mut self, name: ast::Ident, ty: &'ast ast::TypeExpr<'ast>, default_init: Option<&'ast ast::Expr<'ast>>, span: Span) -> &'ast ast::FieldDef<'ast> {
        self.create_node_id(|this, node_id| this.alloc(ast::FieldDef {
            name,
            ty,
            default_init,
            span,
            node_id,
            def_id: OnceCell::new(),
        }))
    }

    fn make_ty_expr(&mut self, kind: ast::TypeExprKind<'ast>, span: Span) -> &'ast ast::TypeExpr<'ast> {
        self.create_node_id(|this, node_id| this.alloc(ast::TypeExpr {
            kind,
            span,
            node_id
        }))
    }

    fn with_owner<R, F: FnOnce(&mut Self) -> PRes<R>>(&mut self, do_work: F) -> PRes<(R, OwnerId, IndexVec<LocalId, ast::Node<'ast>>)> {
        let children = IndexVec::new();
        let prev_children = std::mem::replace(&mut self.local_ids, children);

        let owner_id = self.owners.len_idx();
        self.owners.push(ast::Owner::new(owner_id));
        self.owner_stack.push(owner_id);


        let res = do_work(self);

        assert_eq!(self.owner_stack.pop(), Some(owner_id));
        let children = std::mem::replace(&mut self.local_ids, prev_children);
        let r = res?;

        Ok((r, owner_id, children))
    }

    fn expect_either(&mut self, slice: &[impl Tokenish]) -> PRes<()> {
        let current = self.cursor.current();
        for test in slice {
            if test.matches(current) {
                // only one has to match
                return Ok(());
            }
        }
        let span = self.cursor.span();
        let message = format!("expected {}, found {}", TokenJoiner(slice), self.cursor.current());
        Message::error(message)
            .at(span)
            .push(self.diagnostics);

        self.cursor.try_error_advance();
        Err(span)
    }

    fn expect_one(&mut self, one: impl Tokenish) -> PRes<()> {
        self.expect_either(&[one])
    }

    fn expect_any<P: Parsable>(&mut self) -> PRes<P> {
        if let Some(p) = self.match_on::<P>() {
            return Ok(p);
        }

        let span = self.cursor.span();
        let message = format!("expected {}, found {}", P::CLASSNAME.expect("can't be used with expect_any()"), self.cursor.current());
        Message::error(message)
            .at(span)
            .push(self.diagnostics);
        self.cursor.try_error_advance();
        Err(span)
    }

    fn unexpected(&mut self, message: &str) -> PRes<!> {
        let span = self.cursor.span();
        let message = format!("expected {}, found {}", message, self.cursor.current());
        Message::error(message)
            .at(span)
            .push(self.diagnostics);
        self.cursor.try_error_advance();
        Err(span)
    }

    fn enter_speculative_block<R, F: FnOnce(&mut Self) -> R> (
        &mut self, do_work: F) -> (R, TokenCursor<'src>) {
        let cursor = self.cursor.fork();
        let result = do_work(self);
        let cursor = self.cursor.sync(cursor);
        (result, cursor.unwrap())
    }

    fn maybe_parse_ty_expr(&mut self) -> ParseTry<'src, &'ast ast::TypeExpr<'ast>> {
        let (result, cursor) = self.enter_speculative_block(|this| {
            let mut ty_expr;
            let mut sure = false;
            if let Some(ident) = this.bump_on::<ast::Ident>() {
                let name = ast::Name::from_ident(ident);
                ty_expr = if this.matches(Token![<]) {
                    let generic_args = match this.maybe_parse_generic_args() {
                        ParseTry::Sure(generic_args) => {
                            sure = true;
                            generic_args
                        },
                        ParseTry::Doubt(generic_args, cursor) => {
                            this.cursor.sync(cursor);
                            generic_args
                        }
                        ParseTry::Never =>
                            return None,
                    };

                    let kind = ast::TypeExprKind::Generic(ast::Generic {
                        name,
                        args: generic_args
                    });
                    this.make_ty_expr(kind, this.cursor.span())
                } else {
                    let span = name.ident.span;
                    this.make_ty_expr(ast::TypeExprKind::Name(name), span)
                };
            } else {
                return None;
            }

            while let Some(punct) = this.match_on::<Punctuator>() {
                match punct {
                    Punctuator::LBracket =>
                        ty_expr = this.parse_array_or_slice(ty_expr)
                            .unwrap_or_else(|span| this.make_ty_expr(ast::TypeExprKind::Err, span)),
                    Token![*] => {
                        this.cursor.advance();
                        ty_expr = this.make_ty_expr(ast::TypeExprKind::Ref(ty_expr), this.cursor.span());
                    }
                    _ => break
                }
                if let ast::TypeExprKind::Slice(..) = ty_expr.kind {
                    // slices are unmistakeably slices
                    sure = true;
                }
            }

            Some((ty_expr, sure))
        });

        let Some((ty_expr, sure)) = result else {
            return ParseTry::Never;
        };

        if sure {
            self.cursor.sync(cursor);
            return ParseTry::Sure(ty_expr);
        }

        ParseTry::Doubt(ty_expr, cursor)
    }

    fn parse_array_or_slice(&mut self, ty: &'ast ast::TypeExpr<'ast>) -> PRes<&'ast ast::TypeExpr<'ast>> {
        self.cursor.advance();

        if let Some(tok) = self.bump_if(Punctuator::RBracket) {
            let span = Span::interpolate(ty.span, tok.span);
            return Ok(self.make_ty_expr(ast::TypeExprKind::Slice(ty), span));
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
                let expr = self.parse_expr(Restrictions::empty())
                    .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));
                let expr = self.make_nested_const(expr);
                ast::ArrayCapacity::Discrete(expr)
            }
        };

        let end = self.cursor.span();
        self.expect_one(Punctuator::RBracket)?;

        self.cursor.advance();
        Ok(self.make_ty_expr(ast::TypeExprKind::Array(ast::Array { ty, cap }), Span::interpolate(ty.span, end)))
    }

    fn parse_ty_expr(&mut self) -> PRes<&'ast ast::TypeExpr<'ast>> {
        let ident = self.expect_any::<ast::Ident>()?;
        self.cursor.advance();

        let name = ast::Name::from_ident(ident);
        let mut ty_expr = if self.matches(Token![<]) {
            let generic_args = match self.maybe_parse_generic_args() {
                ParseTry::Sure(generic_args) =>
                    generic_args,
                ParseTry::Doubt(generic_args, cursor) => {
                    self.cursor.sync(cursor); // there is no doubt in forced type expression
                    generic_args
                }
                ParseTry::Never => {
                    self.unexpected("generic arguments")?
                }
            };

            self.make_ty_expr(
                ast::TypeExprKind::Generic(ast::Generic {
                    name,
                    args: generic_args
                }),
                self.cursor.span()
            )
        } else {
            let span = name.ident.span;
            self.make_ty_expr(ast::TypeExprKind::Name(name), span)
        };

        while let Some(punct) = self.match_on::<Punctuator>() {
            match punct {
                Punctuator::LBracket =>
                    ty_expr = self.parse_array_or_slice(ty_expr)?,
                Token![*] => {
                    self.cursor.advance();
                    ty_expr = self.make_ty_expr(ast::TypeExprKind::Ref(ty_expr), self.cursor.span());
                }
                _ => break
            }
        }
        
        Ok(ty_expr)
    }

    fn maybe_parse_generic_args(&mut self) -> ParseTry<'src, &'ast [ast::GenericArgument<'ast>]> {
        // searches through the token stream if there is a corresponding closing delimiter `>`
        // or if any other closing delimiters intefere with the plausiblity of a generic args sequence
        let result = {
            // breaks once we've seen one more closing then opening delimiter
            macro_rules! sub {
                ($stack:ident) => {{
                    let Some(s) = $stack.checked_sub(1) else {
                        return ControlFlow::Break(false);
                    };
                    $stack = s;  
                }};
            }

            // FIXME: we actually should be creating another delimiter stack, reporing them like we
            // do in the lexer at TokenStream::build
            // Stacks
            let mut angle = 0usize;
            let mut paren = 0usize;
            let mut curly = 0usize;
            let mut bracket = 0usize;

            let result = self.cursor.substream(|token| {
                match token.kind {
                    TokenKind::Punctuator(Token![<]) =>
                        angle += 1,
                    TokenKind::Punctuator(Punctuator::LParen) =>
                        paren += 1,
                    TokenKind::Punctuator(Punctuator::LCurly) =>
                        curly += 1,
                    TokenKind::Punctuator(Punctuator::LBracket) =>
                        bracket += 1,

                    TokenKind::Punctuator(Token![>]) => {
                        angle -= 1;
                        if angle == 0 {
                            return ControlFlow::Break(true);
                        }
                    }
                    TokenKind::Punctuator(Punctuator::RParen) =>
                        sub!(paren),
                    TokenKind::Punctuator(Punctuator::RCurly) =>
                        sub!(curly),
                    TokenKind::Punctuator(Punctuator::RBracket) =>
                        sub!(bracket),
                    _ => ()
                }
                ControlFlow::Continue(())
            });

            result
        };
        
        let Some((true, cursor)) = result else {
            return ParseTry::Never;
        };

        let prev_cursor = std::mem::replace(&mut self.cursor, cursor);
        self.cursor.advance();

        let mut args = vec![];

        let mut mismatch = false;
        let mut sure = false;
        while !self.matches(Token![>]) {
            let arg = if self.matches(Punctuator::LCurly) {
                self.cursor.advance();

                let expr = self.parse_expr(Restrictions::empty())
                    .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));

                if self.bump_if(Punctuator::RCurly).is_none() {
                    mismatch = true;
                    break;
                }
                sure = true;

                ast::GenericArgument::Expr(self.make_nested_const(expr))
            } else {
                let ty_expr = match self.maybe_parse_ty_expr() {
                    ParseTry::Sure(ty_expr) => {
                        sure = true;
                        ty_expr
                    }
                    ParseTry::Doubt(ty_expr, cursor) => {
                        self.cursor.sync(cursor);
                        ty_expr
                    }
                    ParseTry::Never => {
                        mismatch = true;
                        break;
                    }
                };
                ast::GenericArgument::Ty(ty_expr)
            };
            args.push(arg);
            
            if self.bump_if(Token![,]).is_none() && !self.matches(Token![>]) {
                mismatch = true;
                break;
            }
        }

        let fake_cursor = std::mem::replace(&mut self.cursor, prev_cursor);
        if mismatch {
            return ParseTry::Never;
        }
        let args = self.alloc_slice(&args);
        if sure || args.len() == 0 {
            self.cursor.advance_to(fake_cursor.pos());
            self.cursor.advance(); // advance over `>`
            return ParseTry::Sure(args);
        }
        let mut cursor = self.cursor.fork();
        cursor.advance_to(fake_cursor.pos());
        cursor.advance(); // advance over `>`
        ParseTry::Doubt(args, cursor)
    }

    fn parse_type_init_body(
        &mut self,
        ty_expr: &'ast ast::TypeExpr<'ast>) -> PRes<&'ast ast::Expr<'ast>> {
        let start = self.cursor.span();
        self.cursor.advance();

        let mut initializers = vec![];

        while !self.matches(Punctuator::RCurly) {
            let mut ident = None;
            if let Some(ident_) = self.match_on::<ast::Ident>() {
                if let TokenKind::Punctuator(Token![=]) = self.cursor.lookahead().kind {
                    self.cursor.advance();
                    self.cursor.advance();
                    ident = Some(ident_);
                }
            }
            let expr = self.parse_expr(Restrictions::empty())
                    .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));

            let initializer = if let Some(ident) = ident {
                ast::TypeInitKind::Field(ident, expr)
            } else {
                ast::TypeInitKind::Direct(expr)
            };

            initializers.push(initializer);


            self.expect_either(&[Token![,], Punctuator::RCurly])?;

            self.bump_if(Token![,]);    
        }
        let end = self.cursor.span();
        self.cursor.advance();

        let initializers = self.alloc_slice(&initializers);

        Ok(self.make_expr(
            ast::ExprKind::TypeInit(ast::TypeInit {
                ty: ty_expr,
                initializers
            }),
            Span::interpolate(start, end)
        ))
    }

    fn parse_expr_primary(&mut self, restrictions: Restrictions) -> PRes<&'ast ast::Expr<'ast>> {
        const UNEXPECTED_NONPRIMARY: &'static str = "null, true, false, <name>, <number>, <string>, <ident>, `(`, `{`"; //})
        let token = self.cursor.current();
        if let Some(keyword) = self.bump_on::<Keyword>() {
            let kind = match keyword {
                Token![null] =>
                    ast::ExprKind::Literal(ast::Literal::Null),
                Token![true] =>
                    ast::ExprKind::Literal(ast::Literal::Boolean(true)),
                Token![false] =>
                    ast::ExprKind::Literal(ast::Literal::Boolean(false)),
                _ => self.unexpected(UNEXPECTED_NONPRIMARY)?
            };
            return Ok(self.make_expr(kind, token.span));
        } else if let Some(literal) = self.bump_on::<Literal>() {
            return Ok(self.make_expr(ast::ExprKind::Literal(literal), token.span));
        } else if let Some(ident) = self.match_on::<ast::Ident>() {
            if !restrictions.contains(Restrictions::NO_CURLY_BLOCKS) {
                // maybe this could be a discrete type init like: 
                // `Simple { a }`, `Wrapper<int> { inner: 42 }` or `int[_] { 1, 2, 3 }`
                let try_ty = self.maybe_parse_ty_expr();
                let mut ty_expr = None;
                match try_ty {
                    ParseTry::Sure(expr) => {
                        ty_expr = Some(expr);
                        self.expect_one(Punctuator::LCurly)?;
                    }
                    ParseTry::Doubt(expr, cursor) => {
                        if let TokenKind::Punctuator(
                            Punctuator::LCurly) = cursor.current().kind {
                            self.cursor.sync(cursor);
                            ty_expr = Some(expr);
                        }
                    }
                    ParseTry::Never => (),
                }
                if let Some(ty_expr) = ty_expr {
                    return self.parse_type_init_body(ty_expr);
                }
            }

            let name = ast::Name::from_ident(ident);
            self.cursor.advance(); // advance past the Symbol we matched
            return Ok(self.make_expr(ast::ExprKind::Name(name), token.span));
        }

        let punct = self.expect_any::<Punctuator>()?;

        // Tuple (or nomral Expr resetting precedence), TypeInit or Block
        let end;
        let kind = match punct {
            Punctuator::LParen => {
                self.cursor.advance();
                if let Some(rparen) = self.bump_if(Punctuator::RParen) {
                    let span = Span::interpolate(token.span, rparen.span);
                    return Ok(self.make_expr(ast::ExprKind::Tuple(&[]), span));
                }

                let mut expr = self.parse_expr(Restrictions::empty())
                    .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));

                let mut tuple_args = vec![];
                let mut flushed = true;
                while let Some(..) = self.bump_if(Token![,]) {
                    tuple_args.push(expr);

                    if self.matches(Punctuator::RParen) {
                        flushed = true;
                        break;
                    }
                    flushed = false;
                    expr = self.parse_expr(Restrictions::empty())
                        .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));
                }
                if !flushed {
                    tuple_args.push(expr);
                }

                self.expect_one(Punctuator::RParen)?;
                end = self.cursor.span();
                self.cursor.advance();
                if tuple_args.is_empty() {
                    // FIXME: we currently don't take into account the added
                    // span changes from the parens, this can only be solved
                    // using new ExprKind::Paren
                    return Ok(expr);
                }
                ast::ExprKind::Tuple(self.alloc_slice(&tuple_args))
            },
            Punctuator::LCurly => {
                let block = self.parse_block(true);
                end = block.span;
                ast::ExprKind::Block(block)
            }
            _ => {
                self.unexpected(UNEXPECTED_NONPRIMARY)?;
            }
        };

        Ok(self.make_expr(kind, Span::interpolate(token.span, end)))
    }

    fn parse_call_expr(&mut self, expr: &'ast ast::Expr<'ast>, generic_args: &'ast [ast::GenericArgument<'ast>]) -> PRes<&'ast ast::Expr<'ast>> {
        self.cursor.advance();

        let mut args = vec![];
        while !self.matches(Punctuator::RParen) {
            let mut keyword = None;
            if let Some(ident) = self.match_on::<ast::Ident>() {
                if let TokenKind::Punctuator(Token![:]) = self.cursor.lookahead().kind {
                    self.cursor.advance();
                    self.cursor.advance();
                    keyword = Some(ident);
                }
            }

            let expr = self.parse_expr(Restrictions::empty())
                .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));

            let argument = if let Some(keyword) = keyword {
                ast::FunctionArgument::Keyword(keyword, expr)
            } else {
                ast::FunctionArgument::Direct(expr)
            };

            args.push(argument);
            self.expect_either(&[Token![,], Punctuator::RParen])?;
            self.bump_if(Token![,]);
        }
        let end = self.cursor.span();
        self.cursor.advance();

        let args = self.alloc_slice(&args);

        Ok(self.make_expr(
            ast::ExprKind::FunctionCall(ast::FunctionCall {
                callable: expr,
                args,
                generic_args
            }),
            Span::interpolate(expr.span, end),
        ))
    }

    fn parse_subscript_expr(
        &mut self, expr: &'ast ast::Expr<'ast>) -> PRes<&'ast ast::Expr<'ast>> {
        self.cursor.advance();

        let mut args = vec![];
        while !self.matches(Punctuator::RBracket) {
            args.push(
                self.parse_expr(Restrictions::empty())
                    .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span))
            );
            
            self.expect_either(&[Token![,], Punctuator::RBracket])?;
            self.bump_if(Token![,]);
        }
        let end = self.cursor.span();
        self.cursor.advance();

        let args = self.alloc_slice(&args);

        Ok(self.make_expr(
            ast::ExprKind::Subscript(ast::Subscript {
                expr,
                args,
            }),
            Span::interpolate(expr.span, end),
        ))
    }

    fn parse_field_expr(
        &mut self, expr: &'ast ast::Expr<'ast>) -> PRes<&'ast ast::Expr<'ast>> {
        let start = self.cursor.current();
        self.cursor.advance();
        
        let field; 
        let end = self.cursor.current();
        if let Some(ident) = self.bump_on::<ast::Ident>() {
            field = ast::FieldIdent::Named(ident)
        } else if let Some(index) = self.bump_on::<u64>() {
            field = ast::FieldIdent::Tuple {
                value: index,
                span: start.span
            }
        } else {
            self.unexpected("<ident> or <intnumber>")?;
        }

        Ok(self.make_expr(
            ast::ExprKind::Field(ast::Field {
                expr,
                field
            }),
            Span::interpolate(expr.span, end.span),
        ))
    }

    fn parse_expr_prefix(&mut self, restrictions: Restrictions) -> PRes<&'ast ast::Expr<'ast>> {
        let start = self.cursor.span();
        if let Some(op) = self.bump_on::<lexer::UnaryOp>() {
            let mut expr = None;
            if op == lexer::UnaryOp::Minus {
                if let Some(lit) = self.match_on::<NumberLiteral>() {
                    expr = Some(self.make_expr(
                        ast::ExprKind::Literal(lit.neg().as_literal()),
                        Span::interpolate(start, self.cursor.span())
                    ));
                    self.cursor.advance();
                }
            }
            let expr = expr.unwrap_or_else(|| self.parse_expr_prefix(restrictions).unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span)));
            return Ok(self.make_expr(
                ast::ExprKind::UnaryOp(ast::UnaryOp {
                    expr,
                    operator: op
                }),
                Span::interpolate(start, expr.span)
            ));
        } else if let Some(..) = self.bump_if(Token![*]) {
            let expr = self.parse_expr_prefix(restrictions).unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));
            return Ok(self.make_expr(
                ast::ExprKind::Deref(expr),
                Span::interpolate(start, expr.span),
            ));
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
            let expr = self.parse_expr_prefix(restrictions).unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));

            return Ok(self.make_expr(
                ast::ExprKind::UnaryOp(ast::UnaryOp {
                    expr,
                    operator: lexer::UnaryOp::Ref
                }),
                Span::interpolate(start, expr.span),
            ));
        } else if self.matches(Token![cast]) || self.matches(Token![transmute]) {
            let token = self.bump_on::<Keyword>();
            let kind = match token {
                Some(Token![cast]) => ast::TypeConversion::Cast,
                Some(Token![transmute]) => ast::TypeConversion::Transmute,
                _ => unreachable!()
            };

            self.expect_one(Punctuator::LParen)?;
            self.cursor.advance();

            let ty = if self.bump_if(Token![_]).is_none() {
                Some(self.parse_ty_expr().unwrap_or_else(|span| self.make_ty_expr(ast::TypeExprKind::Err, span)))
            } else {
                None
            };

            self.expect_one(Punctuator::RParen)?;
            self.cursor.advance();

            let expr = self.parse_expr_prefix(restrictions).unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));

            return Ok(self.make_expr(
                ast::ExprKind::Cast(ast::Cast {
                    expr,
                    ty,
                    kind
                }),
                Span::interpolate(start, expr.span),
            ));
        } else {
            match self.match_on::<Punctuator>() {
                Some(Token![+]) => {
                    Message::error("`+` is not a valid unary operator")
                        .at(self.cursor.span())
                        .push(self.diagnostics);
                    self.cursor.advance();
                },
                Some(Token![++]) => {
                    Message::error("there is no prefix increment operator in this language")
                        .at(self.cursor.span())
                        .note("use `+= 1` instead")
                        .push(self.diagnostics);
                    self.cursor.advance();
                },
                Some(Token![--]) => {
                    Message::error("there is no prefix decrement operator in this language")
                        .at(self.cursor.span())
                        .note("use `-= 1` instead")
                        .push(self.diagnostics);
                    self.cursor.advance();
                },
                _ => ()
            }
        }
        let mut expr = self.parse_expr_primary(restrictions)?;
        while let Some(punct) = self.match_on::<Punctuator>() {
            expr = match punct {
                Punctuator::LParen =>
                    self.parse_call_expr(expr, &[]).unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span)),
                Punctuator::LBracket =>
                    self.parse_subscript_expr(expr).unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span)),
                Token![.] =>
                    self.parse_field_expr(expr).unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span)),
                Token![<] if let ast::ExprKind::Name(..) = expr.kind => {
                    match self.maybe_parse_generic_args() {
                        ParseTry::Sure(generic_args) =>
                            self.parse_call_expr(expr, generic_args)
                                .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span)),
                        ParseTry::Doubt(generic_args, cursor) => {
                            if let TokenKind::Punctuator(Punctuator::LParen) = cursor.current().kind {
                                self.cursor.sync(cursor);
                                self.parse_call_expr(expr, generic_args)
                                    .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span))
                            } else {
                                break;
                            }
                        }
                        ParseTry::Never => break
                    }
                }
                Token![++] => {
                    Message::error("there is no postfix increment operator in this language")
                        .at(self.cursor.span())
                        .note("use `+= 1` instead")
                        .push(self.diagnostics);
                    self.cursor.advance();
                    continue;
                },
                Token![--] => {
                    Message::error("there is no postfix decrement operator in this language")
                        .at(self.cursor.span())
                        .note("use `-= 1` instead")
                        .push(self.diagnostics);
                    self.cursor.advance();
                    continue;
                },
                _ => break,
            };
        }
        Ok(expr)
    }

    fn parse_expr_assoc(&mut self, min_precendence: u32, restrictions: Restrictions) -> PRes<&'ast ast::Expr<'ast>> {
        let mut lhs = self.parse_expr_prefix(restrictions).unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));

        while let Some(op) = self.match_on::<AssociotiveOp>() {
            let prec = op.precedence();
            if prec < min_precendence {
                break;
            }
            self.bump();

            let rhs = self.parse_expr_assoc(prec + op.associotivity() as u32, restrictions)
                .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));

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

            lhs = self.make_expr(kind, span);
        }
        Ok(lhs)
    }

    fn parse_expr(&mut self, restrictions: Restrictions) -> PRes<&'ast ast::Expr<'ast>> {
        self.parse_expr_assoc(0, restrictions)
    }

    fn try_parse_variable_declaration(&mut self, ty_expr: &'ast ast::TypeExpr<'ast>, cursor: TokenCursor<'src>) -> Option<&'ast ast::Stmt<'ast>> {
        let (node, cursor) = self.enter_speculative_block(|this| {
            this.cursor.sync(cursor);
            let start = ty_expr.span;

            let Some(ident) = this.bump_on::<ast::Ident>() else {
                return None;
            };

            let mut end = ident.span;

            let mut init = None;
            if this.bump_if(Token![=]).is_some() {
                let expr = this.parse_expr(Restrictions::empty());
                init = Some(expr.unwrap_or_else(|span| this.make_expr(ast::ExprKind::Err, span)));
                end = expr.map_or_else(|span| span, |expr| expr.span);
            }

            Some(this.make_stmt(
                ast::StmtKind::Local(ast::Local {
                    ident,
                    ty: Some(ty_expr),
                    init
                }),
                Span::interpolate(start, end)
            ))
        });

        let Some(node) = node else {
            return None;
        };

        self.cursor.sync(cursor);
        if let Err(span) = self.expect_one(Token![;]) {
            return Some(self.make_stmt(ast::StmtKind::Err, span));
        }

        self.cursor.advance();

        Some(node)
    }

    fn parse_variable_declaration(&mut self, ty_expr: Option<&'ast ast::TypeExpr<'ast>>) -> PRes<&'ast ast::Stmt<'ast>> {
        let start;
        if let Some(ty_expr) = ty_expr {
            start = ty_expr.span;
        } else {
            start = self.cursor.span();
            self.cursor.advance();
        }

        // TODO: parse Pattern instead of Ident in case of `var`-binding
        let ident = self.expect_any::<ast::Ident>()?;
        self.cursor.advance();

        let mut end = ident.span;

        let mut init = None;
        if self.bump_if(Token![=]).is_some() {
            let expr = self.parse_expr(Restrictions::empty());
            init = Some(expr.unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span)));
            end = expr.map_or_else(|span| span, |expr| expr.span);
        }

        self.expect_one(Token![;])?;
        self.cursor.advance();

        Ok(self.make_stmt(
            ast::StmtKind::Local(ast::Local {
                ident,
                ty: ty_expr,
                init
            }),
            Span::interpolate(start, end)
        ))
    }

    fn parse_if_stmt(&mut self) -> PRes<&'ast ast::Stmt<'ast>> {
        let start = self.cursor.span();
        self.cursor.advance();

        let condition = self.parse_expr(Restrictions::NO_CURLY_BLOCKS)
            .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));

        self.expect_one(Punctuator::LCurly)?;
        let body = self.parse_block(false);

        let mut else_branch = None;
        if self.bump_if(Token![else]).is_some() {
            else_branch = Some(if self.matches(Token![if]) {
                self.parse_if_stmt()
                    .unwrap_or_else(|span| self.make_stmt(ast::StmtKind::Err, span))
            } else {
                self.expect_one(Punctuator::LCurly)?;
                let body = self.parse_block(false);
                let span = body.span;
                self.make_stmt(ast::StmtKind::Block(body), span)
            });
        }

        let end = if let Some(else_branch) = else_branch {
            else_branch.span
        } else {
            body.span
        };

        let span = Span::interpolate(start, end);
        Ok(self.make_stmt(
            ast::StmtKind::If(ast::If {
                condition,
                body,
                else_branch
            }),
            span
        ))
    }

    fn parse_return_stmt(&mut self, keyword: Keyword) -> PRes<&'ast ast::Stmt<'ast>> {
        let start = self.cursor.span();
        self.cursor.advance();
        
        let expr;
        let end;
        if self.bump_if(Token![;]).is_some() {
            expr = None;
            end = start;
        } else {
            let expr_ = self.parse_expr(Restrictions::empty()).unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));
            end = expr_.span;
            expr = Some(expr_);
            self.expect_one(Token![;])?;
            self.cursor.advance();
        }
        
        match keyword {
            Token![return] =>
                Ok(self.make_stmt(
                    ast::StmtKind::Return(expr),
                    Span::interpolate(start, end)
                )),
            Token![yeet] =>
                Ok(self.make_stmt(
                    ast::StmtKind::Yeet(ast::Yeet {
                        expr,
                        origin: ast::YeetOrigin::Explicit,
                        owner: OnceCell::new()
                    }),
                    Span::interpolate(start, end)
                )),
            _ => unreachable!()
        }
    }

    fn parse_for_loop(&mut self) -> PRes<&'ast ast::Stmt<'ast>> {
        let start = self.cursor.span();
        self.cursor.advance();

        let bound_var = self.expect_any::<ast::Ident>()?;
        self.cursor.advance();
        self.expect_one(Token![in])?;
        self.cursor.advance();

        let iterator = self.parse_expr(Restrictions::NO_CURLY_BLOCKS)
            .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));

        self.expect_one(Punctuator::LCurly)?;
        let body = self.parse_block(false);

        let span = Span::interpolate(start, body.span);
        Ok(self.make_stmt(
            ast::StmtKind::For(ast::For {
                bound_var,
                body,
                iterator,
            }),
            span
        ))
    }

    fn parse_while_loop(&mut self) -> PRes<&'ast ast::Stmt<'ast>> {
        let start = self.cursor.span();
        self.cursor.advance();

        let condition = self.parse_expr(Restrictions::NO_CURLY_BLOCKS)
            .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));

        self.expect_one(Punctuator::LCurly)?;
        let body = self.parse_block(false);

        let span = Span::interpolate(start, body.span);
        Ok(self.make_stmt(
            ast::StmtKind::While(ast::While {
                condition, body
            }),
            span
        ))
    }

    fn parse_control_flow(&mut self, keyword: Keyword) -> PRes<&'ast ast::Stmt<'ast>> {
        let control_flow = match keyword {
            Token![break] =>
                ast::ControlFlowKind::Break,
            Token![continue] =>
                ast::ControlFlowKind::Continue,
            _ => unreachable!()
        };
        let span = self.cursor.span();
        self.cursor.advance();
        self.expect_one(Token![;])?;
        self.cursor.advance();
        Ok(self.make_stmt(
            ast::StmtKind::ControlFlow(ast::ControlFlow {
                kind: control_flow,
                destination: OnceCell::new(),
                span
            }),
            span
        ))
    }

    fn parse_stmt(&mut self, allow_implicit_yeet: impl FnOnce(&mut Self) -> bool) -> PRes<&'ast ast::Stmt<'ast>> {
        // if we've got semicolons in the stream at this point, its because the last statement
        // likely errored, so don't warn here as they probably aren't actually redundant
        self.remove_redundant_semis(false);

        if let Some(keyword) = self.match_on::<Keyword>() {
            match keyword {
                Token![var] =>
                    return self.parse_variable_declaration(None),
                Token![if] =>
                    return self.parse_if_stmt(),
                Token![return] | Token![yeet] => 
                    return self.parse_return_stmt(keyword),
                Token![for] => 
                    return self.parse_for_loop(),
                Token![while] => 
                    return self.parse_while_loop(),
                Token![break] | Token![continue] => 
                    return self.parse_control_flow(keyword),
                _ => ()
            };
        }

        let ty_try = self.maybe_parse_ty_expr();
        match ty_try {
            ParseTry::Sure(ty_expr) =>
                return self.parse_variable_declaration(Some(ty_expr)),
            ParseTry::Doubt(ty_expr, cursor) => {
                if let Some(stmt) = self.try_parse_variable_declaration(ty_expr, cursor) {
                    return Ok(stmt);
                }
            }
            ParseTry::Never => ()
        }
        let expr = self.parse_expr(Restrictions::empty())
            .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));

        let end;
        let kind = if allow_implicit_yeet(self) {
            end = expr.span;
            ast::StmtKind::Yeet(ast::Yeet {
                expr: Some(expr),
                origin: ast::YeetOrigin::Implicit,
                owner: OnceCell::new()
            })
        } else if let ast::ExprKind::Block(..) = expr.kind {
            end = self.cursor.span();
            ast::StmtKind::Expr(expr)
        } else {
            self.expect_one(Token![;])?;
            end = self.cursor.span();
            self.cursor.advance();
            ast::StmtKind::Expr(expr)
        };

        self.remove_redundant_semis(true);

        Ok(self.make_stmt(kind, Span::interpolate(expr.span, end)))
    }

    fn remove_redundant_semis(&mut self, warn: bool) {
        let start = self.cursor.span();
        let mut end = None;
        while let Some(tok) = self.bump_if(Token![;]) {
            end = Some(tok.span);
        }

        if !warn {
            return;
        }
        if let Some(end) = end {
            Message::warning("redundant extra semicolons")
                .at(Span::interpolate(start, end))
                .note("remove those semicolons")
                .push(self.diagnostics);
        }
    }

    fn parse_block(&mut self, expr_block: bool) -> ast::Block<'ast> {
        let start = self.cursor.span();
        self.cursor.advance();

        let mut stmts = vec![];
        while !self.matches(Punctuator::RCurly) {
            stmts.push(
                self.parse_stmt(|this| expr_block && this.matches(Punctuator::RCurly))
                    .unwrap_or_else(|span| self.make_stmt(ast::StmtKind::Err, span))
            );
        }
        let end = self.cursor.span();
        self.cursor.advance();

        let stmts = self.alloc(stmts);

        ast::Block {
            stmts,
            span: Span::interpolate(start, end),
        }
    }

    fn parse_struct_item(&mut self) -> PRes<&'ast ast::Item<'ast>> {
        let res = self.with_owner(|this| {
            let start = this.cursor.span();
            this.cursor.advance();

            let ident = this.expect_any::<ast::Ident>()?;
            this.cursor.advance();

            let generics = if this.bump_if(Token![<]).is_some() {
                this.parse_generic_params()?
            } else {
                &[]
            };

            this.expect_either(&[Punctuator::LCurly, Token![;]])?;
            let mut fields = vec![];

            if this.bump_if(Punctuator::LCurly).is_some() {
                while !this.matches(Punctuator::RCurly) {
                    let start = this.cursor.span();

                    let ty = this.parse_ty_expr()
                            .unwrap_or_else(|span| this.make_ty_expr(ast::TypeExprKind::Err, span));
                    let name = this.expect_any::<ast::Ident>()?;
                    this.cursor.advance();

                    let mut init = None;
                    let end;
                    if this.bump_if(Token![=]).is_some() {
                        let expr = this.parse_expr(Restrictions::empty())
                            .unwrap_or_else(|span| this.make_expr(ast::ExprKind::Err, span));
                        end = expr.span;
                        init = Some(expr);
                    } else {
                        end = name.span;
                    }
                    this.expect_one(Token![;])?;

                    let span = Span::interpolate(start, end);
                    this.cursor.advance();
                    fields.push(this.make_field_def(name, ty, init, span));
                }
            }
            let end = this.cursor.span();
            this.cursor.advance();

            let fields = this.alloc_slice(&fields);

            let span = Span::interpolate(start, end);
            Ok((
                ast::ItemKind::Struct(ast::Struct {
                    ident,
                    generics,
                    fields,
                }),
                span
            ))
        });
        let ((kind, span), owner_id, children) = res?;
        let item = self.make_item(kind, span);
        self.owners[owner_id].initialize(item.into_node(), children);
        Ok(item)
    }

    fn parse_enum_item(&mut self) -> PRes<&'ast ast::Item<'ast>> {
        todo!()
    }

    fn parse_generic_params(&mut self) -> PRes<&'ast [&'ast ast::GenericParam<'ast>]> {
        let mut generics = vec![];
        self.cursor.advance();

        while !self.matches(Token![>]) {
            let start = self.cursor.span();

            let kind = if self.bump_if(Token![const]).is_some() {
                // struct Maxtrix<const nuint ROWS, ..
                //                      ^
                let ty = self.parse_ty_expr()
                    .unwrap_or_else(|span| self.make_ty_expr(ast::TypeExprKind::Err, span));
                let ident = self.expect_any::<ast::Ident>()?;
                ast::GenericParamKind::Const(ident, ty)
            } else {
                // struct HashMap<Key,
                //                ^
                let ident = self.expect_any::<ast::Ident>()?;
                ast::GenericParamKind::Type(ident)
            };
            let end = self.cursor.span();
            self.cursor.advance();

            generics.push(
                self.make_generic_param(kind, Span::interpolate(start, end))
            );

            self.expect_either(&[Token![,], Token![>]])?;
            self.bump_if(Token![,]);
        }
        self.cursor.advance();

        let generics = self.alloc_slice(&generics);

        Ok(generics)
    }

    fn parse_function_item(&mut self, ty: &'ast ast::TypeExpr<'ast>, ident: ast::Ident) -> PRes<(ast::ItemKind<'ast>, Span)> {
        // OwnedPtr<int*>[] get_int(...
        //                         ^
        //          OR
        // OwnedPtr<T*>[] get_obj<T>(...
        //                       ^
        let start = self.cursor.span();
        self.cursor.advance();
 
        let generics = if self.bump_if(Token![<]).is_some() {
            self.parse_generic_params()?
        } else {
            &[]
        };

        let mut params = vec![];

        while !self.matches(Punctuator::RParen) {
            let start = self.cursor.span();
            let ty = self.parse_ty_expr()
                .unwrap_or_else(|span| self.make_ty_expr(ast::TypeExprKind::Err, span));
            let ident = self.expect_any::<ast::Ident>()?;
            self.cursor.advance();

            params.push(self.make_param(ident, ty, Span::interpolate(start, ident.span)));

            self.expect_either(&[Token![,], Punctuator::RParen])?;
            self.bump_if(Token![,]);
        }
        let end = self.cursor.span();
        self.cursor.advance();

        let params = self.alloc_slice(&params);

        let sig = ast::FnSignature {
            returns: ty,
            generics,
            params
        };

        let body = match self.match_on::<Punctuator>() {
            Some(Punctuator::LCurly) => {
                let block = self.parse_block(false);
                let span = block.span;
                Some(self.make_expr(ast::ExprKind::Block(block), span))
            }
            Some(Token![;]) => {
                self.cursor.advance();
                None
            },
            _ => self.unexpected("`;` or `{`")?, // }
        };

        let span = Span::interpolate(start, end);
        Ok((
            ast::ItemKind::Function(ast::Function {
                ident,
                sig,
                body,
                span,
            }),
            span 
        ))
    }

    fn parse_global_item(&mut self, ty: &'ast ast::TypeExpr<'ast>, ident: ast::Ident, constant: bool) -> PRes<(ast::ItemKind<'ast>, Span)> {
        let mut init = None;
        if self.bump_if(Token![=]).is_some() {
            init = Some(
                self.parse_expr(Restrictions::empty())
                    .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span))
            );
        }
        self.expect_one(Token![;])?;
        let end = self.cursor.span();
        self.cursor.advance();

        Ok((
            ast::ItemKind::GlobalVar(ast::GlobalVar {
                ident,
                ty,
                init,
                constant
            }),
            Span::interpolate(ty.span, end)
        ))
    }

    fn parse_item(&mut self) -> PRes<&'ast ast::Item<'ast>> {
        if let Some(keyword) = self.match_on::<Keyword>() {
            match keyword {
                Token![struct] =>
                    return self.parse_struct_item(),
                Token![enum] =>
                    return self.parse_enum_item(),
                _ => ()
            }
        }

        let res = self.with_owner(|this| {
            let constant = this.bump_if(Token![const]).is_some();
            let ty = this.parse_ty_expr()
                .unwrap_or_else(|span| this.make_ty_expr(ast::TypeExprKind::Err, span));

            let ident = this.expect_any::<ast::Ident>()?;
            this.cursor.advance();

            if this.matches(Punctuator::LParen) {
                this.parse_function_item(ty, ident)
            } else {
                this.parse_global_item(ty, ident, constant)
            }
        });
        let ((kind, span), owner_id, children) = res?;
        let item = self.make_item(kind, span);
        self.owners[owner_id].initialize(item.into_node(), children);
        Ok(item)
    }

    fn parse_source_file(&mut self, file_span: Span) -> &'ast ast::SourceFile<'ast> {
        let res = self.with_owner(|this| {
            let mut items = vec![];

            while !this.cursor.is_eos() {
                items.push(
                    this.parse_item()
                        .unwrap_or_else(|span| this.make_item(ast::ItemKind::Err, span))
                );
            }

            let items = this.alloc_slice(&items);

            Ok(this.create_node_id(|this, node_id| this.alloc(ast::SourceFile {
                items,
                node_id,
                span: file_span
            })))
        });
        let (source, owner_id, children) = res.unwrap();
        self.owners[owner_id].initialize(source.into_node(), children);

        source
    }
}

pub fn parse_file<'a, 'tcx>(
    session: &'tcx Session,
    path: &Path,
    ast_info: &'tcx ast::AstInfo<'tcx>) -> Result<&'tcx ast::SourceFile<'tcx>, ()> {
    let diagnostics = session.diagnostics();
    let source = session.file_cacher().load_file(path)?;


    let stream = lexer::tokenize(&source, diagnostics)?;
    
    let mut owners = ast_info.global_owners.borrow_mut();
    let source_file = if !stream.is_empty() {
        let arena = &ast_info.arena;
        let mut parser = Parser::new(stream, arena, &mut owners, diagnostics);
        parser.parse_source_file(source.byte_span)
    } else {
        let owner_id = owners.len_idx();
        let owner_id = owners.push(ast::Owner::new(owner_id));
        let node = ast_info.arena.alloc(ast::SourceFile {
            items: &[],
            node_id: NodeId { owner: owner_id, local: LocalId::from_raw(0) },
            span: Span::NULL
        });
        let node = &*node;
        owners[owner_id].initialize(ast::Node::SourceFile(node), IndexVec::new());
        node
    };

    Ok(source_file)
}

