use std::{cell::OnceCell, fmt::Write, ops::ControlFlow, path::Path};

use index_vec::IndexVec;

use super::{
    ast::{self, IntoNode, Literal, LocalId, NodeId, OwnerId}, lexer::{self, AssociotiveOp, Directive, Keyword, LiteralKind, NumberMode, Operator, Punctuator, Span, StringKind, StringParser, Token, TokenKind, TokenStream, Tokenish}, symbol::{sym, Symbol}
};

use crate::{diagnostics::{DiagnosticsCtxt, Message}, session::Session, Token};

enum ParseTry<'src, T> {
    Sure(T),
    Doubt(T, TokenCursor<'src>),
    Never(TokenCursor<'src>),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Delimiter {
    Paren,
    Curly,
    Bracket
}

bitflags::bitflags! {
#[derive(Clone, Copy)]
struct Restrictions: u32 {
    const NO_CURLY_BLOCKS = 0x1;
}
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ItemContext {
    Module,
    Block,
    Struct
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
        // FIXME: this is the only source of unsafety in TokenCursor since it clones 
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

    fn end(&self) -> &Token<'src> {
        unsafe { &*self.end }
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

    fn advance_to(&mut self, pos: &Token<'src>) {
        let pos = (&raw const *pos) as *mut _;
        if (self.current..=self.end).contains(&pos) {
            self.current = pos;
        }
    }

    fn skip_while(&mut self, mut p: impl FnMut(Token) -> bool) {
        while !self.is_eos() {
            if !p(self.current()) {
                break;
            }
            self.advance();
        }
    }

    fn pos(&self) -> &Token<'src> {
        unsafe { &*self.current }
    }
}

trait Parsable: Sized {
    const CLASSNAME: Option<&'static str>;

    fn from_token<'a>(token: Token<'a>) -> Option<Self>;

    fn from_error(_: Span) -> Option<Self> {
        None
    }
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

impl Parsable for Directive {
    const CLASSNAME: Option<&'static str> = Some("<directive>");

    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        if let TokenKind::Directive(directive) = token.kind {
            return Some(directive);
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

    fn from_error(span: Span) -> Option<Self> {
        Some(ast::Ident {
            symbol: Symbol::intern("<err>"),
            span,
        })
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
            TokenKind::Keyword(Token![true]) => Some(Literal::Boolean(true)),
            TokenKind::Keyword(Token![false]) => Some(Literal::Boolean(false)),
            _ => None
        }
    }
}

impl Parsable for String {
    const CLASSNAME: Option<&'static str> = Some("<string>");

    fn from_token<'a>(token: Token<'a>) -> Option<Self> {
        if let TokenKind::Literal(repr, LiteralKind::String) = token.kind {
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
            return Some(buffer);
        }
        None
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

enum DirectiveTree {
    Ident(ast::Ident),
    Value(Literal, Span),
    KeyValue {
        key: ast::Ident,
        value: (Literal, Span)
    }
}

impl DirectiveTree {
    fn span(&self) -> Span {
        match self {
            DirectiveTree::Ident(ident) => ident.span,
            DirectiveTree::Value(_, span) => *span,
            DirectiveTree::KeyValue { key, value } => Span::interpolate(key.span, value.1)
        }
    }
}

impl std::fmt::Display for DirectiveTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DirectiveTree::Ident(ident) => write!(f, "{}", ident.symbol),
            DirectiveTree::Value(literal, _) => write!(f, "{}", literal),
            DirectiveTree::KeyValue { key, value } => write!(f, "{}={}", key.symbol, value.0),
        }
    }
}

/// A list containing a nonzero amount of directive trees
struct DirectiveTrees(Vec<DirectiveTree>);

impl DirectiveTrees {
    /// expects one of `symbols` to be in the directive tree and errors if there are more than one
    /// tree or none of the symbols can be found at all
    fn expect_either(mut self, symbols: &[Symbol], parser: &mut Parser) -> PRes<Symbol> {
        let erroneous = self.0.len() > 1;
        let mut found = None;
        for (idx, tree) in self.0.iter().enumerate() {
            if let DirectiveTree::Ident(ast::Ident { symbol, .. }) = tree && symbols.contains(symbol) && found.is_none() {
                found = Some((idx, *symbol));
            }
        }
        if let Some((idx, _)) = found {
            self.0.remove(idx);
        }
        if erroneous || found.is_none() {
            let tree = self.0.first().unwrap();
            let mut message = Message::error(format!("unexpected directive tree `{}`", tree))
                .at(tree.span());
            if found.is_none() {
                message = message.note(format!("expected {}", TokenJoiner(symbols)));
            }
            message.push(parser.diagnostics);
            return Err(tree.span());
        }
        Ok(found.unwrap().1)
    }

    fn get<R: TryFrom<Literal, Error = &'static str>>(mut self, key: Symbol, single: bool, parser: &mut Parser) -> PRes<R> {
        let erroneous = self.0.len() > 1 && single;
        let mut found = None;
        for (idx, tree) in self.0.iter().enumerate() {
            if let DirectiveTree::KeyValue { key: ast::Ident { symbol, .. }, value } = tree && key == *symbol && found.is_none() {
                found = Some((idx, value.clone()));
            }
        }
        if let Some((idx, _)) = found {
            self.0.remove(idx);
        }
        if erroneous || found.is_none() {
            let tree = self.0.first().unwrap();
            let mut message = Message::error(format!("unexpected directive tree `{}`", tree))
                .at(tree.span());
            if found.is_none() {
                message = message.note(format!("expected `{}=...`", key));
            }
            message.push(parser.diagnostics);
            return Err(tree.span());
        }
        let (literal, span) = found.unwrap().1;
        match R::try_from(literal) {
            Ok(res) => return Ok(res),
            Err(ty) => {
                Message::error("directive tree value is of wrong type")
                    .at(span)
                    .note(format!("expected {} value", ty.to_lowercase()))
                    .push(parser.diagnostics);

                return Err(span);
            }
        }
    }

    fn span(&self) -> Span {
        let start = self.0.first().unwrap().span();
        let end = self.0.last().unwrap().span();
        Span::interpolate(start, end)
    }
}

impl<'ast> ast::Path<'ast> {
    fn from_ident(parser: &Parser<'_, 'ast>, ident: ast::Ident) -> Self {
        let segment = parser.alloc(ast::PathSegment::from_ident(ident));
        Self::from_segments(std::slice::from_ref(segment))
    }

    fn as_ty_expr(self, parser: &mut Parser<'_, 'ast>) -> &'ast ast::TypeExpr<'ast> {
        if self.is_invisible() {
            let ast::GenericArgumentKind::Ty(ty) = self.segments[0].generic_args[0].kind else {
                unreachable!();
            };
            return ty;
        }
        let span = self.span;
        parser.make_ty_expr(ast::TypeExprKind::Path(self), span) 
    }

    fn simple(&self, parser: &mut Parser<'_, 'ast>) -> Self {
        if self.is_invisible() {
            let ast::GenericArgumentKind::Ty(mut ty) = self.segments[0].generic_args[0].kind else {
                unreachable!();
            };

            ty = ty.unwrap().unwrap();
            let ast::TypeExprKind::Path(path) = &ty.kind else {
                unreachable!();
            };

            return path.clone();
        }
        let segments = parser.arena.alloc_slice_clone(self.segments);
        segments.last_mut().unwrap().generic_args = &[];
        Self::from_segments(segments)
    }

    fn is_invisible(&self) -> bool {
        self.segments.len() == 1 && self.segments[0].ident.is_none()
    }
}

impl<'ast> ast::TypeExpr<'ast> {
    fn unwrap(&'ast self) -> Option<&'ast Self> {
        match &self.kind {
            ast::TypeExprKind::Ref(inner) => Some(inner),
            ast::TypeExprKind::Slice(inner) => Some(inner),
            ast::TypeExprKind::Array(inner) => Some(inner.ty),
            ast::TypeExprKind::Path(..) => None,
            ast::TypeExprKind::Err => None,
        }
    }
}

type PRes<T> = Result<T, Span>;

#[derive(Clone, Copy, PartialEq, Eq)]
enum PathMode {
    Normal,
    // `PathMode::Function` changes the doubt mechanism inside `maybe_parse_path`.
    // Instead of making the function question if there even is a path, it allows the function to
    // parse incomplete paths.
    Function,
}

enum ItemHeader<'ast> {
    Ty(&'ast ast::TypeExpr<'ast>),
    Done(ast::ItemKind<'ast>, Span),
    Err(Span),
    None,
}

pub struct Parser<'src, 'ast> {
    _tokens: Box<[Token<'src>]>,
    cursor: TokenCursor<'src>,
    arena: &'ast bumpalo::Bump,
    owners: &'src mut IndexVec<OwnerId, ast::Owner<'ast>>,
    owner_stack: Vec<OwnerId>,
    local_ids: IndexVec<LocalId, ast::Node<'ast>>,
    currrent_item_scope: ast::Scope,
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
            currrent_item_scope: Default::default(),
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
            scope: this.currrent_item_scope,
            def_id: OnceCell::new(),
            node_id
        }))
    }

    fn make_generic_param(&mut self, kind: ast::GenericParamKind<'ast>, span: Span) -> &'ast ast::GenericParam<'ast> {
        self.create_node_id(|this, node_id| this.alloc(ast::GenericParam {
            kind,
            span,
            node_id,
            def_id: OnceCell::new()
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

    fn make_variant_def(&mut self, name: ast::Ident, discriminant: Option<&'ast ast::NestedConst<'ast>>, span: Span) -> &'ast ast::VariantDef<'ast> {
        self.create_node_id(|this, node_id| this.alloc(ast::VariantDef {
            name,
            discriminant,
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

    fn fail_parse_tree<R, F: FnOnce(&mut Self) -> PRes<R>>(&mut self, delim: Delimiter, do_work: F) -> PRes<R> {
        let res = do_work(self);

        if let Err(..) = res {
            let end = match delim {
                Delimiter::Paren => TokenKind::Punctuator(Punctuator::RParen),
                Delimiter::Bracket => TokenKind::Punctuator(Punctuator::RBracket),
                Delimiter::Curly => TokenKind::Punctuator(Punctuator::RCurly),
            };
            self.cursor.skip_while(|token| token.kind != end);
            debug_assert!(!self.cursor.is_eos(), "Bug: opening paren needs respective closing paren");
        }
        res
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
        let message = Message::error(message);

        // recovery:
        //  - if we expected a `;`, but found `,` -> recover
        //  - if we expected a `,`, but found `;` -> recover
        //  - if we expected a `LParen`, `LBracket`, `LCurly` -> fail
    
        //  - in any case if there is an opening delimiter (`LParen`, `LBracket`, `LCurly`) but we
        //  didn't expect one that one, skip until closing delimiter

        let did_expect = |tok: Punctuator| {
            let tok = Token {
                kind: TokenKind::Punctuator(tok),
                span: Span::NULL
            };
            for test in slice {
                if test.matches(tok) {
                    // only one has to match
                    return true;
                }
            }

            false
        };

        if Token![,].matches(current) && did_expect(Token![;]) {
            message.at(current.span).push(self.diagnostics);
            return Ok(());
        }
        if Token![;].matches(current) && did_expect(Token![,]) {
            message.at(current.span).push(self.diagnostics);
            return Ok(());
        }

        if Token![::=].matches(current) && did_expect(Token![=]) {
            message.at(current.span).push(self.diagnostics);
            return Ok(());
        }
        if Token![=].matches(current) && did_expect(Token![::=]) {
            message.at(current.span).push(self.diagnostics);
            return Ok(());
        }

        let skipped_tree;
        match current.kind {
            TokenKind::Punctuator(Punctuator::LParen) => {
                self.cursor.skip_while(|token| !matches!(token.kind, TokenKind::Punctuator(Punctuator::RParen)));
                let end = self.cursor.span();
                message
                    .at(Span::interpolate(current.span, end))
                    .push(self.diagnostics);
                debug_assert!(!self.cursor.is_eos(), "Bug: opening paren needs respective closing paren");
                skipped_tree = true;
            }
            TokenKind::Punctuator(Punctuator::LBracket) => {
                self.cursor.skip_while(|token| !matches!(token.kind, TokenKind::Punctuator(Punctuator::RBracket)));
                let end = self.cursor.span();
                message
                    .at(Span::interpolate(current.span, end))
                    .push(self.diagnostics);
                debug_assert!(!self.cursor.is_eos(), "Bug: opening paren needs respective closing paren");
                skipped_tree = true;
            }
            TokenKind::Punctuator(Punctuator::LCurly) => {
                self.cursor.skip_while(|token| !matches!(token.kind, TokenKind::Punctuator(Punctuator::RCurly)));
                let end = self.cursor.span();
                message
                    .at(Span::interpolate(current.span, end))
                    .push(self.diagnostics);
                debug_assert!(!self.cursor.is_eos(), "Bug: opening paren needs respective closing paren");
                skipped_tree = true;
            }
            _ => {
                message
                    .at(current.span)
                    .push(self.diagnostics);
                skipped_tree = false;
            }
        }

        if skipped_tree {
            // TODO: after we skipped over all of the token-tree maybe we're just fine
            let current = self.cursor.lookahead();
            for test in slice {
                if test.matches(current) {
                    // only one has to match
                    self.cursor.advance();
                    return Ok(());
                }
            }
        }

        if did_expect(Token![;]) && !matches!(self.cursor.current().kind, TokenKind::Punctuator(Punctuator::RParen | Punctuator::RCurly | Punctuator::RBracket)) {
            if !self.cursor.is_eos() {
                self.cursor.advance();
            }
            return Ok(());
        }

        if did_expect(Punctuator::RParen) {
            self.cursor.skip_while(|token| !matches!(token.kind, TokenKind::Punctuator(Punctuator::RParen)));
            debug_assert!(!self.cursor.is_eos(), "Bug: opening paren needs respective closing paren");
        }

        if did_expect(Punctuator::RBracket) {
            self.cursor.skip_while(|token| !matches!(token.kind, TokenKind::Punctuator(Punctuator::RBracket)));
            debug_assert!(!self.cursor.is_eos(), "Bug: opening paren needs respective closing paren");
        }

        if did_expect(Punctuator::RCurly) {
            self.cursor.skip_while(|token| !matches!(token.kind, TokenKind::Punctuator(Punctuator::RCurly)));
            debug_assert!(!self.cursor.is_eos(), "Bug: opening paren needs respective closing paren");
        }

        if !self.cursor.is_eos()
            && (!matches!(self.cursor.current().kind, TokenKind::Punctuator(Punctuator::RParen | Punctuator::RCurly | Punctuator::RBracket)) || skipped_tree) {
            self.cursor.advance();
        }

        Err(span)
    }

    fn expect_one(&mut self, one: impl Tokenish) -> PRes<()> {
        self.expect_either(&[one])
    }

    fn expect_any<P: Parsable + 'static>(&mut self) -> PRes<P> {
        let current = self.cursor.current();
        if let Some(p) = self.match_on::<P>() {
            return Ok(p);
        }

        let span = self.cursor.span();
        let message = format!("expected {}, found {}", P::CLASSNAME.expect("can't be used with expect_any()"), self.cursor.current());
        let message = Message::error(message);

        let p = std::any::TypeId::of::<P>();
        let ident = std::any::TypeId::of::<ast::Ident>();

        if let TokenKind::Keyword(..) = current.kind && p == ident {
            if let Some(p) = P::from_error(span) {
                message.at(span).push(self.diagnostics);
                return Ok(p);
            }
        }

        let skipped_tree;
        match current.kind {
            TokenKind::Punctuator(Punctuator::LParen) => {
                self.cursor.skip_while(|token| !matches!(token.kind, TokenKind::Punctuator(Punctuator::RParen)));
                let end = self.cursor.span();
                message
                    .at(Span::interpolate(current.span, end))
                    .push(self.diagnostics);
                debug_assert!(!self.cursor.is_eos(), "Bug: opening paren needs respective closing paren");
                skipped_tree = true;
            }
            TokenKind::Punctuator(Punctuator::LBracket) => {
                self.cursor.skip_while(|token| !matches!(token.kind, TokenKind::Punctuator(Punctuator::RBracket)));
                let end = self.cursor.span();
                message
                    .at(Span::interpolate(current.span, end))
                    .push(self.diagnostics);
                debug_assert!(!self.cursor.is_eos(), "Bug: opening paren needs respective closing paren");
                skipped_tree = true;
            }
            TokenKind::Punctuator(Punctuator::LCurly) => {
                self.cursor.skip_while(|token| !matches!(token.kind, TokenKind::Punctuator(Punctuator::RCurly)));
                let end = self.cursor.span();
                message
                    .at(Span::interpolate(current.span, end))
                    .push(self.diagnostics);
                debug_assert!(!self.cursor.is_eos(), "Bug: opening paren needs respective closing paren");
                skipped_tree = true;
            }
            _ => {
                message
                    .at(span)
                    .push(self.diagnostics);
                skipped_tree = false;
            }
        }

        if !self.cursor.is_eos()
            && (!matches!(self.cursor.current().kind, TokenKind::Punctuator(Punctuator::RParen | Punctuator::RCurly | Punctuator::RBracket)) || skipped_tree) {
            self.cursor.advance();
        }

        Err(span)
    }

    fn unexpected(&mut self, message: &str) -> PRes<!> {
        let current = self.cursor.current();
        let span = self.cursor.span();
        let message = format!("expected {}, found {}", message, self.cursor.current());
        let message = Message::error(message);

        let skipped_tree;
        match current.kind {
            TokenKind::Punctuator(Punctuator::LParen) => {
                self.cursor.skip_while(|token| !matches!(token.kind, TokenKind::Punctuator(Punctuator::RParen)));
                let end = self.cursor.span();
                message
                    .at(Span::interpolate(current.span, end))
                    .push(self.diagnostics);
                debug_assert!(!self.cursor.is_eos(), "Bug: opening paren needs respective closing paren");
                skipped_tree = true;
            }
            TokenKind::Punctuator(Punctuator::LBracket) => {
                self.cursor.skip_while(|token| !matches!(token.kind, TokenKind::Punctuator(Punctuator::RBracket)));
                let end = self.cursor.span();
                message
                    .at(Span::interpolate(current.span, end))
                    .push(self.diagnostics);
                debug_assert!(!self.cursor.is_eos(), "Bug: opening paren needs respective closing paren");
                skipped_tree = true;
            }
            TokenKind::Punctuator(Punctuator::LCurly) => {
                self.cursor.skip_while(|token| !matches!(token.kind, TokenKind::Punctuator(Punctuator::RCurly)));
                let end = self.cursor.span();
                message
                    .at(Span::interpolate(current.span, end))
                    .push(self.diagnostics);
                debug_assert!(!self.cursor.is_eos(), "Bug: opening paren needs respective closing paren");
                skipped_tree = true;
            }
            _ => {
                message
                    .at(span)
                    .push(self.diagnostics);
                skipped_tree = false;
            }
        }

        if !self.cursor.is_eos()
            && (!matches!(self.cursor.current().kind, TokenKind::Punctuator(Punctuator::RParen | Punctuator::RCurly | Punctuator::RBracket)) || skipped_tree) {
            self.cursor.advance();
        }

        Err(span)
    }

    fn enter_speculative_block<R, F: FnOnce(&mut Self) -> R> (
        &mut self, do_work: F) -> (R, TokenCursor<'src>) {
        let cursor = self.cursor.fork();
        let result = do_work(self);
        let cursor = self.cursor.sync(cursor);
        (result, cursor.unwrap())
    }

    fn maybe_parse_path(&mut self, mode: PathMode) -> ParseTry<'src, ast::Path<'ast>> {
        let cursor = self.cursor.fork();
        let mut prev_cursor = std::mem::replace(&mut self.cursor, cursor);
        if self.match_on::<ast::Ident>().is_none() {
            let mut fake_cursor = std::mem::replace(&mut self.cursor, prev_cursor);
            fake_cursor.advance();
            return ParseTry::Never(fake_cursor);
        }

        let mut segments = vec![];
        // points at last doubtfree position (used in `Normal` mode)
        let mut sure = None;
        // points at last doubtfull position (used in `Function` mode)
        let mut doubt = Some(prev_cursor.fork());

        while let Some(ident) = self.bump_on::<ast::Ident>() {
            // test(std::i32::max < a, b >
            // test(std::i32::max[4],
            //
            let simple;
            sure = None;

            segments.push(ast::PathSegment::from_ident(ident));
            let segment = segments.last_mut().unwrap();
            if self.matches(Token![<]) {
                match self.maybe_parse_generic_args() {
                    ParseTry::Sure(args) => {
                        segment.generic_args = args;
                    }
                    ParseTry::Doubt(args, cursor) => {
                        segment.generic_args = args;
                        sure = Some(self.cursor.sync(cursor).unwrap());
                    }
                    ParseTry::Never(..) => ()
                }
                simple = false;
            } else if self.matches(Punctuator::LBracket) {
                let path = ast::Path::from_segments(self.alloc_slice(&segments));
                let span = path.span;
                let ty_expr = self.make_ty_expr(ast::TypeExprKind::Path(path), span);

                let sure_cursor = self.cursor.fork();
                let ty_expr = self.parse_array_or_slice(ty_expr)
                    .unwrap_or_else(|span| self.make_ty_expr(ast::TypeExprKind::Err, span));

                if !matches!(ty_expr.kind, ast::TypeExprKind::Slice(..)) {
                    // only slices are unmistakeably slices
                    sure = Some(sure_cursor);
                } else {
                    doubt = None;
                }

                let args = std::slice::from_ref(self.alloc(ast::GenericArgument {
                    span: ty_expr.span,
                    kind: ast::GenericArgumentKind::Ty(ty_expr),
                }));

                segments = Vec::new();
                segments.push(ast::PathSegment::from_generic_args(None, args));
                simple = false;
            } else if self.matches(Token![*]) {
                let path = ast::Path::from_segments(self.alloc_slice(&segments));
                let span = path.span;
                let ty_expr = self.make_ty_expr(ast::TypeExprKind::Path(path), span);

                sure = Some(self.cursor.fork());

                let end = self.cursor.span();
                self.cursor.advance();
                let ty_expr = self.make_ty_expr(ast::TypeExprKind::Ref(ty_expr), Span::interpolate(span, end));

                let args = std::slice::from_ref(self.alloc(ast::GenericArgument {
                    span: ty_expr.span,
                    kind: ast::GenericArgumentKind::Ty(ty_expr),
                }));

                segments = Vec::new();
                segments.push(ast::PathSegment::from_generic_args(None, args));
                simple = false;
            } else {
                simple = true;
            }

            if self.bump_if(Token![::]).is_none() {
                break;
            }
            if segments.len() == 1 && simple && self.match_on::<Directive>().is_some() {
                continue;
            }
            if self.match_on::<ast::Ident>().is_none() {
                let _ = self.unexpected("<ident>");
                if mode == PathMode::Function {
                    return ParseTry::Never(self.cursor.fork());
                }
            }
            doubt = Some(self.cursor.fork());
        }

        if mode == PathMode::Function {
            let Some(doubt) = doubt else {
                Message::error("this kind of path cannot be used as function member path")
                    .at(Span::interpolate(prev_cursor.span(), self.cursor.span()))
                    .push(self.diagnostics);
                return ParseTry::Never(self.cursor.fork());
            };
            self.cursor.sync(doubt);

            if segments.len() == 1 {
                // this shoudn't really ever be looked at. It's an empty path and a cursor that
                // doesn't correspond to anything usefull. It just signifies a `None` value in this
                // very weird case
                return ParseTry::Doubt(ast::Path::empty(), prev_cursor);
            }

            segments.pop();

            let segments = self.alloc_slice(&segments);
            let path = ast::Path::from_segments(segments);
            
            return ParseTry::Sure(path);
        }

        let segments = self.alloc_slice(&segments);
        let path = ast::Path::from_segments(segments);

        let fake_cursor = std::mem::replace(&mut self.cursor, prev_cursor);

        if let Some(sure) = sure {
            self.cursor.sync(sure);
            return ParseTry::Doubt(path, fake_cursor);
        }

        self.cursor.sync(fake_cursor);
        ParseTry::Sure(path)
    }

    fn parse_path(&mut self, mode: PathMode) -> PRes<ast::Path<'ast>> {
        match self.maybe_parse_path(mode) {
            ParseTry::Sure(path) => Ok(path),
            ParseTry::Doubt(path, cursor) => {
                self.cursor.sync(cursor);
                Ok(path)
            }
            ParseTry::Never(cursor) => {
                let start = self.cursor.span();
                self.cursor.sync(cursor);
                let end = self.cursor.span();
                let span = Span::interpolate(start, end);
                Message::error("invalid path")
                    .at(span)
                    .push(self.diagnostics);
                Err(span)
            }
        }
    }

    fn maybe_parse_ty_expr(&mut self) -> ParseTry<'src, &'ast ast::TypeExpr<'ast>> {
        let sure_cursor = self.cursor.fork();
        match self.maybe_parse_path(PathMode::Normal) {
            ParseTry::Sure(path) => {
                if path.is_invisible() {
                    ParseTry::Sure(path.as_ty_expr(self))
                } else {
                    let cursor = self.cursor.sync(sure_cursor).unwrap();
                    ParseTry::Doubt(path.as_ty_expr(self), cursor)
                }
            },
            ParseTry::Doubt(path, cursor) => {
                self.cursor.sync(sure_cursor);
                ParseTry::Doubt(path.as_ty_expr(self), cursor)
            }
            ParseTry::Never(span) => ParseTry::Never(span)
        }
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
        self.expect_any::<ast::Ident>()?;
        match self.maybe_parse_ty_expr() {
            ParseTry::Sure(ty_expr) => Ok(ty_expr),
            ParseTry::Doubt(ty_expr, cursor) => {
                self.cursor.sync(cursor);
                Ok(ty_expr)
            }
            ParseTry::Never(cursor) => {
                let start = self.cursor.span();
                self.cursor.sync(cursor);
                let end = self.cursor.span();
                let span = Span::interpolate(start, end);
                Message::error("invalid type expr")
                    .at(span)
                    .push(self.diagnostics);
                Err(span)
            }
        }
    }

    // searches through the token stream if there is a corresponding closing delimiter `>`
    // or if any other closing delimiters intefere with the plausiblity of a generic args sequence
    fn check_if_angle_tree(&mut self) -> Option<(bool, TokenCursor<'src>)> {
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
    }

    fn maybe_parse_generic_args(&mut self) -> ParseTry<'src, &'ast [ast::GenericArgument<'ast>]> { 
        let cursor = match self.check_if_angle_tree() {
            Some((true, cursor)) => cursor,
            Some((_, cursor)) => return ParseTry::Never(cursor),
            None => return ParseTry::Never(self.cursor.fork()) // None = cursor at EOS
        };

        let prev_cursor = std::mem::replace(&mut self.cursor, cursor);
        self.cursor.advance();

        let mut args = vec![];

        let mut mismatch = false;
        let mut sure = false;
        while !self.matches(Token![>]) {
            let span;
            let arg = if self.matches(Punctuator::LCurly) {
                self.cursor.advance();

                let expr = self.parse_expr(Restrictions::empty())
                    .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));

                if self.bump_if(Punctuator::RCurly).is_none() {
                    mismatch = true;
                    break;
                }
                sure = true;

                span = expr.span;
                ast::GenericArgumentKind::Expr(self.make_nested_const(expr))
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
                    ParseTry::Never(..) => {
                        mismatch = true;
                        break;
                    }
                };

                span = ty_expr.span;
                ast::GenericArgumentKind::Ty(ty_expr)
            };
            let arg = ast::GenericArgument {
                kind: arg,
                span,
            };
            args.push(arg);
            
            if self.bump_if(Token![,]).is_none() && !self.matches(Token![>]) {
                mismatch = true;
                break;
            }
        }

        let mut fake_cursor = std::mem::replace(&mut self.cursor, prev_cursor);
        if mismatch {
            fake_cursor.advance(); // advance over `>`
            return ParseTry::Never(fake_cursor);
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

        self.fail_parse_tree(Delimiter::Curly, |this| {
            while !this.matches(Punctuator::RCurly) {
                let mut ident = None;
                if let Some(ident_) = this.match_on::<ast::Ident>() {
                    if let TokenKind::Punctuator(Token![=]) = this.cursor.lookahead().kind {
                        this.cursor.advance();
                        this.cursor.advance();
                        ident = Some(ident_);
                    }
                }
                let expr = this.parse_expr(Restrictions::empty())
                    .unwrap_or_else(|span| this.make_expr(ast::ExprKind::Err, span));

                let initializer = if let Some(ident) = ident {
                    ast::TypeInitKind::Field(ident, expr)
                } else {
                    ast::TypeInitKind::Direct(expr)
                };

                initializers.push(initializer);


                this.expect_either(&[Token![,], Punctuator::RCurly])?;

                this.bump_if(Token![,]);    
            }

            Ok(())
        })?;
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
        }

        let path = match self.maybe_parse_path(PathMode::Normal) {
            ParseTry::Sure(path) => Some(path),
            ParseTry::Doubt(path, cursor) => {
                let invisible = path.is_invisible();
                if (!restrictions.contains(Restrictions::NO_CURLY_BLOCKS) && matches!(cursor.current().kind, TokenKind::Punctuator(Punctuator::LCurly)))
                    || (matches!(cursor.current().kind, TokenKind::Punctuator(Punctuator::LParen)) && !invisible)
                    || (matches!(cursor.current().kind, TokenKind::Punctuator(Token![,])) && !invisible) {
                    // complex path are allowed when there is a `LCurly`, `LParen` or `,`
                    self.cursor.sync(cursor);
                    Some(path)
                } else {
                    Some(path.simple(self))
                }
            }
            ParseTry::Never(..) => None
        };

        if let Some(path) = path {
            if !restrictions.contains(Restrictions::NO_CURLY_BLOCKS) && self.matches(Punctuator::LCurly) {
                // maybe this could be a discrete type init like: 
                // `Simple { a }`, `Wrapper<int> { inner: 42 }` or `int[_] { 1, 2, 3 }`
                let ty = path.as_ty_expr(self);
                return self.parse_type_init_body(ty);
            }
            return Ok(self.make_expr(ast::ExprKind::Path(path), token.span));
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

    fn parse_call_expr(&mut self, expr: &'ast ast::Expr<'ast>) -> PRes<&'ast ast::Expr<'ast>> {
        self.cursor.advance();

        let mut args = vec![];
        self.fail_parse_tree(Delimiter::Paren, |this| {
            while !this.matches(Punctuator::RParen) {
                let mut keyword = None;
                if let Some(ident) = this.match_on::<ast::Ident>() {
                    if let TokenKind::Punctuator(Token![:]) = this.cursor.lookahead().kind {
                        this.cursor.advance();
                        this.cursor.advance();
                        keyword = Some(ident);
                    }
                }

                let expr = this.parse_expr(Restrictions::empty())
                    .unwrap_or_else(|span| this.make_expr(ast::ExprKind::Err, span));

                let argument = if let Some(keyword) = keyword {
                    ast::FunctionArgument::Keyword(keyword, expr)
                } else {
                    ast::FunctionArgument::Direct(expr)
                };

                args.push(argument);
                this.expect_either(&[Token![,], Punctuator::RParen])?;
                this.bump_if(Token![,]);
            }
            Ok(())
        })?;
        let end = self.cursor.span();
        self.cursor.advance();

        let args = self.alloc_slice(&args);

        Ok(self.make_expr(
            ast::ExprKind::FunctionCall(ast::FunctionCall {
                callable: expr,
                args,
            }),
            Span::interpolate(expr.span, end),
        ))
    }

    fn parse_subscript_expr(
        &mut self, expr: &'ast ast::Expr<'ast>) -> PRes<&'ast ast::Expr<'ast>> {
        self.cursor.advance();

        let mut args = vec![];
        self.fail_parse_tree(Delimiter::Bracket, |this| {
            while !this.matches(Punctuator::RBracket) {
                args.push(
                    this.parse_expr(Restrictions::empty())
                    .unwrap_or_else(|span| this.make_expr(ast::ExprKind::Err, span))
                );

                this.expect_either(&[Token![,], Punctuator::RBracket])?;
                this.bump_if(Token![,]);
            }
            Ok(())
        })?;
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
            if op == lexer::UnaryOp::Minus {
                if let Some(lit) = self.match_on::<NumberLiteral>() {
                    let expr = self.make_expr(
                        ast::ExprKind::Literal(lit.neg().as_literal()),
                        Span::interpolate(start, self.cursor.span())
                    );
                    self.cursor.advance();
                    return Ok(expr);
                }
            }
            let expr = self.parse_expr_prefix(restrictions).unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span));
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
                    self.parse_call_expr(expr).unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span)),
                Punctuator::LBracket =>
                    self.parse_subscript_expr(expr).unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span)),
                Token![.] =>
                    self.parse_field_expr(expr).unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span)),
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

        if let Some(item) = self.parse_item_or_directive(ItemContext::Block) {
            return Ok(self.make_stmt(ast::StmtKind::Item(item), item.span));
        }

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
            ParseTry::Never(..) => ()
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
        while !self.matches(Punctuator::RCurly) && !self.cursor.is_eos() {
            stmts.push(
                self.parse_stmt(|this| expr_block && this.matches(Punctuator::RCurly))
                    .unwrap_or_else(|span| self.make_stmt(ast::StmtKind::Err, span))
            );
        }
        let end = self.cursor.span();
        debug_assert!(!self.cursor.is_eos(), "Bug: opening paren needs respective closing paren");
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
            let mut items = vec![];

            if this.bump_if(Punctuator::LCurly).is_some() {
                let _ = this.fail_parse_tree(Delimiter::Curly, |this| {
                    while !this.matches(Punctuator::RCurly) {
                        if let Some(item) = this.parse_item_or_directive(ItemContext::Struct) {
                            items.push(item);
                            continue;
                        }
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
                    Ok(())
                });
            }
            let end = this.cursor.span();
            this.cursor.advance();

            let fields = this.alloc_slice(&fields);
            let items = this.alloc_slice(&items);

            let span = Span::interpolate(start, end);
            Ok((
                ast::ItemKind::Struct(ast::Struct {
                    ident,
                    generics,
                    fields,
                    items
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
        let res = self.with_owner(|this| {
            let start = this.cursor.span();
            this.cursor.advance();

            let ident = this.expect_any::<ast::Ident>()?;
            this.cursor.advance();

            let representation;
            if this.bump_if(Token![:]).is_some() {
                let ty = this.parse_ty_expr()
                    .unwrap_or_else(|span| this.make_ty_expr(ast::TypeExprKind::Err, span));
                representation = Some(ty);
            } else {
                representation = None;
            }

            this.expect_one(Punctuator::LCurly)?;
            this.cursor.advance();

            let mut variants = vec![];

            let _ = this.fail_parse_tree(Delimiter::Curly, |this| {
                while !this.matches(Punctuator::RCurly) {
                    let start = this.cursor.span();

                    let name = this.expect_any::<ast::Ident>()?;
                    this.cursor.advance();

                    let discriminant;
                    let end;
                    this.expect_either(&[Token![;], Token![::=]])?;
                    if this.bump_if(Token![::=]).is_some() || this.bump_if(Token![=]).is_some() {
                        let expr = this.parse_expr(Restrictions::empty())
                            .unwrap_or_else(|span| this.make_expr(ast::ExprKind::Err, span));
                        let expr = this.make_nested_const(expr);
                        end = expr.span;
                        discriminant = Some(expr);
                        this.expect_one(Token![;])?;
                    } else {
                        end = name.span;
                        discriminant = None;
                    }

                    let span = Span::interpolate(start, end);
                    this.cursor.advance();
                    variants.push(this.make_variant_def(name, discriminant, span));
                }
                Ok(())
            });
            let end = this.cursor.span();
            this.cursor.advance();

            let variants = this.alloc_slice(&variants);

            let span = Span::interpolate(start, end);
            Ok((
                ast::ItemKind::Enum(ast::Enum {
                    ident,
                    representation,
                    variants,
                }),
                span
            ))
        });
        let ((kind, span), owner_id, children) = res?;
        let item = self.make_item(kind, span);
        self.owners[owner_id].initialize(item.into_node(), children);
        Ok(item)
    }

    fn parse_generic_params(&mut self) -> PRes<&'ast [&'ast ast::GenericParam<'ast>]> {
        let mut generics = vec![];

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

    fn parse_function_item(&mut self, ty: &'ast ast::TypeExpr<'ast>, ident: ast::Ident, member_path: Option<ast::Path<'ast>>) -> PRes<(ast::ItemKind<'ast>, Span)> {
        // OwnedPtr<int*>[] get_int(...
        //                         ^
        //          OR
        // OwnedPtr<T*>[] get_obj<T>(...
        //                       ^
        let start = self.cursor.span();
 
        let generics = if self.bump_if(Token![<]).is_some() {
            self.parse_generic_params()?
        } else {
            &[]
        };
        self.cursor.advance();

        let mut params = vec![];
        let _res = self.fail_parse_tree(Delimiter::Paren, |this| {
            while !this.matches(Punctuator::RParen) {
                let start = this.cursor.span();
                let ty = this.parse_ty_expr()
                    .unwrap_or_else(|span| this.make_ty_expr(ast::TypeExprKind::Err, span));
                let ident = this.expect_any::<ast::Ident>()?;
                this.cursor.advance();

                params.push(this.make_param(ident, ty, Span::interpolate(start, ident.span)));

                this.expect_either(&[Token![,], Punctuator::RParen])?;
                this.bump_if(Token![,]);
            }
            Ok(())
        });
        let end = self.cursor.span();
        self.cursor.advance();

        let params = self.alloc_slice(&params);

        let mut header = ast::FnHeader::default();
        while let Some(directive) = self.match_on::<Directive>() {
            let span = self.cursor.span();
            self.cursor.advance();
            
            match directive {
                Token![#c_call] => {
                    let mut c_call = ast::CCall {
                        link_name: None,
                        span
                    };
                    if self.matches(Punctuator::LParen) {
                        let trees = self.parse_directive_trees()?;
                        let span = trees.span();
                        let literal: String = trees.get(sym::link_name, true, self)?;
                        c_call.span = Span::interpolate(c_call.span, span);
                        c_call.link_name = Some((span, Symbol::intern(&literal)));
                    }
                    header.c_call = Some(c_call);
                }
                Token![#link] => {
                    header.link = Some(span);
                }
                Token![#compiler_intrinsic] => {
                    header.compiler_intrinsic = Some(span);
                }
                _ => {
                    let mut end = start;
                    if self.matches(Punctuator::LParen) {
                        self.cursor.skip_while(|token| !matches!(token.kind, TokenKind::Punctuator(Punctuator::RParen)));
                        end = self.cursor.span();
                        self.cursor.advance();
                    }
                    Message::error(format!("directive `#{}` cannot be applied to function", directive))
                        .at(Span::interpolate(start, end))
                        .push(self.diagnostics);
                }
            }
        }

        let sig = ast::FnSignature {
            header,
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
                member_path: member_path.map(|xx| self.alloc(xx))
            }),
            span 
        ))
    }

    fn parse_global_item(&mut self, ty: Option<&'ast ast::TypeExpr<'ast>>, ident: ast::Ident) -> PRes<(ast::ItemKind<'ast>, Span)> {
        let mut init = None;
        let mut constant = false;
        if self.bump_if(Token![::=]).is_some() {
            constant = true;
            init = Some(
                self.parse_expr(Restrictions::empty())
                    .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span))
            );
        } else if self.bump_if(Token![=]).is_some() {
            init = Some(
                self.parse_expr(Restrictions::empty())
                    .unwrap_or_else(|span| self.make_expr(ast::ExprKind::Err, span))
            );
        }
        self.expect_one(Token![;])?;
        let end = self.cursor.span();
        self.cursor.advance();

        let span = ty.map_or(ident.span, |ty| ty.span);

        Ok((
            ast::ItemKind::GlobalVar(ast::GlobalVar {
                ident,
                ty,
                init,
                constant
            }),
            Span::interpolate(span, end)
        ))
    }

    fn parse_global_alias(&mut self, context: ItemContext) -> PRes<(ast::ItemKind<'ast>, Span)> {
        let ident = self.bump_on::<ast::Ident>().unwrap();

        let generics = if self.bump_if(Token![<]).is_some() {
            self.parse_generic_params()?
        } else {
            &[]
        };

        self.bump_if(Token![::]).unwrap();
 
        let directive = self.match_on::<Directive>().unwrap();
        match directive {
            Token![#include] if context != ItemContext::Struct => {
                if !generics.is_empty() {
                    let span = Span::interpolate(
                        generics.first().unwrap().span,
                        generics.last().unwrap().span
                    );
                    Message::error("alias for `#include` must not have generic parameters")
                        .at(span)
                        .push(self.diagnostics);
                }

                let (span, kind) = match self.parse_import_directive() {
                    Ok(import) => (import.span, ast::AliasKind::Import(import)),
                    Err(span) => (span, ast::AliasKind::Err)
                };
                let span = Span::interpolate(ident.span, span); 
                return Ok(
                    (
                        ast::ItemKind::Alias(ast::Alias {
                            ident, kind,
                            generics: &[]
                        }),
                        span
                    )
                );
            }
            Token![#type] => {
                let start = self.cursor.span();
                self.cursor.advance();
                let ty = self.parse_ty_expr()
                    .unwrap_or_else(|span| self.make_ty_expr(ast::TypeExprKind::Err, span));
                self.expect_one(Token![;])?;
                self.cursor.advance();

                let span = Span::interpolate(start, ty.span);
                Ok(
                    (
                        ast::ItemKind::Alias(ast::Alias {
                            ident,
                            kind: ast::AliasKind::Type(ty),
                            generics
                        }),
                        span
                    )
                )
            }
            _ => {
                let span = self.cursor.span();
                self.cursor.advance();
                let mut msg = Message::error(format!("directive `#{directive}` is not valid here"))
                    .at(span);
                msg = match context {
                    ItemContext::Struct => msg.note("valid directives are `#type`"),
                    ItemContext::Module | ItemContext::Block => msg.note("valid directives are `#include` and `#type`"),
                };
                msg.push(self.diagnostics);
                // TODO: compliation is erroneous now
                return Err(span);
            }
        }
    }

    fn understand_item(&mut self, context: ItemContext) -> ItemHeader<'ast> {
        let cursor = self.cursor.fork();
        let prev_cursor = std::mem::replace(&mut self.cursor, cursor);

        if self.matches(Token![static]) {
            self.cursor.advance();
            let ty = match self.parse_ty_expr() {
                Ok(ty) => ty,
                Err(span) => return ItemHeader::Err(span),
            };
            let ident = match self.expect_any::<ast::Ident>() {
                Ok(ident) => ident,
                Err(span) => return ItemHeader::Err(span),
            };
            self.cursor.advance();
            let item = match self.parse_global_item(Some(ty), ident) {
                Ok(item) => item,
                Err(span) => return ItemHeader::Err(span),
            };
            return ItemHeader::Done(item.0, item.1);
        }

        enum Kind {
            None,
            TypelessConst,
            Alias,
        }
        let mut detected_kind = Kind::None;
        {
            let cursor = self.cursor.fork();
            let actual_cursor = std::mem::replace(&mut self.cursor, cursor);
            if self.bump_on::<ast::Ident>().is_none() {
                return ItemHeader::None;
            }

            let mut is_generic = false;
            if self.matches(Token![<]) {
                match self.check_if_angle_tree() {
                    Some((true, small_cursor)) => 
                        self.cursor.advance_to(small_cursor.end()),
                    _ => {
                        self.cursor = actual_cursor;
                        return ItemHeader::None;
                    }
                };
                self.cursor.advance();
                is_generic = true;
            }

            match self.cursor.current().kind {
                TokenKind::Punctuator(Token![::=]) if !is_generic =>
                    detected_kind = Kind::TypelessConst,
                TokenKind::Punctuator(Token![::]) if matches!(self.cursor.lookahead().kind, TokenKind::Directive(_)) =>
                    detected_kind = Kind::Alias,
                _ => {}
            }
            self.cursor = actual_cursor;
        }
        let mut ty = None;
        if let Kind::None = detected_kind {
            ty = match self.maybe_parse_ty_expr() {
                ParseTry::Sure(ty) => Some(ty),
                ParseTry::Doubt(ty, cursor) => {
                    if !matches!(cursor.current().kind, TokenKind::Symbol(..)) {
                        return ItemHeader::None;
                    }
                    self.cursor.sync(cursor);
                    Some(ty)
                }
                ParseTry::Never(..) =>
                    return ItemHeader::None,
            };
        }

        let static_var = ty.is_some()
            && matches!(self.cursor.current().kind, TokenKind::Symbol(..))
            && (matches!(self.cursor.lookahead().kind, TokenKind::Punctuator(Token![=])) || matches!(self.cursor.lookahead().kind, TokenKind::Punctuator(Token![;])));

        if static_var && context != ItemContext::Module {
            self.cursor = prev_cursor;
            return ItemHeader::None;
        }

        if let Some(ty) = ty {
            return ItemHeader::Ty(ty);
        }

        match detected_kind {
            Kind::TypelessConst => {
                let ident = self.bump_on::<ast::Ident>().unwrap();
                match self.parse_global_item(ty, ident) {
                    Ok(item) => ItemHeader::Done(item.0, item.1),
                    Err(span) => ItemHeader::Err(span),
                }
            }
            Kind::Alias => {
                match self.parse_global_alias(context) {
                    Ok(item) => ItemHeader::Done(item.0, item.1),
                    Err(span) => ItemHeader::Err(span),
                }
            }
            Kind::None => unreachable!(),
        }
    }

    fn parse_item(&mut self, context: ItemContext) -> PRes<Option<&'ast ast::Item<'ast>>> {
        if let Some(keyword) = self.match_on::<Keyword>() {
            match keyword {
                Token![struct] =>
                    return self.parse_struct_item().map(Some),
                Token![enum] =>
                    return self.parse_enum_item().map(Some),
                _ => ()
            }
        }

        let res = self.with_owner(|this| {
            let ty = match this.understand_item(context) {
                ItemHeader::Ty(ty) => ty,
                ItemHeader::Done(item, span) =>
                    return Ok((item, span)),
                ItemHeader::Err(span) =>
                    return Err(span),
                ItemHeader::None => {
                    if context != ItemContext::Module {
                        return Err(Span::NULL);
                    }
                    this.parse_ty_expr()?
                },
            };

            if context == ItemContext::Struct {
                // In Struct contexts no functions can be parsed
                let name = this.expect_any::<ast::Ident>()?;
                this.cursor.advance();
                return this.parse_global_item(Some(ty), name);
            }

            match this.maybe_parse_path(PathMode::Function) {
                ParseTry::Sure(path) => {
                    let name = this.bump_on::<ast::Ident>().unwrap();

                    this.expect_either(&[Punctuator::LParen, Token![<]])?;

                    this.parse_function_item(ty, name, Some(path))
                }
                ParseTry::Doubt(..) => {
                    let name = this.expect_any::<ast::Ident>()?;
                    this.cursor.advance();

                    if this.matches(Punctuator::LParen) || this.matches(Token![<]) {
                        this.parse_function_item(ty, name, None)
                    } else {
                        this.parse_global_item(Some(ty), name)
                    }
                }
                ParseTry::Never(cursor) => return Err(cursor.span()),
            }
        });
        if let Err(span) = res && span == Span::NULL {
            if context == ItemContext::Module {
                unreachable!()
            }
            return Ok(None);
        }

        let ((kind, span), owner_id, children) = res?;
        let item = self.make_item(kind, span);
        self.owners[owner_id].initialize(item.into_node(), children);
        Ok(Some(item))
    }

    fn parse_directive_trees(&mut self) -> PRes<DirectiveTrees> {
        let start = self.cursor.span();
        self.cursor.advance();

        let mut trees = vec![];
        self.fail_parse_tree(Delimiter::Paren, |this| {
            while !this.matches(Punctuator::RParen) {
                let span = this.cursor.span();
                let tree = if let Some(ident) = this.bump_on::<ast::Ident>() {
                    if let Some(..) = this.bump_if(Token![=]) {
                        let literal = this.expect_any::<Literal>()?;
                        let span = this.cursor.span();
                        this.cursor.advance();
                        DirectiveTree::KeyValue { key: ident, value: (literal, span) }
                    } else {
                        DirectiveTree::Ident(ident)
                    }
                } else if let Some(literal) = this.bump_on::<Literal>() {
                    DirectiveTree::Value(literal, span)
                } else {
                    this.unexpected("`<ident>`, `<literal>` or `key=<value>` pair")?
                };
                trees.push(tree);
                this.expect_either(&[Token![,], Punctuator::RParen])?;
                this.bump_if(Token![,]);
            }
            Ok(())
        })?;
        let end = self.cursor.span();
        self.cursor.advance();

        if trees.is_empty() {
            let span = Span::interpolate(start, end);
            Message::error("invalid empty directive tree")
                .at(span)
                .note("remove empty tree")
                .push(self.diagnostics);
            return Err(span);
        }

        Ok(DirectiveTrees(trees))
    }

    fn parse_import_directive(&mut self) -> PRes<&'ast ast::Import> {
        let start = self.cursor.span();
        self.cursor.advance();

        let path = self.expect_any::<String>();
        self.cursor.advance();

        self.expect_one(Token![;])?;
        let end = self.cursor.span();
        self.cursor.advance();

        let import = self.alloc(ast::Import {
            path: path?,
            span: Span::interpolate(start, end),
        });
        Ok(import)
    }

    fn parse_scope_directive(&mut self) -> PRes<ast::Scope> {
        self.cursor.advance();

        self.expect_one(Punctuator::LParen)?;

        let trees = self.parse_directive_trees()?;
        let symbol = trees.expect_either(&[sym::export, sym::module], self);
        self.expect_one(Token![;])?;
        self.cursor.advance();

        let scope = match symbol? {
            sym::export => ast::Scope::Export,
            sym::module => ast::Scope::Module,
            _ => unreachable!()
        };

        Ok(scope)
    }

    fn parse_item_or_directive(&mut self, context: ItemContext) -> Option<&'ast ast::Item<'ast>> {
        if let Some(directive) = self.match_on::<Directive>() {
            match directive {
                Token![#include] if context != ItemContext::Struct => {
                    let import = match self.parse_import_directive() {
                        Ok(import) => self.make_item(ast::ItemKind::Import(import), import.span),
                        Err(span) => self.make_item(ast::ItemKind::Err, span)
                    };
                    return Some(import);
                }
                Token![#scope] if context != ItemContext::Block =>
                    self.currrent_item_scope = self.parse_scope_directive().unwrap_or_default(),
                _ => {
                    let span = self.cursor.span();
                    self.cursor.advance();
                    let mut msg = Message::error(format!("directive `#{directive}` is not valid here"))
                        .at(span);
                    msg = match context {
                        ItemContext::Block => msg.note("valid directives are `#include`"),
                        ItemContext::Struct => msg.note("valid directives are `#scope`"),
                        ItemContext::Module => msg.note("valid directives are `#include` and `#scope`"),
                    };
                    msg.push(self.diagnostics);
                }
            }

            return None;
        }
        self.parse_item(context)
            .unwrap_or_else(|span| Some(self.make_item(ast::ItemKind::Err, span)))
    }

    fn parse_source_file(&mut self, file_span: Span) -> &'ast ast::SourceFile<'ast> {
        let res = self.with_owner(|this| {
            let mut items = vec![];

            while !this.cursor.is_eos() {
                if let Some(item) = this.parse_item_or_directive(ItemContext::Module) {
                    items.push(item);
                }
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
    let source = session.file_cacher().load_file(path)
        .expect("io error should have been handled already");

    let stream = lexer::tokenize(&source, diagnostics)?;
    if stream.tainted_with_errors() {
        ast_info.tainted_with_errors.set(Some(()));
    }
    
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
            span: source.byte_span
        });
        let node = &*node;
        owners[owner_id].initialize(ast::Node::SourceFile(node), IndexVec::new());
        node
    };

    Ok(source_file)
}

