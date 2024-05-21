use std::ops::Range;
use std::hash::Hash;
use lalrpop_util::{ErrorRecovery, ParseError};

use crate::diagnostics::{JoinToHumanReadable, Diagnostics};
use crate::lexer;
use crate::symbol::Symbol;

pub const DUMMY_SPAN: Range<usize> = 0..0;

#[derive(Debug, Clone, Eq)]
pub struct Ident {
    pub symbol: Symbol,
    pub span: Range<usize>
}

impl Ident {
    pub fn from_str(s: &str) -> Self {
        Self {
            symbol: Symbol::intern(s),
            span: DUMMY_SPAN
        }
    }

    pub fn empty() -> Self {
        Self::from_str("")
    }
}

impl PartialEq for Ident {
    fn eq(&self, other: &Self) -> bool {
        self.symbol.eq(&other.symbol)
    }
}

impl Hash for Ident {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.symbol.hash(state);
    }
}

#[derive(Debug, Clone, Copy)]
pub enum DeclarationKind {
    Local, Global, Function, Type, Primitive, Err
}

#[derive(Debug, Clone)]
pub enum QName {
    Unresolved(Ident),
    Resolved {
        ident: Ident,
        node_id: NodeId,
        res_kind: DeclarationKind 
    },
}

#[derive(Debug, Clone)]
pub enum QPath {
    Unresolved(Path, Ident),
    Resolved,
}

impl<'a> From<&'a mut QPath> for (&'a Path, Ident) {
    fn from(value: &'a mut QPath) -> Self {
        match value {
            QPath::Unresolved(path, ident) => (path, ident.clone()),
            QPath::Resolved => todo!("Multiple namespaces")
        }
    }
}

#[derive(Debug, Clone)]
pub struct Path {
    pub segments: Vec<Ident>,
    pub span: Range<usize>,
}

#[derive(Debug)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Range<usize>,
    pub node_id: NodeId
}

#[derive(Debug)]
pub enum PatternKind {
    Ident(Ident),
    Tuple(Vec<Pattern>),
    Literal(Box<Expr>),
    Path(QPath)
}

#[derive(Debug)]
pub struct Import {
    pub kind: ImportKind,
    pub span: Range<usize>,
    pub node_id: NodeId
}

#[derive(Debug)]
pub enum ImportKind {
    Use(Path),
    With(Path, Option<Ident>)
}

#[derive(Debug)]
pub struct TopLevel {
    pub imports: Vec<Import>,
    pub unit_decl: Option<Path>,
    pub items: Vec<Item>,
    pub span: Range<usize>,
    pub node_id: NodeId,
    pub diagnostics: Diagnostics
}

#[derive(Debug)]
pub struct Item {
    pub kind: ItemKind,
    pub span: Range<usize>,
    pub ident: Ident,
    pub node_id: NodeId
}

#[derive(Debug)]
pub enum ItemKind {
    Proc(Box<Proc>),
    Record(Box<Record>),
    Constant(Box<TypeExpr>, Box<Expr>),
    StaticVar(Option<Box<TypeExpr>>, Option<Box<Expr>>),
    Err
}

#[derive(Debug)]
pub struct Record {
    pub generics: Vec<GenericParam>,
    pub fields: Vec<FieldDef>,
    pub attributes: Vec<Attribute>
}

#[derive(Debug)]
pub struct FieldDef {
    pub name: Ident,
    pub ty: TypeExpr,
    pub span: Range<usize>,
    pub node_id: NodeId
}

#[derive(Debug)]
pub struct Proc {
    pub body: Option<Vec<Stmt>>,
    pub generics: Vec<GenericParam>,
    pub params: Vec<Param>,
    pub returns: Option<TypeExpr>,
    pub span: Range<usize>,
    pub attributes: Vec<Attribute>
}

#[derive(Debug)]
pub struct Attribute {
    pub span: Range<usize>,
    pub token_stream: Vec<TokenTree>,
}

#[derive(Debug)]
pub struct Param {
    pub pat: Pattern,
    pub ty: TypeExpr,
    pub span: Range<usize>,
    pub node_id: NodeId
}

#[derive(Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Range<usize>,
    pub node_id: NodeId
}

#[derive(Debug)]
pub enum StmtKind {
    Expr(Box<Expr>),
    Assign(Box<Expr>, Box<Expr>),
    If(Box<Expr>, Vec<Stmt>, Option<Box<Stmt>>),
    Block(Vec<Stmt>),
    While(Box<Expr>, Vec<Stmt>),
    For(Pattern, Box<Expr>, Vec<Stmt>),
    Local(Pattern, Option<Box<TypeExpr>>, Option<Box<Expr>>),
    Return(Option<Box<Expr>>),
    ControlFlow(ControlFlow),
    Item(Box<Item>),
    Err
}

#[derive(Debug)]
pub enum ControlFlow {
    Break, Continue
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Range<usize>,
    pub node_id: NodeId
}

#[derive(Debug)]
pub enum ExprKind {
    BinOp(Box<BinOp>),
    UnaryOp(Box<Expr>, UnaryOperator),
    Cast(Cast),
    FunctionCall(Box<Expr>, Vec<FunctionArgument>),
    RecordInit(QName, Vec<FieldInit>),
    Subscript(Box<Expr>, Vec<Expr>),
    Attribute(Box<Expr>, Ident),
    Constant(Constant),
    String(String),
    Name(QName),
    Path(QPath),
    ArraySize(Box<Expr>, Box<Expr>),
    ArrayItems(Vec<Expr>),
    Tuple(Vec<Expr>),
    ShorthandEnum(Ident),
    Closure(Closure),
    Range(Box<Expr>, Box<Expr>, bool),
    PatternMatch(Box<Expr>, MatchKind, Box<Pattern>),
    Err
}

#[derive(Debug)]
pub enum MatchKind {
    Is, IsNot
}

#[derive(Debug)]
pub struct Cast {
    pub expr: Box<Expr>,
    pub ty: Box<TypeExpr>, 
    pub is_unsafe: bool
}

#[derive(Debug)]
pub struct Closure {
    pub params: Vec<Pattern>,
    pub body: Vec<Stmt>
}

#[derive(Debug)]
pub struct BinOp {
    pub lhs: Expr,
    pub rhs: Expr,
    pub operator: BinaryOperator
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryOperator {
    Plus, Minus, Mul, Div, Mod,
    ShiftLeft, ShiftRight,
    BitwiseAnd, BitwiseOr, BitwiseXor,
    Equal, NotEqual, GreaterThan, GreaterEqual, LessThan, LessEqual,
    BooleanAnd, BooleanOr
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOperator {
    BooleanNot, BitwiseInvert, Pos, Neg, Ref, Deref
}

#[derive(Debug)]
pub enum FunctionArgument {
    Direct(Box<Expr>),
    OutVar(Pattern),
    Keyword(Ident, Box<Expr>)
}

#[derive(Debug)]
pub struct FieldInit {
    pub field: Ident,
    pub init: Box<Expr>
}

#[derive(Debug)]
pub enum Constant {
    None,
    Integer(u64),
    Boolean(bool)
}

#[derive(Debug)]
pub struct TypeExpr {
    pub kind: TypeExprKind,
    pub span: Range<usize>,
    pub node_id: NodeId
}

#[derive(Debug)]
pub enum TypeExprKind {
    Ref(Box<TypeExpr>),
    Name(QName),
    Generic(QName, Vec<GenericArgument>),
    Function {
        param_tys: Vec<TypeExpr>,
        return_ty: Option<Box<TypeExpr>>,
        is_closure: bool 
    },
}

#[derive(Debug)]
pub enum GenericArgument {
    Ty(TypeExpr),
    Expr(Expr),
    Constant(Constant),
}

#[derive(Debug)]
pub struct GenericParam {
    pub ident: Ident,
    pub kind: GenericParamKind,
    pub span: Range<usize>,
    pub node_id: NodeId
}

#[derive(Debug)]
pub enum GenericParamKind {
    Type(Vec<TypeExpr>),
    Const(TypeExpr)
}

#[derive(Debug)]
pub enum TokenTree {
    Flat(lexer::TokenKind),
    Nested(NestingKind, Vec<TokenTree>),
}

#[derive(Debug)]
pub enum NestingKind {
    Paren, Bracket, Curly
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId(pub u32);
pub const NODE_ID_UNDEF: NodeId = NodeId(u32::MAX);

#[derive(Debug)]
pub struct UserError {
    pub message: &'static str,
    pub span: Range<usize>,
}

impl std::fmt::Debug for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if *self != NODE_ID_UNDEF {
            write!(f, "NodeId({})", self.0)?;
        } else {
            write!(f, "NodeId(UNDEF)").unwrap();
        }
        Ok(())
    }
}

pub fn binop_exprs2expr(mut exprs: Vec<Expr>, kind: BinaryOperator, eloc: usize) -> Expr {
    let mut left = exprs.remove(0);
    for right in exprs {
        let sloc = left.span.start;
        let binop = BinOp {
            lhs: left,
            rhs: right,
            operator: kind 
        };
        left = Expr {
            kind: ExprKind::BinOp(Box::new(binop)),
            span: (sloc..eloc),
            node_id: NODE_ID_UNDEF
        };
    }
    left
}

pub fn handle_stmt_error<'diag>(
    recovery: ErrorRecovery<usize, crate::lexer::TokenKind, UserError>,
    diagnostics: Diagnostics
) -> Result<Stmt, ParseError<usize, crate::lexer::TokenKind, UserError>> {
    match recovery.error {
        lalrpop_util::ParseError::UnrecognizedToken { expected, token } if expected.contains(&"\";\"".to_string())
            => diagnostics.error("forgot semicolon `;`").with_span(token.0-2..token.0-1),
        lalrpop_util::ParseError::UnrecognizedToken { expected, token } => {
            let expected = expected
                .iter()
                .map(|s| s.replace("\x22", "`"))
                .collect::<Vec<_>>()
                .join_to_human_readable();
            diagnostics.error(
                format!("expected one of {}, found `{}`",
                    expected,
                    token.1
                )
            ).with_span(token.0..token.2)
        }
        lalrpop_util::ParseError::UnrecognizedEof { location, .. } 
            => diagnostics.error("unexpected EOF").with_pos(location),
        _ => return Err(recovery.error),
    };
    Ok(Stmt {
        kind: StmtKind::Err,
        span: DUMMY_SPAN,
        node_id: NODE_ID_UNDEF
    })
}

