use std::ops::Range;
use std::hash::Hash;
use lalrpop_util::{ErrorRecovery, ParseError};

use crate::diagnostics::{JoinToHumanReadable, Diagnostics};
use crate::symbol::Symbol;

pub const DUMMY_SPAN: Range<usize> = 0..0;

#[derive(Debug, Clone, Eq)]
pub struct Ident {
    pub symbol: Symbol,
    pub span: Range<usize>
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
}

#[derive(Debug)]
pub struct TopLevel {
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
    Function(Box<Function>),
    Struct(Box<Struct>),
    GlobalVar(Box<TypeExpr>, Option<Box<Expr>>, bool),
    Err
}

#[derive(Debug)]
pub struct Struct {
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
pub struct Function {
    pub body: Option<Vec<Stmt>>,
    pub generics: Vec<GenericParam>,
    pub params: Vec<Param>,
    pub returns: TypeExpr,
    pub span: Range<usize>,
    pub attributes: Vec<Attribute>
}

#[derive(Debug)]
pub struct Attribute {
    pub span: Range<usize>,
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
    Cast(Box<Expr>, Option<Box<TypeExpr>>, TypeConversion),
    FunctionCall(Box<Expr>, Vec<FunctionArgument>, Vec<GenericArgument>),
    TypeInit(Option<Box<TypeExpr>>, Vec<TypeInit>),
    Subscript(Box<Expr>, Vec<Expr>),
    Attribute(Box<Expr>, Ident),
    Constant(Constant),
    String(String),
    Name(QName),
    Tuple(Vec<Expr>),
    ShorthandEnum(Ident),
    Range(Box<Expr>, Box<Expr>, bool),
    Deref(Box<Expr>),
    Err
}

#[derive(Debug)]
pub enum TypeConversion {
    Cast, Pun
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
    BooleanNot, BitwiseInvert, Pos, Neg, Ref
}

#[derive(Debug)]
pub enum FunctionArgument {
    Direct(Box<Expr>),
    OutVar(Pattern),
    Keyword(Ident, Box<Expr>)
}

#[derive(Debug)]
pub enum TypeInit {
    Field(Ident, Box<Expr>),
    Direct(Box<Expr>),
}

#[derive(Debug)]
pub enum Constant {
    Null,
    Integer(u64),
    Boolean(bool),
    Char(char)
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
    Array(Box<TypeExpr>, Option<Box<Expr>>),
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

