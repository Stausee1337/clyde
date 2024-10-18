use std::ops::Range;
use std::hash::Hash;
use lalrpop_util::{ErrorRecovery, ParseError};

use crate::diagnostics::{JoinToHumanReadable, DiagnosticsCtxt};
use crate::symbol::Symbol;

pub const DUMMY_SPAN: Range<usize> = 0..0;

#[derive(Debug, Clone, Copy)]
pub enum Node<'ast> {
    Expr(&'ast Expr),
    NestedConst(&'ast NestedConst),
    Item(&'ast Item),
    SourceFile(&'ast SourceFile),
    Stmt(&'ast Stmt),
    TypeExpr(&'ast TypeExpr),
    Field(&'ast FieldDef),
    Variant(&'ast VariantDef),
}

impl<'ast> Node<'ast> {
    // TODO: body for FieldDef 
    pub fn body(self) -> Option<Body<'ast>> {
        match self {
            Self::Item(item) => match &item.kind {
                ItemKind::Function(func) => {
                    if let Some(ref body) = func.body {
                        Some(Body {
                            params: &func.sig.params,
                            body
                        })
                    } else {
                        None
                    }
                }
                ItemKind::GlobalVar(_, body, _) => {
                    if let Some(ref body) = body {
                        Some(Body { params: &[], body })
                    } else {
                        None
                    }
                },
                _ => None,
            },
            Self::NestedConst(expr) => Some(Body {
                params: &[], body: &expr.expr
            }),
            _ => None
        }
    }

    pub fn signature(self) -> Option<&'ast FnSignature> {
        match self {
            Node::Item(Item { kind: ItemKind::Function(func), .. }) =>
                Some(&func.sig),
            _ => None
        }
    }
}

#[derive(Debug)]
pub struct Body<'ast> {
    pub params: &'ast [Param],
    pub body: &'ast Expr
}

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

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct DefId(pub u32);

impl index_vec::Idx for DefId {
    fn index(self) -> usize {
        self.0 as usize
    }

    fn from_usize(idx: usize) -> Self {
        Self(idx as u32)
    }
}


pub const DEF_ID_UNDEF: DefId = DefId(u32::MAX);

#[derive(Debug, Clone, Copy)]
pub enum DefinitionKind {
    Global,
    Function,
    Struct,
    Enum,
    Const,
}

#[derive(Debug, Clone, Copy)]
pub enum Resolution {
    Def(DefId, DefinitionKind),
    Local(NodeId),
    Primitive,
    Err
}

#[derive(Debug, Clone)]
pub enum QName {
    Unresolved(Ident),
    Resolved {
        ident: Ident,
        res_kind: Resolution
    },
}

impl QName {
    pub fn ident(&self) -> &Ident {
        match self {
            QName::Unresolved(ident) => ident,
            QName::Resolved { ident, .. } => ident,
        }
    }
}

#[derive(Debug)]
pub struct SourceFile {
    pub items: Vec<Item>,
    pub span: Range<usize>,
    pub node_id: NodeId,
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
    Struct(Struct),
    Enum(Enum),
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
    pub default_init: Option<Box<Expr>>,
    pub span: Range<usize>,
    pub node_id: NodeId,
    pub def_id: DefId
}

#[derive(Debug)]
pub struct Enum {
    pub extends: Option<Box<TypeExpr>>,
    pub variants: Vec<VariantDef>,
    pub attributes: Vec<Attribute>
}

#[derive(Debug)]
pub struct VariantDef {
    pub name: Ident,
    pub sset: Option<Box<Expr>>,
    pub span: Range<usize>,
    pub node_id: NodeId,
    pub def_id: DefId
}

#[derive(Debug)]
pub struct Function {
    pub sig: FnSignature,
    pub body: Option<Box<Expr>>,
    pub span: Range<usize>,
    pub attributes: Vec<Attribute>
}

#[derive(Debug)]
pub struct FnSignature {
    pub returns: TypeExpr,
    pub params: Vec<Param>,
    pub generics: Vec<GenericParam>,
}

#[derive(Debug)]
pub struct Attribute {
    pub span: Range<usize>,
}

#[derive(Debug)]
pub struct Param {
    pub ident: Ident,
    pub ty: TypeExpr,
    pub span: Range<usize>,
    pub node_id: NodeId
}

#[derive(Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Range<usize>,
    pub node_id: NodeId,
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
    Block(Block),
    Assign(Box<Expr>, Box<Expr>),
    If(Box<Expr>, Block, Option<Box<Stmt>>),
    While(Box<Expr>, Block),
    For(Ident, Box<Expr>, Block),
    Local(Ident, Option<Box<TypeExpr>>, Option<Box<Expr>>),
    Return(Option<Box<Expr>>),
    ControlFlow(ControlFlow),
    Err
}

#[derive(Debug)]
pub struct OutsideLoopScope;

#[derive(Debug)]
pub struct ControlFlow {
    pub kind: ControlFlowKind,
    pub destination: Result<NodeId, OutsideLoopScope>,
    pub span: Range<usize>,
}

impl ControlFlow {
    pub fn new(kind: ControlFlowKind, span: Range<usize>,) -> ControlFlow { 
        ControlFlow {
            kind, span,
            destination: Err(OutsideLoopScope) 
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlFlowKind {
    Break, Continue
}

impl std::fmt::Display for ControlFlowKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ControlFlowKind::Break => f.write_str("break"),
            ControlFlowKind::Continue => f.write_str("continue"),
        }
    }
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
    Field(Box<Expr>, FieldIdent),
    Constant(Constant),
    String(String),
    Name(QName),
    Tuple(Vec<Expr>),
    EnumVariant(Box<TypeExpr>, Ident),
    ShorthandEnum(Ident),
    Range(Box<Expr>, Box<Expr>, bool),
    Deref(Box<Expr>),
    Block(Block),
    Err
}

#[derive(Debug)]
pub enum FieldIdent {
    Named(Ident),
    Tuple {
        value: u64,
        span: Range<usize>
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TypeConversion {
    Cast, Transmute
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


impl std::fmt::Display for BinaryOperator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use BinaryOperator::{
            Plus, Minus, Mul, Div, Mod,
            ShiftLeft, ShiftRight,
            BitwiseAnd, BitwiseOr, BitwiseXor,
            Equal, NotEqual, GreaterThan, GreaterEqual, LessThan, LessEqual,
            BooleanAnd, BooleanOr
        };
        f.write_str(match self {
            Plus => "+", Minus => "-", Mul => "*", Div => "/", Mod => "%",
            ShiftLeft => "<<", ShiftRight => ">>",
            BitwiseAnd => "&", BitwiseOr => "|", BitwiseXor => "^",
            Equal => "==", NotEqual => "!=", GreaterThan => ">", GreaterEqual => ">=", LessThan => "<", LessEqual => "<=",
            BooleanAnd => "&&", BooleanOr => "||"
        })
    }
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOperator {
    BooleanNot, BitwiseInvert, Neg, Ref
}

#[derive(Debug)]
pub enum FunctionArgument {
    Direct(Box<Expr>),
    Keyword(Ident, Box<Expr>)
}

#[derive(Debug)]
pub enum TypeInit {
    Field(Ident, Box<Expr>),
    Direct(Box<Expr>),
}


#[derive(Debug)]
pub enum ArrayCapacity {
    Infer,
    Dynamic,
    Discrete(NestedConst)
}

#[derive(Debug)]
pub enum Constant {
    Null,
    Integer(u64),
    Boolean(bool),
    Char(char)
}

#[derive(Debug)]
pub struct NestedConst {
    pub expr: Box<Expr>,
    pub span: Range<usize>,
    pub node_id: NodeId,
    pub def_id: DefId,
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
    Array(Box<TypeExpr>, ArrayCapacity),
    Slice(Box<TypeExpr>),
    Tuple(Vec<TypeExpr>),
}

#[derive(Debug)]
pub enum GenericArgument {
    Ty(TypeExpr),
    Expr(NestedConst),
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

pub fn handle_stmt_error<'sess>(
    recovery: ErrorRecovery<usize, crate::lexer::TokenKind, UserError>,
    diagnostics: &'sess DiagnosticsCtxt
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

