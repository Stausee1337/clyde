use std::cell::OnceCell;
use std::hash::Hash;

use crate::lexer::{self, Span};
use crate::symbol::Symbol;

// pub const DUMMY_SPAN: Range<usize> = 0..0;

#[derive(Debug, Clone, Copy)]
pub enum Node<'ast> {
    Expr(&'ast Expr<'ast>),
    NestedConst(&'ast NestedConst<'ast>),
    Item(&'ast Item<'ast>),
    SourceFile(&'ast SourceFile<'ast>),
    Stmt(&'ast Stmt<'ast>),
    TypeExpr(&'ast TypeExpr<'ast>),
    Field(&'ast FieldDef<'ast>),
    Variant(&'ast VariantDef<'ast>),
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
                ItemKind::GlobalVar(global) => {
                    if let Some(ref body) = global.init {
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

    pub fn signature(self) -> Option<&'ast FnSignature<'ast>> {
        match self {
            Node::Item(Item { kind: ItemKind::Function(func), .. }) =>
                Some(&func.sig),
            _ => None
        }
    }
}

#[derive(Debug)]
pub struct Body<'ast> {
    pub params: &'ast [Param<'ast>],
    pub body: &'ast Expr<'ast>
}

#[derive(Debug, Clone, Copy, Eq)]
pub struct Ident {
    pub symbol: Symbol,
    pub span: Span
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
pub struct Name {
    pub ident: Ident,
    resolution: OnceCell<Resolution>
}

impl Name {
    pub fn from_ident(ident: Ident) -> Self {
        Self {
            ident,
            resolution: OnceCell::new()
        }
    }

    pub fn resolution(&self) -> Option<&Resolution> {
        self.resolution.get() 
    }

    pub fn resolve(&self, resolution: Resolution) {
        self.resolution.set(resolution)
            .expect("resolve() on resolved name")
    }
}

#[derive(Debug)]
pub struct SourceFile<'ast> {
    pub items: &'ast [Item<'ast>],
    pub span: Span,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub struct Item<'ast> {
    pub kind: ItemKind<'ast>,
    pub span: Span,
    pub ident: Ident,
    pub node_id: NodeId
}

#[derive(Debug)]
pub enum ItemKind<'ast> {
    Function(Function<'ast>),
    Struct(Struct<'ast>),
    Enum(Enum<'ast>),
    GlobalVar(GlobalVar<'ast>),
    Err
}

#[derive(Debug)]
pub struct GlobalVar<'ast> {
    pub ty: &'ast TypeExpr<'ast>,
    pub init: Option<&'ast Expr<'ast>>,
    pub constant: bool
}

#[derive(Debug)]
pub struct Struct<'ast> {
    pub generics: &'ast [&'ast GenericParam<'ast>],
    pub fields: &'ast [FieldDef<'ast>],
    pub attributes: &'ast [Attribute]
}

#[derive(Debug)]
pub struct FieldDef<'ast> {
    pub name: Ident,
    pub ty: &'ast TypeExpr<'ast>,
    pub default_init: Option<&'ast Expr<'ast>>,
    pub span: Span,
    pub node_id: NodeId,
    pub def_id: OnceCell<DefId>
}

#[derive(Debug)]
pub struct Enum<'ast> {
    pub extends: Option<&'ast TypeExpr<'ast>>,
    pub variants: &'ast [VariantDef<'ast>],
    pub attributes: &'ast [Attribute]
}

#[derive(Debug)]
pub struct VariantDef<'ast> {
    pub name: Ident,
    pub sset: Option<&'ast Expr<'ast>>,
    pub span: Span,
    pub node_id: NodeId,
    pub def_id: OnceCell<DefId>
}

#[derive(Debug)]
pub struct Function<'ast> {
    pub sig: FnSignature<'ast>,
    pub body: Option<&'ast Expr<'ast>>,
    pub span: Span,
    pub attributes: &'ast [Attribute]
}

#[derive(Debug)]
pub struct FnSignature<'ast> {
    pub returns: &'ast TypeExpr<'ast>,
    pub params: &'ast [Param<'ast>],
    pub generics: &'ast [&'ast GenericParam<'ast>],
}

#[derive(Debug)]
pub struct Attribute {
    pub span: Span,
}

#[derive(Debug)]
pub struct Param<'ast> {
    pub ident: Ident,
    pub ty: TypeExpr<'ast>,
    pub span: Span,
    pub node_id: NodeId
}

#[derive(Debug)]
pub struct Block<'ast> {
    pub stmts: &'ast [&'ast Stmt<'ast>],
    pub span: Span,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub struct Stmt<'ast> {
    pub kind: StmtKind<'ast>,
    pub span: Span,
    pub node_id: NodeId
}

#[derive(Debug)]
pub enum StmtKind<'ast> {
    Expr(&'ast Expr<'ast>),
    Block(Block<'ast>),
    If(If<'ast>),
    While(While<'ast>),
    For(For<'ast>),
    Local(Local<'ast>),
    Return(Option<&'ast Expr<'ast>>),
    ControlFlow(ControlFlow),
    Err
}

#[derive(Debug)]
pub struct Local<'ast> {
    pub ident: Ident,
    pub ty: Option<&'ast TypeExpr<'ast>>,
    pub init: Option<&'ast Expr<'ast>>
}

#[derive(Debug)]
pub struct For<'ast> {
    pub bound_var: Ident,
    pub iterator: &'ast Expr<'ast>,
    pub body: Block<'ast>
}

#[derive(Debug)]
pub struct While<'ast> {
    pub condition: &'ast Expr<'ast>,
    pub body: Block<'ast>,
}

#[derive(Debug)]
pub struct If<'ast> {
    pub condition: &'ast Expr<'ast>,
    pub body: Block<'ast>,
    pub else_branch: Option<&'ast Stmt<'ast>>
}

#[derive(Debug)]
pub struct OutsideLoopScope;

#[derive(Debug)]
pub struct ControlFlow {
    pub kind: ControlFlowKind,
    pub destination: OnceCell<Result<NodeId, OutsideLoopScope>>,
    pub span: Span,
}

impl ControlFlow {
    pub fn new(kind: ControlFlowKind, span: Span,) -> ControlFlow { 
        ControlFlow {
            kind, span,
            destination: OnceCell::new()
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
pub struct Expr<'ast> {
    pub kind: ExprKind<'ast>,
    pub span: Span,
    pub node_id: NodeId
}

#[derive(Debug)]
pub enum ExprKind<'ast> {
    BinaryOp(BinaryOp<'ast>),
    AssignOp(AssignOp<'ast>),
    UnaryOp(UnaryOp<'ast>),
    Cast(Cast<'ast>),
    FunctionCall(FunctionCall<'ast>),
    TypeInit(TypeInit<'ast>),
    Subscript(Subscript<'ast>),
    Field(Field<'ast>),
    Constant(Constant),
    String(String),
    Tuple(&'ast [&'ast Expr<'ast>]),
    // FIXME: EnumVariant (and ShorthandEnum) need to be handled using `Path`
    // (which will replace Name) since those will be resolvable using the OnceCell<Resolution>
    // field.
    // NOTE: Path is going to be a slice of `Ident`s representing a coloned path
    // (e.g. sys::io::file or FileMode::Read for enum variants)
    /*EnumVariant(EnumVariant<'ast>),*/
    Name(Name),
    /*ShorthandEnum(Ident),*/
    Range(Range<'ast>),
    Deref(&'ast Expr<'ast>),
    Block(Block<'ast>),
    Err
}

#[derive(Debug)]
pub struct AssignOp<'ast> {
    pub lhs: &'ast Expr<'ast>,
    pub rhs: &'ast Expr<'ast>,
    pub operator: lexer::AssignmentOp
}

#[derive(Debug)]
pub struct Range<'ast> {
    pub start: &'ast Expr<'ast>,
    pub end: &'ast Expr<'ast>,
    pub inclusive: bool
}

#[derive(Debug)]
pub struct Field<'ast> {
    pub expr: &'ast Expr<'ast>,
    pub field: FieldIdent
}

#[derive(Debug)]
pub struct Subscript<'ast> {
    pub expr: &'ast Expr<'ast>,
    pub args: &'ast [&'ast Expr<'ast>]

}

#[derive(Debug)]
pub struct TypeInit<'ast> {
    pub ty: Option<&'ast TypeExpr<'ast>>,
    pub initializers: &'ast [TypeInitKind<'ast>]
}

#[derive(Debug)]
pub enum TypeInitKind<'ast> {
    Direct(&'ast Expr<'ast>),
    Field(Ident, &'ast Expr<'ast>)
}

#[derive(Debug)]
pub struct FunctionCall<'ast> {
    pub callable: &'ast Expr<'ast>,
    pub args: &'ast [FunctionArgument<'ast>],
    pub generic_args: &'ast [GenericArgument<'ast>]
}

#[derive(Debug)]
pub struct Cast<'ast> {
    pub expr: &'ast Expr<'ast>,
    pub ty: Option<&'ast TypeExpr<'ast>>,
    pub kind: TypeConversion
}

#[derive(Debug)]
pub enum FieldIdent {
    Named(Ident),
    Tuple {
        value: u64,
        span: Span
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TypeConversion {
    Cast, Transmute
}

#[derive(Debug)]
pub struct BinaryOp<'ast> {
    pub lhs: &'ast Expr<'ast>,
    pub rhs: &'ast Expr<'ast>,
    pub operator: lexer::BinaryOp
}

#[derive(Debug)]
pub struct UnaryOp<'ast> {
    pub expr: &'ast Expr<'ast>,
    pub operator: lexer::UnaryOp
}

#[derive(Debug, Clone, Copy)]
pub enum FunctionArgument<'ast> {
    Direct(&'ast Expr<'ast>),
    Keyword(Ident, &'ast Expr<'ast>)
}

#[derive(Debug)]
pub enum ArrayCapacity<'ast> {
    Infer,
    Dynamic,
    Discrete(NestedConst<'ast>)
}

#[derive(Debug)]
pub enum Constant {
    Null,
    Integer(u64),
    Floating(f64),
    Boolean(bool),
    Char(char)
}

#[derive(Debug)]
pub struct NestedConst<'ast> {
    pub expr: &'ast Expr<'ast>,
    pub span: Span,
    pub node_id: NodeId,
    pub def_id: OnceCell<DefId>,
}

#[derive(Debug)]
pub struct TypeExpr<'ast> {
    pub kind: TypeExprKind<'ast>,
    pub span: Span,
    pub node_id: NodeId
}

#[derive(Debug)]
pub enum TypeExprKind<'ast> {
    Ref(&'ast TypeExpr<'ast>),
    Name(Name),
    Generic(Generic<'ast>),
    Array(Array<'ast>),
    Slice(&'ast TypeExpr<'ast>),
    Tuple(&'ast  [&'ast TypeExpr<'ast>]),
}
#[derive(Debug)]
pub struct Array<'ast> {
    pub ty: &'ast TypeExpr<'ast>,
    pub cap: ArrayCapacity<'ast>
}

#[derive(Debug)]
pub struct Generic<'ast> {
    pub name: Name,
    pub args: &'ast [GenericArgument<'ast>]
}

#[derive(Debug)]
pub enum GenericArgument<'ast> {
    Ty(&'ast TypeExpr<'ast>),
    Expr(NestedConst<'ast>),
    Constant(Constant),
}

#[derive(Debug)]
pub struct GenericParam<'ast> {
    pub ident: Ident,
    pub kind: GenericParamKind<'ast>,
    pub span: Span,
    pub node_id: NodeId
}

#[derive(Debug)]
pub enum GenericParamKind<'ast> {
    Type(&'ast [&'ast TypeExpr<'ast>]),
    Const(&'ast TypeExpr<'ast>)
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId(pub u32);
pub const NODE_ID_UNDEF: NodeId = NodeId(u32::MAX);

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

