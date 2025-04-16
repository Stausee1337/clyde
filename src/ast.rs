use std::cell::OnceCell;
use std::hash::Hash;

use index_vec::IndexVec;

use crate::lexer::{self, Span};
use crate::symbol::Symbol;

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub enum Node<'ast> {
    Expr(&'ast Expr<'ast>),
    NestedConst(&'ast NestedConst<'ast>),
    Item(&'ast Item<'ast>),
    SourceFile(&'ast SourceFile<'ast>),
    Stmt(&'ast Stmt<'ast>),
    TypeExpr(&'ast TypeExpr<'ast>),
    FieldDef(&'ast FieldDef<'ast>),
    Variant(&'ast VariantDef<'ast>),
    Param(&'ast Param<'ast>),
    GenericParam(&'ast GenericParam<'ast>),
}

impl<'ast> Node<'ast> {
    // TODO: body for FieldDef/Struct
    pub fn body(self) -> Option<Body<'ast>> {
        match self {
            Self::Item(item) => match &item.kind {
                ItemKind::Function(func @ Function { body: Some(body), .. }) =>
                    return Some(Body {
                        params: &func.sig.params,
                        body
                    }),
                ItemKind::GlobalVar(GlobalVar { init: Some(body), .. }) => {
                    return Some(Body { params: &[], body })
                },
                _ => (),
            },
            Self::NestedConst(expr) => return Some(Body {
                params: &[], body: &expr.expr
            }),
            _ => ()
        }
        None
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
    pub params: &'ast [&'ast Param<'ast>],
    pub body: &'ast Expr<'ast>
}

pub struct Owner<'ast> {
    pub id: OwnerId,
    data: OnceCell<OwnerData<'ast>>,
}

pub struct OwnerData<'ast> {
    pub node: Node<'ast>,
    pub children: IndexVec<LocalId, Node<'ast>>
}

impl<'ast> Owner<'ast> {
    pub fn new(id: OwnerId) -> Self {
        Self {
            id,
            data: OnceCell::new()
        }
    }

    pub fn initialize(&self, node: Node<'ast>, children: IndexVec<LocalId, Node<'ast>>) {
        let data = OwnerData { node, children };
        if let Err(..) = self.data.set(data) {
            panic!("owner already initialized");
        }
    }
}

impl<'ast> std::ops::Deref for Owner<'ast> {
    type Target = OwnerData<'ast>;

    fn deref(&self) -> &Self::Target {
        self.data.get().expect("fully initialized owner")
    }
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
    Static,
    Function,
    Struct,
    Enum,
    Const,
    NestedConst,
    Field,
    Variant,
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
    pub items: &'ast [&'ast Item<'ast>],
    pub span: Span,
    pub node_id: NodeId,
}

impl<'ast> IntoNode<'ast> for SourceFile<'ast>  {
    fn into_node(&'ast self) -> Node<'ast> {
        Node::SourceFile(self)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Item<'ast> {
    pub kind: ItemKind<'ast>,
    pub span: Span,
    pub node_id: NodeId
}

impl<'ast> IntoNode<'ast> for Item<'ast>  {
    fn into_node(&'ast self) -> Node<'ast> {
        Node::Item(self)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ItemKind<'ast> {
    Function(Function<'ast>),
    Struct(Struct<'ast>),
    Enum(Enum<'ast>),
    GlobalVar(GlobalVar<'ast>),
    Err
}

#[derive(Debug, Clone, Copy)]
pub struct GlobalVar<'ast> {
    pub ident: Ident,
    pub ty: &'ast TypeExpr<'ast>,
    pub init: Option<&'ast Expr<'ast>>,
    pub constant: bool
}

#[derive(Debug, Clone, Copy)]
pub struct Struct<'ast> {
    pub ident: Ident,
    pub generics: &'ast [&'ast GenericParam<'ast>],
    pub fields: &'ast [&'ast FieldDef<'ast>],
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

impl<'ast> IntoNode<'ast> for FieldDef<'ast>  {
    fn into_node(&'ast self) -> Node<'ast> {
        Node::FieldDef(self)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Enum<'ast> {
    pub ident: Ident,
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

impl<'ast> IntoNode<'ast> for VariantDef<'ast>  {
    fn into_node(&'ast self) -> Node<'ast> {
        Node::Variant(self)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Function<'ast> {
    pub ident: Ident,
    pub sig: FnSignature<'ast>,
    pub body: Option<&'ast Expr<'ast>>,
    pub span: Span,
    pub attributes: &'ast [Attribute]
}

#[derive(Debug, Clone, Copy)]
pub struct FnSignature<'ast> {
    pub returns: &'ast TypeExpr<'ast>,
    pub params: &'ast [&'ast Param<'ast>],
    pub generics: &'ast [&'ast GenericParam<'ast>],
}

#[derive(Debug)]
pub struct Attribute {
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Param<'ast> {
    pub ident: Ident,
    pub ty: &'ast TypeExpr<'ast>,
    pub span: Span,
    pub node_id: NodeId
}

#[derive(Debug)]
pub struct Block<'ast> {
    pub stmts: &'ast [&'ast Stmt<'ast>],
    pub span: Span,
}

#[derive(Debug)]
pub struct Stmt<'ast> {
    pub kind: StmtKind<'ast>,
    pub span: Span,
    pub node_id: NodeId
}

impl<'ast> IntoNode<'ast> for Stmt<'ast>  {
    fn into_node(&'ast self) -> Node<'ast> {
        Node::Stmt(self)
    }
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
    Yeet(Yeet<'ast>),
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
pub struct Yeet<'ast> {
    pub expr: Option<&'ast Expr<'ast>>,
    pub origin: YeetOrigin
}

#[derive(Debug, Clone, Copy)]
pub enum YeetOrigin {
    Explicit, Implicit
}

#[derive(Debug)]
pub struct Expr<'ast> {
    pub kind: ExprKind<'ast>,
    pub span: Span,
    pub node_id: NodeId
}

impl<'ast> IntoNode<'ast> for Expr<'ast>  {
    fn into_node(&'ast self) -> Node<'ast> {
        Node::Expr(self)
    }
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
    Literal(Literal),
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
    pub ty: &'ast TypeExpr<'ast>,
    pub initializers: &'ast [TypeInitKind<'ast>]
}

#[derive(Debug, Clone)]
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
    Discrete(&'ast NestedConst<'ast>)
}

#[derive(Debug, Clone)]
pub enum Literal {
    Null,
    Integer(i64),
    Floating(f64),
    Boolean(bool),
    Char(char),
    String(String)
}

#[derive(Debug, Clone)]
pub struct NestedConst<'ast> {
    pub expr: &'ast Expr<'ast>,
    pub span: Span,
    pub node_id: NodeId,
    pub def_id: OnceCell<DefId>,
}

impl<'ast> IntoNode<'ast> for NestedConst<'ast>  {
    fn into_node(&'ast self) -> Node<'ast> {
        Node::NestedConst(self)
    }
}

#[derive(Debug)]
pub struct TypeExpr<'ast> {
    pub kind: TypeExprKind<'ast>,
    pub span: Span,
    pub node_id: NodeId
}

impl<'ast> IntoNode<'ast> for TypeExpr<'ast>  {
    fn into_node(&'ast self) -> Node<'ast> {
        Node::TypeExpr(self)
    }
}

#[derive(Debug)]
pub enum TypeExprKind<'ast> {
    Ref(&'ast TypeExpr<'ast>),
    Name(Name),
    Generic(Generic<'ast>),
    Array(Array<'ast>),
    Slice(&'ast TypeExpr<'ast>),
    Err,
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

#[derive(Debug, Clone)]
pub enum GenericArgument<'ast> {
    Ty(&'ast TypeExpr<'ast>),
    Expr(&'ast NestedConst<'ast>),
    Literal(Literal),
}

#[derive(Debug)]
pub struct GenericParam<'ast> {
    pub kind: GenericParamKind<'ast>,
    pub span: Span,
    pub node_id: NodeId
}

impl<'ast> IntoNode<'ast> for GenericParam<'ast>  {
    fn into_node(&'ast self) -> Node<'ast> {
        Node::GenericParam(self)
    }
}

#[derive(Debug)]
pub enum GenericParamKind<'ast> {
    Type(Ident),
    Const(Ident, &'ast TypeExpr<'ast>),
    Err
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId {
    pub owner: OwnerId,
    pub local: LocalId
}

pub trait IntoNode<'ast> {
    fn into_node(&'ast self) -> Node<'ast>;
}

index_vec::define_index_type! {
    pub struct OwnerId = u32;
    IMPL_RAW_CONVERSIONS = true;
}

index_vec::define_index_type! {
    pub struct LocalId = u32;
    IMPL_RAW_CONVERSIONS = true;
}

