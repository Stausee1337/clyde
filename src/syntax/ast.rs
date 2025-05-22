use std::cell::{Cell, OnceCell, RefCell};
use std::hash::Hash;

use index_vec::IndexVec;

use super::{lexer::{self, Span}, symbol::Symbol};

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

    pub fn node_id(self) -> NodeId {
        match self {
            Node::Expr(expr) => expr.node_id,
            Node::NestedConst(nconst) => nconst.node_id,
            Node::Item(item) => item.node_id,
            Node::SourceFile(file) => file.node_id,
            Node::Stmt(stmt) => stmt.node_id,
            Node::TypeExpr(expr) => expr.node_id,
            Node::FieldDef(field) => field.node_id,
            Node::Variant(variant) => variant.node_id,
            Node::Param(param) => param.node_id,
            Node::GenericParam(param) => param.node_id,
        }
    }

    pub fn generics(self) -> &'ast [&'ast GenericParam<'ast>] {
        let Node::Item(item) = self else {
            panic!("node.generics() called for {self:?}");
        };

        match item.kind {
            ItemKind::Function(func) => func.sig.generics,
            ItemKind::Struct(strct) => strct.generics,
            ItemKind::Alias(alias) => alias.generics,
            _ => unreachable!("item {item:?} does not have generics")
        }

    }

    /*pub fn span(self) -> Span {
        match self {
            Node::Expr(expr) => expr.span,
            Node::NestedConst(nconst) => nconst.span,
            Node::Item(item) => item.span,
            Node::SourceFile(file) => file.span,
            Node::Stmt(stmt) => stmt.span,
            Node::TypeExpr(expr) => expr.span,
            Node::FieldDef(field) => field.span,
            Node::Variant(variant) => variant.span,
            Node::Param(param) => param.span,
            Node::GenericParam(param) => param.span,
        }
    }*/
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

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, bytemuck::Pod, bytemuck::Zeroable)]
#[repr(transparent)]
pub struct DefId(pub u32);

impl index_vec::Idx for DefId {
    fn index(self) -> usize {
        self.0 as usize
    }

    fn from_usize(idx: usize) -> Self {
        Self(idx as u32)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum DefinitionKind {
    Static,
    Function,
    Struct,
    Enum,
    Const,
    NestedConst,
    Field,
    TypeAlias,
    Variant,
    ParamTy,
    ParamConst,
}

#[derive(Debug, Clone, Copy)]
pub enum Resolution {
    Def(DefId, DefinitionKind),
    Local(NodeId),
    Primitive(Symbol),
    Err
}

#[derive(Debug, Clone)]
pub struct Path<'ast> {
    pub segments: &'ast [PathSegment<'ast>],
    pub span: Span,
}

impl<'ast> Path<'ast> {
    // From an API point of view this could be considered unsafe
    pub fn empty() -> Self {
        Self {
            segments: &[],
            span: Span::NULL,
        }
    }

    pub fn from_segments(segments: &'ast [PathSegment<'ast>]) -> Self {
        let start = segments.first().unwrap().span; 
        let end = segments.last().unwrap().span; 
        Self {
            segments,
            span: Span::interpolate(start, end),
        }
    }

    pub fn resolution(&self) -> Option<&Resolution> {
        self.segments.last().unwrap().resolution.get()
    }
}

#[derive(Debug, Clone)]
pub struct PathSegment<'ast> {
    pub ident: Option<Ident>,
    pub generic_args: &'ast [GenericArgument<'ast>],
    resolution: OnceCell<Resolution>,
    pub span: Span,
}

impl<'ast> PathSegment<'ast> {
    pub fn from_ident(ident: Ident) -> Self {
        Self {
            ident: Some(ident),
            generic_args: &[],
            resolution: OnceCell::new(),
            span: ident.span
        }
    }

    pub fn from_generic_args(ident: Option<Ident>, generic_args: &'ast [GenericArgument<'ast>]) -> Self {
        let start = generic_args.first().map(|a| a.span).unwrap_or_else(|| ident.unwrap().span);
        let end = generic_args.last().map(|a| a.span).unwrap_or_else(|| ident.unwrap().span);
        Self {
            ident,
            generic_args,
            resolution: OnceCell::new(),
            span: Span::interpolate(start, end)
        }
    }

    pub fn resolution(&self) -> Option<&Resolution> {
        self.resolution.get()
    }

    pub fn resolve(&self, resolution: Resolution) {
        if let Err(_) = self.resolution.set(resolution) {
            unreachable!("tried to resolve resolved path segment")
        };
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

#[derive(Debug, Clone)]
pub struct Item<'ast> {
    pub kind: ItemKind<'ast>,
    pub scope: Scope,
    pub span: Span,
    pub node_id: NodeId,
    pub def_id: OnceCell<DefId>,
}

impl<'ast> IntoNode<'ast> for Item<'ast>  {
    fn into_node(&'ast self) -> Node<'ast> {
        Node::Item(self)
    }
}

impl<'ast> Item<'ast> {
    pub fn ident(&self) -> Ident {
        match self.kind {
            ItemKind::Enum(enm) => enm.ident,
            ItemKind::Struct(strct) => strct.ident,
            ItemKind::Function(func) => func.ident,
            ItemKind::GlobalVar(var) => var.ident, 
            ItemKind::Alias(alias) => alias.ident, 
            ItemKind::Import(..) | ItemKind::Err => unreachable!()
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ItemKind<'ast> {
    Function(Function<'ast>),
    Struct(Struct<'ast>),
    Enum(Enum<'ast>),
    GlobalVar(GlobalVar<'ast>),
    Import(&'ast Import),
    Alias(Alias<'ast>),
    Err
}

#[derive(Default, Debug, Clone, Copy)]
pub enum Scope {
    #[default]
    Export,
    Module
}

#[derive(Debug, Clone, Copy)]
pub struct Alias<'ast> {
    pub ident: Ident,
    pub kind: AliasKind<'ast>,
    pub generics: &'ast [&'ast GenericParam<'ast>],
}

#[derive(Debug, Clone, Copy)]
pub enum AliasKind<'ast> {
    Type(&'ast TypeExpr<'ast>),
    Import(&'ast Import),
    Err
}

#[derive(Debug, Clone)]
pub struct Import {
    pub path: String,
    pub span: Span,
}

#[derive(Debug, Clone, Copy)]
pub struct GlobalVar<'ast> {
    pub ident: Ident,
    pub ty: Option<&'ast TypeExpr<'ast>>,
    pub init: Option<&'ast Expr<'ast>>,
    pub constant: bool
}

#[derive(Debug, Clone, Copy)]
pub struct Struct<'ast> {
    pub ident: Ident,
    pub generics: &'ast [&'ast GenericParam<'ast>],
    pub fields: &'ast [&'ast FieldDef<'ast>],
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
    pub representation: Option<&'ast TypeExpr<'ast>>,
    pub variants: &'ast [&'ast VariantDef<'ast>],
}

#[derive(Debug, Clone)]
pub struct VariantDef<'ast> {
    pub name: Ident,
    pub discriminant: Option<&'ast NestedConst<'ast>>,
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
    pub member_path: Option<&'ast Path<'ast>>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy)]
pub struct CCall {
    pub link_name: Option<(Span, Symbol)>,
    pub span: Span 
}

#[derive(Debug, Default, Clone, Copy)]
pub struct FnHeader {
    pub c_call: Option<CCall>,
    pub link: Option<Span>,
    pub compiler_intrinsic: Option<Span>
}

#[derive(Debug, Clone, Copy)]
pub struct FnSignature<'ast> {
    pub header: FnHeader,
    pub returns: &'ast TypeExpr<'ast>,
    pub params: &'ast [&'ast Param<'ast>],
    pub generics: &'ast [&'ast GenericParam<'ast>],
}

#[derive(Debug, Clone)]
pub struct Param<'ast> {
    pub ident: Ident,
    pub ty: &'ast TypeExpr<'ast>,
    pub span: Span,
    pub node_id: NodeId
}

impl<'ast> IntoNode<'ast> for Param<'ast> {
    fn into_node(&'ast self) -> Node<'ast> {
        Node::Param(self)
    }
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
    Item(&'ast Item<'ast>),
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
pub struct OutsideScope;

#[derive(Debug)]
pub struct ControlFlow {
    pub kind: ControlFlowKind,
    pub destination: OnceCell<Result<NodeId, OutsideScope>>,
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
    pub origin: YeetOrigin,
    pub owner: OnceCell<Result<NodeId, OutsideScope>>
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
    Path(Path<'ast>),
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
    Integer(Integer),
    Floating(f64),
    Boolean(bool),
    Char(char),
    String(String)
}

impl std::fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Null => f.write_str("null"),
            Literal::Integer(i) => write!(f, "{i}"),
            Literal::Floating(fp) => write!(f, "{fp}"),
            Literal::Boolean(b) => write!(f, "{b}"),
            Literal::Char(c) => write!(f, "{c}"),
            Literal::String(s) => write!(f, "{s:?}"),
        }
    }
}

impl TryFrom<Literal> for u64 {
    type Error = &'static str;

    fn try_from(literal: Literal) -> Result<Self, Self::Error> {
        if let Literal::Integer(int) = literal && !int.signed {
            return Ok(int.value);
        }
        Err("unsigned integer")
    }
}

impl TryFrom<Literal> for i128 {
    type Error = &'static str;

    fn try_from(literal: Literal) -> Result<Self, Self::Error> {
        if let Literal::Integer(int) = literal {
            return Ok((int.value as i128) * if int.signed { -1 } else { 1 });
        }
        Err("integer")
    }
}

macro_rules! impl_literal_conversion {
    ($variant:ident -> $res:ty) => {
        impl TryFrom<Literal> for $res {
            type Error = &'static str;

            fn try_from(literal: Literal) -> Result<$res, Self::Error> {
                if let Literal::$variant(res) = literal {
                    return Ok(res);
                }
                Err(stringify!($res))
            }
        }
    };
}

impl_literal_conversion!(Floating -> f64);
impl_literal_conversion!(Boolean -> bool);
impl_literal_conversion!(Char -> char);
impl_literal_conversion!(String -> String);


#[derive(Debug, Clone, Copy)]
pub struct Integer {
    pub value: u64,
    pub signed: bool
}

impl std::fmt::Display for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.signed {
            f.write_str("-").unwrap();
        }
        write!(f, "{}", self.value)
    }
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
    Path(Path<'ast>),
    Array(Array<'ast>),
    Slice(&'ast TypeExpr<'ast>),
    Err,
}

#[derive(Debug)]
pub struct Array<'ast> {
    pub ty: &'ast TypeExpr<'ast>,
    pub cap: ArrayCapacity<'ast>
}

#[derive(Debug, Clone)]
pub struct GenericArgument<'ast> {
    pub kind: GenericArgumentKind<'ast>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum GenericArgumentKind<'ast> {
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId {
    pub owner: OwnerId,
    pub local: LocalId
}

pub struct AstInfo<'ast> {
    pub arena: bumpalo::Bump,
    pub global_owners: RefCell<IndexVec<OwnerId, Owner<'ast>>>,
    pub tainted_with_errors: Cell<Option<()>>
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

