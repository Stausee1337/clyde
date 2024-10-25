use std::{mem::transmute, ops::Deref};

use num_traits::{Num, ToPrimitive};

use crate::{ast::{DefId, NodeId, self}, symbol::Symbol, context::TyCtxt, lexer::Span};
use clyde_macros::Internable;

#[derive(Debug, Hash)]
#[repr(u32)]
pub enum AdtKind {
    Enum,
    Struct,
    Union,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct FieldIdx(pub u32);

impl index_vec::Idx for FieldIdx {
    fn index(self) -> usize {
        return self.0 as usize
    }

    fn from_usize(idx: usize) -> Self {
        Self(idx as u32)
    }
}

#[derive(Debug, Hash, Internable)]
#[alias(AdtDef)]
pub struct AdtDefInner {
    pub def: DefId,
    pub name: Symbol,
    fields: index_vec::IndexVec<FieldIdx, FieldDef>,
    pub kind: AdtKind,
}

impl AdtDefInner {
    pub fn new(
        def: DefId,
        name: Symbol,
        fields: index_vec::IndexVec<FieldIdx, FieldDef>,
        kind: AdtKind
    ) -> Self {
        Self {
            def, name, fields, kind
        }
    }

    pub fn fields(&self) -> impl Iterator<Item = (FieldIdx, &FieldDef)> {
        self.fields.iter_enumerated()
    }
}

impl PartialEq for AdtDefInner {
    fn eq(&self, other: &Self) -> bool {
        self.def == other.def
    }
}

impl Eq for AdtDefInner {}

#[derive(Debug, Hash)]
pub struct FieldDef {
    pub def: DefId,
    pub symbol: Symbol
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub struct AdtDef<'tcx>(&'tcx AdtDefInner);

impl<'tcx> Deref for AdtDef<'tcx> {
    type Target = AdtDefInner;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

#[derive(Clone, Copy)]
pub struct Signature<'tcx> {
    pub returns: Ty<'tcx>,
    pub params: &'tcx [Param<'tcx>],
    pub name: Symbol,
}

#[derive(Clone, Copy)]
pub struct Param<'tcx> {
    pub name: Symbol,
    pub ty: Ty<'tcx>,
    pub node_id: NodeId
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Scalar {
    size: usize,
    data: u128
}

impl Scalar {
    pub fn from_number<N: Num + ToPrimitive>(number: N) -> Self {
        let size = std::mem::size_of::<N>();
        Scalar { size, data: number.to_u128().unwrap() }
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum ValTree<'tcx> {
    Scalar(Scalar),
    Branch(&'tcx [ValTree<'tcx>])
}

#[derive(Debug, Hash, PartialEq, Eq, Internable)]
#[alias(Const)]
pub enum ConstInner<'tcx> {
    Value(Ty<'tcx>, ValTree<'tcx>),
    Placeholder,
    Err {
        msg: String,
        span: Span
    }
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub struct Const<'tcx>(pub &'tcx ConstInner<'tcx>);

impl<'tcx> Const<'tcx> {
    pub fn from_definition(tcx: TyCtxt<'tcx>, def_id: DefId) -> Const<'tcx> {
        let node = tcx.node_by_def_id(def_id);

        let body = node.body()
            .expect("create const without a body?");

        let ty = tcx.type_of(def_id);
        match Self::try_val_from_literal(tcx, ty, body.body) {
            Some(v) => v,
            None => tcx.intern(ConstInner::Err {
                msg: "Sry, propper const evaluation is not a priority".to_string(),
                span: body.body.span
            })
        }
    }

    fn int_to_val(
        tcx: TyCtxt<'tcx>, val: u64, ty: Ty<'tcx>, sign: NumberSign, span: Span) -> ConstInner<'tcx> {
        if let Ty(TyKind::Primitive(primitive)) = ty {
            if primitive.integer_fit(val, sign) {
                let scalar = Scalar {
                    size: primitive.size() / 8,
                    data: val as u128
                };
                return ConstInner::Value(ty, ValTree::Scalar(scalar)); 
            }
        }
        for primitive in [Primitive::Int, Primitive::Long, Primitive::ULong] {
            if primitive.integer_fit(val, sign) {
                return ConstInner::Err {
                    msg: format!("mismatched types: expected {ty}, found {}",
                                 Ty::new_primitive(tcx, primitive)),
                    span
                }
            }
        }
        panic!("u64 to big for ulong ???")
    }

    fn kind_to_ty(tcx: TyCtxt<'tcx>, kind: &'tcx ast::ExprKind) -> Ty<'tcx> {
        use ast::{ExprKind, Constant};
        match kind {
            ExprKind::String(..) => Ty::new_primitive(tcx, Primitive::String),
            ExprKind::Constant(Constant::Char(..)) => Ty::new_primitive(tcx, Primitive::Char),
            ExprKind::Constant(Constant::Boolean(..)) => Ty::new_primitive(tcx, Primitive::Bool),
            ExprKind::Constant(Constant::Integer(..)) | ExprKind::UnaryOp(..)
                => Ty::new_primitive(tcx, Primitive::Int),
            _ => unreachable!("simple kind_to_ty doesn't support {:?}", kind)
        }
    }

    fn try_val_from_literal(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, expr: &'tcx ast::Expr) -> Option<Self> {
        use ast::{ExprKind, Constant, UnaryOperator};
        use Primitive::*;
        match &expr.kind {
            ExprKind::String(..) | ExprKind::Constant(..) => (),
            ExprKind::UnaryOp(expr, ast::UnaryOperator::Neg)
                if matches!(expr.kind, ExprKind::Constant(ast::Constant::Integer(..))) => (),
            _ => return None
        }
        let inner = match (ty.0, &expr.kind) {
            (TyKind::Primitive(String), ExprKind::String(str)) =>  {
                let mut slice = Vec::new();
                for byte in str.as_bytes() {
                    let val = Scalar::from_number(*byte);
                    slice.push(ValTree::Scalar(val));
                }

                let slice = slice.into_boxed_slice();
                let slice: &[ValTree] = tcx.arena.alloc(slice);

                ConstInner::Value(ty, ValTree::Branch(slice))
            }
            (TyKind::Primitive(Bool), ExprKind::Constant(Constant::Boolean(bool))) =>
                ConstInner::Value(ty, ValTree::Scalar(Scalar::from_number(*bool as u8))),
            (TyKind::Primitive(Char), ExprKind::Constant(Constant::Char(char))) =>
                ConstInner::Value(ty, ValTree::Scalar(Scalar::from_number(*char as u32))),
            (TyKind::Primitive(SByte|Byte|Short|UShort|Int|Uint|Long|ULong|Nint|NUint), ExprKind::Constant(Constant::Integer(int))) =>
                Self::int_to_val(tcx, *int, ty, NumberSign::Positive, expr.span),
            (TyKind::Primitive(SByte|Byte|Short|UShort|Int|Uint|Long|ULong|Nint|NUint), ExprKind::UnaryOp(iexpr, UnaryOperator::Neg))
                if matches!(iexpr.kind, ExprKind::Constant(Constant::Integer(..))) => {
                let ExprKind::Constant(Constant::Integer(int)) = iexpr.kind else {
                    unreachable!()
                };
                Self::int_to_val(tcx, int, ty, NumberSign::Negative, expr.span)
            }
            (TyKind::Refrence(..), ExprKind::Constant(ast::Constant::Null)) =>
                // FIXME: `as usize` here will make the size of the scalar depend on the size
                // of the architecture the compiler was compiled on, not the target usize
                ConstInner::Value(ty, ValTree::Scalar(Scalar::from_number(0 as usize))),
            (_, ExprKind::Constant(ast::Constant::Null)) => ConstInner::Err {
                msg: format!("non refrence-type {ty} cannot be null"),
                span: expr.span
            },
            _ => ConstInner::Err {
                msg: format!("mismatched types: expected {ty}, found {}", Self::kind_to_ty(tcx, &expr.kind)),
                span: expr.span
            }
        };

        Some(tcx.intern(inner))
    }

    pub fn try_as_usize(&self) -> Option<usize> {
        match self.0 {
            ConstInner::Placeholder | ConstInner::Err { .. } => None,
            ConstInner::Value(ty, val) => {
                let Ty(TyKind::Primitive(Primitive::NUint)) = ty else {
                    return None;
                };
                let ValTree::Scalar(Scalar { size: 8, data }) = val else {
                    unreachable!("const nuint is not stored as a scalar of size 8");
                };
                Some(*data as usize)
            }
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Internable)]
#[alias(Ty)]
pub enum TyKind<'tcx> {
    Primitive(Primitive),
    Adt(AdtDef<'tcx>),
    Refrence(Ty<'tcx>),
    Range(Ty<'tcx>, bool),
    Slice(Ty<'tcx>),
    Array(Ty<'tcx>, Const<'tcx>),
    Tuple(Vec<Ty<'tcx>>),
    DynamicArray(Ty<'tcx>),
    Function(DefId),
    Never,
    Err
}

#[derive(Debug, Clone, Copy, Hash)]
pub struct Ty<'tcx>(pub &'tcx TyKind<'tcx>);

impl<'tcx> PartialEq for Ty<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        if let Ty(TyKind::Never | TyKind::Err) = self {
            return true;
        }
        if let Ty(TyKind::Never | TyKind::Err) = other {
            return true;
        }
        std::ptr::eq(self.0, other.0)
    }
}

impl<'tcx> Eq for Ty<'tcx> {}

impl<'tcx> std::fmt::Display for Ty<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            TyKind::Never => write!(f, "never"),
            TyKind::Primitive(p) => write!(f, "{p}"),
            TyKind::Adt(adt) => f.write_str(adt.name.get()),
            TyKind::Refrence(ty) => write!(f, "*{ty}"),
            TyKind::Slice(ty) => write!(f, "[]{ty}"),
            TyKind::Array(ty, _) => write!(f, "[?]{ty}"),
            TyKind::DynamicArray(ty) => write!(f, "[..]{ty}"),
            TyKind::Function(_) => write!(f, "function"),
            TyKind::Range(ty, _) => write!(f, "Range<{ty}>"),
            TyKind::Tuple(tys) => {
                f.write_str("(")?;
                for (idx, ty) in tys.iter().enumerate() {
                    write!(f, "{ty}")?;
                    if idx != tys.len() - 1 {        
                        f.write_str(", ")?;
                    }
                }
                f.write_str(")")?;
                Ok(())
            }
            TyKind::Err => write!(f, "Err"),
        }
    }
}

impl<'tcx> Ty<'tcx> {
    pub fn new_array(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, cnst: Const<'tcx>) -> Ty<'tcx> {
        tcx.intern(TyKind::Array(ty, cnst))
    }

    pub fn new_slice(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        tcx.intern(TyKind::Slice(ty))
    }

    pub fn new_dyn_array(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        tcx.intern(TyKind::DynamicArray(ty))
    }

    pub fn new_refrence(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        tcx.intern(TyKind::Refrence(ty))
    }

    pub fn new_error(tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        tcx.intern(TyKind::Err)
    }

    pub fn new_never(tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        tcx.intern(TyKind::Never)
    }

    pub fn new_primitive(tcx: TyCtxt<'tcx>, primitive: Primitive) -> Ty<'tcx> {
        tcx.intern(TyKind::Primitive(primitive))
    }

    pub fn new_adt(tcx: TyCtxt<'tcx>, adt: AdtDef<'tcx>) -> Ty<'tcx> {
        tcx.intern(TyKind::Adt(adt))
    }

    pub fn new_function(tcx: TyCtxt<'tcx>, def: DefId) -> Ty<'tcx> {
        tcx.intern(TyKind::Function(def))
    }

    pub fn new_range(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, inclusive: bool) -> Ty<'tcx> {
        tcx.intern(TyKind::Range(ty, inclusive))
    }

    pub fn new_tuple(tcx: TyCtxt<'tcx>, tys: Vec<Ty<'tcx>>) -> Ty<'tcx> {
        tcx.intern(TyKind::Tuple(tys))
    }

    /// Searches slice types for bendable types (Never, Err)
    /// while preferring Err over Never
    pub fn with_bendable(types: &[Ty<'tcx>]) -> Option<Ty<'tcx>> {
        let mut found = None;
        for ty in types {
            if let Ty(TyKind::Err) = ty {
                return Some(*ty);
            } else if let Ty(TyKind::Never) = ty {
                found = Some(*ty);
            }
        }

        return found;
    }

    pub fn is_incomplete(&self) -> bool {
        match self {
            Ty(TyKind::Array(_, Const(ConstInner::Placeholder))) => true,
            _ => false
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NumberSign {
    Positive, Negative
}

#[repr(u32)]
#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub enum Primitive {
    Bool, Void,
    SByte, Byte, Short, UShort, Int, Uint, Long, ULong, Nint, NUint,
    Char, String
}

impl TryFrom<Symbol> for Primitive {
    type Error = ();

    fn try_from(value: Symbol) -> Result<Self, Self::Error> {
        if !value.is_primtive() {
            return Err(());
        }
        Ok(unsafe { transmute(value) })
    }
}

impl From<Primitive> for Symbol {
    fn from(value: Primitive) -> Self {
        unsafe { transmute(value) }
    }
}

impl std::fmt::Display for Primitive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let symbol: Symbol = (*self).into();
        f.write_str(symbol.get())
    }
}

impl Primitive {
    pub fn integer_fit(&self, int: u64, sign: NumberSign) -> bool {
        use Primitive::*;
        if sign == NumberSign::Negative && matches!(self, Byte | UShort | Uint | ULong | NUint) {
            return false;
        }

        let signed = match self.signed() {
            Some(signed) => signed,
            None => return false,
        };
        let bits = self.size() as u32;

        let range = if sign == NumberSign::Negative { // create lower range
            1 << (bits - 1)
        } else if signed { // create "small" upper range
            (1 << (bits - 1)) - 1
        } else { // create "big" upper range
            (1u64).checked_shl(bits).unwrap_or(0).wrapping_sub(1)
        };

        int <= range
    }

    pub fn signed(&self) -> Option<bool> {
        use Primitive::*;
        Some(match self {
            SByte | Short | Int | Long | Nint => true,
            Byte | UShort | Uint | ULong | NUint  => false,
            _ => return None
        })
    }

    pub fn size(&self) -> usize {
        use Primitive::*;
        // TODO: Decide based on platform
        // (currently only valid for 64bit platforms)
        match self {
            SByte | Byte => 8,
            Short | UShort => 16,
            Int | Uint => 32,
            Long | ULong => 64,
            Nint | NUint => 64, 
            Bool => 8, Void => 0,
            Char => 32, String => 128
        }
    }
}

