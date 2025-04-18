use std::{mem::transmute, ops::Deref};

use num_traits::{Num, ToPrimitive};

use crate::{ast::{self, DefId, NodeId}, context::TyCtxt, lexer::Span, symbol::Symbol};
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

#[derive(Hash, Clone, Copy, PartialEq, Eq)]
pub struct Const<'tcx>(pub &'tcx ConstInner<'tcx>);

impl<'tcx> Const<'tcx> {
    pub fn void_value(tcx: TyCtxt<'tcx>) -> Const<'tcx> {
        let void = Ty::new_primitive(tcx, Primitive::Void);
        let value = ValTree::Branch(&[]);
        tcx.intern(ConstInner::Value(void, value))
    }

    pub fn from_definition(tcx: TyCtxt<'tcx>, def_id: DefId) -> Const<'tcx> {
        let node = tcx.node_by_def_id(def_id);

        let body = node.body()
            .expect("const should have a body");

        let ty = tcx.type_of(def_id);
        match Self::try_val_from_simple_expr(tcx, ty, body.body) {
            Some(v) => v,
            None => tcx.intern(ConstInner::Err {
                msg: "Sry, propper const evaluation is not a priority".to_string(),
                span: body.body.span
            })
        }
    }

    fn int_to_val(
        tcx: TyCtxt<'tcx>, val: i64, ty: Ty<'tcx>) -> Result<ConstInner<'tcx>, String> {
        if let Ty(TyKind::Primitive(primitive)) = ty {
            if primitive.integer_fit(val) {
                let scalar = Scalar {
                    size: primitive.size() / 8,
                    data: val as u128
                };
                return Ok(ConstInner::Value(ty, ValTree::Scalar(scalar))); 
            }
        }
        for primitive in [Primitive::Int, Primitive::Long, Primitive::ULong] {
            if primitive.integer_fit(val) {
                return Err(format!("mismatched types: expected {ty}, found {}", Ty::new_primitive(tcx, primitive)));
            }
        }
        panic!("u64 to big for ulong ???")
    }

    fn literal_to_ty(tcx: TyCtxt<'tcx>, literal: &ast::Literal) -> Ty<'tcx> {
        match literal {
            ast::Literal::String(..) => Ty::new_primitive(tcx, Primitive::String),
            ast::Literal::Char(..) => Ty::new_primitive(tcx, Primitive::Char),
            ast::Literal::Boolean(..) => Ty::new_primitive(tcx, Primitive::Bool),
            ast::Literal::Integer(..) => Ty::new_primitive(tcx, Primitive::Int),
            ast::Literal::Floating(..) => Ty::new_primitive(tcx, Primitive::Float),
            ast::Literal::Null => panic!("can't infer type from null")
        }
    }

    fn try_val_from_simple_expr(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, expr: &'tcx ast::Expr) -> Option<Self> {
        let ast::ExprKind::Literal(literal) = &expr.kind else {
            return None;
        };
        match Self::from_literal(tcx, ty, literal) {
            Ok(cnst) => Some(cnst),
            Err(msg) => Some(tcx.intern(ConstInner::Err {
                msg, span: expr.span
            }))
        }
    }

    pub fn from_literal(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, literal: &ast::Literal) -> Result<Self, String> {
        use Primitive::*;
        let inner = match (ty.0, literal) {
            (TyKind::Primitive(String), ast::Literal::String(str)) =>  {
                let mut slice = Vec::new();
                for byte in str.as_bytes() {
                    let val = Scalar::from_number(*byte);
                    slice.push(ValTree::Scalar(val));
                }

                let slice = slice.into_boxed_slice();
                let slice: &[ValTree] = tcx.arena.alloc(slice);

                ConstInner::Value(ty, ValTree::Branch(slice))
            }
            (TyKind::Primitive(Bool), ast::Literal::Boolean(bool)) =>
                ConstInner::Value(ty, ValTree::Scalar(Scalar::from_number(*bool as u8))),
            (TyKind::Primitive(Char), ast::Literal::Char(char)) =>
                ConstInner::Value(ty, ValTree::Scalar(Scalar::from_number(*char as u32))),
            (TyKind::Primitive(SByte|Byte|Short|UShort|Int|Uint|Long|ULong|Nint|NUint), ast::Literal::Integer(int)) =>
                Self::int_to_val(tcx, *int, ty)?,
            (TyKind::Refrence(..), ast::Literal::Null) =>
                // FIXME: `as usize` here will make the size of the scalar depend on the size
                // of the architecture the compiler was compiled on, not the target usize
                ConstInner::Value(ty, ValTree::Scalar(Scalar::from_number(0 as usize))),
            (_, ast::Literal::Null) =>
                return Err(format!("non refrence-type {ty} cannot be null")),
            _ =>
                return Err(format!("mismatched types: expected {ty}, found {}", Self::literal_to_ty(tcx, literal))),
        };

        Ok(tcx.intern(inner))
    }

    pub fn from_bool(tcx: TyCtxt<'tcx>, value: bool) -> Const<'tcx> {
        let bool = Ty::new_primitive(tcx, Primitive::Bool);
        tcx.intern(ConstInner::Value(bool, ValTree::Scalar(Scalar::from_number(value as u8))))
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

impl<'tcx> std::fmt::Debug for Const<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            ConstInner::Value(Ty(TyKind::Primitive(primitive)), value) => {
                let scalar = if let ValTree::Scalar(scalar) = value {
                    Some(scalar.data)
                } else {
                    None
                };
                match primitive {
                    Primitive::Void => f.write_str("<empty>"),
                    Primitive::Bool =>
                        write!(f, "{}_bool", scalar.unwrap() != 0),
                    Primitive::Char =>
                        write!(f, "{}_char", char::from_u32(scalar.unwrap() as u32).unwrap()),
                    Primitive::String => f.write_str("<string>"),
                    Primitive::Float => todo!(),
                    _ => {
                        if primitive.signed().unwrap() {
                            write!(f, "{}_{primitive}", scalar.unwrap() as i64)
                        } else {
                            write!(f, "{}_{primitive}", scalar.unwrap() as u64)
                        }
                    }
                }
            }
            ConstInner::Value(..) => f.write_str("<value>"),
            ConstInner::Placeholder => f.write_str("_"),
            ConstInner::Err { .. } => f.write_str("<err>"),
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
            TyKind::Refrence(ty) => write!(f, "{ty}*"),
            TyKind::Slice(ty) => write!(f, "{ty}[]"),
            TyKind::Array(ty, _) => write!(f, "{ty}[_]"),
            TyKind::DynamicArray(ty) => write!(f, "{ty}[..]"),
            TyKind::Function(_) => write!(f, "function"),
            TyKind::Range(ty, _) => write!(f, "Range<{ty}>"),
            TyKind::Tuple(tys) => {
                f.write_str("tuple<")?;
                for (idx, ty) in tys.iter().enumerate() {
                    write!(f, "{ty}")?;
                    if idx != tys.len() - 1 {        
                        f.write_str(", ")?;
                    }
                }
                f.write_str(">")?;
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

    /// Searches slice types for bendable types (Never, Err)
    /// while preferring Err and rejecting Never
    pub fn with_non_bendable(types: &[Ty<'tcx>]) -> Option<Ty<'tcx>> {
        let mut never = None;
        for ty in types {
            if let Ty(TyKind::Err) = ty {
                return Some(*ty);
            } else if let Ty(TyKind::Never) = ty {
                never = Some(*ty);
                continue;
            }
            return Some(*ty);
        }
        never
    }

    pub fn is_incomplete(&self) -> bool {
        match self {
            Ty(TyKind::Array(_, Const(ConstInner::Placeholder))) => true,
            _ => false
        }
    }
}

#[repr(u32)]
#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub enum Primitive {
    Bool, Void,
    SByte, Byte, Short, UShort, Int, Uint, Long, ULong, Nint, NUint,
    Float,
    Char, String,
    Tuple
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
    pub fn integer_fit(&self, int: i64) -> bool {
        use Primitive::*;
        if int < 0 && matches!(self, Byte | UShort | Uint | ULong | NUint) {
            return false;
        }

        let signed = match self.signed() {
            Some(signed) => signed,
            None => return false,
        };
        let bits = self.size() as u32;

        let range = if int < 0 { // create lower range
            1 << (bits - 1)
        } else if signed { // create "small" upper range
            (1 << (bits - 1)) - 1
        } else { // create "big" upper range
            (1u64).checked_shl(bits).unwrap_or(0).wrapping_sub(1)
        };

        int.abs() as u64 <= range
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
            Char => 32, String => 128,
            Float => 32,
            Tuple => panic!()
        }
    }
}

