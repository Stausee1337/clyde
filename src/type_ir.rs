use core::panic;
use std::{any::TypeId, cell::Cell, fmt::Write, marker::{PhantomData, Unsize}, ops::Deref, ptr::NonNull};

use bytemuck::Pod;
use index_vec::IndexVec;
use num_traits::{Num, ToPrimitive};

use crate::{context::{self, FromCycleError, InternerExt, Interners, TyCtxt}, diagnostics::Message, mapping, syntax::{ast::{self, DefId, NodeId}, lexer::Span, symbol::{sym, Symbol}}, target::{DataLayoutExt, TargetDataLayout}};

impl DefId {
    pub fn normalized_generics<'tcx>(&self, tcx: TyCtxt<'tcx>) -> &'tcx [GenericArg<'tcx>] {
        let node = tcx.node_by_def_id(*self);
        let generics = node.generics();

        let mut generic_args = vec![];
        for param in generics {
            let def_id = *param.def_id.get().unwrap();
            let generic_arg = match param.kind {
                ast::GenericParamKind::Type(..) =>
                    GenericArg::from_ty(tcx.type_of(def_id)),
                ast::GenericParamKind::Const(..) => 
                    GenericArg::from_const(Const::from_definition(tcx, def_id)),
            };
            generic_args.push(generic_arg);
        }
        tcx.arena.alloc_slice_copy(&generic_args)
    }
}

pub trait Instatiatable<'tcx> {
    fn instantiate(self, generic_args: &'tcx [GenericArg<'tcx>], tcx: TyCtxt<'tcx>) -> Self;
}

pub trait AsType<'tcx> {
    fn as_type(&self) -> Option<Ty<'tcx>>;
}

impl<'tcx, T: mapping::Recursible<'tcx> + AsType<'tcx>> Instatiatable<'tcx> for T {
    fn instantiate(self, generic_args: &'tcx [GenericArg<'tcx>], tcx: TyCtxt<'tcx>) -> Self {
        let mut handler = mapping::InstantiationMapper::new(tcx, self.as_type(), generic_args);
        self.map_recurse(&mut handler)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GenericArg<'tcx> {
    ptr: NonNull<()>,
    phantom: PhantomData<&'tcx ()>
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GenericArgKind<'tcx> {
    Ty(Ty<'tcx>),
    Const(Const<'tcx>),
}

impl<'tcx> GenericArg<'tcx> {
    const TY_ENCODED: usize = 0b01;
    const CONST_ENCODED: usize = 0b10;
    const ENCODING_MASK: usize = 0b11;

    pub fn from_ty(ty: Ty<'tcx>) -> Self {
        let ptr = unsafe { Self::pack(ty.0, Self::TY_ENCODED) };
        Self {
            ptr,
            phantom: PhantomData
        }
    }

    pub fn from_const(cnst: Const<'tcx>) -> Self {
        let ptr = unsafe { Self::pack(cnst.0, Self::CONST_ENCODED) };
        Self {
            ptr,
            phantom: PhantomData
        }
    }

    pub fn kind(self) -> GenericArgKind<'tcx> {
        let kind = self.ptr.addr().get() & Self::ENCODING_MASK;
        match kind {
            Self::TY_ENCODED => GenericArgKind::Ty(Ty(unsafe { self.unpack() })),
            Self::CONST_ENCODED => GenericArgKind::Const(Const(unsafe { self.unpack() })),
            _ => panic!("invalid generic argument encoding"),
        }
    }

    #[inline]
    unsafe fn unpack<T>(self) -> &'tcx T {
        let addr = self.ptr.addr().get() & !Self::ENCODING_MASK;
        std::mem::transmute(addr as *const T)
    }

    #[inline]
    unsafe fn pack<T>(refrence: &T, encoded: usize) -> NonNull<()> {
        assert!(std::mem::align_of::<T>() >= 4);
        let addr = (refrence as *const T).addr();
        NonNull::new_unchecked((addr | encoded) as *mut ())
    }
}

impl<'tcx> std::fmt::Display for GenericArg<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind() {
            GenericArgKind::Ty(ty) => write!(f, "{ty}"),
            GenericArgKind::Const(cnst) => write!(f, "{cnst:?}"),
        }
    }
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub struct AdtDef<'tcx>(pub &'tcx AdtKind);

impl<'tcx> Deref for AdtDef<'tcx> {
    type Target = AdtKind;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

#[derive(Debug, Hash)]
#[repr(u32)]
pub enum AdtKind {
    Struct(Struct),
    Union,
}

impl AdtKind {
    pub fn def(&self) -> DefId {
        match self {
            AdtKind::Struct(strct) => strct.def,
            AdtKind::Union => todo!()
        }
    }

    pub fn name(&self) -> Symbol {
        match self {
            AdtKind::Struct(strct) => strct.name,
            AdtKind::Union => todo!()
        }
    }

    pub fn kind(&self) -> &'static str {
        match self {
            AdtKind::Struct(..) => "struct",
            AdtKind::Union => "union"
        }
    }
}

impl PartialEq for AdtKind {
    fn eq(&self, other: &Self) -> bool {
        self.def() == other.def()
    }
}

impl Eq for AdtKind {}

#[derive(Debug, Hash)]
pub struct Struct {
    pub def: DefId,
    pub name: Symbol,
    fields: IndexVec<FieldIdx, FieldDef>,
}

impl Struct {
    pub fn new(
        def: DefId,
        name: Symbol,
        fields: IndexVec<FieldIdx, FieldDef>,
    ) -> Self {
        Self { def, name, fields }
    }

    pub fn fields(&self) -> impl Iterator<Item = (FieldIdx, &FieldDef)> {
        self.fields.iter_enumerated()
    }

    pub fn get_field(&self, field: FieldIdx) -> &FieldDef {
        &self.fields[field]
    }
}

#[derive(Debug, Hash)]
pub struct FieldDef {
    pub def: DefId,
    pub symbol: Symbol
}

index_vec::define_index_type! {
    pub struct FieldIdx = u32;
    IMPL_RAW_CONVERSIONS = true;
}

#[derive(Clone, Copy)]
pub struct Signature<'tcx> {
    pub returns: Ty<'tcx>,
    pub params: &'tcx [Param<'tcx>],
    pub name: Symbol,
    pub has_errors: bool,
    pub intrinsic: bool
}

#[derive(Clone, Copy)]
pub struct Param<'tcx> {
    pub name: Symbol,
    pub ty: Ty<'tcx>,
    pub node_id: NodeId
}

#[derive(Hash, PartialEq, Eq, Clone, Copy)]
struct Erased<'a>(&'a [u8]);

impl<'a> Erased<'a> {
    fn from_ref<T: Pod>(r: &'a T) -> Self {
        let slice = std::slice::from_ref(r);
        let data: &[u8] = bytemuck::cast_slice(slice);
        Erased(data)
    }
}

#[derive(Clone, Copy)]
struct Eraser<'tcx> {
    arena: &'tcx bumpalo::Bump
}

impl<'tcx> Eraser<'tcx> {
    fn from_tcx(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            arena: &tcx.arena
        }
    }

    fn erase<T: Pod>(&self, val: T) -> Erased<'tcx> {
        let x = self.arena.alloc(val);
        let slice = std::slice::from_ref(x);
        let slice: &[u8] = bytemuck::cast_slice(slice);
        Erased(slice)
    }
}

#[derive(Hash, PartialEq, Eq)]
pub struct Value<'tcx> {
    pub ty: Ty<'tcx>,
    erased: Erased<'tcx>
}

/// Tries to turn `&S` into `&T` (`T` being `dyn Trt`), by checking if `T` is `U` and enforcing
/// that `S` implements `U`
#[inline]
fn downcast_sized_knowingly<'a, T, U, S>(erased: Erased<'a>) -> Option<&'a T>
where 
    T: std::ptr::Pointee<Metadata = std::ptr::DynMetadata<T>> + ?Sized + 'static,
    U: std::ptr::Pointee<Metadata = std::ptr::DynMetadata<U>> + ?Sized + 'static,
    S: Unsize<U> + Sized + 'a
{

    if TypeId::of::<U>() != TypeId::of::<T>() {
        return None;
    }

    let data = erased.0.as_ptr() as *const ();

    let align = std::mem::align_of::<S>();
    assert!(data.addr() & (align - 1) == 0);
    assert!(erased.0.len() == std::mem::size_of::<S>());

    let vtable: std::ptr::DynMetadata<U> = const { get_vtable::<U, S>() };

    // SAFETY:
    //  since T == U (through dynamic TypeId check),
    //      <S as Unsize<U>> == <S as Unsize<T>>
    //  &S -> &dyn T
    unsafe {
        let trait_ = std::ptr::from_raw_parts(data, vtable) as *const U;
        let trait_ = &*trait_;
        Some(std::mem::transmute(trait_))
    }
}

impl<'tcx> Value<'tcx> {
    pub fn from_array_with_ty(data: &'tcx [u8], ty: Ty<'tcx>) -> Self {
        let erased = Erased(data);
        Value { ty, erased }
    }

    pub fn from_integer_with_ty(tcx: TyCtxt<'tcx>, value: impl Num + ToPrimitive, ty: Ty<'tcx>) -> Self {
        let (int, signed) = match ty {
            Ty(TyKind::Int(int, signed)) => (*int, *signed),
            Ty(TyKind::Bool) => (Integer::I8, false),
            Ty(TyKind::Char) => (Integer::I32, false),
            Ty(TyKind::Enum(_enm)) => (Integer::I32, true), // FIXME: use data from layout query
                                                           // here
            _ => {
                panic!("from_integer_with_ty expects TyKind::Int, TyKind::Char or TyKind::Bool")
            }
        };
        let eraser = Eraser::from_tcx(tcx);
        let erased = int.convert(signed, &tcx, value, eraser);
        Value { ty, erased }
    }

    pub fn from_size(tcx: TyCtxt<'tcx>, size: u64) -> Self {
        let int = Integer::ISize.normalize(&tcx);
        let eraser = Eraser::from_tcx(tcx);
        let erased = int.convert(false, &tcx, size, eraser);
        Value { ty: tcx.basic_types.nuint, erased }
    }

    pub fn from_float(tcx: TyCtxt<'tcx>, value: f64, float: Float) -> Self {
        let eraser = Eraser::from_tcx(tcx);
        let erased = eraser.erase(value);
        Value { ty: Ty::new_float(tcx, float), erased }
    }

    pub fn downcast_unsized<T: std::ptr::Pointee<Metadata = std::ptr::DynMetadata<T>> + ?Sized + 'static>(&self) -> Option<&T> {
        // NOTE: for Value this could be a query, allowing polymorphic data to be provided from
        // much further than just rust itself, but including compile-time executions (e.g.
        // generating vtables at runtime)

        match self.ty {
            Ty(TyKind::Int(int, signedness)) =>
                int.downcast_unsized::<T>(*signedness, self.erased),
            Ty(TyKind::Bool) =>
                Integer::I8.downcast_unsized::<T>(false, self.erased),
            Ty(TyKind::Char) =>
                Integer::I32.downcast_unsized::<T>(false, self.erased),
            Ty(TyKind::Float(float)) =>
                float.downcast_unsized::<T>(self.erased),
            _ => None
        }
    }

    pub fn as_bytes(&self) -> &'tcx [u8] {
        self.erased.0
    }
}

impl<'tcx> std::fmt::Debug for Value<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Some(d) = self.downcast_unsized::<dyn std::fmt::Debug>() else {
            return write!(f, "<value> of {}", self.ty);
        };
        write!(f, "{d:?}_{}", self.ty)
    }
}

const fn get_vtable<T: ?Sized + 'static, S: Unsize<T>>() -> <T as std::ptr::Pointee>::Metadata { 
    let ptr: *const S = std::ptr::null();
    let ptr: *const T = ptr;

    let (_, b) = ptr.to_raw_parts();
    b
}

#[derive(Hash, PartialEq, Eq)]
pub enum ConstKind<'tcx> {
    Value(Value<'tcx>),
    Param(Symbol, usize),
    Infer,
    Err
}

#[derive(Hash, Clone, Copy, PartialEq, Eq)]
pub struct Const<'tcx>(pub &'tcx ConstKind<'tcx>);

impl<'tcx> Const<'tcx> {
    pub fn from_definition(tcx: TyCtxt<'tcx>, def_id: DefId) -> Const<'tcx> {
        let ty = tcx.type_of(def_id);

        let node = tcx.node_by_def_id(def_id);
        let body = node.body().expect("const should have a body");

        match Self::try_val_from_simple_expr(tcx, ty, body.body) {
            Some(v) => v,
            None => {
                Message::error("Sry, propper const evaluation is not a priority".to_string())
                    .at(body.body.span)
                    .push(tcx.diagnostics());
                tcx.intern_const(ConstKind::Err)
            }
        }
    }

    fn int_to_val(tcx: TyCtxt<'tcx>, int: ast::Integer, ty: Ty<'tcx>) -> Result<ConstKind<'tcx>, String> {
        let min_int = if int.signed {
            let Some(int) = Integer::fit_signed(-(int.value as i128)) else {
                return Err(format!("{} does not fit into signed long", int.value));
            };
            int
        } else {
            Integer::fit_unsigned(int.value)
        };

        if let Ty(TyKind::Int(integer, signed)) = ty && *signed | !int.signed {
            let min_int = if *signed {
                Integer::fit_signed((int.value as i128) * if int.signed { -1 } else { 1 }).map_or(Size::from_bits(128), |i| i.size(&tcx))
            } else {
                Integer::fit_unsigned(int.value).size(&tcx)
            };

            if integer.size(&tcx) >= min_int {
                if int.signed {
                    return Ok(ConstKind::Value(Value::from_integer_with_ty(tcx, -(int.value as i64), ty)));
                } else { 
                    return Ok(ConstKind::Value(Value::from_integer_with_ty(tcx, int.value, ty)));
                }
            }
        }

        Err(format!("mismatched types: expected {ty}, found {}", Ty::new_int(tcx, min_int, int.signed)))
    }

    fn literal_to_ty(tcx: TyCtxt<'tcx>, literal: &ast::Literal) -> Ty<'tcx> {
        match literal {
            ast::Literal::String(..) => 
                tcx.basic_types.string,
            ast::Literal::Boolean(..) =>
                tcx.basic_types.bool,
            ast::Literal::Char(..) =>
                tcx.basic_types.char,
            ast::Literal::Integer(..) =>
                tcx.basic_types.int,
            ast::Literal::Floating(..) =>
                tcx.basic_types.double,
            ast::Literal::Null => panic!("can't infer type from null")
        }
    }

    fn try_val_from_simple_expr(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, expr: &'tcx ast::Expr) -> Option<Self> {
        if let ast::ExprKind::Literal(literal) = &expr.kind {
            return match Self::from_literal(tcx, ty, literal) {
                Ok(cnst) => Some(cnst),
                Err(msg) => {
                    Message::error(msg)
                        .at(expr.span)
                        .push(tcx.diagnostics());
                    Some(tcx.intern_const(ConstKind::Err))
                }
            };
        } else if let ast::ExprKind::Path(name) = &expr.kind  {
            match name.resolution() {
                Some(ast::Resolution::Def(def_id, ast::DefinitionKind::Const)) => {
                    let found_ty = tcx.type_of(*def_id);
                    if found_ty != ty {
                        Message::error(format!("mismatched types: expected {ty}, found {found_ty}"))
                            .at(expr.span)
                            .push(tcx.diagnostics());
                        return Some(tcx.intern_const(ConstKind::Err));
                    }
                    return Some(Const::from_definition(tcx, *def_id));
                }
                Some(ast::Resolution::Def(def_id, ast::DefinitionKind::ParamConst)) => {
                    let ast::Node::GenericParam(param @ ast::GenericParam { kind: ast::GenericParamKind::Const(name, _), .. }) = tcx.node_by_def_id(*def_id) else {
                        unreachable!();
                    };

                    let owner_node = tcx.owner_node(param.node_id);

                    let generics = owner_node.generics();
                    let index = generics
                        .iter()
                        .position(|p| p.node_id == param.node_id)
                        .expect("`param` should be a generic param on its owner");

                    return Some(tcx.intern_const(ConstKind::Param(name.symbol, index)));
                }
                _ => ()
            }
        }
        None
    }

    fn new_size(tcx: TyCtxt<'tcx>, size: u64) -> Self {
        tcx.intern_const(ConstKind::Value(Value::from_size(tcx, size)))
    }

    fn zeroed(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Self {
        let Ok(layout) = tcx.layout_of(ty) else {
            return tcx.intern_const(ConstKind::Err);
        };
        let data = tcx.arena.alloc_slice_fill_copy(layout.size.in_bytes as usize, 0u8);
        tcx.intern_const(ConstKind::Value(Value::from_array_with_ty(data, ty)))
    }

    pub fn from_literal(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, literal: &'tcx ast::Literal) -> Result<Self, String> {
        let inner = match (ty.0, literal) {
            (TyKind::Bool, ast::Literal::Boolean(bool)) =>
                ConstKind::Value(Value::from_integer_with_ty(tcx, *bool as u8, tcx.basic_types.bool)),
            (TyKind::Char, ast::Literal::Char(char)) =>
                ConstKind::Value(Value::from_integer_with_ty(tcx, *char as u32, tcx.basic_types.char)),
            (TyKind::Int(..), ast::Literal::Integer(int)) =>
                Self::int_to_val(tcx, *int, ty)?,
            (TyKind::Float(ty), ast::Literal::Floating(float)) =>
                ConstKind::Value(Value::from_float(tcx, *float, *ty)),
            (TyKind::Refrence(..), ast::Literal::Null) =>
                ConstKind::Value(Value::from_size(tcx, 0)),
            (_, ast::Literal::Null) =>
                return Err(format!("non refrence-type {ty} cannot be null")),
            _ =>
                return Err(format!("mismatched types: expected {ty}, found {}", Self::literal_to_ty(tcx, literal))),
        };

        Ok(tcx.intern_const(inner))
    }

    pub fn from_bool(tcx: TyCtxt<'tcx>, value: bool) -> Const<'tcx> {
        tcx.intern_const(ConstKind::Value(Value::from_integer_with_ty(tcx, value as u8, tcx.basic_types.bool)))
    }

    pub fn downcast_unsized<T: std::ptr::Pointee<Metadata = std::ptr::DynMetadata<T>> + ?Sized + 'static>(&self) -> Option<&T> {
        match self {
            Const(ConstKind::Value(value)) => value.downcast_unsized::<T>(),
            _ => None
        }
    }

    pub fn new_error(tcx: TyCtxt<'tcx>) -> Self {
        tcx.intern_const(ConstKind::Err)
    }
}

impl<'tcx> std::fmt::Debug for Const<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Const(ConstKind::Value(value)) => write!(f, "{value:?}"),
            Const(ConstKind::Infer) => write!(f, "_"),
            Const(ConstKind::Param(symbol, _)) => write!(f, "{symbol}"),
            Const(ConstKind::Err) => write!(f, "<error>")
        }
    }
}

#[derive(Hash, PartialEq, Eq)]
pub enum GlobalKind<'tcx> {
    Function {
        def: DefId
    },
    EnumVariant {
        def: DefId
    },
    Static {
        def: DefId,
        initializer: Const<'tcx>
    },
    /// Similar to `GlobalKind::Static`, but it doesn't have a `DefId` associated with it and is
    /// used e.g. for interning the data of string literals.
    Indirect {
        allocation: Box<[u8]>,
        align: Align,
        ty: Ty<'tcx>,
    }
}

#[derive(Hash, Clone, Copy, PartialEq, Eq)]
pub struct Global<'tcx>(pub &'tcx GlobalKind<'tcx>);

impl<'tcx> Global<'tcx> {
    pub fn from_definition(tcx: TyCtxt<'tcx>, def: DefId) -> Self {
        let node = tcx.node_by_def_id(def);
        match node {
            ast::Node::Item(ast::Item { kind: ast::ItemKind::Function(..), .. }) =>
                tcx.intern_global(GlobalKind::Function { def }),
            ast::Node::Item(ast::Item { kind: ast::ItemKind::GlobalVar(glob), .. })
                if !glob.constant => {
                let ty = tcx.type_of(def);
                let initializer = glob.init
                    .map(|expr| Const::try_val_from_simple_expr(tcx, ty, expr))
                    .flatten()
                    .unwrap_or_else(|| Const::zeroed(tcx, ty));
                tcx.intern_global(GlobalKind::Static { def, initializer })
            }
            ast::Node::Variant(..) => tcx.intern_global(GlobalKind::EnumVariant { def }),
            _ => panic!("unexpected Node {node:?} in Global::from_definition"),
        }
    }

    pub fn from_array_with_ty(
        tcx: TyCtxt<'tcx>,
        data: &[u8],
        element_ty: Ty<'tcx>,
        allocation_ty: Ty<'tcx>
    ) -> Self {
        let array_ty = Ty::new_array(tcx, element_ty, Const::new_size(tcx, data.len() as u64));
        let layout = tcx.layout_of(array_ty).unwrap();
        let allocation = data.to_vec().into_boxed_slice();
        tcx.intern_global(GlobalKind::Indirect {
            allocation,
            align: layout.align,
            ty: allocation_ty
        })
    }
}

impl<'tcx> std::fmt::Debug for Global<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { 
        match self {
            Global(GlobalKind::Function { def } | GlobalKind::Static { def, .. }) => {
                let ident = context::with_tcx(|tcx| {
                    let node = tcx.expect("pretty-print IR Operand in valid TCX context").node_by_def_id(*def);
                    if let ast::Node::Item(item) = node {
                        return item.ident();
                    } else {
                        panic!("non-item in definition");
                    };
                });

                write!(f, "{}", ident.symbol.get())
            }
            Global(GlobalKind::EnumVariant { def }) => {
                let xxx = context::with_tcx(|tcx| {
                    let (ty, _) = tcx
                        .expect("pretty-print IR Operand in valid TCX context")
                        .enum_variant(*def);
                    format!("<value> as {ty}")
                });
                f.write_str(&xxx)
            },
            Global(GlobalKind::Indirect { allocation, .. }) =>
                // TODO: maybe represent it's layout too
                write!(f, "{:?}", allocation.escape_ascii())
        }
    }
}

#[derive(Debug)]
pub struct Enum<'tcx> {
    pub def: DefId,
    pub name: Symbol,
    pub representation: Option<Ty<'tcx>>,
    pub variants: Vec<DefId>,
}

impl<'tcx> Enum<'tcx> {
    pub fn new(
        def: DefId,
        name: Symbol,
        representation: Option<Ty<'tcx>>,
        variants: Vec<DefId>,
    ) -> Self {
        Self { def, name, representation, variants }
    }
}

impl<'tcx> std::hash::Hash for Enum<'tcx> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.def.hash(state);
        self.name.hash(state);
    }
}

impl<'tcx> PartialEq for Enum<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.def == other.def
    }
}

impl<'tcx> Eq for Enum<'tcx> {}

#[derive(Default, Debug, Clone, Copy)]
pub enum VariantDescriminant<'tcx> {
    #[default]
    Lazy,
    Uncalculated(Const<'tcx>),
    Calculated(i128),
}

#[derive(Debug)]
pub struct VariantDef<'tcx> {
    pub def: DefId,
    pub symbol: Symbol,
    pub discriminant: Cell<VariantDescriminant<'tcx>>
}

impl<'tcx> VariantDef<'tcx> {
    pub fn discriminant(&self) -> i128 {
        let VariantDescriminant::Calculated(calc) = self.discriminant.get() else {
            panic!("uncalculated discriminant: call layout_of(enum) first")
        };
        calc
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParamTy {
    pub index: usize,
    pub symbol: Symbol
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum TyKind<'tcx> {
    Bool,
    Void,
    Char,
    String,
    Int(Integer, bool),
    Float(Float),
    Adt(AdtDef<'tcx>, &'tcx [GenericArg<'tcx>]),
    Enum(Enum<'tcx>),
    Refrence(Ty<'tcx>),
    Range(Ty<'tcx>, bool),
    Slice(Ty<'tcx>),
    Array(Ty<'tcx>, Const<'tcx>),
    Tuple(&'tcx [Ty<'tcx>]),
    UinstantiatedTuple,
    DynamicArray(Ty<'tcx>),
    Function(DefId, &'tcx [GenericArg<'tcx>]),
    Param(ParamTy),
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
        context::with_tcx(|tcx| {
            let tcx = *tcx.unwrap();
            let ty = self.lift(tcx).unwrap();
            let string = ty.print(tcx);
            write!(f, "{string}")
        })
    }
}

impl<'tcx> FromCycleError<'tcx> for Ty<'tcx> {
    fn from_cycle_error(tcx: TyCtxt<'tcx>) -> Self {
        Ty::new_error(tcx)
    }
}

impl<'tcx> AsType<'tcx> for Ty<'tcx> {
    fn as_type(&self) -> Option<Ty<'tcx>> {
        Some(*self)
    }
}

impl<'tcx> Ty<'tcx> {
    pub fn new_array(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, cnst: Const<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Array(ty, cnst))
    }

    pub fn new_slice(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Slice(ty))
    }

    pub fn new_dyn_array(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::DynamicArray(ty))
    }

    pub fn new_refrence(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Refrence(ty))
    }

    pub fn new_error(tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Err)
    }

    pub fn new_int(tcx: TyCtxt<'tcx>, int: Integer, signed: bool) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Int(int, signed))
    }

    pub fn new_float(tcx: TyCtxt<'tcx>, float: Float) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Float(float))
    }

    pub fn new_enum(tcx: TyCtxt<'tcx>, enm: Enum<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Enum(enm))
    }

    pub fn new_adt(tcx: TyCtxt<'tcx>, adt: AdtDef<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Adt(adt, adt.def().normalized_generics(tcx)))
    }

    pub fn new_function(tcx: TyCtxt<'tcx>, def: DefId) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Function(def, def.normalized_generics(tcx)))
    }

    pub fn new_range(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, inclusive: bool) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Range(ty, inclusive))
    }

    pub fn new_uninstantiated_tuple(tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::UinstantiatedTuple)
    }

    pub fn new_tuple(tcx: TyCtxt<'tcx>, tys: &'tcx [Ty<'tcx>]) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Tuple(tys))
    }

    pub fn new_param(tcx: TyCtxt<'tcx>, symbol: Symbol, index: usize) -> Ty<'tcx> {
        tcx.intern_ty(TyKind::Param(ParamTy {
            symbol,
            index
        }))
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
            Ty(TyKind::Array(_, Const(ConstKind::Infer))) => true,
            _ => false
        }
    }

    pub fn print(self, tcx: TyCtxt<'tcx>) -> String {
        /*
        match self.0 {
            TyKind::Never => write!(f, "never"),
            TyKind::Int(integer, signed) => {
                let sym = integer.to_symbol(*signed);
                f.write_str(sym.get())
            },
            TyKind::Bool => f.write_str("bool"),
            TyKind::Void => f.write_str("void"),
            TyKind::Char => f.write_str("char"),
            TyKind::String => f.write_str("string"),
            TyKind::Float(Float::F32) => f.write_str("float"),
            TyKind::Float(Float::F64) => f.write_str("double"),
            TyKind::Adt(adt, generics) => {
                f.write_str(adt.name().get())?;
                if generics.len() > 0 {
                    f.write_str("<")?;
                    for (idx, arg) in generics.iter().enumerate() {
                        write!(f, "{arg}")?;
                        if idx != generics.len() - 1 {        
                            f.write_str(", ")?;
                        }
                    }
                    f.write_str(">")?;

                }
                Ok(())
            },
            TyKind::Enum(enm) => f.write_str(enm.name.get()),
            TyKind::Refrence(ty) => write!(f, "{ty}*"),
            TyKind::Slice(ty) => write!(f, "{ty}[]"),
            TyKind::Array(ty, cap) => write!(f, "{ty}[{cap:?}]"),
            TyKind::DynamicArray(ty) => write!(f, "{ty}[..]"),
            // TODO: query function name and display it here
            TyKind::Function(def_id, generics) => write!(f, "function"),
            TyKind::Range(ty, _) => write!(f, "Range<{ty}>"),
            TyKind::Param(param_ty) => write!(f, "{}", param_ty.symbol),
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
            TyKind::UinstantiatedTuple => f.write_str("tuple"),
            TyKind::Err => write!(f, "Err"),
        }
        */
        todo!()
    }
}

impl Symbol {
    pub fn is_primitive_ty<'tcx>(&self) -> bool {
        match *self {
            sym::bool => true,
            sym::void => true,
            sym::byte => true,
            sym::sbyte => true,
            sym::short => true,
            sym::ushort => true,
            sym::int => true,
            sym::uint => true,
            sym::long => true,
            sym::ulong => true,
            sym::nint => true,
            sym::nuint => true,
            sym::char => true,
            sym::string => true,
            sym::float => true,
            sym::double => true,
            sym::tuple => true,
            _ => false
        }
    }

    pub fn get_primitive_ty<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Option<Ty<'tcx>> {
        match *self {
            sym::bool => Some(tcx.basic_types.bool),
            sym::void => Some(tcx.basic_types.void),
            sym::byte => Some(tcx.basic_types.byte),
            sym::sbyte => Some(tcx.basic_types.sbyte),
            sym::short => Some(tcx.basic_types.short),
            sym::ushort => Some(tcx.basic_types.ushort),
            sym::int => Some(tcx.basic_types.int),
            sym::uint => Some(tcx.basic_types.uint),
            sym::long => Some(tcx.basic_types.long),
            sym::ulong => Some(tcx.basic_types.ulong),
            sym::nint => Some(tcx.basic_types.nint),
            sym::nuint => Some(tcx.basic_types.nuint),
            sym::char => Some(tcx.basic_types.char),
            sym::string => Some(tcx.basic_types.string),
            sym::float => Some(tcx.basic_types.float),
            sym::double => Some(tcx.basic_types.double),
            sym::tuple => Some(Ty::new_uninstantiated_tuple(tcx)),

            _ => None
        }
    }
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub enum Integer {
    I8,
    I16,
    I32,
    I64,
    ISize
}

impl Integer {
    pub fn fit_signed(value: i128) -> Option<Self> {
        use Integer::*;
        match value {
            -0x0000_0000_0000_0080..=0x0000_0000_0000_007f => Some(I8),
            -0x0000_0000_0000_8000..=0x0000_0000_0000_7fff => Some(I16),
            -0x0000_0000_8000_0000..=0x0000_0000_7fff_ffff => Some(I32),
            -0x8000_0000_0000_0000..=0x7fff_ffff_ffff_ffff => Some(I64),
            _ => None,
        }

    }

    pub fn fit_unsigned(value: u64) -> Self {
        use Integer::*;
        match value {
            0..=0x0000_00ff => I8,
            0..=0x0000_ffff => I16,
            0..=0xffff_ffff => I32,
            _ => I64
        }
    }

    pub fn size(&self, provider: &impl DataLayoutExt) -> Size {
        let data_layout = provider.data_layout();
        use Integer::*;
        match self {
            I8 => Size::from_bits(8),
            I16 => Size::from_bits(16),
            I32 => Size::from_bits(32),
            I64 => Size::from_bits(64),
            ISize => data_layout.ptr_size
        }
    }

    pub fn align(&self, provider: &impl DataLayoutExt) -> Align {
        let data_layout = provider.data_layout();
        use Integer::*;
        match self {
            I8 => data_layout.i8_align,
            I16 => data_layout.i16_align,
            I32 => data_layout.i32_align,
            I64 => data_layout.i64_align,
            ISize => data_layout.ptr_align
        }
    }

    pub fn normalize(&self, provider: &impl DataLayoutExt) -> Self {
        let Integer::ISize = self else {
            return *self;
        };
        let data_layout = provider.data_layout();
        match data_layout.ptr_size.in_bytes {
            1 => Integer::I8,
            2 => Integer::I16,
            4 => Integer::I32,
            8 => Integer::I64,
            _ => unreachable!("target has invalid ISize")
        }
    }

    fn convert<'a>(&self, signedness: bool, provider: &impl DataLayoutExt, value: impl Num + ToPrimitive, eraser: Eraser<'a>) -> Erased<'a> {
        macro_rules! expect_and_convert {
            ($expr:expr) => {{
                return eraser.erase(($expr).expect("value corresponds to type"));
            }};
        }
        match self {
            Integer::I8 if signedness => expect_and_convert!(value.to_i8()),
            Integer::I16 if signedness => expect_and_convert!(value.to_i16()),
            Integer::I32 if signedness => expect_and_convert!(value.to_i32()),
            Integer::I64 if signedness => expect_and_convert!(value.to_i64()),

            Integer::I8 => expect_and_convert!(value.to_u8()),
            Integer::I16 => expect_and_convert!(value.to_u16()),
            Integer::I32 => expect_and_convert!(value.to_u32()),
            Integer::I64 => expect_and_convert!(value.to_u64()),

            Integer::ISize =>
                self.normalize(provider)
                    .convert(signedness, provider, value, eraser)
        }

    }

    fn downcast_unsized<'a, T: std::ptr::Pointee<Metadata = std::ptr::DynMetadata<T>> + ?Sized + 'static>(&self, signedness: bool, erased: Erased<'a>) -> Option<&'a T> {
        // FIXME: here we once again run into problems with ISize types. We'd need a tcx to pass
        // through the `downcast_unsized` system in order to obtain a TargetDataLayout here.
        // Passing this tcx is not possible at the moment as the `downcast_unsized` is vital for
        // `Debug` formatting and (`context::enter` does not work because of lifetime recstrictions).
        macro_rules! hack_normalize_from_data_size {
            (signed $trait:ty, $erased:expr) => {
                match $erased.0.len() {
                    1 => downcast_sized_knowingly::<T, $trait, i8>(erased),
                    2 => downcast_sized_knowingly::<T, $trait, i16>(erased),
                    4 => downcast_sized_knowingly::<T, $trait, i32>(erased),
                    8 => downcast_sized_knowingly::<T, $trait, i64>(erased),
                    _ => unreachable!("non-sensible ISize"),
                }
            };
            (unsigned $trait:ty, $erased:expr) => {
                match $erased.0.len() {
                    1 => downcast_sized_knowingly::<T, $trait, u8>($erased),
                    2 => downcast_sized_knowingly::<T, $trait, u16>($erased),
                    4 => downcast_sized_knowingly::<T, $trait, u32>($erased),
                    8 => downcast_sized_knowingly::<T, $trait, u64>($erased),
                    _ => unreachable!("non-sensible ISize"),
                }
            };
        }
        macro_rules! downcast_for_every_int {
            ($trait:ty) => { 
                match self {
                    Integer::I8 if signedness =>
                        downcast_sized_knowingly::<T, $trait, i8>(erased),
                    Integer::I16 if signedness =>
                        downcast_sized_knowingly::<T, $trait, i16>(erased),
                    Integer::I32 if signedness =>
                        downcast_sized_knowingly::<T, $trait, i32>(erased),
                    Integer::I64 if signedness =>
                        downcast_sized_knowingly::<T, $trait, i64>(erased),
                    Integer::ISize if signedness =>
                        hack_normalize_from_data_size!(signed $trait, erased),

                    Integer::I8 =>
                        downcast_sized_knowingly::<T, $trait, u8>(erased),
                    Integer::I16 =>
                        downcast_sized_knowingly::<T, $trait, u16>(erased),
                    Integer::I32 =>
                        downcast_sized_knowingly::<T, $trait, u32>(erased),
                    Integer::I64 =>
                        downcast_sized_knowingly::<T, $trait, u64>(erased),
                    Integer::ISize =>
                        hack_normalize_from_data_size!(unsigned $trait, erased),
                }
            };
        }
        let id = TypeId::of::<T>();
        if id == TypeId::of::<dyn ToPrimitive>() {
            return downcast_for_every_int!(dyn ToPrimitive);
        } else if id == TypeId::of::<dyn std::fmt::Debug>() {
            return downcast_for_every_int!(dyn std::fmt::Debug);
        }
        None
    }

    pub fn to_symbol(&self, signedness: bool) -> Symbol {
        use Integer::*;
        match (self, signedness) {
            (I8, false) => sym::byte,
            (I16, false) => sym::ushort,
            (I32, false) => sym::uint,
            (I64, false) => sym::ulong,
            (ISize, false) => sym::nuint,

            (I8, true) => sym::sbyte,
            (I16, true) => sym::short,
            (I32, true) => sym::int,
            (I64, true) => sym::long,
            (ISize, true) => sym::nint,
        }
    }

}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub enum Float {
    F32,
    F64
}

impl Float {
    pub fn size(&self) -> Size {
        match self {
            Float::F32 => Size::from_bits(32),
            Float::F64 => Size::from_bits(64),
        }
    }

    pub fn align(&self, provider: &impl DataLayoutExt) -> Align {
        let data_layout = provider.data_layout();
        match self {
            Float::F32 => data_layout.f32_align,
            Float::F64 => data_layout.f64_align,
        }
    }

    fn downcast_unsized<'a, T: std::ptr::Pointee<Metadata = std::ptr::DynMetadata<T>> + ?Sized + 'static>(&self, erased: Erased<'a>) -> Option<&'a T> {
        macro_rules! downcast_for_every_float {
            ($trait:ty) => { 
                match self {
                    Float::F32 =>
                        downcast_sized_knowingly::<T, $trait, f32>(erased),
                    Float::F64 =>
                        downcast_sized_knowingly::<T, $trait, f64>(erased),
                }
            };
        }
        let id = TypeId::of::<T>();
        if id == TypeId::of::<dyn ToPrimitive>() {
            return downcast_for_every_float!(dyn ToPrimitive);
        } else if id == TypeId::of::<dyn std::fmt::Debug>() {
            return downcast_for_every_float!(dyn std::fmt::Debug);
        }
        None
    }
}

pub struct BasicTypes<'tcx> {
    pub bool: Ty<'tcx>,
    pub void: Ty<'tcx>,
    pub byte: Ty<'tcx>,
    pub sbyte: Ty<'tcx>,
    pub short: Ty<'tcx>,
    pub ushort: Ty<'tcx>,
    pub int: Ty<'tcx>,
    pub uint: Ty<'tcx>,
    pub long: Ty<'tcx>,
    pub ulong: Ty<'tcx>,
    pub nint: Ty<'tcx>,
    pub nuint: Ty<'tcx>,
    pub float: Ty<'tcx>,
    pub double: Ty<'tcx>,
    pub char: Ty<'tcx>,
    pub string: Ty<'tcx>,
    pub never: Ty<'tcx>,
}

impl<'tcx> BasicTypes<'tcx> {
    pub fn alloc(interners: &Interners<'tcx>) -> Self {
        use Integer::*;
        use Float::*;
        use TyKind::{Bool, Char, String, Void, Never, Int};
        let mk = |ty| interners.intern_ty(ty);

        Self {
            bool: mk(Bool),
            void: mk(Void),
            char: mk(Char),
            string: mk(String),
            never: mk(Never),
            
            byte: mk(Int(I8, false)),
            sbyte: mk(Int(I8, true)),
            short: mk(Int(I16, true)),
            ushort: mk(Int(I16, false)),
            int: mk(Int(I32, true)),
            uint: mk(Int(I32, false)),
            long: mk(Int(I64, true)),
            ulong: mk(Int(I64, false)),
            nint: mk(Int(ISize, true)),
            nuint: mk(Int(ISize, false)),

            float: mk(TyKind::Float(F32)),
            double: mk(TyKind::Float(F64)),
        }
    }
}

impl<'tcx> Interners<'tcx> {
    fn intern_ty(&self, kind: TyKind<'tcx>) -> Ty<'tcx> {
        use crate::context::InternerExt;
        let interner = &self.tys;
        Ty(interner.intern(kind, |kind| {
            self.arena.alloc(kind)
        }))
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Endianness {
    Little, Big
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Align {
    pow2: u8
}

impl Align {
    const ONE: Align = Align::from_bytes(1);
    const LLVM_MAX_ALIGN: u32 = 29;

    pub const fn from_bits(bits: u64) -> Self {
        Self::from_bytes((bits + 7) / 8)
    }

    pub const fn from_bytes(size: u64) -> Self {
        // TODO: make this function fallible when users can request specific type alignment
        let zeros = size.trailing_zeros();
        if size != (1 << zeros) {
            panic!("non power of 2 alignment");
        }
        if zeros > Self::LLVM_MAX_ALIGN {
            panic!("to big alignment: > 536870912");
        }
        Self { pow2: zeros as u8 }
    }

    pub const fn in_bytes(&self) -> u64 {
        1 << (self.pow2 as u64)
    }
}

impl std::fmt::Debug for Align {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Align({})", 1 << self.pow2)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Size {
    pub in_bytes: u64
}

impl Size {
    pub const fn from_bits(bits: u64) -> Self {
        Size { in_bytes: (bits + 7) / 8 }
    }

    pub fn from_bytes(bytes: impl TryInto<u64>) -> Self {
        Size { in_bytes: bytes.try_into().map_err(|_| "u64 conversion failure in Size::from_bytes").unwrap() }
    }

    pub const fn align_up(&self, align: Align) -> u64 {
        let align_mask = align.in_bytes() - 1;
        if self.in_bytes & align_mask == 0 {
            self.in_bytes // already aligned
        } else {
            // FIXME: Replace with .expect, once `Option::expect` is const.
            if let Some(aligned) = (self.in_bytes | align_mask).checked_add(1) {
                aligned
            } else {
                panic!("attempt to add with overflow")
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Fields {
    /// For Scalar types being backed exclusively BackendRepr::Scalar
    Scalar,
    /// For fix-size Array types
    Array {
        stride: u64,
        count: u64
    },
    /// Including but not limited to structure types, zst types, functions, etc
    Struct {
        fields: IndexVec<FieldIdx, u64>
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Scalar {
    Int(Integer, bool),
    Float(Float),
    Pointer
}

impl Scalar {
    pub fn align(&self, provider: &impl DataLayoutExt) -> Align {
        match self {
            Scalar::Int(int, _) => int.align(provider),
            Scalar::Float(float) => float.align(provider),
            Scalar::Pointer => {
                let data_layout = provider.data_layout();
                data_layout.ptr_align
            }
        }
    }

    pub fn size(&self, provider: &impl DataLayoutExt) -> Size {
        match self {
            Scalar::Int(int, _) => int.size(provider),
            Scalar::Float(float) => float.size(),
            Scalar::Pointer => {
                let data_layout = provider.data_layout();
                data_layout.ptr_size
            }
        }
    }

    pub fn get_type<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        match *self {
            Scalar::Int(int, signed) =>
                Ty::new_int(tcx, int, signed),
            Scalar::Float(float) =>
                Ty::new_float(tcx, float),
            Scalar::Pointer =>
                Ty::new_refrence(tcx, tcx.basic_types.void)
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BackendRepr {
    Scalar(Scalar),
    ScalarPair(Scalar, Scalar),
    Memory
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct LayoutData {
    pub size: Size,
    pub align: Align,
    pub fields: Fields,
    pub repr: BackendRepr
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyLayoutTuple<'tcx> {
    pub ty: Ty<'tcx>,
    pub layout: Layout<'tcx>
}

impl<'tcx> std::ops::Deref for TyLayoutTuple<'tcx> {
    type Target = LayoutData;

    fn deref(&self) -> &Self::Target {
        self.layout.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Layout<'tcx>(pub &'tcx LayoutData);

impl<'tcx> std::ops::Deref for Layout<'tcx> {
    type Target = LayoutData;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'tcx> Layout<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, size: Size, align: Align, fields: Fields, repr: BackendRepr) -> Self {
        tcx.intern_layout(LayoutData { size, align, fields, repr })
    }
}

#[derive(Debug, Clone, Copy)]
pub enum LayoutError {
    /// The Ty was erroneous to begin with (TyKind::Error), no sensible layout can be computed
    Erroneous,
    /// A struct is too big for the backend to handle, or an enum has to many variants for the
    /// representation chosen
    TooBig,
    /// For the type provided no sensible layout can be computed as it is not specific. This can
    /// happen for `Param` or `Infer` types.
    Inspecific,
    /// The Ty's layout is cyclic: Ty contains itself without any indirection
    Cyclic
}

impl<'tcx> FromCycleError<'tcx> for Result<TyLayoutTuple<'tcx>, LayoutError> {
    fn from_cycle_error(_tcx: TyCtxt<'tcx>) -> Self {
        Result::Err(LayoutError::Cyclic)
    }
}

struct LayoutCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    data_layout: TargetDataLayout
}

impl<'tcx> LayoutCtxt<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            data_layout: *tcx.data_layout()
        }
    }

    fn layout_for_array_like(&self, dynamic_sized: bool) -> Layout<'tcx> {
        let data_layout = self.data_layout();
        let align = data_layout.ptr_align;
        let ptr_size = data_layout.ptr_size;

        let nuint = Scalar::Int(Integer::ISize.normalize(self), false);

        let mut fields = IndexVec::new();
        fields.push(0);
        fields.push(ptr_size.in_bytes);
        if dynamic_sized {
            fields.push(ptr_size.in_bytes * 2);
        }

        Layout::new(
            self.tcx,
            Size::from_bytes(ptr_size.in_bytes * (2 + dynamic_sized as u64)),
            align,
            Fields::Struct { fields },
            if !dynamic_sized {
                BackendRepr::ScalarPair(Scalar::Pointer, nuint)
            } else {
                BackendRepr::Memory
            }
        )
    }

    fn layout_for_integer(&self, integer: Integer, signedness: bool) -> Layout<'tcx> {
        let size = integer.size(self);
        let align = integer.align(self);
        Layout::new(
            self.tcx,
            size,
            align,
            Fields::Scalar,
            BackendRepr::Scalar(Scalar::Int(integer, signedness))
        )
    }

    fn layout_for_float(&self, float: Float) -> Layout<'tcx> {
        let size = float.size();
        let align = float.align(self);
        Layout::new(
            self.tcx,
            size,
            align,
            Fields::Scalar,
            BackendRepr::Scalar(Scalar::Float(float))
        )
    }

    fn layout_for_struct(&self, fields: IndexVec<FieldIdx, Layout<'tcx>>) -> Layout<'tcx> {
        let mut align = Align::ONE;
        let mut offset = 0;
        let mut offsets = IndexVec::new();
        let mut size = 0;
        for field in &fields {
            size += field.size.in_bytes;
            align = std::cmp::max(align, field.align);
            if offset % field.align.in_bytes() != 0 {
                offset = align_up(offset, field.align);
            }
            offsets.push(offset);
        }

        let mut repr = BackendRepr::Memory;

        let mut fiter = fields.iter();
        match (fiter.next(), fiter.next(), fiter.next()) {
            (Some(field), None, None) => {
                match field.repr {
                    frepr @ BackendRepr::Scalar(..) => repr = frepr,
                    frepr @ BackendRepr::ScalarPair(..) => repr = frepr,
                    _ => ()
                }
            }
            (Some(field1), Some(field2), None) if let BackendRepr::Scalar(scalar1) = field1.repr && let BackendRepr::Scalar(scalar2) = field2.repr =>
                repr = BackendRepr::ScalarPair(scalar1, scalar2),
            _ => ()
        }


        Layout::new(
            self.tcx,
            Size::from_bytes(size),
            align,
            Fields::Struct { fields: offsets },
            repr
        )
    }

    fn layout_for_array(&self, ty: Ty<'tcx>, count: u64) -> Result<Layout<'tcx>, LayoutError> {
        let tuple = match self.tcx.layout_of(ty) {
            Ok(tuple) => tuple,
            Err(LayoutError::Cyclic) => {
                // A type refrencing itself like this should only be possible using type aliases 
                // (NOTE: in the future maybe through compile-time meta programming)
                // TODO: once type aliases become a thing: unintern the Ty IR into it's AST Node
                todo!("type alias cyclic types");
            }
            Err(err) => return Err(err)
        };
        let align = tuple.layout.align;
        Ok(Layout::new(
            self.tcx,
            Size { in_bytes: count * tuple.layout.size.in_bytes },
            align,
            Fields::Array { stride: tuple.layout.size.in_bytes, count },
            BackendRepr::Memory
        ))
    }

    fn layout_for_enum(&self, enm: &'tcx Enum<'tcx>) -> Result<Layout<'tcx>, LayoutError> {
        if let Some(Ty(TyKind::Err)) = enm.representation {
            return Err(LayoutError::Erroneous);
        }
        let mut prev_discriminant: i128 = 0;
        let mut min_discriminant = i128::MAX;
        let mut max_discriminant = i128::MIN;
        let mut erroneous = false;
        for variant_id in &enm.variants {
            let (_, variant) = self.tcx.enum_variant(*variant_id);

            let discriminant = match variant.discriminant.get() {
                VariantDescriminant::Lazy => prev_discriminant + 1, 
                VariantDescriminant::Uncalculated(cnst) if let Const(ConstKind::Err) = cnst => {
                    erroneous = true;
                    continue;
                }
                VariantDescriminant::Uncalculated(cnst) => {
                    cnst.downcast_unsized::<dyn ToPrimitive>()
                        .unwrap()
                        .to_i128()
                        .unwrap()
                }
                VariantDescriminant::Calculated(..) => unreachable!()
            };
            variant.discriminant.set(VariantDescriminant::Calculated(discriminant));
            min_discriminant = min_discriminant.min(discriminant);
            max_discriminant = max_discriminant.max(discriminant);

            prev_discriminant = discriminant;
        }
        if erroneous {
            return Err(LayoutError::Erroneous);
        }

        let repr = match enm.representation {
            Some(repr) => {
                let layout = self.tcx.layout_of(repr)?;
                let BackendRepr::Scalar(Scalar::Int(int, signed)) = layout.repr else {
                    unreachable!()
                };

                if min_discriminant < 0 && !signed {
                    let ast::Node::Item(item) = self.tcx.node_by_def_id(enm.def) else { unreachable!() };
                    Message::error(format!("some variants of enum `{}` have negative discriminats", enm.name))
                        .at(item.span)
                        .note(format!("specifiy a signed represenation, using `enum {}: <type>`", enm.name))
                        .push(self.tcx.diagnostics());
                    return Err(LayoutError::TooBig);
                }
                
                let fit_fn = |value: i128| {
                    if signed {
                        Integer::fit_signed(value).unwrap()
                    } else {
                        Integer::fit_unsigned(value as u64)
                    }
                };

                let min_size = fit_fn(min_discriminant).size(self).max(fit_fn(max_discriminant).size(self));
                if int.size(self) < min_size {
                    let ast::Node::Item(item) = self.tcx.node_by_def_id(enm.def) else { unreachable!() };
                    Message::error(format!("all variants in enum `{}` don't fit into representation of {repr}", enm.name))
                        .at(item.span)
                        .note(format!("specifiy a bigger represenation, using `enum {}: <type>`", enm.name))
                        .push(self.tcx.diagnostics());
                    return Err(LayoutError::TooBig);
                }

                repr
            }
            None if enm.variants.len() > 0 => {
                let a = Integer::fit_signed(min_discriminant).unwrap();
                let Some(b) = Integer::fit_signed(max_discriminant) else {
                    let ast::Node::Item(item) = self.tcx.node_by_def_id(enm.def) else { unreachable!() };
                    Message::error(format!("variants of enum `{}` don't fit into a sigend integer", enm.name))
                        .at(item.span)
                        .note(format!("specifiy a specific represenation, using `enum {}: <type>`", enm.name))
                        .push(self.tcx.diagnostics());
                    return Err(LayoutError::TooBig);
                };
                let size = a.size(self).max(b.size(self));

                if size <= Integer::I32.size(self) {
                    self.tcx.basic_types.int
                } else {
                    Ty::new_int(self.tcx, Integer::I64, true)
                }
            }
            None => self.tcx.basic_types.int
        };

        Ok(self.tcx.layout_of(repr)?.layout)
    }

    fn calculate_layout_for_ty(&self, ty: Ty<'tcx>) -> Result<TyLayoutTuple<'tcx>, LayoutError> {
        let layout = match ty {
            Ty(TyKind::Void) | Ty(TyKind::Never) =>
                Layout::new(
                    self.tcx,
                    Size::from_bytes(0),
                    Align::ONE,
                    Fields::Struct { fields: IndexVec::new() },
                    BackendRepr::Memory
                ),
            Ty(TyKind::Bool) =>
                self.tcx.layout_of(self.tcx.basic_types.byte)?.layout,
            Ty(TyKind::Char) =>
                self.tcx.layout_of(self.tcx.basic_types.uint)?.layout,
            Ty(TyKind::String) =>
                self.layout_for_array_like(false),
            Ty(TyKind::Int(integer, signedness)) =>
                self.layout_for_integer(*integer, *signedness),
            Ty(TyKind::Float(float)) =>
                self.layout_for_float(*float),
            Ty(TyKind::Enum(enm)) => 
                self.layout_for_enum(enm)?,
            Ty(TyKind::Adt(adt, generics)) => {
                match adt {
                    AdtDef(AdtKind::Struct(strct)) => {
                        let mut fields = IndexVec::new();
                        for field in strct.fields.iter() {
                            let tuple = match self.tcx.layout_of(self.tcx.type_of(field.def).instantiate(*generics, self.tcx)) {
                                Ok(tuple) => tuple,
                                err @ Err(LayoutError::Cyclic) => {
                                    let ast::Node::Item(item) = self.tcx.node_by_def_id(strct.def) else { unreachable!() };
                                    let ast::Node::FieldDef(def) = self.tcx.node_by_def_id(field.def) else { unreachable!() };
                                    self.report_cycle_error(item.ident().span, def.ty.span, format_args!("struct `{}`", strct.name.get()));
                                    return err;
                                }
                                err @ Err(_) => return err
                            };
                            fields.push(tuple.layout); 
                        }
                        self.layout_for_struct(fields)
                    }
                    AdtDef(AdtKind::Union) => todo!(),
                }
            }
            Ty(TyKind::Refrence(..)) => {
                let data_layout = self.data_layout();
                Layout::new(
                    self.tcx,
                    data_layout.ptr_size,
                    data_layout.ptr_align,
                    Fields::Scalar,
                    BackendRepr::Scalar(Scalar::Pointer)
                )
            }
            Ty(TyKind::Range(..)) => todo!(),
            Ty(TyKind::Slice(_)) =>
                self.layout_for_array_like(false),
            Ty(TyKind::Array(base, count)) => {
                let count = count.downcast_unsized::<dyn ToPrimitive>()
                    .map(|val| val.to_u64())
                    .flatten()
                    .unwrap();
                self.layout_for_array(*base, count)?
            }
            Ty(TyKind::Tuple(tys)) => {
                let mut fields = IndexVec::new();
                for ty in tys.iter() {
                    let tuple = match self.tcx.layout_of(*ty) {
                        Ok(tuple) => tuple,
                        Err(LayoutError::Cyclic) => {
                            // A type refrencing itself like this should only be possible using type aliases 
                            // (NOTE: in the future maybe through compile-time meta programming)
                            // TODO: once type aliases become a thing: unintern the Ty IR into it's AST Node
                            todo!("type alias cyclic types");
                        }
                        err @ Err(_) => return err
                    };
                    fields.push(tuple.layout); 
                }
                self.layout_for_struct(fields)
            },
            Ty(TyKind::DynamicArray(_)) =>
                self.layout_for_array_like(true),
            Ty(TyKind::Function(..)) => 
                Layout::new(
                    self.tcx,
                    Size::from_bytes(0),
                    Align::ONE,
                    Fields::Struct { fields: IndexVec::new() },
                    BackendRepr::Memory
                ),
            Ty(TyKind::Param(_)) => return Err(LayoutError::Inspecific),
            Ty(TyKind::UinstantiatedTuple) => return Err(LayoutError::Inspecific),
            Ty(TyKind::Err) => return Err(LayoutError::Erroneous),
        };
        Ok(TyLayoutTuple { ty, layout })
    }

    fn report_cycle_error(&self, item_span: Span, recursion_span: Span, kind: std::fmt::Arguments) {
        Message::error(format!("infinite size {} contains itself without indirection", kind))
            .at(item_span)
            .hint(format!("recursion without indirection"), recursion_span)
            .push(self.tcx.diagnostics());
    }
}

impl<'tcx> DataLayoutExt for LayoutCtxt<'tcx> {
    fn data_layout(&self) -> &TargetDataLayout {
        &self.data_layout
    }
}

pub fn layout_of<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Result<TyLayoutTuple<'tcx>, LayoutError> {
    let ctxt = LayoutCtxt::new(tcx);
    ctxt.calculate_layout_for_ty(ty)
}

#[inline]
const fn align_up(addr: u64, align: Align) -> u64 {
    let align_mask = align.in_bytes() - 1;
    if addr & align_mask == 0 {
        addr // already aligned
    } else {
        // FIXME: Replace with .expect, once `Option::expect` is const.
        if let Some(aligned) = (addr | align_mask).checked_add(1) {
            aligned
        } else {
            panic!("attempt to add with overflow")
        }
    }
}
