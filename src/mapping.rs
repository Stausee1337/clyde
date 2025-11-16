use std::cell::OnceCell;

use crate::{context::TyCtxt, type_ir::{Const, ConstKind, GenericArg, GenericArgKind, Ty, TyKind}};


pub trait Mapper<'tcx>: Sized {
    fn tcx(&self) -> TyCtxt<'tcx>;

    fn map_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
        ty_map_recurse_impl(ty, self)
    }

    fn map_const(&mut self, cnst: Const<'tcx>) -> Const<'tcx> {
        cnst
    }
}

fn ty_map_recurse_impl<'tcx>(ty: Ty<'tcx>, handler: &mut impl Mapper<'tcx>) -> Ty<'tcx> {
    match ty {
        Ty(TyKind::Slice(ty)) => Ty::new_slice(handler.tcx(), ty.map_recurse(handler)),
        Ty(TyKind::Array(ty, cap)) => Ty::new_array(handler.tcx(), ty.map_recurse(handler), *cap),
        Ty(TyKind::DynamicArray(ty)) => Ty::new_dyn_array(handler.tcx(), ty.map_recurse(handler)),
        Ty(TyKind::Refrence(ty)) => Ty::new_refrence(handler.tcx(), ty.map_recurse(handler)),
        Ty(TyKind::Range(ty, exclusive)) => Ty::new_range(handler.tcx(), ty.map_recurse(handler), *exclusive),
        Ty(TyKind::Tuple(args)) => {
            let new_args = args 
                .iter()
                .map(|arg| arg.map_recurse(handler))
                .collect::<Vec<_>>();
            let tcx = handler.tcx();
            let args = tcx.arena.alloc_slice_copy(&new_args);
            tcx.intern_ty(TyKind::Tuple(args))
        },
        Ty(TyKind::Adt(adt_def, generics)) => {
            let new_args = generics
                .iter()
                .map(|arg| {
                    match arg.kind() {
                        GenericArgKind::Ty(ty) => GenericArg::from_ty(handler.map_ty(ty)),
                        GenericArgKind::Const(cnst) => GenericArg::from_const(handler.map_const(cnst)),
                    }
                })
                .collect::<Vec<_>>();
            let tcx = handler.tcx();
            let generics = tcx.make_args(&new_args);
            tcx.intern_ty(TyKind::Adt(*adt_def, generics))
        },
        Ty(TyKind::Function(def_id, generics)) => {
            let new_args = generics
                .iter()
                .map(|arg| {
                    match arg.kind() {
                        GenericArgKind::Ty(ty) => GenericArg::from_ty(handler.map_ty(ty)),
                        GenericArgKind::Const(cnst) => GenericArg::from_const(handler.map_const(cnst)),
                    }
                })
                .collect::<Vec<_>>();
            let tcx = handler.tcx();
            let generics = tcx.make_args(&new_args);
            tcx.intern_ty(TyKind::Function(*def_id, generics))
        },
        _ => ty
    }
}

pub trait Recursible<'tcx> {
    fn map_recurse(self, handler: &mut impl Mapper<'tcx>) -> Self;
}

impl<'tcx> Recursible<'tcx> for Ty<'tcx> {
    fn map_recurse(self, handler: &mut impl Mapper<'tcx>) -> Self {
        handler.map_ty(self)
    }
}

impl<'tcx> Recursible<'tcx> for Const<'tcx> {
    fn map_recurse(self, handler: &mut impl Mapper<'tcx>) -> Self {
        handler.map_const(self)
    }
}

impl<'tcx, T: Recursible<'tcx> + Clone> Recursible<'tcx> for &'tcx [T] {
    fn map_recurse(self, handler: &mut impl Mapper<'tcx>) -> Self {
        let result = self
            .iter()
            .map(|x| Recursible::map_recurse(x.clone(), handler))
            .collect::<Vec<_>>();
        handler.tcx().arena.alloc_slice_clone(&result)
    }
}

impl<'tcx, T: Recursible<'tcx>> Recursible<'tcx> for Option<T> {
    fn map_recurse(self, handler: &mut impl Mapper<'tcx>) -> Self {
        self.map(|x| Recursible::map_recurse(x, handler))
    }
}

impl<'tcx, T: Recursible<'tcx>> Recursible<'tcx> for OnceCell<T> {
    fn map_recurse(self, handler: &mut impl Mapper<'tcx>) -> Self {
        match self.into_inner() {
            Some(x) => {
                let cell = OnceCell::new();
                let _ = cell.set(Recursible::map_recurse(x, handler));
                cell
            }
            None => OnceCell::new()
        }
    }
}

impl<'tcx, T: Recursible<'tcx>> Recursible<'tcx> for Vec<T> {
    fn map_recurse(self, handler: &mut impl Mapper<'tcx>) -> Self {
        self
            .into_iter()
            .map(|x| Recursible::map_recurse(x, handler))
            .collect::<Vec<_>>()
    }
}

impl<'tcx, T: Recursible<'tcx>> Recursible<'tcx> for Box<[T]> {
    fn map_recurse(self, handler: &mut impl Mapper<'tcx>) -> Self {
        Recursible::map_recurse(self.into_vec(), handler)
            .into_boxed_slice()
    }
}

impl<'tcx, I: index_vec::Idx, T: Recursible<'tcx>> Recursible<'tcx> for index_vec::IndexVec<I, T> {
    fn map_recurse(self, handler: &mut impl Mapper<'tcx>) -> Self {
        self
            .into_iter()
            .map(|x| Recursible::map_recurse(x, handler))
            .collect::<index_vec::IndexVec<I, _>>()
    }
}

pub struct InstantiationMapper<'tcx> {
    tcx: TyCtxt<'tcx>,
    generics: &'tcx [GenericArg<'tcx>]
}

impl<'tcx> InstantiationMapper<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, generics: &'tcx [GenericArg<'tcx>]) -> Self {
        Self {
            tcx,
            generics
        }
    }
}

impl<'tcx> Mapper<'tcx> for InstantiationMapper<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn map_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
        match ty {
            Ty(TyKind::Param(param_ty)) => {
                let GenericArgKind::Ty(ty) = self.generics[param_ty.index as usize].kind() else {
                    unreachable!("insufficient generic arg validataion before instantiation")
                };
                ty
            }
            _ => ty_map_recurse_impl(ty, self)
        }
    }

    fn map_const(&mut self, cnst: Const<'tcx>) -> Const<'tcx> {
        let Const(ConstKind::Param(_, index)) = cnst else {
            return cnst;
        };
        let GenericArgKind::Const(cnst) = self.generics[*index].kind() else {
            unreachable!("insufficient generic arg validataion before instantiation")
        };
        cnst
    }
}

