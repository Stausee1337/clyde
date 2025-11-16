use std::fmt::{Write, Formatter, Result as PrintResult, Error as PrintError};

use crate::{analysis::resolve, context::TyCtxt, syntax::ast, type_ir::{self, Const, DebruijnIdx, Float, GenericArg, GenericArgKind, Instance, Ty, TyKind}};


pub struct PrettyPrinter<'tcx> {
    buffer: *mut dyn Write,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> PrettyPrinter<'tcx> {
    pub fn print_into_string(tcx: TyCtxt<'tcx>, f: impl FnOnce(&mut Self) -> PrintResult) -> Result<String, PrintError> {
        let mut string = String::new();
        Self::print_into_buffer(tcx, &mut string, f)?;
        Ok(string)
    }

    pub fn print_to_formatter(tcx: TyCtxt<'tcx>, formatter: &mut Formatter<'_>, f: impl FnOnce(&mut Self) -> PrintResult) -> PrintResult {
        Self::print_into_buffer(tcx, formatter, f)
    }

    fn print_into_buffer<'a>(
        tcx: TyCtxt<'tcx>,
        buffer: &'a mut dyn Write,
        f: impl FnOnce(&mut Self) -> PrintResult
    ) -> PrintResult {
        // SAFETY: buffer (and all its data) lives at least as long as the printer, which lifetime
        // is constrained to the closure
        let mut printer = PrettyPrinter {
            tcx,
            buffer: unsafe { std::mem::transmute(buffer) }
        };
        f(&mut printer)
    }

    fn print_path_recursively(
        &mut self,
        args: &'tcx type_ir::GenericArgs,
        params: &'tcx [type_ir::GenericParam],
        def: ast::DefId,
        debruijn_level: DebruijnIdx,
    ) -> PrintResult {
        let node = self.tcx.node_by_def_id(def);
        let ident = node.ident().unwrap();

        if let resolve::DefParent::Definition(parent) = self.tcx.resolutions.declarations[def].parent {
            self.print_path_recursively(args, params, parent, debruijn_level + 1)?;
            self.write_str("::")?;
        }

        self.write_str(ident.symbol.get())?;
        if let ast::Node::Item(item) = node {
            if params.len() > 0 {
                self.write_char('<')?;
                for (idx, _param) in params.iter().enumerate().filter(|(_idx, p)| p.debruijn == debruijn_level) {
                    let arg = args[idx];
                    // if let type_ir::GenericParamKind::Const = param.kind {
                    //     self.write_str("const ")?;
                    // }
                    arg.print(self)?;
                    // self.write_str(param.name.get())?;
                    if idx != params.len() - 1 {        
                        self.write_str(", ")?;
                    }
                }
                self.write_char('>')?;
            }
            
            if let ast::ItemKind::Function(..) = item.kind {
                let sig = self.tcx.fn_sig(def);
                self.write_char('(')?; //)
                for (idx, param) in sig.params.iter().enumerate() {
                    param.ty.print(self)?;
                    if idx != sig.params.len() - 1 {        
                        self.write_str(", ")?;
                    }
                }
                self.write_char(')')?; 
            }
        }
        Ok(())
    }

    pub fn print_instance(&mut self, instance: Instance<'tcx>) -> PrintResult {
        let node = self.tcx.node_by_def_id(instance.def);

        let params: &'tcx [type_ir::GenericParam] = match node {
            ast::Node::Item(..) =>
                &self.tcx.generics_of(instance.def).params,
            _ => &[]
        };
        self.print_path_recursively(instance.args, &params, instance.def, DebruijnIdx::from_raw(0))
    }
}

impl<'tcx> Write for PrettyPrinter<'tcx> {
    fn write_str(&mut self, s: &str) -> PrintResult {
        unsafe { &mut *self.buffer }.write_str(s)
    }

    fn write_char(&mut self, c: char) -> PrintResult { 
        unsafe { &mut *self.buffer }.write_char(c)
    }

    fn write_fmt(&mut self, args: std::fmt::Arguments<'_>) -> PrintResult {  
        unsafe { &mut *self.buffer }.write_fmt(args)
    }
}

pub trait Print<'tcx> {
    fn print(&self, p: &mut PrettyPrinter<'tcx>) -> PrintResult;
}

impl<'tcx> Print<'tcx> for Ty<'tcx> {
    fn print(&self, p: &mut PrettyPrinter<'tcx>) -> PrintResult {
        match self.0 {
            TyKind::Never => write!(p, "never"),
            TyKind::Int(integer, signed) => {
                let sym = integer.to_symbol(*signed);
                p.write_str(sym.get())
            },
            TyKind::Bool => p.write_str("bool"),
            TyKind::Void => p.write_str("void"),
            TyKind::Char => p.write_str("char"),
            TyKind::String => p.write_str("string"),
            TyKind::Float(Float::F32) => p.write_str("float"),
            TyKind::Float(Float::F64) => p.write_str("double"),
            TyKind::Adt(adt, args) => { 
                p.print_instance(Instance { def: adt.def(), args })
            },
            TyKind::Enum(enm) =>
                p.print_instance(Instance { def: enm.def, args: type_ir::GenericArgs::empty() }),
            TyKind::Refrence(ty) => write!(p, "{ty}*"),
            TyKind::Slice(ty) => write!(p, "{ty}[]"),
            TyKind::Array(ty, cap) => write!(p, "{ty}[{cap}]"),
            TyKind::DynamicArray(ty) => write!(p, "{ty}[..]"),
            // TODO: query function name and display it here
            &TyKind::Function(def, args) =>
                p.print_instance(Instance { def, args }),
            TyKind::Range(ty, _) => {
                p.write_str("Range<")?;
                ty.print(p)?;
                p.write_str(">")?;
                Ok(())
            },
            TyKind::Param(param_ty) => write!(p, "{}", param_ty.symbol),
            TyKind::Tuple(tys) => {
                p.write_str("tuple<")?;
                for (idx, ty) in tys.iter().enumerate() {
                    ty.print(p)?;
                    if idx != tys.len() - 1 {        
                        p.write_str(", ")?;
                    }
                }
                p.write_str(">")?;
                Ok(())
            }
            TyKind::Err => write!(p, "Err"),
        }
    }
}

impl<'tcx> Print<'tcx> for GenericArg<'tcx> {
    fn print(&self, p: &mut PrettyPrinter<'tcx>) -> PrintResult {
        match self.kind() {
            GenericArgKind::Ty(ty) => ty.print(p),
            GenericArgKind::Const(cnst) => cnst.print(p),
        }
    }
}

impl<'tcx> Print<'tcx> for Const<'tcx> {
    fn print(&self, p: &mut PrettyPrinter<'tcx>) -> PrintResult {
        match self {
            Const(&type_ir::ConstKind::Value(value)) => match value.kind {
                type_ir::ScalarKind::Signed => write!(p, "{}", value.as_signed()),
                type_ir::ScalarKind::Unsigned => write!(p, "{}", value.as_unsigned()),
                type_ir::ScalarKind::Float => write!(p, "{}", value.as_float())
            }
            Const(type_ir::ConstKind::Infer(..)) => write!(p, "_"),
            Const(type_ir::ConstKind::Param(symbol, _)) => write!(p, "{symbol}"),
            Const(type_ir::ConstKind::Err) => write!(p, "<error>")
        }
    }
}

impl<'tcx> Print<'tcx> for Instance<'tcx> {
    fn print(&self, p: &mut PrettyPrinter<'tcx>) -> PrintResult {
        p.print_instance(*self)
    }
}

