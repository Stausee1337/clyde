use std::fmt::{Write, Formatter, Result as PrintResult, Error as PrintError};

use crate::{analysis::resolve, context::TyCtxt, syntax::ast, type_ir::{self, Const, Float, GenericArg, GenericArgKind, Global, Ty, TyKind}};


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

    fn print_parent_path_recursively(&mut self, def_id: ast::DefId, surface: bool) -> PrintResult {
        let node = self.tcx.node_by_def_id(def_id);
        let ident = node.ident().unwrap();

        if let resolve::DefParent::Definition(parent) = self.tcx.resolutions.declarations[def_id].parent {
            self.print_parent_path_recursively(parent, false)?;
            self.write_str("::")?;
        }

        self.write_str(ident.symbol.get())?;
        if let ast::Node::Item(item) = node && !surface {
            let generics = node.generics();
            if generics.len() > 0 {
                self.write_char('<')?;
                for (idx, param) in generics.iter().enumerate() {
                    let ident = match &param.kind {
                        ast::GenericParamKind::Type(name) => name,
                        ast::GenericParamKind::Const(name, _) => {
                            self.write_str("const ")?;
                            name
                        }
                    };
                    self.write_str(ident.symbol.get())?;
                    if idx != generics.len() - 1 {        
                        self.write_str(", ")?;
                    }
                }
                self.write_char('>')?;
            }
            
            if let ast::ItemKind::Function(..) = item.kind {
                let sig = self.tcx.fn_sig(def_id);
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

    fn print_def_path(&mut self, def_id: ast::DefId) -> PrintResult {
        self.print_parent_path_recursively(def_id, true)
    }

    fn print_generics(&mut self, generics: &[GenericArg<'tcx>]) -> PrintResult {
        if generics.len() > 0 {
            self.write_str("<")?;
            for (idx, arg) in generics.iter().enumerate() {
                arg.print(self)?;
                if idx != generics.len() - 1 {
                    self.write_str(", ")?;
                }
            }
            self.write_str(">")?;
        }
        Ok(())
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
            TyKind::Adt(adt, generics) => {
                p.print_def_path(adt.def())?;
                p.print_generics(generics)
            },
            TyKind::Enum(enm) => p.print_def_path(enm.def),
            TyKind::Refrence(ty) => write!(p, "{ty}*"),
            TyKind::Slice(ty) => write!(p, "{ty}[]"),
            TyKind::Array(ty, cap) => write!(p, "{ty}[{cap:?}]"),
            TyKind::DynamicArray(ty) => write!(p, "{ty}[..]"),
            // TODO: query function name and display it here
            TyKind::Function(def_id, generics) => {
                p.print_def_path(*def_id)?;
                p.print_generics(generics)
            },
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
            Const(type_ir::ConstKind::Value(value)) => write!(p, "{value}"),
            Const(type_ir::ConstKind::Infer) => write!(p, "_"),
            Const(type_ir::ConstKind::Param(symbol, _)) => write!(p, "{symbol}"),
            Const(type_ir::ConstKind::Err) => write!(p, "<error>")
        }
    }
}

impl<'tcx> Print<'tcx> for Global<'tcx> {
    fn print(&self, p: &mut PrettyPrinter<'tcx>) -> PrintResult {
        match self {
            Global(type_ir::GlobalKind::Function { def, generics }) => {
                p.print_def_path(*def)?;
                p.print_generics(generics)
            },
            Global(type_ir::GlobalKind::EnumVariant { def }) =>
                p.print_def_path(*def),
            Global(type_ir::GlobalKind::Static { def, .. }) =>
                p.print_def_path(*def),
            Global(type_ir::GlobalKind::Indirect { allocation, ty, .. }) => {
                let len = allocation.len();
                write!(p, "[{len}xu8] \"{}\" as ", allocation.escape_ascii())?;
                ty.print(p)
            }
        }
    }
}
