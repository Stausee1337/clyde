
use std::cell::OnceCell;

use index_vec::IndexVec;

use crate::{ast::{self, DefId, DefinitionKind, NodeId}, context::TyCtxt, lexer::Span, typecheck::TypecheckResults, types::{Const, FieldIdx, Ty}};


pub struct Body<'tcx> {
    pub basic_blocks: IndexVec<BlockId, BasicBlock<'tcx>>,
    pub local_registers: IndexVec<RegisterId, Register<'tcx>>,
}

pub struct Register<'tcx> {
    pub mutability: Mutability,
    pub ty: Ty<'tcx>
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Mutability {
    Const, Mut
}

index_vec::define_index_type! {
    pub struct RegisterId = u32;
    IMPL_RAW_CONVERSIONS = true;
}

pub struct BasicBlock<'tcx> {
    pub statements: Vec<Statement<'tcx>>,
    pub terminator: OnceCell<Terminator>
}

index_vec::define_index_type! {
    pub struct BlockId = u32;
    IMPL_RAW_CONVERSIONS = true;
}

pub struct Statement<'tcx> {
    pub kind: StatementKind<'tcx>,
    pub span: Span
}

pub enum StatementKind<'tcx> {
    Assign {
        place: Place<'tcx>,
        rhs: RValue<'tcx>
    },
    Call {
        result: Option<Place<'tcx>>,
        callee: Operand<'tcx>
    }
}

pub struct Terminator {
    pub kind: TerminatorKind,
    pub span: Span
}

pub enum TerminatorKind {
    Goto(BlockId),
    Diverge {
        condition: RegisterId,
        true_target: BlockId,
        false_target: BlockId
    },
    Return {
        value: Option<RegisterId>
    }
}

pub enum Place<'tcx> {
    Register(RegisterId),
    Deref(RegisterId),
    Field {
        target: RegisterId,
        field: FieldIdx,
        ty: Ty<'tcx>
    },
    Index {
        target: RegisterId,
        idx: usize
    }
}

pub enum Operand<'tcx> {
    Place(Place<'tcx>),
    Const(Const<'tcx>),
}

pub enum RValue<'tcx> {
    Copy(Operand<'tcx>),
    BinaryOp {
        lhs: Operand<'tcx>,
        rhs: Operand<'tcx>,
        op: BinaryOp
    },
    Invert(Operand<'tcx>),
    Negate(Operand<'tcx>),
    Ref(Operand<'tcx>),
}

pub enum BinaryOp {
    Mul, Div, Rem,
    Add, Sub,
    Xor, Or, And, Shl, Shr,
    Eq, Ne, Lt, Le, Gt, Ge
}


struct TranslationCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    typecheck: &'tcx TypecheckResults<'tcx>,
    registers: IndexVec<RegisterId, Register<'tcx>>,
}

impl<'tcx> TranslationCtxt<'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        typecheck: &'tcx TypecheckResults<'tcx>,
        params: &'tcx [&'tcx ast::Param<'tcx>]) -> Self {
        let mut ctxt = Self {
            tcx,
            typecheck,
            registers: IndexVec::with_capacity(params.len())
        };

        for param in params {
            ctxt.create_register(param.node_id, Mutability::Mut);
        }

        ctxt
    }

    fn create_register(&mut self, node_id: NodeId, mutability: Mutability) -> RegisterId {
        self.registers.push(Register {
            mutability,
            ty: self.typecheck.associations[&node_id],
        })
    }

    fn expr_to_operand(&mut self, expr: &'tcx ast::Expr<'tcx>) -> Operand<'tcx> {
        match &expr.kind {
            /*ast::ExprKind::Constant(constant) => {
                types
            }*/
            _ => todo!()
        }
    }

    fn build(self) -> &'tcx Body<'tcx> {
        todo!()
    }
}

pub fn build_ir(tcx: TyCtxt<'_>, def_id: DefId) -> &'_ Body<'_> {

    let node = tcx.node_by_def_id(def_id);

    let body = node.body()
        .expect("build ir for node without a body");

    let typecheck_results = tcx.typecheck(def_id);

    let mut ctxt = TranslationCtxt::new(tcx, typecheck_results, body.params);

    match tcx.def_kind(def_id) {
        DefinitionKind::Function => {
        }
        DefinitionKind::NestedConst | DefinitionKind::Const |  DefinitionKind::Static => {
            todo!()
        }
        _ => unreachable!()
    }

    ctxt.build()
}

