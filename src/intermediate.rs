
use std::{cell::OnceCell, collections::HashMap};

use index_vec::{Idx, IndexVec};

use crate::{ast::{self, DefId, DefinitionKind, NodeId}, context::TyCtxt, lexer::{self, Span}, typecheck::TypecheckResults, types::{Const, FieldIdx, Ty, TyKind}};


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

#[derive(Default)]
pub struct BasicBlock<'tcx> {
    pub statements: Vec<Statement<'tcx>>,
    pub terminator: OnceCell<Terminator<'tcx>>
}

index_vec::define_index_type! {
    pub struct BlockId = u32;
    IMPL_RAW_CONVERSIONS = true;
}

pub struct Statement<'tcx> {
    pub place: Place<'tcx>,
    pub rhs: RValue<'tcx>,
    pub span: Span
}

pub struct Terminator<'tcx> {
    pub kind: TerminatorKind<'tcx>,
    pub span: Span
}

pub enum TerminatorKind<'tcx> {
    Goto(BlockId),
    Diverge {
        condition: Operand<'tcx>,
        true_target: BlockId,
        false_target: BlockId
    },
    Return {
        value: Operand<'tcx>
    }
}

#[derive(Clone, Copy)]
pub enum Place<'tcx> {
    Register(RegisterId),
    Deref(RegisterId),
    Field {
        target: Operand<'tcx>,
        field: FieldIdx,
        ty: Ty<'tcx>
    },
    Index {
        target: Operand<'tcx>,
        idx: Operand<'tcx>
    }
}

impl<'tcx> Place<'tcx> {
    /*fn ty(&self, ctxt: &TranslationCtxt<'tcx>) -> Ty<'tcx> {
        match self {
            Place::Register(reg) =>
                ctxt.registers[*reg].ty,
            Place::Deref(reg) => {
                let Ty(TyKind::Refrence(ty)) = ctxt.registers[*reg].ty else {
                    panic!("no-refrence type in ir Place::Deref(..)");
                };
                *ty
            }
            Place::Field { ty, .. } => *ty,
            Place::Index { target, .. } => {
                let Ty(TyKind::Array(ty, _)) = target.ty(ctxt) else {
                    panic!("non-array type in ir Place::Index {{  }}");
                };
                *ty
            }
        }
    }*/
}

#[derive(Clone, Copy)]
pub enum Operand<'tcx> {
    Copy(RegisterId),
    Const(Const<'tcx>),
    Definition(DefId)
}

#[derive(Clone, Copy)]
pub struct SpanOperand<'tcx> {
    pub operand: Operand<'tcx>,
    pub span: Span
}

impl<'tcx> Operand<'tcx> {
    /*fn ty(&self, ctxt: &TranslationCtxt<'tcx>) -> Ty<'tcx> {
        match self {
            Operand::Copy(reg) =>
                ctxt.registers[*reg].ty,
            Operand::Const(cnst) => cnst.ty().unwrap_or_else(|| Ty::new_error(ctxt.tcx)),
            Operand::Definition(def_id) => ctxt.tcx.type_of(*def_id)
        }
    }*/

    fn with_span(self, span: Span) -> SpanOperand<'tcx> {
        SpanOperand {
            operand: self,
            span
        }
    }
}

pub enum RValue<'tcx> {
    Use(Operand<'tcx>),
    Read(Place<'tcx>),
    Ref(Place<'tcx>),
    Invert(Operand<'tcx>),
    Negate(Operand<'tcx>),
    BinaryOp {
        lhs: Operand<'tcx>,
        rhs: Operand<'tcx>,
        op: BinaryOp
    },
    Cast {
        value: Operand<'tcx>,
        ty: Ty<'tcx>
    },
    Call {
        callee: Operand<'tcx>,
        args: Box<[SpanOperand<'tcx>]>,
    },
    ExplicitInit {
        ty: Ty<'tcx>,
        initializers: Box<[(FieldIdx, SpanOperand<'tcx>)]>,
    }
}

#[derive(Clone, Copy)]
pub enum BinaryOp {
    Mul, Div, Rem,
    Add, Sub,
    Xor, Or, And, Shl, Shr,
    Eq, Ne, Lt, Le, Gt, Ge
}

#[derive(Clone, Copy)]
pub enum LogicalOp {
    And, Or
}

struct TranslationCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    typecheck: &'tcx TypecheckResults<'tcx>,
    registers: IndexVec<RegisterId, Register<'tcx>>,
    register_lookup: HashMap<ast::NodeId, RegisterId, ahash::RandomState>,
    blocks: IndexVec<BlockId, BasicBlock<'tcx>>
}

impl<'tcx> TranslationCtxt<'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        typecheck: &'tcx TypecheckResults<'tcx>,
        params: &'tcx [&'tcx ast::Param<'tcx>]) -> Self {
        let mut ctxt = Self {
            tcx,
            typecheck,
            registers: IndexVec::with_capacity(params.len()),
            register_lookup: Default::default(),
            blocks: IndexVec::new()
        };

        for param in params {
            ctxt.create_register(param.node_id, Mutability::Mut);
        }

        ctxt
    }

    fn create_register(&mut self, node_id: NodeId, mutability: Mutability) -> RegisterId {
        let reg = self.registers.push(Register {
            mutability,
            ty: self.typecheck.associations[&node_id],
        });
        self.register_lookup.insert(node_id, reg);
        reg
    }

    fn tmp_register(&mut self, ty: Ty<'tcx>, mutability: Mutability) -> RegisterId {
        self.registers.push(Register { mutability, ty })
    }

    fn create_block(&mut self) -> BlockId {
        self.blocks.push(BasicBlock::default())
    }

    fn emit_into(&mut self, block: BlockId, stmt: Statement<'tcx>) {
        let block = &mut self.blocks[block];
        let None = block.terminator.get() else {
            panic!("can't emit into terminated block");
        };
        block.statements.push(stmt);
    }

    fn write_expr_into(&mut self, dest: Place<'tcx>, mut block: BlockId, expr: &'tcx ast::Expr<'tcx>) -> BlockId {
        match &expr.kind {
            ast::ExprKind::Name(name) if matches!(name.resolution(), Some(ast::Resolution::Local(..))) => {
                let place;
                (block, place) = self.expr_as_place(block, expr);

                self.emit_into(
                    block,
                    Statement {
                        place: dest,
                        rhs: RValue::Read(place),
                        span: expr.span
                    }
                );

                block
            }
            ast::ExprKind::Name(..) => {
                let operand;
                (block, operand) = self.expr_as_operand(block, expr);

                self.emit_into(
                    block,
                    Statement {
                        place: dest,
                        rhs: RValue::Use(operand),
                        span: expr.span
                    }
                );

                block
            }
            ast::ExprKind::BinaryOp(binary) if matches!(binary.operator, lexer::BinaryOp::BooleanOr | lexer::BinaryOp::BooleanAnd) => {
                let logical = match binary.operator {
                    lexer::BinaryOp::BooleanOr => LogicalOp::Or,
                    lexer::BinaryOp::BooleanAnd => LogicalOp::And,
                    _ => unreachable!()
                };

                todo!()
            }
            ast::ExprKind::BinaryOp(binary) => {
                let binop = match binary.operator {
                    lexer::BinaryOp::Mul => BinaryOp::Mul,
                    lexer::BinaryOp::Div => BinaryOp::Div,
                    lexer::BinaryOp::Mod => BinaryOp::Rem,

                    lexer::BinaryOp::Plus => BinaryOp::Add,
                    lexer::BinaryOp::Minus => BinaryOp::Sub,

                    lexer::BinaryOp::BitwiseXor => BinaryOp::Xor,
                    lexer::BinaryOp::BitwiseOr => BinaryOp::Or,
                    lexer::BinaryOp::BitwiseAnd => BinaryOp::And,

                    lexer::BinaryOp::LeftShift => BinaryOp::Shl,
                    lexer::BinaryOp::RightShift => BinaryOp::Shr,

                    lexer::BinaryOp::Equals=> BinaryOp::Eq,
                    lexer::BinaryOp::NotEquals => BinaryOp::Ne,
                    lexer::BinaryOp::LessThan => BinaryOp::Lt,
                    lexer::BinaryOp::LessEqual => BinaryOp::Le,
                    lexer::BinaryOp::GreaterThan => BinaryOp::Gt,
                    lexer::BinaryOp::GreaterEqual => BinaryOp::Ge,
                    lexer::BinaryOp::BooleanOr | lexer::BinaryOp::BooleanAnd => 
                        unreachable!(),
                };
                let (lhs, rhs);

                (block, lhs) = self.expr_as_operand(block, binary.lhs);
                (block, rhs) = self.expr_as_operand(block, binary.rhs);

                self.emit_into(
                    block,
                    Statement {
                        place: dest,
                        rhs: RValue::BinaryOp {
                            lhs, rhs,
                            op: binop
                        },
                        span: expr.span
                    }
                );

                block
            }
            ast::ExprKind::UnaryOp(ast::UnaryOp { expr: rexpr, operator: lexer::UnaryOp::Ref }) => {
                let place = if let Some(result) = self.try_expr_as_place(block, rexpr) {
                    let place;
                    (block, place) = result;
                    place
                } else {
                    // create fake-place for expression
                    let reg;
                    (block, reg) = self.as_tmp(block, rexpr);
                    Place::Register(reg)
                };
                self.emit_into(
                    block,
                    Statement {
                        place: dest,
                        rhs: RValue::Ref(place),
                        span: expr.span
                    }
                );
                block
            }
            ast::ExprKind::UnaryOp(unary) => match unary.operator {
                lexer::UnaryOp::Not | lexer::UnaryOp::BitwiseNot => {
                    let operand;
                    (block, operand) = self.expr_as_operand(block, unary.expr);

                    self.emit_into(
                        block,
                        Statement {
                            place: dest,
                            rhs: RValue::Invert(operand),
                            span: expr.span
                        }
                    );
                    block
                }
                lexer::UnaryOp::Minus => {
                    let operand;
                    (block, operand) = self.expr_as_operand(block, unary.expr);

                    self.emit_into(
                        block,
                        Statement {
                            place: dest,
                            rhs: RValue::Negate(operand),
                            span: expr.span
                        }
                    );
                    block
                }
                lexer::UnaryOp::Ref => unreachable!()
            }
            ast::ExprKind::FunctionCall(call) => {
                let callee;
                (block, callee) = self.expr_as_operand(block, call.callable);

                let mut args = vec![];

                for arg in call.args {
                    let arg = match arg {
                        ast::FunctionArgument::Direct(expr) => expr,
                        ast::FunctionArgument::Keyword(..) => todo!()
                    };
                    let ir_arg;
                    (block, ir_arg) = self.expr_as_operand(block, arg);
                    args.push(ir_arg.with_span(arg.span));
                }

                self.emit_into(
                    block,
                    Statement {
                        rhs: RValue::Call {
                            callee,
                            args: args.into_boxed_slice()
                        },
                        place: dest,
                        span: expr.span
                    }
                );
                block
            }
            ast::ExprKind::Cast(cast) => {
                let ty = self.typecheck.associations[&cast.expr.node_id];
                let value;
                (block, value) = self.expr_as_operand(block, cast.expr);

                self.emit_into(
                    block,
                    Statement {
                        place: dest,
                        rhs: RValue::Cast {
                            ty,
                            value
                        },
                        span: expr.span
                    }
                );

                block
            }
            ast::ExprKind::TypeInit(init) => {
                let ty = self.typecheck.associations[&expr.node_id];

                let mut initializers = vec![];

                for (idx, init) in init.initializers.iter().enumerate() {
                    let ir_init;
                    let ir_idx;
                    let span;
                    match init {
                        ast::TypeInitKind::Field(ident, expr) => {
                            span = Span::interpolate(ident.span, expr.span);
                            (block, ir_init) = self.expr_as_operand(block, expr);
                            ir_idx = self.typecheck.field_indices[&expr.node_id];
                        }
                        ast::TypeInitKind::Direct(expr) => {
                            span = expr.span;
                            (block, ir_init) = self.expr_as_operand(block, expr);
                            ir_idx = FieldIdx::from_usize(idx);
                        }
                    }

                    initializers.push((ir_idx, ir_init.with_span(span)));
                }

                self.emit_into(
                    block,
                    Statement {
                        place: dest,
                        rhs: RValue::ExplicitInit {
                            ty,
                            initializers: initializers.into_boxed_slice()
                        },
                        span: expr.span
                    }
                );

                block
            }
            ast::ExprKind::Subscript(..) | ast::ExprKind::Field(..) |
            ast::ExprKind::Deref(..) => {
                let place;
                (block, place) = self.expr_as_place(block, expr);

                self.emit_into(
                    block,
                    Statement {
                        place: dest,
                        rhs: RValue::Read(place),
                        span: expr.span
                    }
                );

                block
            }
            _ => todo!()
        }
    }

    fn as_tmp(&mut self, block: BlockId, expr: &'tcx ast::Expr<'tcx>) -> (BlockId, RegisterId) {
        let ty = self.typecheck.associations[&expr.node_id];
        let reg = self.tmp_register(ty, Mutability::Const);
        let dest = Place::Register(reg);
        let block = self.write_expr_into(dest, block, expr);
        (block, reg)
    }

    fn try_expr_as_place(&mut self, mut block: BlockId, expr: &'tcx ast::Expr<'tcx>) -> Option<(BlockId, Place<'tcx>)> {
        let res = match &expr.kind {
            ast::ExprKind::Name(name) if matches!(name.resolution(), Some(ast::Resolution::Local(..))) => {
                let Some(ast::Resolution::Local(local)) = name.resolution() else {
                    unreachable!();
                };

                (block, Place::Register(self.register_lookup[&local]))
            }
            ast::ExprKind::Subscript(subscript) => {
                debug_assert_eq!(subscript.args.len(), 1);
                let target;
                (block, target) = self.expr_as_operand(block, subscript.expr);
                let idx;
                (block, idx) = self.expr_as_operand(block, subscript.args[0]);
                (block, Place::Index { target, idx })
            }
            ast::ExprKind::Field(field) => {
                let target;
                (block, target) = self.expr_as_operand(block, field.expr);
                let field = match field.field {
                    ast::FieldIdent::Named(..) =>
                        self.typecheck.field_indices[&expr.node_id],
                    ast::FieldIdent::Tuple { value, .. } =>
                        FieldIdx::from_usize(value as usize)
                };
                let ty = self.typecheck.associations[&expr.node_id];
                // field.field
                (block, Place::Field { target, field, ty })
            }
            ast::ExprKind::Deref(expr) => {
                let register;
                (block, register) = self.as_tmp(block, expr);
                (block, Place::Deref(register))
            }
            _ => return None
        };
        Some(res)
    }

    fn expr_as_place(&mut self, block: BlockId, expr: &'tcx ast::Expr<'tcx>) -> (BlockId, Place<'tcx>) {
        self.try_expr_as_place(block, expr).expect("expr has a place")
    }

    fn expr_as_operand(
        &mut self,
        mut block: BlockId,
        expr: &'tcx ast::Expr<'tcx>,
    ) -> (BlockId, Operand<'tcx>) {
        match &expr.kind {
            ast::ExprKind::Literal(literal) => {
                let ty = self.typecheck.associations[&expr.node_id];
                (block, Operand::Const(Const::from_literal(self.tcx, ty, literal).unwrap()))
            }
            ast::ExprKind::Name(name) if !matches!(name.resolution(), Some(ast::Resolution::Local(..))) => match name.resolution() {
                Some(ast::Resolution::Def(def_id, DefinitionKind::Static | DefinitionKind::Const | DefinitionKind::Function)) =>
                    (block, Operand::Definition(*def_id)),
                Some(ast::Resolution::Def(..) | ast::Resolution::Primitive) => panic!("unexpected type-like resolution"),
                Some(ast::Resolution::Err) => todo!("mayge try to create some fallback value"),
                Some(ast::Resolution::Local(..)) => unreachable!(),
                None => panic!("unresolved Name at ir stage")
            }
            ast::ExprKind::Name(name) if matches!(name.resolution(), Some(ast::Resolution::Local(..))) => {
                let Some(ast::Resolution::Local(local)) = name.resolution() else {
                    unreachable!();
                };

                // FIXME: remove duplication with Place and Temporaray handling
                // TODO: I think this is the point we should build a copy if the register is mutable

                (block, Operand::Copy(self.register_lookup[&local]))
            }
            _ => {
                let register;
                (block, register) = self.as_tmp(block, expr);
                (block, Operand::Copy(register))
            }
        }
    }

    fn ret(&mut self,  block: BlockId, op: SpanOperand<'tcx>) {
        let terminator = Terminator {
            kind: TerminatorKind::Return { value: op.operand },
            span: op.span
        };
        let Err(..) = self.blocks[block].terminator.set(terminator) else {
            panic!("terminating terminated block");
        };
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
            // let start = ctxt.create_block();
            todo!()
        }
        DefinitionKind::NestedConst | DefinitionKind::Const |  DefinitionKind::Static => {
            let result;
            let mut block = ctxt.create_block();
            (block, result) = ctxt.expr_as_operand(block, body.body);
            ctxt.ret(block, result.with_span(Span::NULL));
        }
        _ => unreachable!()
    }

    ctxt.build()
}

