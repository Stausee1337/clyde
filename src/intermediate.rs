
use std::{cell::OnceCell, collections::HashMap, fmt::Write};

use index_vec::{Idx, IndexVec};

use crate::{ast::{self, DefId, DefinitionKind, NodeId}, context::{self, TyCtxt}, lexer::{self, Span}, typecheck::TypecheckResults, types::{Const, FieldIdx, Ty, TyKind}};


pub struct Body<'tcx> {
    pub origin: DefId,
    pub result_ty: Ty<'tcx>,
    pub num_params: usize,
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

impl std::fmt::Debug for Mutability {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Mutability::Mut => f.write_str("mut"),
            Mutability::Const => f.write_str("const"),
        }
    }
}

index_vec::define_index_type! {
    pub struct RegisterId = u32;
    IMPL_RAW_CONVERSIONS = true;
    DEBUG_FORMAT = "%{}";
}

#[derive(Default)]
pub struct BasicBlock<'tcx> {
    pub statements: Vec<Statement<'tcx>>,
    pub terminator: OnceCell<Terminator<'tcx>>
}

index_vec::define_index_type! {
    pub struct BlockId = u32;
    IMPL_RAW_CONVERSIONS = true;
    DEBUG_FORMAT = "bb{}";
}

pub struct Statement<'tcx> {
    pub place: Place<'tcx>,
    pub rhs: RValue<'tcx>,
    pub span: Span
}

impl<'tcx> std::fmt::Debug for Statement<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Place::None = self.place {
            return write!(f, "{:?}", self.rhs);
        }
        write!(f, "{:?} = {:?}", self.place, self.rhs)
    }
}

pub struct Terminator<'tcx> {
    pub kind: TerminatorKind<'tcx>,
    pub span: Span
}

impl<'tcx> std::fmt::Debug for Terminator<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            TerminatorKind::Goto(block) => write!(f, "goto {block:?}"),
            TerminatorKind::Diverge { condition, true_target, false_target } =>
                write!(f, "diverge {condition:?} ? true -> {true_target:?} : false -> {false_target:?}"),
            TerminatorKind::Return { value } => write!(f, "return {value:?}"),
        }
    }
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
    },
    None
}

impl<'tcx> std::fmt::Debug for Place<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Place::None => Ok(()),
            Place::Register(reg) => write!(f, "{reg:?}"),
            Place::Deref(reg) => write!(f, "*{reg:?}"),
            Place::Field { target, field, ty: _ty } => write!(f, "({target:?}).{}", field.0),
            Place::Index { target, idx } => write!(f, "{target:?}[{idx:?}]"),
        }
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
    Definition(DefId),
    Uninit // Used for void values
}

impl<'tcx> std::fmt::Debug for Operand<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operand::Copy(reg) => write!(f, "copy {reg:?}"),
            Operand::Const(_cnst) => write!(f, "const XXX"), // TODO: simple constant display
            Operand::Definition(def_id) => {
                let ident = context::with_tcx(|tcx| {
                    let node = tcx.expect("pretty-print IR Operand in valid TCX context").node_by_def_id(*def_id);
                    if let ast::Node::Item(item) = node {
                        return item.ident();
                    } else {
                        panic!("non-item in definition");
                    };
                });

                write!(f, "{}", ident.symbol.get())
            },
            Operand::Uninit => write!(f, "---"),
        }
    }
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

impl<'tcx> std::fmt::Debug for RValue<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RValue::Use(operand) => write!(f, "{operand:?}"),
            RValue::Read(place) => write!(f, "{place:?}"),
            RValue::Ref(place) => write!(f, "&{place:?}"),
            RValue::Invert(operand) => write!(f, "Inv({operand:?})"),
            RValue::Negate(operand) => write!(f, "Neg({operand:?})"),
            RValue::BinaryOp { op, lhs, rhs } => write!(f, "{op:?}({lhs:?}, {rhs:?})"),
            RValue::Cast { value, ty } => write!(f, "{value:?} as {ty}"),
            RValue::Call { callee, args: args1 } => {
                let mut args = vec![];
                for arg in args1 {
                    args.push(format!("{:?}", arg.operand));
                }
                let args = args.join(", ");
                write!(f, "{callee:?}({args})")
            },
            RValue::ExplicitInit { ty, initializers } => todo!(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
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
    def: DefId,
    num_params: usize,
    typecheck: &'tcx TypecheckResults<'tcx>,
    registers: IndexVec<RegisterId, Register<'tcx>>,
    register_lookup: HashMap<ast::NodeId, RegisterId, ahash::RandomState>,
    blocks: IndexVec<BlockId, BasicBlock<'tcx>>
}

impl<'tcx> TranslationCtxt<'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        def: DefId,
        typecheck: &'tcx TypecheckResults<'tcx>,
        params: &'tcx [&'tcx ast::Param<'tcx>]) -> Self {
        let mut ctxt = Self {
            tcx,
            def,
            num_params: params.len(),
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
        if let Place::None = stmt.place {
            let RValue::Call { .. } = stmt.rhs else {
                return;
            };
        }
        block.statements.push(stmt);
    }

    fn build_diverge(&mut self, mut block: BlockId, expr: &'tcx ast::Expr<'tcx>) -> (BlockId, BlockId) {
        match &expr.kind {
            ast::ExprKind::BinaryOp(logical @ ast::BinaryOp { operator: lexer::BinaryOp::BooleanOr, .. }) => {
                let (true_block, mut continuation) = self.build_diverge(block, logical.lhs);
                let false_block = self.create_block();

                let condition;
                (continuation, condition) = self.expr_as_operand(continuation, logical.rhs);
                self.diverge(continuation, condition, true_block, false_block, logical.rhs.span);

                (true_block, false_block)
            }
            ast::ExprKind::BinaryOp(logical @ ast::BinaryOp { operator: lexer::BinaryOp::BooleanAnd, .. }) => {
                let (mut continuation, false_block) = self.build_diverge(block, logical.lhs);

                let true_block = self.create_block();

                let condition;
                (continuation, condition) = self.expr_as_operand(continuation, logical.rhs);
                self.diverge(continuation, condition, true_block, false_block, logical.rhs.span);

                (true_block, false_block)
            }
            _ => {
                let true_block = self.create_block();
                let false_block = self.create_block();

                let condition;
                (block, condition) = self.expr_as_operand(block, expr);
                self.diverge(block, condition, true_block, false_block, expr.span);

                (true_block, false_block)
            }
        }
    }

    fn cover_ast_stmt(&mut self, mut block: BlockId, stmt: &'tcx ast::Stmt<'tcx>) -> BlockId {
        match &stmt.kind {
            ast::StmtKind::Local(local) => {
                let reg = self.create_register(stmt.node_id, Mutability::Mut);
                if let Some(init) = local.init {
                    self.write_expr_into(Place::Register(reg), block, init);
                }
                block
            }
            ast::StmtKind::Expr(expr) =>
                self.write_expr_into(Place::None, block, expr),
            ast::StmtKind::If(if_stmt) => {
                let (mut then_block, mut else_block) = self.build_diverge(block, if_stmt.condition);
                then_block = self.cover_ast_block(then_block, &if_stmt.body);

                let join_block;
                if let Some(else_branch) = if_stmt.else_branch {
                    else_block = self.cover_ast_stmt(else_block, else_branch);
                    if !self.is_terminated(else_block) {
                        join_block = self.create_block();
                        self.goto(else_block, join_block, else_branch.span);
                    } else {
                        join_block = else_block;
                    }
                } else {
                    join_block = else_block;
                }

                if !self.is_terminated(then_block) {
                    self.goto(then_block, join_block, stmt.span);
                }
                join_block
            },
            ast::StmtKind::For(..) | ast::StmtKind::While(..) => block,
            ast::StmtKind::ControlFlow(..) => block,
            ast::StmtKind::Return(ret) => {
                let op;
                (block, op) = ret.map(|expr| self.expr_as_operand(block, expr))
                    .unwrap_or_else(|| (block, Operand::Uninit));
                self.ret(block, op.with_span(stmt.span));
                block
            }
            ast::StmtKind::Yeet(_yeet) => {
                // TODO: create Ctxt around yeet-able blocks.
                // Here the place given by the Ctxt will be used to write in the given value
                // Also this block should be terminated here
                todo!()
            }
            ast::StmtKind::Block(ast_block) =>
                self.cover_ast_block(block, ast_block),
            ast::StmtKind::Err => block
        }
    }

    fn cover_ast_block(&mut self, mut block: BlockId, ast_block: &ast::Block<'tcx>) -> BlockId {
        for stmt in ast_block.stmts {
            block = self.cover_ast_stmt(block, stmt);
        }

        block
    }

    fn handle_logical_op(&mut self, dest: Place<'tcx>, block: BlockId, logical: LogicalOp, lhs: &'tcx ast::Expr<'tcx>, rhs: &'tcx ast::Expr<'tcx>) -> BlockId {
        let (then_block, else_block) = self.build_diverge(block, lhs);
        let (short_circuit, continuation, constant) = match logical {
            LogicalOp::Or => (then_block, else_block, true),
            LogicalOp::And => (else_block, then_block, false),
        };

        let constant = Const::from_bool(self.tcx, constant);
        self.emit_into(
            short_circuit,
            Statement {
                place: dest,
                rhs: RValue::Use(Operand::Const(constant)),
                span: lhs.span
            }
        );
        
        let rhs_block = self.write_expr_into(dest, continuation, rhs);

        let join_block = self.create_block();
        self.goto(short_circuit, join_block, lhs.span);
        self.goto(rhs_block, join_block, rhs.span);

        join_block
    }

    fn write_expr_into(&mut self, dest: Place<'tcx>, mut block: BlockId, expr: &ast::Expr<'tcx>) -> BlockId {
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
            ast::ExprKind::Name(..) | ast::ExprKind::Literal(..) => {
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

                self.handle_logical_op(dest, block, logical, binary.lhs, binary.rhs)
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
            ast::ExprKind::AssignOp(assign) => {
                let dest2;
                (block, dest2) = self.expr_as_place(block, assign.lhs);

                let binop = match assign.operator {
                    lexer::AssignmentOp::Assign => {
                        let rhs;
                        (block, rhs) = self.expr_as_operand(block, assign.rhs);

                        self.emit_into(
                            block,
                            Statement {
                                place: dest2,
                                rhs: RValue::Use(rhs),
                                span: expr.span
                            }
                        );

                        self.emit_into(
                            block,
                            Statement {
                                place: dest,
                                rhs: RValue::Read(dest2),
                                span: expr.span
                            }
                        );

                        return block;
                    }
                    lexer::AssignmentOp::MulAssign => BinaryOp::Mul,
                    lexer::AssignmentOp::DivAssign => BinaryOp::Div,
                    lexer::AssignmentOp::ModAssign => BinaryOp::Rem,

                    lexer::AssignmentOp::PlusAssign => BinaryOp::Add,
                    lexer::AssignmentOp::MinusAssign => BinaryOp::Sub,

                    lexer::AssignmentOp::BitwiseXorAssign => BinaryOp::Xor,
                    lexer::AssignmentOp::BitwiseOrAssign => BinaryOp::Or,
                    lexer::AssignmentOp::BitwiseAndAssign => BinaryOp::And,

                    lexer::AssignmentOp::LeftShiftAssign => BinaryOp::Shl,
                    lexer::AssignmentOp::RightShiftAssign => BinaryOp::Shr
                };

                let rhs;
                (block, rhs) = self.expr_as_operand(block, assign.rhs);

                let lhs = if let Place::Register(reg) = dest2 {
                    Operand::Copy(reg)
                } else {
                    let reg = self.tmp_register(self.typecheck.associations[&expr.node_id], Mutability::Const);
                    self.emit_into(
                        block,
                        Statement {
                            place: Place::Register(reg),
                            rhs: RValue::Read(dest2),
                            span: Span::NULL
                        }
                    );
                    Operand::Copy(reg)
                };

                self.emit_into(
                    block,
                    Statement {
                        place: dest2,
                        rhs: RValue::BinaryOp {
                            lhs, rhs,
                            op: binop
                        },
                        span: expr.span
                    }
                );

                self.emit_into(
                    block,
                    Statement {
                        place: dest,
                        rhs: RValue::Read(dest2),
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
                    (block, reg) = self.as_register(block, rexpr);
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
            ast::ExprKind::Block(ast_block) => {
                block = self.cover_ast_block(block, ast_block);
                // TODO: create YeetCtxt around blocks that aren't bodies and do something with
                // them here. 
                // The `dest` param of this function is provided as `Place` to place the result
                // into
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
            ast::ExprKind::Tuple(..) | ast::ExprKind::Range(..) => todo!(),
            ast::ExprKind::Err => block
        }
    }

    fn as_register(&mut self, block: BlockId, expr: &ast::Expr<'tcx>) -> (BlockId, RegisterId) {
        if let ast::ExprKind::Name(name) = &expr.kind {
            if let Some(ast::Resolution::Local(local)) = name.resolution() {
                return (block, self.register_lookup[&local]);
            }
        }
        let ty = self.typecheck.associations[&expr.node_id];
        let reg = self.tmp_register(ty, Mutability::Const);
        let dest = Place::Register(reg);
        let block = self.write_expr_into(dest, block, expr);
        (block, reg)
    }

    fn try_expr_as_place(&mut self, mut block: BlockId, expr: &ast::Expr<'tcx>) -> Option<(BlockId, Place<'tcx>)> {
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
                (block, register) = self.as_register(block, expr);
                (block, Place::Deref(register))
            }
            _ => return None
        };
        Some(res)
    }

    fn expr_as_place(&mut self, block: BlockId, expr: &ast::Expr<'tcx>) -> (BlockId, Place<'tcx>) {
        self.try_expr_as_place(block, expr).expect("expr has a place")
    }

    fn expr_as_operand(
        &mut self,
        mut block: BlockId,
        expr: &ast::Expr<'tcx>,
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
                (block, register) = self.as_register(block, expr);
                (block, Operand::Copy(register))
            }
        }
    }

    fn ret(&mut self, block: BlockId, op: SpanOperand<'tcx>) {
        let terminator = Terminator {
            kind: TerminatorKind::Return { value: op.operand },
            span: op.span
        };
        if let Err(..) = self.blocks[block].terminator.set(terminator) {
            panic!("terminating terminated block");
        }
    }

    fn diverge(&mut self, block: BlockId, condition: Operand<'tcx>, true_dest: BlockId, false_dest: BlockId, span: Span) {
        let terminator = Terminator {
            kind: TerminatorKind::Diverge {
                condition,
                true_target: true_dest,
                false_target: false_dest
            },
            span
        };
        if let Err(..) = self.blocks[block].terminator.set(terminator) {
            panic!("terminating terminated block");
        }
    }

    fn goto(&mut self, block: BlockId, dest: BlockId, span: Span) {
        let terminator = Terminator {
            kind: TerminatorKind::Goto(dest),
            span
        };
        if let Err(..) = self.blocks[block].terminator.set(terminator) {
            panic!("terminating terminated block");
        }
    }

    fn is_terminated(&self, block: BlockId) -> bool {
        self.blocks[block].terminator.get().is_some()
    }

    fn build(self, result_ty: Ty<'tcx>) -> &'tcx Body<'tcx> {
        self.tcx.arena.alloc(Body {
            result_ty,
            origin: self.def,
            num_params: self.num_params,
            basic_blocks: self.blocks,
            local_registers: self.registers
        })
    }
}

pub fn build_ir(tcx: TyCtxt<'_>, def_id: DefId) -> &'_ Body<'_> {

    let node = tcx.node_by_def_id(def_id);

    let body = node.body()
        .expect("build ir for node without a body");

    let typecheck_results = tcx.typecheck(def_id);



    let mut ctxt = TranslationCtxt::new(tcx, def_id, typecheck_results, body.params);

    let result_ty = match tcx.def_kind(def_id) {
        DefinitionKind::Function => {
            let start = ctxt.create_block();
            // TODO: enter block-body scope
            let block = ctxt.write_expr_into(Place::None, start, body.body);
            if !ctxt.is_terminated(block) {
                ctxt.ret(block, Operand::Uninit.with_span(Span::NULL));
            }

            let sig = tcx.fn_sig(def_id);
            sig.returns
        }
        DefinitionKind::NestedConst | DefinitionKind::Const |  DefinitionKind::Static => {
            let result;
            let mut block = ctxt.create_block();
            (block, result) = ctxt.expr_as_operand(block, body.body);
            ctxt.ret(block, result.with_span(Span::NULL));

            tcx.type_of(def_id)
        }
        _ => unreachable!()
    };

    ctxt.build(result_ty)
}

const INDENT: &'static str = "    ";

pub fn display_ir_body<'tcx>(tcx: TyCtxt<'tcx>, body: &'tcx Body<'tcx>, out: &mut dyn Write) -> Result<(), std::fmt::Error> {
    let node = tcx.node_by_def_id(body.origin);
    let ident = match node {
        ast::Node::Item(item) => item.ident(),
        _ => unreachable!()
    };
    let mut args = vec![];
    for i in 0..body.num_params {
        let reg = RegisterId::from_usize(i);
        let reg_info = &body.local_registers[reg];
        args.push(format!("{:?} {reg:?}: {}", reg_info.mutability, reg_info.ty));
    }
    let args = args.join(", ");
    let result_ty = body.result_ty;
    write!(out, "fn {}({args}) -> {result_ty} {{\n", ident.symbol.get())?;

    for i in body.num_params..body.local_registers.len() {
        let reg = RegisterId::from_usize(i);
        let reg_info = &body.local_registers[reg];
        write!(out, "{INDENT}{:?} {reg:?}: {};\n", reg_info.mutability, reg_info.ty)?;
    }

    for (block, bb) in body.basic_blocks.iter_enumerated() {
        display_bb(block, bb, out)?;
    }

    write!(out, "}}\n")?;

    Ok(())
}

fn display_bb(block: BlockId, bb: &BasicBlock, out: &mut dyn Write) -> Result<(), std::fmt::Error> {
    write!(out, "{INDENT}{block:?} {{\n")?;

    for stmt in &bb.statements {
        write!(out, "{INDENT}{INDENT}{stmt:?};\n")?;
    }

    let terminator = bb.terminator.get().expect("terminated basic block");

    write!(out, "{INDENT}{INDENT}{terminator:?};\n")?;

    write!(out, "{INDENT}}}\n")?;

    Ok(())
}

