
use std::{cell::OnceCell, fmt::Write, hash::Hash};

use hashbrown::HashMap;
use index_vec::IndexVec;

use crate::{context::TyCtxt, mapping, pretty_print::Print, syntax::{ast::{self, DefId, DefinitionKind, NodeId}, lexer::{self, Span}}, type_ir::{Const, FieldIdx, Global, Ty, TyKind}};
use super::typecheck::TypecheckResults;

#[derive(Clone, clyde_macros::Recursible)]
pub struct Body<'tcx> {
    #[non_recursible]
    pub entry: BlockId,
    #[non_recursible]
    pub origin: DefId,
    pub result_ty: Ty<'tcx>,
    #[non_recursible]
    pub num_params: usize,
    pub basic_blocks: IndexVec<BlockId, BasicBlock<'tcx>>,
    pub local_registers: IndexVec<RegisterId, Register<'tcx>>,
}

impl<'tcx> Hash for &'tcx Body<'tcx> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let address = (*self as *const Body<'tcx>).addr();
        state.write_usize(address);
    }
}

impl<'tcx> PartialEq for &'tcx Body<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(*self, *other)
    }
}

impl<'tcx> Eq for &'tcx Body<'tcx> {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegKind {
    Param,
    Local,
    Temp
}

#[derive(Clone, clyde_macros::Recursible)]
pub struct Register<'tcx> {
    #[non_recursible]
    pub kind: RegKind,
    #[non_recursible]
    pub mutability: Mutability,
    pub ty: Ty<'tcx>
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Mutability {
    Const, Mut
}

impl std::fmt::Display for Mutability {
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
    DISPLAY_FORMAT = "%{}";
}

#[derive(Default, Clone, clyde_macros::Recursible)]
pub struct BasicBlock<'tcx> {
    pub statements: Vec<Statement<'tcx>>,
    pub terminator: OnceCell<Terminator<'tcx>>
}

index_vec::define_index_type! {
    #[must_use]
    pub struct BlockId = u32;
    IMPL_RAW_CONVERSIONS = true;
    DISPLAY_FORMAT = "bb{}";
}

#[derive(Clone, clyde_macros::Recursible)]
pub struct Statement<'tcx> {
    pub place: Option<Place<'tcx>>,
    pub rhs: RValue<'tcx>,
    #[non_recursible]
    pub span: Span
}

impl<'tcx> std::fmt::Display for Statement<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Some(place) = self.place else {
            return write!(f, "{}", self.rhs);
        };
        write!(f, "{} = {}", place, self.rhs)
    }
}

#[derive(Clone, clyde_macros::Recursible)]
pub struct Terminator<'tcx> {
    pub kind: TerminatorKind<'tcx>,
    #[non_recursible]
    pub span: Span
}

impl<'tcx> std::fmt::Display for Terminator<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            TerminatorKind::Goto(block) => write!(f, "goto {block:?}"),
            TerminatorKind::Diverge { condition, true_target, false_target } =>
                write!(f, "diverge {condition} ? true -> {true_target} : false -> {false_target}"),
            TerminatorKind::Return { value } => {
                f.write_str("return")?;
                if let Some(value) = value {
                    write!(f, " {value}")?;
                }
                Ok(())
            },
        }
    }
}

#[derive(Clone, clyde_macros::Recursible)]
pub enum TerminatorKind<'tcx> {
    Goto(#[non_recursible] BlockId),
    Diverge {
        condition: Operand<'tcx>,
        #[non_recursible]
        true_target: BlockId,
        #[non_recursible]
        false_target: BlockId
    },
    Return {
        value: Option<Operand<'tcx>>
    }
}

#[derive(Clone, Copy, clyde_macros::Recursible)]
pub struct Place<'tcx> {
    #[non_recursible]
    pub origin: RegisterId,
    pub translation_chain: &'tcx [PtrTranslation<'tcx>]
}

impl<'tcx> Place<'tcx> {
    fn register(origin: RegisterId) -> Self {
        Self {
            origin,
            translation_chain: &[]
        }
    }

    fn as_register(&self) -> Option<RegisterId> {
        if self.translation_chain.is_empty() {
            return Some(self.origin);
        }
        None
    }
}

#[derive(Clone, Copy, clyde_macros::Recursible)]
pub enum PtrTranslation<'tcx> {
    Deref,
    Field {
        #[non_recursible]
        field: FieldIdx,
        ty: Ty<'tcx>
    },
    Index {
        idx: Operand<'tcx>
    }
}


impl<'tcx> std::fmt::Display for Place<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut out = String::new();
        write!(out, "{:?}", self.origin)?;

        for translation in self.translation_chain {
            match translation {
                PtrTranslation::Deref =>
                    out = format!("(*{out})"),
                PtrTranslation::Index { idx } =>
                    write!(out, "[{idx}]")?,
                PtrTranslation::Field { field, .. } =>
                    write!(out, ".{}", field.raw())?,
            }
        }
        write!(f, "{out}")
    }
}

#[derive(Clone, Copy, clyde_macros::Recursible)]
pub enum Operand<'tcx> {
    Copy(#[non_recursible] RegisterId),
    Const(Const<'tcx>),
    Global(Global<'tcx>),
}

impl<'tcx> std::fmt::Display for Operand<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operand::Copy(reg) => write!(f, "copy {reg:?}"),
            Operand::Const(cnst) => write!(f, "const {cnst}"),
            Operand::Global(global) => write!(f, "{global}"),
       }
    }
}

#[derive(Clone, Copy, clyde_macros::Recursible)]
pub struct SpanOperand<'tcx> {
    pub operand: Operand<'tcx>,
    #[non_recursible]
    pub span: Span
}

impl<'tcx> Operand<'tcx> {
    fn with_span(self, span: Span) -> SpanOperand<'tcx> {
        SpanOperand {
            operand: self,
            span
        }
    }
}

#[derive(Clone, clyde_macros::Recursible)]
pub enum RValue<'tcx> {
    Const(Const<'tcx>),
    Read(Place<'tcx>),
    Ref(Place<'tcx>),
    Invert(Operand<'tcx>),
    Negate(Operand<'tcx>),
    Global(Global<'tcx>),
    BinaryOp {
        lhs: Operand<'tcx>,
        rhs: Operand<'tcx>,
        #[non_recursible]
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

impl<'tcx> From<Operand<'tcx>> for RValue<'tcx> {
    fn from(value: Operand<'tcx>) -> Self {
        match value {
            Operand::Copy(reg) => RValue::Read(Place::register(reg)),
            Operand::Const(cnst) => RValue::Const(cnst),
            Operand::Global(global) => RValue::Global(global)
        }
    }
}

impl<'tcx> std::fmt::Display for RValue<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            // RValue::Use(operand) => write!(f, "{operand:?}"),
            RValue::Read(place) => write!(f, "{place}"),
            RValue::Ref(place) => write!(f, "&{place}"),
            RValue::Invert(operand) => write!(f, "Inv({operand})"),
            RValue::Negate(operand) => write!(f, "Neg({operand})"),
            RValue::Global(global) => write!(f, "{global}"),
            RValue::BinaryOp { op, lhs, rhs } => write!(f, "{op:?}({lhs}, {rhs})"),
            RValue::Cast { value, ty } => write!(f, "{value} as {ty}"),
            RValue::Call { callee, args: args1 } => {
                let mut args = vec![];
                for arg in args1 {
                    args.push(format!("{}", arg.operand));
                }
                let args = args.join(", ");
                write!(f, "{callee}({args})")
            },
            RValue::Const(cnst) => write!(f, "const {cnst}"),
            RValue::ExplicitInit { ty, initializers } => {
                let mut args = vec![];
                for (idx, operand) in initializers {
                    args.push(format!(".{} = {}", idx.raw(), operand.operand));
                }
                let args = args.join(", ");
                write!(f, "{ty} {{ {args} }}")
            }
        }
    }
}

impl<'tcx> mapping::Recursible<'tcx> for (FieldIdx, SpanOperand<'tcx>) {
    fn map_recurse(self, handler: &mut impl mapping::Mapper<'tcx>) -> Self {
        (self.0, mapping::Recursible::map_recurse(self.1, handler))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

enum ScopeKind<'tcx> {
    Loop {
        continue_target: BlockId,
        break_target: BlockId,
    },
    BlockExpr {
        result_dest: OnceCell<Place<'tcx>>,
        join_block: OnceCell<BlockId>
    },
    Body
}

struct BlockScope<'tcx> {
    owner: NodeId,
    scope: ScopeKind<'tcx>
}

struct TranslationCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    def: DefId,
    num_params: usize,
    typecheck: &'tcx TypecheckResults<'tcx>,
    registers: IndexVec<RegisterId, Register<'tcx>>,
    register_lookup: HashMap<ast::NodeId, RegisterId>,
    blocks: IndexVec<BlockId, BasicBlock<'tcx>>,
    scope_stack: Vec<BlockScope<'tcx>>
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
            blocks: IndexVec::new(),
            scope_stack: vec![],
        };

        for param in params {
            ctxt.create_register(param.node_id, Mutability::Mut);
        }

        ctxt
    }

    fn create_register(&mut self, node_id: NodeId, mutability: Mutability) -> RegisterId {
        let kind = if self.registers.len() < self.num_params {
            RegKind::Param
        } else {
            RegKind::Local
        };
        let reg = self.registers.push(Register {
            kind,
            mutability,
            ty: self.typecheck.locals[&node_id],
        });
        self.register_lookup.insert(node_id, reg);
        reg
    }

    fn tmp_register(&mut self, ty: Ty<'tcx>) -> RegisterId {
        self.registers.push(Register {
            kind: RegKind::Temp,
            mutability: Mutability::Const, ty
        })
    }

    fn create_block(&mut self) -> BlockId {
        self.blocks.push(BasicBlock::default())
    }

    fn emit_into(&mut self, block: BlockId, stmt: Statement<'tcx>) {
        let bb = &mut self.blocks[block];
        if let Some(terminator) = bb.terminator.get() {
            panic!("can't emit into terminated block {block}\n{terminator}");
        }
        if stmt.place.is_none() {
            let RValue::Call { .. } = stmt.rhs else {
                return;
            };
        }
        bb.statements.push(stmt);
    }

    fn enter_block_scope<F: FnOnce(&mut Self) -> R, R>(&mut self, owner: NodeId, scope: ScopeKind<'tcx>, f: F) -> R {
        self.scope_stack.push(BlockScope {
            owner,
            scope
        });
        let rv = f(self);
        let _scope = self.scope_stack.pop().unwrap();
        rv
    }

    fn find_scope(&mut self, owner: NodeId) -> Option<&mut ScopeKind<'tcx>> {
        for scope in self.scope_stack.iter_mut().rev() {
            if scope.owner == owner {
                return Some(&mut scope.scope);
            }
        }
        None
    }

    fn try_get_join_block(&mut self) -> Option<BlockId> {
        let blocks = &mut self.blocks;

        if let Some(BlockScope { scope: ScopeKind::BlockExpr { join_block, .. }, .. }) = self.scope_stack
            .iter_mut()
            .rev()
            .find(|scope| matches!(scope.scope, ScopeKind::BlockExpr { .. })) {
            return Some(*join_block.get_or_init(|| blocks.push(BasicBlock::default())));
        }

        None
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
            ast::ExprKind::UnaryOp(ast::UnaryOp { expr, operator: lexer::UnaryOp::Not }) => {
                let (true_block, false_block) = self.build_diverge(block, expr);
                (false_block, true_block) // it's boolean inv: just flip the targets
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
                    block = self.write_expr_into(Some(Place::register(reg)), block, init);
                }
                block
            }
            ast::StmtKind::Expr(expr) =>
                self.write_expr_into(None, block, expr),
            ast::StmtKind::If(if_stmt) => {
                let (mut then_block, mut else_block) = self.build_diverge(block, if_stmt.condition);

                // FIXME: for now (just if stmts in body-scopes or expr-scopes) this seems to work
                // out. If it will hold up with if-stms within loop-ctxt's or vica verca: 
                // We'll see.
                // One idea for improvement: if the then_ or the else_block, diverge via a
                // `return` terminator, we could potentially skip creating a join_block.
                // I'd also like to not hardcode this in here, but find an even more general
                // solution

                let mut join_block = self.try_get_join_block();
                then_block = self.cover_ast_block(then_block, &if_stmt.body);

                if let Some(else_branch) = if_stmt.else_branch {
                    else_block = self.cover_ast_stmt(else_block, else_branch);
                    if !self.is_terminated(else_block) && Some(then_block) != join_block {
                        let jblock = self.create_block();
                        self.goto(else_block, jblock, else_branch.span);
                        join_block = Some(jblock);
                    }
                }

                let join_block = join_block.unwrap_or(else_block);

                if then_block == join_block {
                    return else_block;
                }

                if !self.is_terminated(then_block) {
                    self.goto(then_block, join_block, stmt.span);
                }

                join_block
            },
            ast::StmtKind::While(while_loop) => {
                let condition_block = self.create_block();
                self.goto(block, condition_block, while_loop.condition.span);

                let (mut then_block, else_block) = self.build_diverge(condition_block, while_loop.condition);
                then_block = self.enter_block_scope(
                    stmt.node_id,
                    ScopeKind::Loop { continue_target: condition_block, break_target: else_block },
                    |this| this.cover_ast_block(then_block, &while_loop.body)
                );
                if !self.is_terminated(then_block) {
                    self.goto(then_block, condition_block, stmt.span);
                }

                else_block
            },
            ast::StmtKind::For(..) => block,
            ast::StmtKind::ControlFlow(control_flow) => {
                if let Ok(dest) = control_flow.destination.get().unwrap() {
                    let Some(ScopeKind::Loop { break_target, continue_target }) = self.find_scope(*dest) else {
                        panic!("expected loop scope");
                    };
                    let (break_target, continue_target) = (*break_target, *continue_target);

                    match control_flow.kind {
                        ast::ControlFlowKind::Break => 
                            self.goto(block, break_target, stmt.span),
                        ast::ControlFlowKind::Continue =>
                            self.goto(block, continue_target, stmt.span),
                    }
                }

                block
            },
            ast::StmtKind::Return(ret) => {
                let op;
                (block, op) = ret.map_or_else(
                    || (block, None),
                    |expr| {
                        let (block, op) = self.expr_as_operand(block, expr);
                        (block, Some(op))
                    });
                self.ret(block, op, stmt.span);
                block
            }
            ast::StmtKind::Yeet(yeet) => {
                if let Ok(owner) = yeet.owner.get().unwrap() {
                    let Some(ScopeKind::BlockExpr { join_block, result_dest }) = self.find_scope(*owner) else {
                        panic!("expected block scope")
                    };
                    let join_block = join_block.get().map(|b| *b);

                    let reg = if yeet.expr.is_some() {
                        result_dest.get().map(|p| *p)
                    } else {
                        None
                    };

                    let dest = if let Some(expr) = yeet.expr {
                        let dest = reg.unwrap_or_else(|| {
                            let ty = self.typecheck.associations[&expr.node_id];
                            Place::register(self.tmp_register(ty))
                        });
                        block = self.write_expr_into(Some(dest), block, expr);

                        Some(dest)
                    } else {
                        None
                    };

                    if let Some(dest) = dest {
                        let Some(ScopeKind::BlockExpr { result_dest, .. }) = self.find_scope(*owner) else {
                            unreachable!()
                        };
                        let _ = result_dest.set(dest);
                    }

                    if let Some(join_block) = join_block {
                        self.goto(block, join_block, stmt.span);
                        return join_block;
                    }
                }

                block
            }
            ast::StmtKind::Block(ast_block) =>
                self.cover_ast_block(block, ast_block),
            ast::StmtKind::Item(_item) => block,
            ast::StmtKind::Err => block
        }
    }

    fn cover_ast_block(&mut self, mut block: BlockId, ast_block: &ast::Block<'tcx>) -> BlockId {
        for stmt in ast_block.stmts {
            block = self.cover_ast_stmt(block, stmt);
            if let Ty(TyKind::Never) = self.typecheck.associations[&stmt.node_id] {
                break; // don't emit after diverging statement, even if there is code, it's
                       // unreachable
            }
        }

        block
    }

    fn handle_logical_op(&mut self, dest: Option<Place<'tcx>>, block: BlockId, logical: LogicalOp, lhs: &'tcx ast::Expr<'tcx>, rhs: &'tcx ast::Expr<'tcx>) -> BlockId {
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
                rhs: Operand::Const(constant).into(),
                span: lhs.span
            }
        );
        
        let rhs_block = self.write_expr_into(dest, continuation, rhs);

        let join_block = self.create_block();
        self.goto(short_circuit, join_block, lhs.span);
        self.goto(rhs_block, join_block, rhs.span);

        join_block
    }

    fn write_expr_into(&mut self, dest: Option<Place<'tcx>>, mut block: BlockId, expr: &'tcx ast::Expr<'tcx>) -> BlockId {
        match &expr.kind {
            ast::ExprKind::Path(path) if let Some(ast::Resolution::Local(..) | ast::Resolution::Def(_, DefinitionKind::Static)) = path.resolution() => {
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
            ast::ExprKind::Path(..) | ast::ExprKind::Literal(..) => {
                let operand;
                (block, operand) = self.expr_as_operand(block, expr);

                self.emit_into(
                    block,
                    Statement {
                        place: dest,
                        rhs: operand.into(),
                        span: expr.span
                    }
                );

                block
            }
            ast::ExprKind::BinaryOp(binary) if let op @ (lexer::BinaryOp::BooleanOr | lexer::BinaryOp::BooleanAnd) = binary.operator => {
                let logical = match op {
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
                                place: Some(dest2),
                                rhs: rhs.into(),
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

                let lhs = if let Some(reg) = dest2.as_register() {
                    Operand::Copy(reg)
                } else {
                    let reg = self.tmp_register(self.typecheck.associations[&expr.node_id]);
                    self.emit_into(
                        block,
                        Statement {
                            place: Some(Place::register(reg)),
                            rhs: RValue::Read(dest2),
                            span: Span::NULL
                        }
                    );
                    Operand::Copy(reg)
                };

                self.emit_into(
                    block,
                    Statement {
                        place: Some(dest2),
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
                    Place::register(reg)
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
                let ty = self.typecheck.associations[&expr.node_id];
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
                if let Some(ScopeKind::Body) = self.find_scope(expr.node_id) {
                    return self.cover_ast_block(block, ast_block);
                }
                let result_dest = if let Some(dest) = dest {
                    let cell = OnceCell::new();
                    let _ = cell.set(dest);
                    cell
                } else {
                    OnceCell::new()
                };

                block = self.enter_block_scope(
                    expr.node_id,
                    ScopeKind::BlockExpr { join_block: OnceCell::new(), result_dest },
                    |this| this.cover_ast_block(block, ast_block)
                );
                block
            }
            ast::ExprKind::Tuple(args) => {

                let ty = self.typecheck.associations[&expr.node_id];

                let mut initializers = vec![];

                for (idx, expr) in args.iter().enumerate() {
                    let ir_init;
                    (block, ir_init) = self.expr_as_operand(block, expr);
                    let ir_idx = FieldIdx::from_usize(idx);

                    initializers.push((ir_idx, ir_init.with_span(expr.span)));
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
            },
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
            ast::ExprKind::Range(..) => todo!(),
            ast::ExprKind::Err => block
        }
    }

    fn as_register(&mut self, block: BlockId, expr: &'tcx ast::Expr<'tcx>) -> (BlockId, RegisterId) {
        if let ast::ExprKind::Path(path) = &expr.kind {
            if let Some(ast::Resolution::Local(local)) = path.resolution() {
                return (block, self.register_lookup[local]);
            }
        }
        let ty = self.typecheck.associations[&expr.node_id];
        let reg = self.tmp_register(ty);
        let dest = Place::register(reg);
        let block = self.write_expr_into(Some(dest), block, expr);
        (block, reg)
    }

    fn convert_to_place_recursively(&mut self,
        translation_chain: &mut Vec<PtrTranslation<'tcx>>,
        mut block: BlockId,
        expr: &ast::Expr<'tcx>
    ) -> Option<(BlockId, RegisterId)> {
        let res = match &expr.kind {
            ast::ExprKind::Path(path) if let Some(ast::Resolution::Local(local)) = path.resolution() =>
                (block, self.register_lookup[local]),
            ast::ExprKind::Path(path) if let Some(ast::Resolution::Def(def_id, DefinitionKind::Static)) = path.resolution() => {
                // IDEA: we need to be hadling things like this:
                // ```clyde
                // static int count = 0;
                // void fn(...) {
                //     ...
                //     count = ...;
                //     ...
                // }
                // ```
                // which in IR should look smth like this:
                // ```
                // bb... {
                //     %0 = ...
                //     %1 = { read count as *int }
                //     *%1 = %0
                // }
                // ```
                // Despite the type of the global being `int` the thing we'll read and get is
                // an `int*`, which means:
                //  - Statics can only really be used as RValues
                //  - Loaded as pointers (or strings + slices) to the value in memory
                //  - Need to be derefrenced to be used effectively

                let ref_ty = Ty::new_refrence(self.tcx, self.tcx.type_of(*def_id));
                let reg = self.tmp_register(ref_ty);
                self.emit_into(block,
                    Statement {
                        place: Some(Place::register(reg)),
                        rhs: RValue::Global(Global::from_definition(self.tcx, *def_id)),
                        span: expr.span
                    }
                );

                translation_chain.push(PtrTranslation::Deref);

                (block, reg)
            }
            ast::ExprKind::Subscript(subscript) => {
                debug_assert_eq!(subscript.args.len(), 1);
                let target;
                (block, target) = self.convert_to_place_recursively(translation_chain, block, subscript.expr)
                    .unwrap_or_else(|| self.as_register(block, subscript.expr));
                let idx;
                (block, idx) = self.expr_as_operand(block, subscript.args[0]);

                // FIXME: eventhough this is very C-like, refrences (really pointers) shoudn't be
                // trivially indexable, as this goes against how I imagine the language to become
                // at the moment:
                //  - Types should be able to overload the Index operator in order to define thier
                //  own behaviour, which would get really confusing cosidering indexing into a
                //  pointer to a type whose Index operator is overloaded
                //  - Even once refrences are added into the language, as refs and ptrs should be
                //  able to be used somewhat interchanibly (niether semantically very different
                //  like in C++, nor refs = safe and ptrs = unsafe like in rust) making ptrs and
                //  refs behave differently here isn't a solution either
                // So the idea would be to add an `offset` method to every ptr like so
                // `*ptr.offset(i) = 42; print(*ptr.offset(i));` but obviously we don't have
                // methods yet

                let base_ty = self.typecheck.associations[&subscript.expr.node_id];
                if let Ty(TyKind::Refrence(..) | TyKind::Slice(..) | TyKind::String) = base_ty {
                    translation_chain.push(PtrTranslation::Deref);
                }

                translation_chain.push(PtrTranslation::Index { idx });
                (block, target)
            }
            ast::ExprKind::Field(field) => {
                let target;
                (block, target) = self.convert_to_place_recursively(translation_chain, block, field.expr)
                    .unwrap_or_else(|| self.as_register(block, field.expr));

                let mut base_ty = self.typecheck.associations[&field.expr.node_id];
                while let Ty(TyKind::Refrence(inner_ty)) = base_ty {
                    translation_chain.push(PtrTranslation::Deref);
                    base_ty = *inner_ty;
                }

                let field = match field.field {
                    ast::FieldIdent::Named(..) =>
                        self.typecheck.field_indices[&expr.node_id],
                    ast::FieldIdent::Tuple { value, .. } =>
                        FieldIdx::from_usize(value as usize)
                };
                let ty = self.typecheck.associations[&expr.node_id];
                translation_chain.push(PtrTranslation::Field { field, ty });

                // field.field
                (block, target)
            }
            ast::ExprKind::Deref(expr) => {
                let register;
                (block, register) = self.as_register(block, expr);
                translation_chain.push(PtrTranslation::Deref);
                (block, register)
            }
            _ => return None
        };
        Some(res)

    }

    fn try_expr_as_place(&mut self, block: BlockId, expr: &ast::Expr<'tcx>) -> Option<(BlockId, Place<'tcx>)> {
        let mut translation_chain = vec![];
        let Some((block, origin)) = self.convert_to_place_recursively(&mut translation_chain, block, expr) else {
            return None;
        };
        let translation_chain = self.tcx.arena.alloc_slice_copy(&translation_chain);
        let place = Place {
            origin,
            translation_chain
        };
        Some((block, place))
    }

    fn expr_as_place(&mut self, block: BlockId, expr: &ast::Expr<'tcx>) -> (BlockId, Place<'tcx>) {
        self.try_expr_as_place(block, expr).expect("expr should have a place")
    }

    fn expr_as_operand(
        &mut self,
        mut block: BlockId,
        expr: &'tcx ast::Expr<'tcx>,
    ) -> (BlockId, Operand<'tcx>) {
        match &expr.kind {
            ast::ExprKind::Literal(literal) => {
                let ty = self.typecheck.associations[&expr.node_id];
                if let Ty(TyKind::String) = ty {
                    let ast::Literal::String(str) = literal else { unreachable!() };
                    let global = Global::from_array_with_ty(self.tcx, str.as_bytes(), self.tcx.basic_types.byte, ty);
                    (block, Operand::Global(global))
                } else {
                    (block, Operand::Const(Const::from_literal(self.tcx, ty, literal).unwrap()))
                }
            }
            ast::ExprKind::Path(path) if let Some(ast::Resolution::Local(local)) = path.resolution() => {
                // FIXME: remove duplication with Place and Temporaray handling
                
                let mut reg = self.register_lookup[local];
                let info = &self.registers[reg];
                if info.mutability == Mutability::Mut {
                    let tmp = self.tmp_register(info.ty);
                    self.emit_into(
                        block,
                        Statement {
                            place: Some(Place::register(tmp)),
                            rhs: RValue::Read(Place::register(reg)),
                            span: Span::NULL
                        }
                    );
                    reg = tmp;
                }

                (block, Operand::Copy(reg))
            }
            ast::ExprKind::Path(path) => match path.resolution() {
                Some(ast::Resolution::Def(def_id, DefinitionKind::Const)) =>
                    (block, Operand::Const(Const::from_definition(self.tcx, *def_id))),
                Some(ast::Resolution::Def(def_id, DefinitionKind::Variant)) =>
                    (block, Operand::Global(Global::from_definition(self.tcx, *def_id))),
                Some(ast::Resolution::Def(_, DefinitionKind::Function)) => {
                    let func = self.typecheck.associations[&expr.node_id];
                    (block, Operand::Global(Global::from_fn_with_generics(self.tcx, func)))
                },
                Some(ast::Resolution::Def(_, DefinitionKind::Static)) => {
                    // FIXME: remove duplicaiton
                    let register;
                    (block, register) = self.as_register(block, expr);
                    (block, Operand::Copy(register))
                }
                Some(ast::Resolution::Def(..) | ast::Resolution::Primitive(_)) => panic!("unexpected type-like resolution"),
                Some(ast::Resolution::Err) => panic!("ill-resolved name at IR stage"),
                Some(ast::Resolution::Local(..)) => unreachable!(),
                None => panic!("unresolved Name at IR stage")
            }
            _ => {
                let register;
                (block, register) = self.as_register(block, expr);
                (block, Operand::Copy(register))
            }
        }
    }

    fn ret(&mut self, block: BlockId, op: Option<Operand<'tcx>>, span: Span) {
        let terminator = Terminator {
            kind: TerminatorKind::Return { value: op },
            span
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
        assert_ne!(block, dest);
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

    fn build(self, entry: BlockId, result_ty: Ty<'tcx>) -> &'tcx Body<'tcx> {
        self.tcx.arena.alloc(Body {
            entry,
            result_ty,
            origin: self.def,
            num_params: self.num_params,
            basic_blocks: self.blocks,
            local_registers: self.registers
        })
    }
}

pub fn build_ir(tcx: TyCtxt<'_>, def_id: DefId) -> Result<&'_ Body<'_>, ()> {

    let node = tcx.node_by_def_id(def_id);

    let body = node.body()
        .expect("build ir for node without a body");

    let typecheck_results = tcx.typecheck(def_id);
    if typecheck_results.has_errors {
        return Err(());
    }

    let mut ctxt = TranslationCtxt::new(tcx, def_id, typecheck_results, body.params);

    let entry;
    let result_ty = match tcx.def_kind(def_id) {
        DefinitionKind::Function => {
            entry = ctxt.create_block();
            let block = ctxt.enter_block_scope(
                body.body.node_id,
                ScopeKind::Body,
                |ctxt| ctxt.write_expr_into(None, entry, body.body)
            );
            if !ctxt.is_terminated(block) {
                ctxt.ret(
                    block,
                    None,
                    Span::NULL
                );
            }

            let sig = tcx.fn_sig(def_id);
            sig.returns
        }
        DefinitionKind::NestedConst | DefinitionKind::Const |  DefinitionKind::Static => {
            let (block, result);
            entry = ctxt.create_block();
            (block, result) = ctxt.expr_as_operand(entry, body.body);
            ctxt.ret(block, Some(result), Span::NULL);

            tcx.type_of(def_id)
        }
        _ => unreachable!()
    };

    Ok(ctxt.build(entry, result_ty))
}

const INDENT: &'static str = "    ";

impl<'tcx> Print<'tcx> for Body<'tcx> {
    fn print(&self, p: &mut crate::pretty_print::PrettyPrinter<'tcx>) -> std::fmt::Result {
        let node = p.tcx.node_by_def_id(self.origin);
        let ident = match node {
            ast::Node::Item(item) => item.ident(),
            _ => unreachable!()
        };
        let mut args = vec![];
        for i in 0..self.num_params {
            let reg = RegisterId::from_usize(i);
            let reg_info = &self.local_registers[reg];
            args.push(format!("{} {reg}: {}", reg_info.mutability, reg_info.ty));
        }
        let args = args.join(", ");
        let result_ty = self.result_ty;
        write!(p, "fn {}({args}) -> {result_ty} {{\n", ident.symbol.get())?;

        for i in self.num_params..self.local_registers.len() {
            let reg = RegisterId::from_usize(i);
            let reg_info = &self.local_registers[reg];
            write!(p, "{INDENT}{} {reg}: {};\n", reg_info.mutability, reg_info.ty)?;
        }

        for (block, bb) in self.basic_blocks.iter_enumerated() {
            write!(p, "{INDENT}{block} ")?;
            bb.print(p)?;
        }

        write!(p, "}}\n")?;

        Ok(())
    }
}

impl<'tcx> Print<'tcx> for BasicBlock<'tcx> {
    fn print(&self, p: &mut crate::pretty_print::PrettyPrinter<'tcx>) -> std::fmt::Result {     
        write!(p, "{{\n")?;

        for stmt in &self.statements {
            write!(p, "{INDENT}{INDENT}{stmt};\n")?;
        }

        if let Some(terminator) = self.terminator.get() {
            write!(p, "{INDENT}{INDENT}{terminator};\n")?;
        }

        write!(p, "{INDENT}}}\n")
    }
}

