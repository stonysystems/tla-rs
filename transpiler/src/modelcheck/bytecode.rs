//! Stack-based bytecode VM for fast expression evaluation.
//!
//! This module defines the instruction set, chunk representation, and
//! compiler for translating spec expressions into bytecode. The VM uses
//! a simple stack-machine model: operands are pushed onto the stack,
//! operations pop their inputs and push their result.
//!
//! Phase 38.22.1.b.i: Opcode enum and Chunk struct definitions.
//! Phase 38.22.1.b.ii: Bytecode compiler for expressions.

use crate::ast::{BinOp, Expr, Literal, Path, Pattern, UnaryOp};
use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::symbol::Symbol;
use crate::modelcheck::value::RuntimeValue;

/// Index into a `Chunk`'s constant pool.
pub type ConstIdx = u16;

/// Index into the local variable slots.
pub type LocalIdx = u16;

/// Offset for jump instructions (relative to current pc).
pub type JumpOffset = u16;

/// Number of arguments or fields.
pub type ArgCount = u8;

/// A single bytecode instruction.
#[derive(Debug, Clone, PartialEq)]
pub enum Opcode {
    // ── Stack management ──────────────────────────────────────────────
    /// Push a constant from the chunk's constant pool onto the stack.
    LoadConst(ConstIdx),
    /// Push a local variable's value onto the stack.
    LoadLocal(LocalIdx),
    /// Pop the top of stack and store it in a local variable slot.
    StoreLocal(LocalIdx),
    /// Discard the top of stack.
    Pop,
    /// Duplicate the top of stack.
    Dup,

    // ── Field / index access ──────────────────────────────────────────
    /// Pop a struct/enum, push the value of the named field.
    LoadField(Symbol),
    /// Pop an enum, push the value of the named variant field (arrow access).
    LoadArrow(Symbol),
    /// Pop [collection, index], push collection[index].
    GetIndex,

    // ── Comparisons ───────────────────────────────────────────────────
    /// Pop [a, b], push a == b.
    Eq,
    /// Pop [a, b], push a != b.
    Ne,
    /// Pop [a, b], push a < b.
    Lt,
    /// Pop [a, b], push a <= b.
    Le,
    /// Pop [a, b], push a > b.
    Gt,
    /// Pop [a, b], push a >= b.
    Ge,

    // ── Arithmetic / logic ────────────────────────────────────────────
    /// Pop [a, b], push the result of a binary operation.
    BinaryOp(BinOp),
    /// Pop a, push !a (boolean negation).
    UnaryNot,
    /// Pop a, push -a (integer negation).
    UnaryNeg,

    // ── Type tests ────────────────────────────────────────────────────
    /// Pop a value, push whether it `is` the named variant.
    Is(Symbol),

    // ── Collection literals ───────────────────────────────────────────
    /// Pop `n` values, construct a set literal, push it.
    SetLit(ArgCount),
    /// Pop `2*n` values (key, value pairs), construct a map literal, push it.
    MapLit(ArgCount),
    /// Pop `n` values, construct a sequence literal, push it.
    SeqLit(ArgCount),

    // ── Struct construction ───────────────────────────────────────────
    /// Pop `n` field values (in the order given by `field_names` in the
    /// chunk's struct-field table at `struct_idx`), construct a struct, push it.
    /// The `ConstIdx` indexes into `Chunk::struct_metas`.
    StructNew(ConstIdx),
    /// Pop [base_struct, n field values], apply field updates, push result.
    /// `ConstIdx` indexes into `Chunk::struct_update_metas`.
    StructUpdate(ConstIdx),

    // ── Control flow ──────────────────────────────────────────────────
    /// If top-of-stack is false, jump forward by `offset` instructions.
    /// Pops the condition.
    JumpIfFalse(JumpOffset),
    /// If top-of-stack is true, jump forward by `offset` instructions.
    /// Pops the condition.
    JumpIfTrue(JumpOffset),
    /// Unconditional forward jump by `offset` instructions.
    Jump(JumpOffset),

    // ── Function / method calls ───────────────────────────────────────
    /// Pop `n` arguments (topmost = last arg), call a named function, push result.
    /// `ConstIdx` indexes into `Chunk::call_targets`.
    Call(ConstIdx, ArgCount),
    /// Pop [receiver, n arguments], call a named method, push result.
    /// The `Symbol` is the method name.
    MethodCall(Symbol, ArgCount),

    // ── Quantifiers ───────────────────────────────────────────────────
    /// Universal quantifier. The body is the next `body_len` instructions.
    /// The VM iterates the domain (popped from stack), binds each element
    /// to `LocalIdx`, executes the body, and short-circuits on false.
    /// Pushes the final boolean result.
    Forall {
        var: LocalIdx,
        body_len: JumpOffset,
    },
    /// Existential quantifier. Same as Forall but short-circuits on true.
    Exists {
        var: LocalIdx,
        body_len: JumpOffset,
    },
    /// Choose: find a value satisfying the body predicate. Body is the
    /// next `body_len` instructions. Iterates domain, returns first match.
    Choose {
        var: LocalIdx,
        body_len: JumpOffset,
    },

    // ── Termination ───────────────────────────────────────────────────
    /// Return the top-of-stack value from the current chunk.
    Return,
}

/// Metadata for `StructNew` instructions.
#[derive(Debug, Clone)]
pub struct StructNewMeta {
    /// The type name for the struct.
    pub type_name: String,
    /// Field names in the order values are expected on the stack
    /// (first pushed = first field).
    pub field_names: Vec<Symbol>,
}

/// Metadata for `StructUpdate` instructions.
#[derive(Debug, Clone)]
pub struct StructUpdateMeta {
    /// Optional type name (None = infer from base).
    pub type_name: Option<String>,
    /// Field names being updated, in the order values are on the stack.
    pub update_field_names: Vec<Symbol>,
}

/// A compiled bytecode chunk for a single expression or function body.
#[derive(Debug, Clone)]
pub struct Chunk {
    /// The instruction sequence.
    pub ops: Vec<Opcode>,
    /// Constant pool: literals and other immutable values.
    pub constants: Vec<RuntimeValue>,
    /// Metadata for `StructNew` instructions, indexed by the `ConstIdx`
    /// in the opcode.
    pub struct_metas: Vec<StructNewMeta>,
    /// Metadata for `StructUpdate` instructions, indexed by the `ConstIdx`
    /// in the opcode.
    pub struct_update_metas: Vec<StructUpdateMeta>,
    /// Function call targets, indexed by the `ConstIdx` in `Call` opcodes.
    pub call_targets: Vec<Path>,
    /// Number of local variable slots needed.
    pub num_locals: u16,
}

impl Chunk {
    /// Create an empty chunk.
    pub fn new() -> Self {
        Self {
            ops: Vec::new(),
            constants: Vec::new(),
            struct_metas: Vec::new(),
            struct_update_metas: Vec::new(),
            call_targets: Vec::new(),
            num_locals: 0,
        }
    }

    /// Append an opcode and return its index.
    pub fn emit(&mut self, op: Opcode) -> usize {
        let idx = self.ops.len();
        self.ops.push(op);
        idx
    }

    /// Add a constant to the pool and return its index.
    pub fn add_const(&mut self, value: RuntimeValue) -> ConstIdx {
        let idx = self.constants.len();
        self.constants.push(value);
        idx as ConstIdx
    }

    /// Add a struct-new metadata entry and return its index.
    pub fn add_struct_meta(&mut self, meta: StructNewMeta) -> ConstIdx {
        let idx = self.struct_metas.len();
        self.struct_metas.push(meta);
        idx as ConstIdx
    }

    /// Add a struct-update metadata entry and return its index.
    pub fn add_struct_update_meta(&mut self, meta: StructUpdateMeta) -> ConstIdx {
        let idx = self.struct_update_metas.len();
        self.struct_update_metas.push(meta);
        idx as ConstIdx
    }

    /// Add a call target and return its index.
    pub fn add_call_target(&mut self, path: Path) -> ConstIdx {
        let idx = self.call_targets.len();
        self.call_targets.push(path);
        idx as ConstIdx
    }

    /// Allocate a new local variable slot and return its index.
    pub fn alloc_local(&mut self) -> LocalIdx {
        let idx = self.num_locals;
        self.num_locals += 1;
        idx
    }

    /// Patch a jump instruction at `op_idx` with the correct offset
    /// from `op_idx` to the current end of the ops list.
    pub fn patch_jump(&mut self, op_idx: usize) {
        let offset = (self.ops.len() - op_idx - 1) as JumpOffset;
        match &mut self.ops[op_idx] {
            Opcode::JumpIfFalse(ref mut o)
            | Opcode::JumpIfTrue(ref mut o)
            | Opcode::Jump(ref mut o) => *o = offset,
            _ => panic!("patch_jump called on non-jump opcode at index {}", op_idx),
        }
    }
}

// ── Bytecode compiler ─────────────────────────────────────────────────

/// Maps variable names to local slot indices, with scoped push/pop.
pub struct LocalTable {
    entries: Vec<(String, LocalIdx)>,
}

impl LocalTable {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Look up a variable, searching from most recent to oldest.
    pub fn get(&self, name: &str) -> Option<LocalIdx> {
        self.entries
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, idx)| *idx)
    }

    /// Push a new variable binding.
    pub fn push(&mut self, name: String, idx: LocalIdx) {
        self.entries.push((name, idx));
    }

    /// Save the current depth for later restoration.
    pub fn save_depth(&self) -> usize {
        self.entries.len()
    }

    /// Restore to a previously saved depth.
    pub fn restore(&mut self, depth: usize) {
        self.entries.truncate(depth);
    }
}

/// Compile a top-level expression into a `Chunk`.
pub fn compile(expr: &Expr) -> TranspileResult<Chunk> {
    let mut chunk = Chunk::new();
    let mut locals = LocalTable::new();
    compile_expr(expr, &mut chunk, &mut locals)?;
    chunk.emit(Opcode::Return);
    Ok(chunk)
}

/// Compile an expression, emitting opcodes that leave one value on the stack.
pub fn compile_expr(
    expr: &Expr,
    chunk: &mut Chunk,
    locals: &mut LocalTable,
) -> TranspileResult<()> {
    match expr {
        Expr::ConstantValue(v) => {
            let ci = chunk.add_const(v.clone());
            chunk.emit(Opcode::LoadConst(ci));
        }
        Expr::Literal(lit) => {
            let v = match lit {
                Literal::Bool(b) => RuntimeValue::Bool(*b),
                Literal::Int(i) => RuntimeValue::Int(*i),
                Literal::String(s) => RuntimeValue::String(s.clone()),
            };
            let ci = chunk.add_const(v);
            chunk.emit(Opcode::LoadConst(ci));
        }
        Expr::Ident(name) => {
            if let Some(slot) = locals.get(name) {
                chunk.emit(Opcode::LoadLocal(slot));
            } else {
                // Unresolved ident — could be an enum variant path.
                // Encode as a constant placeholder that the VM resolves.
                let ci = chunk.add_const(RuntimeValue::String(name.clone()));
                chunk.emit(Opcode::LoadConst(ci));
            }
        }

        // ── Field / index access ──────────────────────────────────────
        Expr::Field(base, field) => {
            compile_expr(base, chunk, locals)?;
            chunk.emit(Opcode::LoadField(Symbol::intern(field)));
        }
        Expr::Arrow(base, field) => {
            compile_expr(base, chunk, locals)?;
            chunk.emit(Opcode::LoadArrow(Symbol::intern(field)));
        }
        Expr::Index(base, idx) => {
            compile_expr(base, chunk, locals)?;
            compile_expr(idx, chunk, locals)?;
            chunk.emit(Opcode::GetIndex);
        }

        // ── Comparisons ───────────────────────────────────────────────
        Expr::Eq(lhs, rhs) => {
            compile_expr(lhs, chunk, locals)?;
            compile_expr(rhs, chunk, locals)?;
            chunk.emit(Opcode::Eq);
        }
        Expr::Ne(lhs, rhs) => {
            compile_expr(lhs, chunk, locals)?;
            compile_expr(rhs, chunk, locals)?;
            chunk.emit(Opcode::Ne);
        }
        Expr::Lt(lhs, rhs) => {
            compile_expr(lhs, chunk, locals)?;
            compile_expr(rhs, chunk, locals)?;
            chunk.emit(Opcode::Lt);
        }
        Expr::Le(lhs, rhs) => {
            compile_expr(lhs, chunk, locals)?;
            compile_expr(rhs, chunk, locals)?;
            chunk.emit(Opcode::Le);
        }
        Expr::Gt(lhs, rhs) => {
            compile_expr(lhs, chunk, locals)?;
            compile_expr(rhs, chunk, locals)?;
            chunk.emit(Opcode::Gt);
        }
        Expr::Ge(lhs, rhs) => {
            compile_expr(lhs, chunk, locals)?;
            compile_expr(rhs, chunk, locals)?;
            chunk.emit(Opcode::Ge);
        }

        // ── Logical operators ─────────────────────────────────────────
        Expr::Not(inner) => {
            compile_expr(inner, chunk, locals)?;
            chunk.emit(Opcode::UnaryNot);
        }
        Expr::Conjunction(items) => {
            // Short-circuit AND: if any item is false, jump to end with false.
            // Each item: compile, JumpIfFalse(end), ...
            // After all items: push true, Jump(past_false).
            // At end: push false.
            if items.is_empty() {
                let ci = chunk.add_const(RuntimeValue::Bool(true));
                chunk.emit(Opcode::LoadConst(ci));
                return Ok(());
            }
            let mut false_jumps = Vec::new();
            for item in items {
                compile_expr(item, chunk, locals)?;
                let jmp = chunk.emit(Opcode::JumpIfFalse(0));
                false_jumps.push(jmp);
            }
            // All items were true
            let ci_true = chunk.add_const(RuntimeValue::Bool(true));
            chunk.emit(Opcode::LoadConst(ci_true));
            let done_jmp = chunk.emit(Opcode::Jump(0));
            // False target
            let false_pos = chunk.ops.len();
            let ci_false = chunk.add_const(RuntimeValue::Bool(false));
            chunk.emit(Opcode::LoadConst(ci_false));
            // Patch all false jumps to point here
            for jmp in false_jumps {
                let offset = (false_pos - jmp - 1) as JumpOffset;
                match &mut chunk.ops[jmp] {
                    Opcode::JumpIfFalse(ref mut o) => *o = offset,
                    _ => unreachable!(),
                }
            }
            // Patch done jump to skip past the false push
            chunk.patch_jump(done_jmp);
        }
        Expr::Disjunction(items) => {
            // Short-circuit OR: if any item is true, jump to end with true.
            if items.is_empty() {
                let ci = chunk.add_const(RuntimeValue::Bool(false));
                chunk.emit(Opcode::LoadConst(ci));
                return Ok(());
            }
            let mut true_jumps = Vec::new();
            for item in items {
                compile_expr(item, chunk, locals)?;
                let jmp = chunk.emit(Opcode::JumpIfTrue(0));
                true_jumps.push(jmp);
            }
            // All items were false
            let ci_false = chunk.add_const(RuntimeValue::Bool(false));
            chunk.emit(Opcode::LoadConst(ci_false));
            let done_jmp = chunk.emit(Opcode::Jump(0));
            // True target
            let true_pos = chunk.ops.len();
            let ci_true = chunk.add_const(RuntimeValue::Bool(true));
            chunk.emit(Opcode::LoadConst(ci_true));
            for jmp in true_jumps {
                let offset = (true_pos - jmp - 1) as JumpOffset;
                match &mut chunk.ops[jmp] {
                    Opcode::JumpIfTrue(ref mut o) => *o = offset,
                    _ => unreachable!(),
                }
            }
            chunk.patch_jump(done_jmp);
        }
        Expr::Implies(lhs, rhs) => {
            // !lhs || rhs — short-circuit: if lhs is false, result is true
            compile_expr(lhs, chunk, locals)?;
            let false_jmp = chunk.emit(Opcode::JumpIfFalse(0));
            // lhs was true, evaluate rhs
            compile_expr(rhs, chunk, locals)?;
            let done_jmp = chunk.emit(Opcode::Jump(0));
            // lhs was false → result is true
            chunk.patch_jump(false_jmp);
            let ci = chunk.add_const(RuntimeValue::Bool(true));
            chunk.emit(Opcode::LoadConst(ci));
            chunk.patch_jump(done_jmp);
        }
        Expr::Iff(lhs, rhs) => {
            compile_expr(lhs, chunk, locals)?;
            compile_expr(rhs, chunk, locals)?;
            chunk.emit(Opcode::Eq);
        }

        // ── Arithmetic / unary ────────────────────────────────────────
        Expr::Binary(lhs, op, rhs) => {
            // Short-circuit for And/Or
            match op {
                BinOp::And => {
                    compile_expr(lhs, chunk, locals)?;
                    let false_jmp = chunk.emit(Opcode::JumpIfFalse(0));
                    compile_expr(rhs, chunk, locals)?;
                    let done_jmp = chunk.emit(Opcode::Jump(0));
                    chunk.patch_jump(false_jmp);
                    let ci = chunk.add_const(RuntimeValue::Bool(false));
                    chunk.emit(Opcode::LoadConst(ci));
                    chunk.patch_jump(done_jmp);
                }
                BinOp::Or => {
                    compile_expr(lhs, chunk, locals)?;
                    let true_jmp = chunk.emit(Opcode::JumpIfTrue(0));
                    compile_expr(rhs, chunk, locals)?;
                    let done_jmp = chunk.emit(Opcode::Jump(0));
                    chunk.patch_jump(true_jmp);
                    let ci = chunk.add_const(RuntimeValue::Bool(true));
                    chunk.emit(Opcode::LoadConst(ci));
                    chunk.patch_jump(done_jmp);
                }
                _ => {
                    compile_expr(lhs, chunk, locals)?;
                    compile_expr(rhs, chunk, locals)?;
                    chunk.emit(Opcode::BinaryOp(*op));
                }
            }
        }
        Expr::Unary(op, inner) => {
            compile_expr(inner, chunk, locals)?;
            match op {
                UnaryOp::Not => {
                    chunk.emit(Opcode::UnaryNot);
                }
                UnaryOp::Neg => {
                    chunk.emit(Opcode::UnaryNeg);
                }
                UnaryOp::Deref => {
                    // Deref is a no-op in model-check context
                }
            }
        }

        // ── Type tests ────────────────────────────────────────────────
        Expr::Is(base, variant) => {
            compile_expr(base, chunk, locals)?;
            chunk.emit(Opcode::Is(Symbol::intern(variant)));
        }

        // ── Collection literals ───────────────────────────────────────
        Expr::SetLit(items) => {
            for item in items {
                compile_expr(item, chunk, locals)?;
            }
            chunk.emit(Opcode::SetLit(items.len() as ArgCount));
        }
        Expr::SeqLit(items) => {
            for item in items {
                compile_expr(item, chunk, locals)?;
            }
            chunk.emit(Opcode::SeqLit(items.len() as ArgCount));
        }
        Expr::MapLit(entries) => {
            for (key, value) in entries {
                compile_expr(key, chunk, locals)?;
                compile_expr(value, chunk, locals)?;
            }
            chunk.emit(Opcode::MapLit(entries.len() as ArgCount));
        }
        Expr::SetEmpty => {
            chunk.emit(Opcode::SetLit(0));
        }
        Expr::SeqEmpty => {
            chunk.emit(Opcode::SeqLit(0));
        }
        Expr::MapEmpty => {
            chunk.emit(Opcode::MapLit(0));
        }

        // ── Struct construction ───────────────────────────────────────
        Expr::Struct { name, fields } => {
            // Separate out `..base` field if present
            let mut base_expr = None;
            let mut regular_fields = Vec::new();
            for (field, value_expr) in fields {
                if field == ".." {
                    base_expr = Some(value_expr);
                } else {
                    regular_fields.push((field.as_str(), value_expr));
                }
            }
            if let Some(base_expr) = base_expr {
                // This is a struct update via Struct syntax
                compile_expr(base_expr, chunk, locals)?;
                for (_, value_expr) in &regular_fields {
                    compile_expr(value_expr, chunk, locals)?;
                }
                let meta_idx = chunk.add_struct_update_meta(StructUpdateMeta {
                    type_name: if name.segments.is_empty() {
                        None
                    } else {
                        Some(crate::modelcheck::evaluator::path_name(name))
                    },
                    update_field_names: regular_fields
                        .iter()
                        .map(|(f, _)| Symbol::intern(f))
                        .collect(),
                });
                chunk.emit(Opcode::StructUpdate(meta_idx));
            } else {
                for (_, value_expr) in &regular_fields {
                    compile_expr(value_expr, chunk, locals)?;
                }
                let meta_idx = chunk.add_struct_meta(StructNewMeta {
                    type_name: crate::modelcheck::evaluator::path_name(name),
                    field_names: regular_fields
                        .iter()
                        .map(|(f, _)| Symbol::intern(f))
                        .collect(),
                });
                chunk.emit(Opcode::StructNew(meta_idx));
            }
        }
        Expr::StructUpdate { name, base, fields } => {
            compile_expr(base, chunk, locals)?;
            for (_, value_expr) in fields {
                compile_expr(value_expr, chunk, locals)?;
            }
            let meta_idx = chunk.add_struct_update_meta(StructUpdateMeta {
                type_name: name.as_ref().map(|n| crate::modelcheck::evaluator::path_name(n)),
                update_field_names: fields.iter().map(|(f, _)| Symbol::intern(f)).collect(),
            });
            chunk.emit(Opcode::StructUpdate(meta_idx));
        }

        // ── Control flow ──────────────────────────────────────────────
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            compile_expr(cond, chunk, locals)?;
            let false_jmp = chunk.emit(Opcode::JumpIfFalse(0));
            compile_expr(then_branch, chunk, locals)?;
            let done_jmp = chunk.emit(Opcode::Jump(0));
            chunk.patch_jump(false_jmp);
            if let Some(else_branch) = else_branch {
                compile_expr(else_branch, chunk, locals)?;
            } else {
                let ci = chunk.add_const(RuntimeValue::Unit);
                chunk.emit(Opcode::LoadConst(ci));
            }
            chunk.patch_jump(done_jmp);
        }
        Expr::Let {
            binding,
            value,
            body,
        } => {
            let Pattern::Ident(name) = &binding.pattern else {
                return Err(TranspileError::UnsupportedPattern {
                    message: "non-identifier let binding in bytecode compiler".to_string(),
                    span: None,
                    help: None,
                });
            };
            compile_expr(value, chunk, locals)?;
            let slot = chunk.alloc_local();
            chunk.emit(Opcode::StoreLocal(slot));
            let saved = locals.save_depth();
            locals.push(name.clone(), slot);
            compile_expr(body, chunk, locals)?;
            locals.restore(saved);
        }

        // ── Function / method calls ───────────────────────────────────
        Expr::Call { func, args } => {
            for arg in args {
                compile_expr(arg, chunk, locals)?;
            }
            let ci = chunk.add_call_target(func.clone());
            chunk.emit(Opcode::Call(ci, args.len() as ArgCount));
        }
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => {
            compile_expr(receiver, chunk, locals)?;
            for arg in args {
                compile_expr(arg, chunk, locals)?;
            }
            chunk.emit(Opcode::MethodCall(
                Symbol::intern(method),
                args.len() as ArgCount,
            ));
        }

        // ── View / Cast (pass-through) ────────────────────────────────
        Expr::View(inner) => {
            compile_expr(inner, chunk, locals)?;
        }
        Expr::Cast(inner, _ty) => {
            // In model-check context, casts are mostly no-ops or int→nat.
            // The VM will handle type coercion at runtime.
            compile_expr(inner, chunk, locals)?;
        }

        // ── Quantifiers ───────────────────────────────────────────────
        Expr::Forall { vars, body, .. } => {
            compile_quantifier(vars, body, chunk, locals, QuantifierOp::Forall)?;
        }
        Expr::Exists { vars, body } => {
            compile_quantifier(vars, body, chunk, locals, QuantifierOp::Exists)?;
        }
        Expr::Choose { vars, body } => {
            compile_quantifier(vars, body, chunk, locals, QuantifierOp::Choose)?;
        }

        // ── Match ─────────────────────────────────────────────────────
        Expr::Match { scrutinee, arms } => {
            compile_match(scrutinee, arms, chunk, locals)?;
        }

        // ── Closure (not directly evaluable) ──────────────────────────
        Expr::Closure { .. } => {
            return Err(TranspileError::UnsupportedPattern {
                message: "Closure expressions cannot be compiled to bytecode directly".to_string(),
                span: None,
                help: None,
            });
        }
    }
    Ok(())
}

enum QuantifierOp {
    Forall,
    Exists,
    Choose,
}

/// Compile a quantifier expression. For multi-variable quantifiers, we
/// nest: the outermost variable's body is the compilation of the remaining
/// variables + the actual body.
fn compile_quantifier(
    vars: &[crate::ast::Binding],
    body: &Expr,
    chunk: &mut Chunk,
    locals: &mut LocalTable,
    op: QuantifierOp,
) -> TranspileResult<()> {
    if vars.is_empty() {
        // Degenerate: just compile the body directly
        compile_expr(body, chunk, locals)?;
        return Ok(());
    }

    // For single-variable quantifiers, emit directly.
    // For multi-variable, we recurse: compile inner quantifiers as the body.
    let var = &vars[0];
    let Pattern::Ident(name) = &var.pattern else {
        return Err(TranspileError::UnsupportedPattern {
            message: "non-identifier quantifier binding".to_string(),
            span: None,
            help: None,
        });
    };

    let slot = chunk.alloc_local();
    let saved = locals.save_depth();
    locals.push(name.clone(), slot);

    // Emit a placeholder quantifier opcode; we'll patch body_len after
    // compiling the body.
    let q_idx = match op {
        QuantifierOp::Forall => chunk.emit(Opcode::Forall {
            var: slot,
            body_len: 0,
        }),
        QuantifierOp::Exists => chunk.emit(Opcode::Exists {
            var: slot,
            body_len: 0,
        }),
        QuantifierOp::Choose => chunk.emit(Opcode::Choose {
            var: slot,
            body_len: 0,
        }),
    };

    let body_start = chunk.ops.len();
    if vars.len() > 1 {
        compile_quantifier(&vars[1..], body, chunk, locals, op)?;
    } else {
        compile_expr(body, chunk, locals)?;
    }
    let body_len = (chunk.ops.len() - body_start) as JumpOffset;

    // Patch the body_len
    match &mut chunk.ops[q_idx] {
        Opcode::Forall {
            body_len: ref mut bl,
            ..
        }
        | Opcode::Exists {
            body_len: ref mut bl,
            ..
        }
        | Opcode::Choose {
            body_len: ref mut bl,
            ..
        } => *bl = body_len,
        _ => unreachable!(),
    }

    locals.restore(saved);
    Ok(())
}

/// Compile a match expression into a chain of Is-checks + destructures.
fn compile_match(
    scrutinee: &Expr,
    arms: &[crate::ast::MatchArm],
    chunk: &mut Chunk,
    locals: &mut LocalTable,
) -> TranspileResult<()> {
    // Compile scrutinee once and store in a local
    compile_expr(scrutinee, chunk, locals)?;
    let scrut_slot = chunk.alloc_local();
    chunk.emit(Opcode::StoreLocal(scrut_slot));

    let mut end_jumps = Vec::new();

    for arm in arms {
        let saved = locals.save_depth();

        // Check pattern match — emit code that pushes true/false
        compile_pattern_check(&arm.pattern, scrut_slot, chunk, locals)?;
        let skip_jmp = chunk.emit(Opcode::JumpIfFalse(0));

        // If pattern matched, bind variables and evaluate guard + body
        compile_pattern_bind(&arm.pattern, scrut_slot, chunk, locals)?;

        if let Some(guard) = &arm.guard {
            compile_expr(guard, chunk, locals)?;
            let guard_fail = chunk.emit(Opcode::JumpIfFalse(0));
            compile_expr(&arm.body, chunk, locals)?;
            let end_jmp = chunk.emit(Opcode::Jump(0));
            end_jumps.push(end_jmp);
            chunk.patch_jump(guard_fail);
            // Guard failed — need to jump to next arm, but first clean up
            locals.restore(saved);
            let skip2 = chunk.emit(Opcode::Jump(0));
            chunk.patch_jump(skip_jmp);
            chunk.patch_jump(skip2);
            continue;
        }

        compile_expr(&arm.body, chunk, locals)?;
        let end_jmp = chunk.emit(Opcode::Jump(0));
        end_jumps.push(end_jmp);

        locals.restore(saved);
        chunk.patch_jump(skip_jmp);
    }

    // If no arm matched, push Unit (shouldn't happen in well-typed code)
    let ci = chunk.add_const(RuntimeValue::Unit);
    chunk.emit(Opcode::LoadConst(ci));

    // Patch all end jumps
    for jmp in end_jumps {
        chunk.patch_jump(jmp);
    }

    Ok(())
}

/// Emit code that pushes true/false indicating whether the pattern matches
/// the value in `scrut_slot`.
fn compile_pattern_check(
    pattern: &Pattern,
    scrut_slot: LocalIdx,
    chunk: &mut Chunk,
    _locals: &mut LocalTable,
) -> TranspileResult<()> {
    match pattern {
        Pattern::Wildcard | Pattern::Ident(_) => {
            // Always matches
            let ci = chunk.add_const(RuntimeValue::Bool(true));
            chunk.emit(Opcode::LoadConst(ci));
        }
        Pattern::Literal(lit) => {
            chunk.emit(Opcode::LoadLocal(scrut_slot));
            let v = match lit {
                Literal::Bool(b) => RuntimeValue::Bool(*b),
                Literal::Int(i) => RuntimeValue::Int(*i),
                Literal::String(s) => RuntimeValue::String(s.clone()),
            };
            let ci = chunk.add_const(v);
            chunk.emit(Opcode::LoadConst(ci));
            chunk.emit(Opcode::Eq);
        }
        Pattern::Struct { name, .. } | Pattern::Variant { name, fields: _ } => {
            // Check if the scrutinee is the right variant
            let variant = name.segments.last().cloned().unwrap_or_default();
            chunk.emit(Opcode::LoadLocal(scrut_slot));
            chunk.emit(Opcode::Is(Symbol::intern(&variant)));
        }
        Pattern::Tuple(_) => {
            // Tuples always match (structural), push true
            let ci = chunk.add_const(RuntimeValue::Bool(true));
            chunk.emit(Opcode::LoadConst(ci));
        }
    }
    Ok(())
}

/// Emit code to bind pattern variables (assumes pattern already matched).
fn compile_pattern_bind(
    pattern: &Pattern,
    scrut_slot: LocalIdx,
    chunk: &mut Chunk,
    locals: &mut LocalTable,
) -> TranspileResult<()> {
    match pattern {
        Pattern::Wildcard | Pattern::Literal(_) => {}
        Pattern::Ident(name) => {
            chunk.emit(Opcode::LoadLocal(scrut_slot));
            let slot = chunk.alloc_local();
            chunk.emit(Opcode::StoreLocal(slot));
            locals.push(name.clone(), slot);
        }
        Pattern::Struct { fields, .. } => {
            for (field_name, field_pattern) in fields {
                chunk.emit(Opcode::LoadLocal(scrut_slot));
                chunk.emit(Opcode::LoadArrow(Symbol::intern(field_name)));
                let field_slot = chunk.alloc_local();
                chunk.emit(Opcode::StoreLocal(field_slot));
                compile_pattern_bind(field_pattern, field_slot, chunk, locals)?;
            }
        }
        Pattern::Variant { fields, .. } => {
            // Variant fields are positional, keyed by `_0`, `_1`, etc.
            for (i, field_pattern) in fields.iter().enumerate() {
                chunk.emit(Opcode::LoadLocal(scrut_slot));
                let key = format!("_{i}");
                chunk.emit(Opcode::LoadArrow(Symbol::intern(&key)));
                let field_slot = chunk.alloc_local();
                chunk.emit(Opcode::StoreLocal(field_slot));
                compile_pattern_bind(field_pattern, field_slot, chunk, locals)?;
            }
        }
        Pattern::Tuple(patterns) => {
            for (i, sub_pattern) in patterns.iter().enumerate() {
                chunk.emit(Opcode::LoadLocal(scrut_slot));
                let idx_const = chunk.add_const(RuntimeValue::Int(i as i128));
                chunk.emit(Opcode::LoadConst(idx_const));
                chunk.emit(Opcode::GetIndex);
                let elem_slot = chunk.alloc_local();
                chunk.emit(Opcode::StoreLocal(elem_slot));
                compile_pattern_bind(sub_pattern, elem_slot, chunk, locals)?;
            }
        }
    }
    Ok(())
}

// ── VM interpreter ────────────────────────────────────────────────────

use crate::modelcheck::evaluator::{
    eval_binary, eval_builtin_method, eval_builtin_static_call, expect_bool, expect_index,
    expect_number, split_variant_path, type_error,
};
use crate::modelcheck::value::RuntimeCollectionBounds;

/// Context for VM execution. Mirrors `EvalContext` but without the
/// binding stack (the VM uses local slots instead).
pub struct VmContext<'a> {
    pub bounds: RuntimeCollectionBounds,
    pub call_evaluator: Option<&'a dyn Fn(&Path, &[RuntimeValue]) -> TranspileResult<RuntimeValue>>,
    pub method_evaluator:
        Option<&'a dyn Fn(&RuntimeValue, &str, &[RuntimeValue]) -> TranspileResult<RuntimeValue>>,
    pub quantifier_domain:
        Option<&'a dyn Fn(&crate::ast::Binding) -> TranspileResult<Vec<RuntimeValue>>>,
}

/// Execute a compiled chunk, returning the result value.
pub fn vm_eval(chunk: &Chunk, ctx: &VmContext<'_>) -> TranspileResult<RuntimeValue> {
    let mut pc: usize = 0;
    let mut stack: Vec<RuntimeValue> = Vec::with_capacity(32);
    let mut locals: Vec<RuntimeValue> = vec![RuntimeValue::Unit; chunk.num_locals as usize];

    while pc < chunk.ops.len() {
        match &chunk.ops[pc] {
            Opcode::LoadConst(ci) => {
                stack.push(chunk.constants[*ci as usize].clone());
            }
            Opcode::LoadLocal(slot) => {
                stack.push(locals[*slot as usize].clone());
            }
            Opcode::StoreLocal(slot) => {
                locals[*slot as usize] = stack.pop().unwrap();
            }
            Opcode::Pop => {
                stack.pop();
            }
            Opcode::Dup => {
                let top = stack.last().unwrap().clone();
                stack.push(top);
            }

            // ── Field / index access ──────────────────────────────────
            Opcode::LoadField(sym) => {
                let base = stack.pop().unwrap();
                match base.field_sym(*sym).cloned() {
                    Some(value) => stack.push(value),
                    None => {
                        let name = sym.resolve();
                        if name == "tag" {
                            stack.push(base);
                        } else {
                            return Err(type_error(&format!(
                                "VM: field `.{}` not valid for `{}`",
                                name,
                                base.canonical_key()
                            )));
                        }
                    }
                }
            }
            Opcode::LoadArrow(sym) => {
                let base = stack.pop().unwrap();
                match base.field_sym(*sym).cloned() {
                    Some(value) => stack.push(value),
                    None => {
                        return Err(type_error(&format!(
                            "VM: arrow `->{}` not valid for `{}`",
                            sym.resolve(),
                            base.canonical_key()
                        )));
                    }
                }
            }
            Opcode::GetIndex => {
                let idx = stack.pop().unwrap();
                let base = stack.pop().unwrap();
                match &base {
                    RuntimeValue::Seq(items) => {
                        let pos = expect_index(&idx, "VM seq index")?;
                        stack.push(items.get(pos).cloned().ok_or_else(|| {
                            type_error(&format!(
                                "VM: index {} out of bounds for len {}",
                                pos,
                                items.len()
                            ))
                        })?);
                    }
                    RuntimeValue::Tuple(items) => {
                        let pos = expect_index(&idx, "VM tuple index")?;
                        stack.push(items.get(pos).cloned().ok_or_else(|| {
                            type_error(&format!(
                                "VM: index {} out of bounds for tuple len {}",
                                pos,
                                items.len()
                            ))
                        })?);
                    }
                    RuntimeValue::Map(entries) => {
                        stack.push(entries.get(&idx).cloned().ok_or_else(|| {
                            type_error(&format!(
                                "VM: map key `{}` not found",
                                idx.canonical_key()
                            ))
                        })?);
                    }
                    other => {
                        return Err(type_error(&format!(
                            "VM: index on non-indexable `{}`",
                            other.canonical_key()
                        )));
                    }
                }
            }

            // ── Comparisons ───────────────────────────────────────────
            Opcode::Eq => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                stack.push(RuntimeValue::Bool(lhs == rhs));
            }
            Opcode::Ne => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                stack.push(RuntimeValue::Bool(lhs != rhs));
            }
            Opcode::Lt => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                let l = expect_number(&lhs, "VM lt lhs")?;
                let r = expect_number(&rhs, "VM lt rhs")?;
                stack.push(RuntimeValue::Bool(l < r));
            }
            Opcode::Le => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                let l = expect_number(&lhs, "VM le lhs")?;
                let r = expect_number(&rhs, "VM le rhs")?;
                stack.push(RuntimeValue::Bool(l <= r));
            }
            Opcode::Gt => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                let l = expect_number(&lhs, "VM gt lhs")?;
                let r = expect_number(&rhs, "VM gt rhs")?;
                stack.push(RuntimeValue::Bool(l > r));
            }
            Opcode::Ge => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                let l = expect_number(&lhs, "VM ge lhs")?;
                let r = expect_number(&rhs, "VM ge rhs")?;
                stack.push(RuntimeValue::Bool(l >= r));
            }

            // ── Arithmetic / logic ────────────────────────────────────
            Opcode::BinaryOp(op) => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                stack.push(eval_binary(&lhs, *op, &rhs)?);
            }
            Opcode::UnaryNot => {
                let val = stack.pop().unwrap();
                stack.push(RuntimeValue::Bool(!expect_bool(&val, "VM not")?));
            }
            Opcode::UnaryNeg => {
                let val = stack.pop().unwrap();
                stack.push(RuntimeValue::Int(-expect_number(&val, "VM neg")?));
            }

            // ── Type tests ────────────────────────────────────────────
            Opcode::Is(variant_sym) => {
                let val = stack.pop().unwrap();
                let variant_name = variant_sym.resolve();
                let result = match &val {
                    RuntimeValue::Enum { variant, .. } => *variant == variant_name,
                    _ => false,
                };
                stack.push(RuntimeValue::Bool(result));
            }

            // ── Collection literals ───────────────────────────────────
            Opcode::SetLit(n) => {
                let n = *n as usize;
                let items: Vec<RuntimeValue> = stack.drain(stack.len() - n..).collect();
                stack.push(RuntimeValue::set_bounded(items, &ctx.bounds)?);
            }
            Opcode::SeqLit(n) => {
                let n = *n as usize;
                let items: Vec<RuntimeValue> = stack.drain(stack.len() - n..).collect();
                stack.push(RuntimeValue::seq_bounded(items, &ctx.bounds)?);
            }
            Opcode::MapLit(n) => {
                let n = *n as usize;
                let pairs: Vec<RuntimeValue> = stack.drain(stack.len() - 2 * n..).collect();
                let entries: Vec<(RuntimeValue, RuntimeValue)> = pairs
                    .chunks(2)
                    .map(|chunk| (chunk[0].clone(), chunk[1].clone()))
                    .collect();
                stack.push(RuntimeValue::map_bounded(entries, &ctx.bounds)?);
            }

            // ── Struct construction ───────────────────────────────────
            Opcode::StructNew(meta_idx) => {
                let meta = &chunk.struct_metas[*meta_idx as usize];
                let n = meta.field_names.len();
                let values: Vec<RuntimeValue> = stack.drain(stack.len() - n..).collect();
                let ty_or_variant = &meta.type_name;
                if let Some((ty, variant)) = split_variant_path(ty_or_variant) {
                    let fields: Vec<(String, RuntimeValue)> = meta
                        .field_names
                        .iter()
                        .zip(values)
                        .map(|(sym, v)| (sym.resolve(), v))
                        .collect();
                    stack.push(RuntimeValue::enum_value(ty, variant, fields)?);
                } else {
                    let fields: Vec<(String, RuntimeValue)> = meta
                        .field_names
                        .iter()
                        .zip(values)
                        .map(|(sym, v)| (sym.resolve(), v))
                        .collect();
                    stack.push(RuntimeValue::struct_value(ty_or_variant.clone(), fields)?);
                }
            }
            Opcode::StructUpdate(meta_idx) => {
                let meta = &chunk.struct_update_metas[*meta_idx as usize];
                let n = meta.update_field_names.len();
                let values: Vec<RuntimeValue> = stack.drain(stack.len() - n..).collect();
                let base = stack.pop().unwrap();
                match base {
                    RuntimeValue::Struct {
                        ty, mut fields, ..
                    } => {
                        for (sym, value) in meta.update_field_names.iter().zip(values) {
                            fields.insert(*sym, value);
                        }
                        stack.push(RuntimeValue::struct_value_sym(ty, fields));
                    }
                    RuntimeValue::Enum {
                        ty,
                        variant,
                        mut fields,
                        ..
                    } => {
                        for (sym, value) in meta.update_field_names.iter().zip(values) {
                            fields.insert(*sym, value);
                        }
                        stack.push(RuntimeValue::enum_value_sym(ty, variant, fields));
                    }
                    other => {
                        return Err(type_error(&format!(
                            "VM: struct update on non-struct `{}`",
                            other.canonical_key()
                        )));
                    }
                }
            }

            // ── Control flow ──────────────────────────────────────────
            Opcode::JumpIfFalse(offset) => {
                let val = stack.pop().unwrap();
                if !expect_bool(&val, "VM jump-if-false")? {
                    pc += *offset as usize;
                    // pc will be incremented at end of loop
                }
            }
            Opcode::JumpIfTrue(offset) => {
                let val = stack.pop().unwrap();
                if expect_bool(&val, "VM jump-if-true")? {
                    pc += *offset as usize;
                }
            }
            Opcode::Jump(offset) => {
                pc += *offset as usize;
            }

            // ── Function / method calls ───────────────────────────────
            Opcode::Call(target_idx, argc) => {
                let argc = *argc as usize;
                let args: Vec<RuntimeValue> = stack.drain(stack.len() - argc..).collect();
                let func = &chunk.call_targets[*target_idx as usize];

                // Try builtin static calls first
                if let Some(result) = eval_builtin_static_call(func, &args, ctx.bounds)? {
                    stack.push(result);
                } else if let Some(evaluator) = ctx.call_evaluator {
                    stack.push(evaluator(func, &args)?);
                } else {
                    return Err(type_error(&format!(
                        "VM: call `{}` without call evaluator",
                        crate::modelcheck::evaluator::path_name(func)
                    )));
                }
            }
            Opcode::MethodCall(method_sym, argc) => {
                let argc = *argc as usize;
                let args: Vec<RuntimeValue> = stack.drain(stack.len() - argc..).collect();
                let receiver = stack.pop().unwrap();
                let method_name = method_sym.resolve();

                if let Some(result) =
                    eval_builtin_method(&receiver, &method_name, &args, ctx.bounds)?
                {
                    stack.push(result);
                } else if let Some(evaluator) = ctx.method_evaluator {
                    stack.push(evaluator(&receiver, &method_name, &args)?);
                } else {
                    return Err(type_error(&format!(
                        "VM: method `.{}(...)` without method evaluator",
                        method_name
                    )));
                }
            }

            // ── Quantifiers ───────────────────────────────────────────
            Opcode::Forall { var, body_len } => {
                let body_len = *body_len as usize;
                let var_slot = *var as usize;
                // Quantifier domain is not on the stack — it comes from the
                // quantifier_domain callback (same as the AST evaluator).
                // For now, the VM cannot directly run quantifiers without
                // a domain callback. The body is the next `body_len` ops.
                let domain_eval = ctx.quantifier_domain.ok_or_else(|| {
                    type_error("VM: forall without domain evaluator")
                })?;
                // We need the binding info — but the VM doesn't have it.
                // For now, use a dummy binding. The real integration (b.vi)
                // will thread binding metadata through.
                // Skip over the body; quantifiers in pure VM mode need
                // domain info that the compiler doesn't yet embed.
                // For correctness, fall through to a helper:
                let result = vm_eval_quantifier(
                    chunk,
                    ctx,
                    &mut locals,
                    pc + 1,
                    body_len,
                    var_slot,
                    QuantifierMode::Forall,
                    domain_eval,
                )?;
                stack.push(result);
                pc += body_len; // skip body (already executed by helper)
            }
            Opcode::Exists { var, body_len } => {
                let body_len = *body_len as usize;
                let var_slot = *var as usize;
                let domain_eval = ctx.quantifier_domain.ok_or_else(|| {
                    type_error("VM: exists without domain evaluator")
                })?;
                let result = vm_eval_quantifier(
                    chunk,
                    ctx,
                    &mut locals,
                    pc + 1,
                    body_len,
                    var_slot,
                    QuantifierMode::Exists,
                    domain_eval,
                )?;
                stack.push(result);
                pc += body_len;
            }
            Opcode::Choose { var, body_len } => {
                let body_len = *body_len as usize;
                let var_slot = *var as usize;
                let domain_eval = ctx.quantifier_domain.ok_or_else(|| {
                    type_error("VM: choose without domain evaluator")
                })?;
                let result = vm_eval_quantifier(
                    chunk,
                    ctx,
                    &mut locals,
                    pc + 1,
                    body_len,
                    var_slot,
                    QuantifierMode::Choose,
                    domain_eval,
                )?;
                stack.push(result);
                pc += body_len;
            }

            // ── Termination ───────────────────────────────────────────
            Opcode::Return => {
                return stack.pop().ok_or_else(|| type_error("VM: return on empty stack"));
            }
        }
        pc += 1;
    }

    // Fell off the end without Return
    stack.pop().ok_or_else(|| type_error("VM: ended without value on stack"))
}

enum QuantifierMode {
    Forall,
    Exists,
    Choose,
}

/// Execute a quantifier body sub-slice for each domain value.
fn vm_eval_quantifier(
    chunk: &Chunk,
    ctx: &VmContext<'_>,
    locals: &mut [RuntimeValue],
    body_start: usize,
    body_len: usize,
    var_slot: usize,
    mode: QuantifierMode,
    _domain_eval: &dyn Fn(&crate::ast::Binding) -> TranspileResult<Vec<RuntimeValue>>,
) -> TranspileResult<RuntimeValue> {
    // Build a sub-chunk from the body instructions for recursive evaluation.
    // This is simpler than trying to re-enter the main loop at an offset.
    // For the domain, we need the Binding metadata. Since the compiler
    // doesn't embed it yet, we create a dummy int binding.
    let dummy_binding = crate::ast::Binding {
        pattern: Pattern::Ident(format!("__vm_var_{}", var_slot)),
        ty: Some(crate::ast::Type::Int),
        variable_mode: crate::ast::VariableMode::Exec,
    };

    let domain = _domain_eval(&dummy_binding)?;

    match mode {
        QuantifierMode::Forall => {
            if domain.is_empty() {
                return Ok(RuntimeValue::Bool(true));
            }
            for val in domain {
                locals[var_slot] = val;
                let result = vm_eval_body_slice(chunk, ctx, locals, body_start, body_len)?;
                if !expect_bool(&result, "VM forall body")? {
                    return Ok(RuntimeValue::Bool(false));
                }
            }
            Ok(RuntimeValue::Bool(true))
        }
        QuantifierMode::Exists => {
            if domain.is_empty() {
                return Ok(RuntimeValue::Bool(false));
            }
            for val in domain {
                locals[var_slot] = val;
                let result = vm_eval_body_slice(chunk, ctx, locals, body_start, body_len)?;
                if expect_bool(&result, "VM exists body")? {
                    return Ok(RuntimeValue::Bool(true));
                }
            }
            Ok(RuntimeValue::Bool(false))
        }
        QuantifierMode::Choose => {
            for val in &domain {
                locals[var_slot] = val.clone();
                let result = vm_eval_body_slice(chunk, ctx, locals, body_start, body_len)?;
                if expect_bool(&result, "VM choose body")? {
                    return Ok(val.clone());
                }
            }
            Err(type_error("VM: choose found no satisfying value"))
        }
    }
}

/// Execute a sub-slice of a chunk's opcodes using the shared locals array.
fn vm_eval_body_slice(
    chunk: &Chunk,
    ctx: &VmContext<'_>,
    locals: &mut [RuntimeValue],
    start: usize,
    len: usize,
) -> TranspileResult<RuntimeValue> {
    // Create a temporary sub-chunk that references the same constants/metadata
    // but only contains the body instructions.
    let mut sub_chunk = Chunk {
        ops: chunk.ops[start..start + len].to_vec(),
        constants: chunk.constants.clone(),
        struct_metas: chunk.struct_metas.clone(),
        struct_update_metas: chunk.struct_update_metas.clone(),
        call_targets: chunk.call_targets.clone(),
        num_locals: chunk.num_locals,
    };
    // Add a Return at the end so vm_eval terminates properly
    sub_chunk.ops.push(Opcode::Return);

    // We need to use the shared locals. Since vm_eval creates its own,
    // we run inline instead.
    let mut pc: usize = 0;
    let mut stack: Vec<RuntimeValue> = Vec::with_capacity(16);
    let end = sub_chunk.ops.len();

    while pc < end {
        match &sub_chunk.ops[pc] {
            Opcode::LoadConst(ci) => {
                stack.push(sub_chunk.constants[*ci as usize].clone());
            }
            Opcode::LoadLocal(slot) => {
                stack.push(locals[*slot as usize].clone());
            }
            Opcode::StoreLocal(slot) => {
                locals[*slot as usize] = stack.pop().unwrap();
            }
            Opcode::Pop => {
                stack.pop();
            }
            Opcode::Dup => {
                let top = stack.last().unwrap().clone();
                stack.push(top);
            }
            Opcode::LoadField(sym) => {
                let base = stack.pop().unwrap();
                match base.field_sym(*sym).cloned() {
                    Some(value) => stack.push(value),
                    None => {
                        let name = sym.resolve();
                        if name == "tag" {
                            stack.push(base);
                        } else {
                            return Err(type_error(&format!(
                                "VM: field `.{}` not valid",
                                name
                            )));
                        }
                    }
                }
            }
            Opcode::LoadArrow(sym) => {
                let base = stack.pop().unwrap();
                match base.field_sym(*sym).cloned() {
                    Some(value) => stack.push(value),
                    None => {
                        return Err(type_error(&format!(
                            "VM: arrow `->{}` not valid",
                            sym.resolve()
                        )));
                    }
                }
            }
            Opcode::GetIndex => {
                let idx = stack.pop().unwrap();
                let base = stack.pop().unwrap();
                match &base {
                    RuntimeValue::Seq(items) => {
                        let pos = expect_index(&idx, "VM seq index")?;
                        stack.push(items[pos].clone());
                    }
                    RuntimeValue::Tuple(items) => {
                        let pos = expect_index(&idx, "VM tuple index")?;
                        stack.push(items[pos].clone());
                    }
                    RuntimeValue::Map(entries) => {
                        stack.push(entries[&idx].clone());
                    }
                    _ => return Err(type_error("VM: index on non-indexable")),
                }
            }
            Opcode::Eq => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                stack.push(RuntimeValue::Bool(lhs == rhs));
            }
            Opcode::Ne => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                stack.push(RuntimeValue::Bool(lhs != rhs));
            }
            Opcode::Lt => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                stack.push(RuntimeValue::Bool(
                    expect_number(&lhs, "lt")? < expect_number(&rhs, "lt")?,
                ));
            }
            Opcode::Le => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                stack.push(RuntimeValue::Bool(
                    expect_number(&lhs, "le")? <= expect_number(&rhs, "le")?,
                ));
            }
            Opcode::Gt => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                stack.push(RuntimeValue::Bool(
                    expect_number(&lhs, "gt")? > expect_number(&rhs, "gt")?,
                ));
            }
            Opcode::Ge => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                stack.push(RuntimeValue::Bool(
                    expect_number(&lhs, "ge")? >= expect_number(&rhs, "ge")?,
                ));
            }
            Opcode::BinaryOp(op) => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                stack.push(eval_binary(&lhs, *op, &rhs)?);
            }
            Opcode::UnaryNot => {
                let val = stack.pop().unwrap();
                stack.push(RuntimeValue::Bool(!expect_bool(&val, "not")?));
            }
            Opcode::UnaryNeg => {
                let val = stack.pop().unwrap();
                stack.push(RuntimeValue::Int(-expect_number(&val, "neg")?));
            }
            Opcode::Is(variant_sym) => {
                let val = stack.pop().unwrap();
                let vn = variant_sym.resolve();
                let r = matches!(&val, RuntimeValue::Enum { variant, .. } if *variant == vn);
                stack.push(RuntimeValue::Bool(r));
            }
            Opcode::SetLit(n) => {
                let n = *n as usize;
                let items: Vec<RuntimeValue> = stack.drain(stack.len() - n..).collect();
                stack.push(RuntimeValue::set_bounded(items, &ctx.bounds)?);
            }
            Opcode::SeqLit(n) => {
                let n = *n as usize;
                let items: Vec<RuntimeValue> = stack.drain(stack.len() - n..).collect();
                stack.push(RuntimeValue::seq_bounded(items, &ctx.bounds)?);
            }
            Opcode::MapLit(n) => {
                let n = *n as usize;
                let pairs: Vec<RuntimeValue> = stack.drain(stack.len() - 2 * n..).collect();
                let entries: Vec<(RuntimeValue, RuntimeValue)> = pairs
                    .chunks(2)
                    .map(|c| (c[0].clone(), c[1].clone()))
                    .collect();
                stack.push(RuntimeValue::map_bounded(entries, &ctx.bounds)?);
            }
            Opcode::StructNew(meta_idx) => {
                let meta = &sub_chunk.struct_metas[*meta_idx as usize];
                let n = meta.field_names.len();
                let values: Vec<RuntimeValue> = stack.drain(stack.len() - n..).collect();
                let ty_or_variant = &meta.type_name;
                if let Some((ty, variant)) = split_variant_path(ty_or_variant) {
                    let fields: Vec<(String, RuntimeValue)> = meta
                        .field_names
                        .iter()
                        .zip(values)
                        .map(|(sym, v)| (sym.resolve(), v))
                        .collect();
                    stack.push(RuntimeValue::enum_value(ty, variant, fields)?);
                } else {
                    let fields: Vec<(String, RuntimeValue)> = meta
                        .field_names
                        .iter()
                        .zip(values)
                        .map(|(sym, v)| (sym.resolve(), v))
                        .collect();
                    stack.push(RuntimeValue::struct_value(ty_or_variant.clone(), fields)?);
                }
            }
            Opcode::StructUpdate(meta_idx) => {
                let meta = &sub_chunk.struct_update_metas[*meta_idx as usize];
                let n = meta.update_field_names.len();
                let values: Vec<RuntimeValue> = stack.drain(stack.len() - n..).collect();
                let base = stack.pop().unwrap();
                match base {
                    RuntimeValue::Struct {
                        ty, mut fields, ..
                    } => {
                        for (sym, value) in meta.update_field_names.iter().zip(values) {
                            fields.insert(*sym, value);
                        }
                        stack.push(RuntimeValue::struct_value_sym(ty, fields));
                    }
                    RuntimeValue::Enum {
                        ty,
                        variant,
                        mut fields,
                        ..
                    } => {
                        for (sym, value) in meta.update_field_names.iter().zip(values) {
                            fields.insert(*sym, value);
                        }
                        stack.push(RuntimeValue::enum_value_sym(ty, variant, fields));
                    }
                    _ => return Err(type_error("VM: struct update on non-struct")),
                }
            }
            Opcode::JumpIfFalse(offset) => {
                let val = stack.pop().unwrap();
                if !expect_bool(&val, "jif")? {
                    pc += *offset as usize;
                }
            }
            Opcode::JumpIfTrue(offset) => {
                let val = stack.pop().unwrap();
                if expect_bool(&val, "jit")? {
                    pc += *offset as usize;
                }
            }
            Opcode::Jump(offset) => {
                pc += *offset as usize;
            }
            Opcode::Call(target_idx, argc) => {
                let argc = *argc as usize;
                let args: Vec<RuntimeValue> = stack.drain(stack.len() - argc..).collect();
                let func = &sub_chunk.call_targets[*target_idx as usize];
                if let Some(result) = eval_builtin_static_call(func, &args, ctx.bounds)? {
                    stack.push(result);
                } else if let Some(evaluator) = ctx.call_evaluator {
                    stack.push(evaluator(func, &args)?);
                } else {
                    return Err(type_error("VM: call without evaluator"));
                }
            }
            Opcode::MethodCall(method_sym, argc) => {
                let argc = *argc as usize;
                let args: Vec<RuntimeValue> = stack.drain(stack.len() - argc..).collect();
                let receiver = stack.pop().unwrap();
                let method_name = method_sym.resolve();
                if let Some(result) =
                    eval_builtin_method(&receiver, &method_name, &args, ctx.bounds)?
                {
                    stack.push(result);
                } else if let Some(evaluator) = ctx.method_evaluator {
                    stack.push(evaluator(&receiver, &method_name, &args)?);
                } else {
                    return Err(type_error(&format!(
                        "VM: method `.{}` without evaluator",
                        method_name
                    )));
                }
            }
            Opcode::Forall { var, body_len } => {
                let bl = *body_len as usize;
                let vs = *var as usize;
                let de = ctx.quantifier_domain.ok_or_else(|| {
                    type_error("VM: forall without domain")
                })?;
                let result = vm_eval_quantifier(
                    &sub_chunk, ctx, locals, pc + 1, bl, vs,
                    QuantifierMode::Forall, de,
                )?;
                stack.push(result);
                pc += bl;
            }
            Opcode::Exists { var, body_len } => {
                let bl = *body_len as usize;
                let vs = *var as usize;
                let de = ctx.quantifier_domain.ok_or_else(|| {
                    type_error("VM: exists without domain")
                })?;
                let result = vm_eval_quantifier(
                    &sub_chunk, ctx, locals, pc + 1, bl, vs,
                    QuantifierMode::Exists, de,
                )?;
                stack.push(result);
                pc += bl;
            }
            Opcode::Choose { var, body_len } => {
                let bl = *body_len as usize;
                let vs = *var as usize;
                let de = ctx.quantifier_domain.ok_or_else(|| {
                    type_error("VM: choose without domain")
                })?;
                let result = vm_eval_quantifier(
                    &sub_chunk, ctx, locals, pc + 1, bl, vs,
                    QuantifierMode::Choose, de,
                )?;
                stack.push(result);
                pc += bl;
            }
            Opcode::Return => {
                return stack.pop().ok_or_else(|| type_error("VM: return on empty stack"));
            }
        }
        pc += 1;
    }

    stack.pop().ok_or_else(|| type_error("VM: body ended without value"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_chunk_emit_and_const() {
        let mut chunk = Chunk::new();
        let ci = chunk.add_const(RuntimeValue::Int(42));
        let op_idx = chunk.emit(Opcode::LoadConst(ci));

        assert_eq!(ci, 0);
        assert_eq!(op_idx, 0);
        assert_eq!(chunk.constants.len(), 1);
        assert_eq!(chunk.ops.len(), 1);
        assert_eq!(chunk.ops[0], Opcode::LoadConst(0));
    }

    #[test]
    fn test_chunk_alloc_locals() {
        let mut chunk = Chunk::new();
        let a = chunk.alloc_local();
        let b = chunk.alloc_local();
        assert_eq!(a, 0);
        assert_eq!(b, 1);
        assert_eq!(chunk.num_locals, 2);
    }

    #[test]
    fn test_chunk_patch_jump() {
        let mut chunk = Chunk::new();
        // Emit a placeholder jump
        let jmp = chunk.emit(Opcode::JumpIfFalse(0));
        // Emit some instructions
        chunk.emit(Opcode::Pop);
        chunk.emit(Opcode::Pop);
        chunk.emit(Opcode::Pop);
        // Patch: should jump over the 3 Pops (offset = 3)
        chunk.patch_jump(jmp);

        match chunk.ops[jmp] {
            Opcode::JumpIfFalse(offset) => assert_eq!(offset, 3),
            _ => panic!("expected JumpIfFalse"),
        }
    }

    #[test]
    fn test_chunk_struct_meta() {
        let mut chunk = Chunk::new();
        let field_a = Symbol::intern("field_a");
        let field_b = Symbol::intern("field_b");
        let idx = chunk.add_struct_meta(StructNewMeta {
            type_name: "MyStruct".to_string(),
            field_names: vec![field_a, field_b],
        });
        assert_eq!(idx, 0);
        assert_eq!(chunk.struct_metas[0].type_name, "MyStruct");
        assert_eq!(chunk.struct_metas[0].field_names.len(), 2);
    }

    #[test]
    fn test_chunk_call_target() {
        let mut chunk = Chunk::new();
        let path = Path::new(vec!["module".to_string(), "func".to_string()]);
        let idx = chunk.add_call_target(path);
        assert_eq!(idx, 0);
        assert_eq!(chunk.call_targets[0].segments, vec!["module", "func"]);
    }

    #[test]
    fn test_opcode_debug_display() {
        // Ensure Debug is derivable and doesn't panic
        let op = Opcode::LoadConst(0);
        let _ = format!("{:?}", op);

        let op = Opcode::Forall {
            var: 0,
            body_len: 5,
        };
        let _ = format!("{:?}", op);
    }

    #[test]
    fn test_multiple_constants() {
        let mut chunk = Chunk::new();
        let c0 = chunk.add_const(RuntimeValue::Bool(true));
        let c1 = chunk.add_const(RuntimeValue::Int(100));
        let c2 = chunk.add_const(RuntimeValue::Unit);
        assert_eq!(c0, 0);
        assert_eq!(c1, 1);
        assert_eq!(c2, 2);
        assert_eq!(chunk.constants.len(), 3);
    }

    #[test]
    fn test_struct_update_meta() {
        let mut chunk = Chunk::new();
        let field = Symbol::intern("updated_field");
        let idx = chunk.add_struct_update_meta(StructUpdateMeta {
            type_name: Some("Foo".to_string()),
            update_field_names: vec![field],
        });
        assert_eq!(idx, 0);
        assert_eq!(
            chunk.struct_update_metas[0].type_name,
            Some("Foo".to_string())
        );
    }

    // ── Compiler tests (Phase 38.22.1.b.ii) ──────────────────────────

    #[test]
    fn test_compile_literal_int() {
        let expr = Expr::Literal(Literal::Int(42));
        let chunk = compile(&expr).unwrap();
        assert_eq!(chunk.ops.len(), 2); // LoadConst + Return
        assert_eq!(chunk.ops[0], Opcode::LoadConst(0));
        assert_eq!(chunk.ops[1], Opcode::Return);
        assert_eq!(chunk.constants[0], RuntimeValue::Int(42));
    }

    #[test]
    fn test_compile_literal_bool() {
        let expr = Expr::Literal(Literal::Bool(true));
        let chunk = compile(&expr).unwrap();
        assert_eq!(chunk.ops[0], Opcode::LoadConst(0));
        assert_eq!(chunk.constants[0], RuntimeValue::Bool(true));
    }

    #[test]
    fn test_compile_constant_value() {
        let expr = Expr::ConstantValue(RuntimeValue::String("hello".to_string()));
        let chunk = compile(&expr).unwrap();
        assert_eq!(chunk.constants[0], RuntimeValue::String("hello".to_string()));
    }

    #[test]
    fn test_compile_ident_local() {
        // Compile a let binding that creates a local, then references it
        let expr = Expr::Let {
            binding: crate::ast::Binding {
                pattern: Pattern::Ident("x".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            },
            value: Box::new(Expr::Literal(Literal::Int(10))),
            body: Box::new(Expr::Ident("x".to_string())),
        };
        let chunk = compile(&expr).unwrap();
        // Should have: LoadConst(10), StoreLocal(0), LoadLocal(0), Return
        assert!(chunk.ops.contains(&Opcode::StoreLocal(0)));
        assert!(chunk.ops.contains(&Opcode::LoadLocal(0)));
    }

    #[test]
    fn test_compile_field_access() {
        let expr = Expr::Field(
            Box::new(Expr::Ident("s".to_string())),
            "name".to_string(),
        );
        let chunk = compile(&expr).unwrap();
        // Ident "s" → LoadConst (unresolved ident), then LoadField
        let has_load_field = chunk.ops.iter().any(|op| matches!(op, Opcode::LoadField(_)));
        assert!(has_load_field);
    }

    #[test]
    fn test_compile_arrow_access() {
        let expr = Expr::Arrow(
            Box::new(Expr::Ident("e".to_string())),
            "value".to_string(),
        );
        let chunk = compile(&expr).unwrap();
        let has_arrow = chunk.ops.iter().any(|op| matches!(op, Opcode::LoadArrow(_)));
        assert!(has_arrow);
    }

    #[test]
    fn test_compile_index() {
        let expr = Expr::Index(
            Box::new(Expr::Ident("arr".to_string())),
            Box::new(Expr::Literal(Literal::Int(0))),
        );
        let chunk = compile(&expr).unwrap();
        assert!(chunk.ops.contains(&Opcode::GetIndex));
    }

    #[test]
    fn test_compile_eq() {
        let expr = Expr::Eq(
            Box::new(Expr::Literal(Literal::Int(1))),
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        let chunk = compile(&expr).unwrap();
        assert!(chunk.ops.contains(&Opcode::Eq));
    }

    #[test]
    fn test_compile_ne() {
        let expr = Expr::Ne(
            Box::new(Expr::Literal(Literal::Int(1))),
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        let chunk = compile(&expr).unwrap();
        assert!(chunk.ops.contains(&Opcode::Ne));
    }

    #[test]
    fn test_compile_lt() {
        let expr = Expr::Lt(
            Box::new(Expr::Literal(Literal::Int(1))),
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        assert!(compile(&expr).unwrap().ops.contains(&Opcode::Lt));
    }

    #[test]
    fn test_compile_le() {
        let expr = Expr::Le(
            Box::new(Expr::Literal(Literal::Int(1))),
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        assert!(compile(&expr).unwrap().ops.contains(&Opcode::Le));
    }

    #[test]
    fn test_compile_gt() {
        let expr = Expr::Gt(
            Box::new(Expr::Literal(Literal::Int(1))),
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        assert!(compile(&expr).unwrap().ops.contains(&Opcode::Gt));
    }

    #[test]
    fn test_compile_ge() {
        let expr = Expr::Ge(
            Box::new(Expr::Literal(Literal::Int(1))),
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        assert!(compile(&expr).unwrap().ops.contains(&Opcode::Ge));
    }

    #[test]
    fn test_compile_not() {
        let expr = Expr::Not(Box::new(Expr::Literal(Literal::Bool(true))));
        let chunk = compile(&expr).unwrap();
        assert!(chunk.ops.contains(&Opcode::UnaryNot));
    }

    #[test]
    fn test_compile_is() {
        let expr = Expr::Is(
            Box::new(Expr::Ident("msg".to_string())),
            "Data".to_string(),
        );
        let chunk = compile(&expr).unwrap();
        let has_is = chunk.ops.iter().any(|op| matches!(op, Opcode::Is(_)));
        assert!(has_is);
    }

    #[test]
    fn test_compile_conjunction_short_circuit() {
        let expr = Expr::Conjunction(vec![
            Expr::Literal(Literal::Bool(true)),
            Expr::Literal(Literal::Bool(false)),
        ]);
        let chunk = compile(&expr).unwrap();
        // Should have JumpIfFalse for short-circuit
        let has_jif = chunk
            .ops
            .iter()
            .any(|op| matches!(op, Opcode::JumpIfFalse(_)));
        assert!(has_jif);
    }

    #[test]
    fn test_compile_disjunction_short_circuit() {
        let expr = Expr::Disjunction(vec![
            Expr::Literal(Literal::Bool(false)),
            Expr::Literal(Literal::Bool(true)),
        ]);
        let chunk = compile(&expr).unwrap();
        let has_jit = chunk
            .ops
            .iter()
            .any(|op| matches!(op, Opcode::JumpIfTrue(_)));
        assert!(has_jit);
    }

    #[test]
    fn test_compile_implies() {
        let expr = Expr::Implies(
            Box::new(Expr::Literal(Literal::Bool(true))),
            Box::new(Expr::Literal(Literal::Bool(false))),
        );
        let chunk = compile(&expr).unwrap();
        // Should have JumpIfFalse for lhs-is-false shortcut
        let has_jif = chunk
            .ops
            .iter()
            .any(|op| matches!(op, Opcode::JumpIfFalse(_)));
        assert!(has_jif);
    }

    #[test]
    fn test_compile_iff() {
        let expr = Expr::Iff(
            Box::new(Expr::Literal(Literal::Bool(true))),
            Box::new(Expr::Literal(Literal::Bool(true))),
        );
        let chunk = compile(&expr).unwrap();
        // Iff compiles to Eq
        assert!(chunk.ops.contains(&Opcode::Eq));
    }

    #[test]
    fn test_compile_binary_add() {
        let expr = Expr::Binary(
            Box::new(Expr::Literal(Literal::Int(1))),
            BinOp::Add,
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        let chunk = compile(&expr).unwrap();
        assert!(chunk.ops.contains(&Opcode::BinaryOp(BinOp::Add)));
    }

    #[test]
    fn test_compile_binary_and_short_circuit() {
        let expr = Expr::Binary(
            Box::new(Expr::Literal(Literal::Bool(false))),
            BinOp::And,
            Box::new(Expr::Literal(Literal::Bool(true))),
        );
        let chunk = compile(&expr).unwrap();
        let has_jif = chunk
            .ops
            .iter()
            .any(|op| matches!(op, Opcode::JumpIfFalse(_)));
        assert!(has_jif);
    }

    #[test]
    fn test_compile_unary_neg() {
        let expr = Expr::Unary(UnaryOp::Neg, Box::new(Expr::Literal(Literal::Int(5))));
        let chunk = compile(&expr).unwrap();
        assert!(chunk.ops.contains(&Opcode::UnaryNeg));
    }

    #[test]
    fn test_compile_set_lit() {
        let expr = Expr::SetLit(vec![
            Expr::Literal(Literal::Int(1)),
            Expr::Literal(Literal::Int(2)),
        ]);
        let chunk = compile(&expr).unwrap();
        assert!(chunk.ops.contains(&Opcode::SetLit(2)));
    }

    #[test]
    fn test_compile_seq_lit() {
        let expr = Expr::SeqLit(vec![Expr::Literal(Literal::Int(10))]);
        let chunk = compile(&expr).unwrap();
        assert!(chunk.ops.contains(&Opcode::SeqLit(1)));
    }

    #[test]
    fn test_compile_map_lit() {
        let expr = Expr::MapLit(vec![(
            Expr::Literal(Literal::Int(1)),
            Expr::Literal(Literal::Bool(true)),
        )]);
        let chunk = compile(&expr).unwrap();
        assert!(chunk.ops.contains(&Opcode::MapLit(1)));
    }

    #[test]
    fn test_compile_empty_collections() {
        assert!(compile(&Expr::SetEmpty).unwrap().ops.contains(&Opcode::SetLit(0)));
        assert!(compile(&Expr::SeqEmpty).unwrap().ops.contains(&Opcode::SeqLit(0)));
        assert!(compile(&Expr::MapEmpty).unwrap().ops.contains(&Opcode::MapLit(0)));
    }

    #[test]
    fn test_compile_struct_new() {
        let expr = Expr::Struct {
            name: Path::new(vec!["Point".to_string()]),
            fields: vec![
                ("x".to_string(), Expr::Literal(Literal::Int(1))),
                ("y".to_string(), Expr::Literal(Literal::Int(2))),
            ],
        };
        let chunk = compile(&expr).unwrap();
        let has_struct_new = chunk
            .ops
            .iter()
            .any(|op| matches!(op, Opcode::StructNew(_)));
        assert!(has_struct_new);
        assert_eq!(chunk.struct_metas[0].type_name, "Point");
        assert_eq!(chunk.struct_metas[0].field_names.len(), 2);
    }

    #[test]
    fn test_compile_struct_update() {
        let expr = Expr::StructUpdate {
            name: Some(Path::new(vec!["Point".to_string()])),
            base: Box::new(Expr::Ident("p".to_string())),
            fields: vec![("x".to_string(), Expr::Literal(Literal::Int(99)))],
        };
        let chunk = compile(&expr).unwrap();
        let has_struct_update = chunk
            .ops
            .iter()
            .any(|op| matches!(op, Opcode::StructUpdate(_)));
        assert!(has_struct_update);
    }

    #[test]
    fn test_compile_if_then_else() {
        let expr = Expr::If {
            cond: Box::new(Expr::Literal(Literal::Bool(true))),
            then_branch: Box::new(Expr::Literal(Literal::Int(1))),
            else_branch: Some(Box::new(Expr::Literal(Literal::Int(2)))),
        };
        let chunk = compile(&expr).unwrap();
        let has_jif = chunk
            .ops
            .iter()
            .any(|op| matches!(op, Opcode::JumpIfFalse(_)));
        let has_jmp = chunk
            .ops
            .iter()
            .any(|op| matches!(op, Opcode::Jump(_)));
        assert!(has_jif);
        assert!(has_jmp);
    }

    #[test]
    fn test_compile_if_no_else() {
        let expr = Expr::If {
            cond: Box::new(Expr::Literal(Literal::Bool(true))),
            then_branch: Box::new(Expr::Literal(Literal::Int(1))),
            else_branch: None,
        };
        let chunk = compile(&expr).unwrap();
        // Should push Unit for the else branch
        assert!(chunk.constants.contains(&RuntimeValue::Unit));
    }

    #[test]
    fn test_compile_let_binding() {
        let expr = Expr::Let {
            binding: crate::ast::Binding {
                pattern: Pattern::Ident("x".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            },
            value: Box::new(Expr::Literal(Literal::Int(42))),
            body: Box::new(Expr::Binary(
                Box::new(Expr::Ident("x".to_string())),
                BinOp::Add,
                Box::new(Expr::Literal(Literal::Int(1))),
            )),
        };
        let chunk = compile(&expr).unwrap();
        assert!(chunk.ops.contains(&Opcode::StoreLocal(0)));
        assert!(chunk.ops.contains(&Opcode::LoadLocal(0)));
        assert!(chunk.ops.contains(&Opcode::BinaryOp(BinOp::Add)));
    }

    #[test]
    fn test_compile_call() {
        let expr = Expr::Call {
            func: Path::new(vec!["foo".to_string()]),
            args: vec![Expr::Literal(Literal::Int(1))],
        };
        let chunk = compile(&expr).unwrap();
        assert!(chunk.ops.iter().any(|op| matches!(op, Opcode::Call(_, 1))));
        assert_eq!(chunk.call_targets[0].segments, vec!["foo"]);
    }

    #[test]
    fn test_compile_method_call() {
        let expr = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("s".to_string())),
            method: "len".to_string(),
            args: vec![],
        };
        let chunk = compile(&expr).unwrap();
        let has_mc = chunk
            .ops
            .iter()
            .any(|op| matches!(op, Opcode::MethodCall(_, 0)));
        assert!(has_mc);
    }

    #[test]
    fn test_compile_view_passthrough() {
        let expr = Expr::View(Box::new(Expr::Literal(Literal::Int(5))));
        let chunk = compile(&expr).unwrap();
        // View is pass-through, so just the inner literal
        assert_eq!(chunk.constants[0], RuntimeValue::Int(5));
    }

    #[test]
    fn test_compile_forall() {
        let expr = Expr::Forall {
            vars: vec![crate::ast::Binding {
                pattern: Pattern::Ident("i".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            }],
            triggers: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        let chunk = compile(&expr).unwrap();
        let has_forall = chunk
            .ops
            .iter()
            .any(|op| matches!(op, Opcode::Forall { .. }));
        assert!(has_forall);
    }

    #[test]
    fn test_compile_exists() {
        let expr = Expr::Exists {
            vars: vec![crate::ast::Binding {
                pattern: Pattern::Ident("x".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            }],
            body: Box::new(Expr::Eq(
                Box::new(Expr::Ident("x".to_string())),
                Box::new(Expr::Literal(Literal::Int(0))),
            )),
        };
        let chunk = compile(&expr).unwrap();
        let has_exists = chunk
            .ops
            .iter()
            .any(|op| matches!(op, Opcode::Exists { .. }));
        assert!(has_exists);
    }

    #[test]
    fn test_compile_choose() {
        let expr = Expr::Choose {
            vars: vec![crate::ast::Binding {
                pattern: Pattern::Ident("x".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            }],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        let chunk = compile(&expr).unwrap();
        let has_choose = chunk
            .ops
            .iter()
            .any(|op| matches!(op, Opcode::Choose { .. }));
        assert!(has_choose);
    }

    #[test]
    fn test_compile_match_with_wildcard() {
        use crate::ast::MatchArm;
        let expr = Expr::Match {
            scrutinee: Box::new(Expr::Literal(Literal::Int(1))),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Literal(Literal::Int(1)),
                    guard: None,
                    body: Expr::Literal(Literal::Bool(true)),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::Literal(Literal::Bool(false)),
                },
            ],
        };
        let chunk = compile(&expr).unwrap();
        // Match compiles to store scrutinee + pattern checks + jumps
        assert!(chunk.ops.contains(&Opcode::StoreLocal(0)));
        let has_jif = chunk
            .ops
            .iter()
            .any(|op| matches!(op, Opcode::JumpIfFalse(_)));
        assert!(has_jif);
    }

    #[test]
    fn test_compile_conjunction_empty() {
        let expr = Expr::Conjunction(vec![]);
        let chunk = compile(&expr).unwrap();
        assert_eq!(chunk.constants[0], RuntimeValue::Bool(true));
    }

    #[test]
    fn test_compile_disjunction_empty() {
        let expr = Expr::Disjunction(vec![]);
        let chunk = compile(&expr).unwrap();
        assert_eq!(chunk.constants[0], RuntimeValue::Bool(false));
    }

    #[test]
    fn test_compile_nested_let() {
        // let x = 1 in (let y = 2 in x + y)
        let expr = Expr::Let {
            binding: crate::ast::Binding {
                pattern: Pattern::Ident("x".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            },
            value: Box::new(Expr::Literal(Literal::Int(1))),
            body: Box::new(Expr::Let {
                binding: crate::ast::Binding {
                    pattern: Pattern::Ident("y".to_string()),
                    ty: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                },
                value: Box::new(Expr::Literal(Literal::Int(2))),
                body: Box::new(Expr::Binary(
                    Box::new(Expr::Ident("x".to_string())),
                    BinOp::Add,
                    Box::new(Expr::Ident("y".to_string())),
                )),
            }),
        };
        let chunk = compile(&expr).unwrap();
        // x at slot 0, y at slot 1
        assert!(chunk.ops.contains(&Opcode::StoreLocal(0)));
        assert!(chunk.ops.contains(&Opcode::StoreLocal(1)));
        assert!(chunk.ops.contains(&Opcode::LoadLocal(0)));
        assert!(chunk.ops.contains(&Opcode::LoadLocal(1)));
        assert_eq!(chunk.num_locals, 2);
    }

    #[test]
    fn test_compile_closure_error() {
        let expr = Expr::Closure {
            params: vec![],
            body: Box::new(Expr::Literal(Literal::Int(1))),
        };
        assert!(compile(&expr).is_err());
    }

    #[test]
    fn test_local_table_scoping() {
        let mut t = LocalTable::new();
        t.push("a".to_string(), 0);
        t.push("b".to_string(), 1);
        let depth = t.save_depth();
        t.push("a".to_string(), 2); // shadow
        assert_eq!(t.get("a"), Some(2)); // finds shadowed
        t.restore(depth);
        assert_eq!(t.get("a"), Some(0)); // back to original
        assert_eq!(t.get("b"), Some(1));
    }

    #[test]
    fn test_compile_multi_var_forall() {
        // forall |x, y| true
        let expr = Expr::Forall {
            vars: vec![
                crate::ast::Binding {
                    pattern: Pattern::Ident("x".to_string()),
                    ty: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                },
                crate::ast::Binding {
                    pattern: Pattern::Ident("y".to_string()),
                    ty: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                },
            ],
            triggers: vec![],
            body: Box::new(Expr::Literal(Literal::Bool(true))),
        };
        let chunk = compile(&expr).unwrap();
        // Should nest: outer Forall contains inner Forall
        let forall_count = chunk
            .ops
            .iter()
            .filter(|op| matches!(op, Opcode::Forall { .. }))
            .count();
        assert_eq!(forall_count, 2);
    }

    #[test]
    fn test_compile_struct_with_base_update() {
        // Struct { name: Point, fields: [("x", 1), ("..", base)] }
        let expr = Expr::Struct {
            name: Path::new(vec!["Point".to_string()]),
            fields: vec![
                ("x".to_string(), Expr::Literal(Literal::Int(1))),
                ("..".to_string(), Expr::Ident("old_point".to_string())),
            ],
        };
        let chunk = compile(&expr).unwrap();
        let has_struct_update = chunk
            .ops
            .iter()
            .any(|op| matches!(op, Opcode::StructUpdate(_)));
        assert!(has_struct_update);
    }

    // ── VM interpreter tests (Phase 38.22.1.b.iv+v) ──────────────────

    fn simple_ctx() -> VmContext<'static> {
        VmContext {
            bounds: RuntimeCollectionBounds {
                max_seq_len: 100,
                max_set_len: 100,
                max_map_len: 100,
            },
            call_evaluator: None,
            method_evaluator: None,
            quantifier_domain: None,
        }
    }

    /// Helper: compile + run an expression
    fn eval(expr: &Expr) -> TranspileResult<RuntimeValue> {
        let chunk = compile(expr)?;
        vm_eval(&chunk, &simple_ctx())
    }

    #[test]
    fn test_vm_literal_int() {
        assert_eq!(
            eval(&Expr::Literal(Literal::Int(42))).unwrap(),
            RuntimeValue::Int(42)
        );
    }

    #[test]
    fn test_vm_literal_bool() {
        assert_eq!(
            eval(&Expr::Literal(Literal::Bool(true))).unwrap(),
            RuntimeValue::Bool(true)
        );
    }

    #[test]
    fn test_vm_arithmetic() {
        let expr = Expr::Binary(
            Box::new(Expr::Literal(Literal::Int(10))),
            BinOp::Add,
            Box::new(Expr::Literal(Literal::Int(32))),
        );
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Int(42));
    }

    #[test]
    fn test_vm_subtraction() {
        let expr = Expr::Binary(
            Box::new(Expr::Literal(Literal::Int(50))),
            BinOp::Sub,
            Box::new(Expr::Literal(Literal::Int(8))),
        );
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Int(42));
    }

    #[test]
    fn test_vm_eq_true() {
        let expr = Expr::Eq(
            Box::new(Expr::Literal(Literal::Int(1))),
            Box::new(Expr::Literal(Literal::Int(1))),
        );
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(true));
    }

    #[test]
    fn test_vm_eq_false() {
        let expr = Expr::Eq(
            Box::new(Expr::Literal(Literal::Int(1))),
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(false));
    }

    #[test]
    fn test_vm_ne() {
        let expr = Expr::Ne(
            Box::new(Expr::Literal(Literal::Int(1))),
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(true));
    }

    #[test]
    fn test_vm_lt() {
        let expr = Expr::Lt(
            Box::new(Expr::Literal(Literal::Int(1))),
            Box::new(Expr::Literal(Literal::Int(2))),
        );
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(true));
    }

    #[test]
    fn test_vm_not() {
        let expr = Expr::Not(Box::new(Expr::Literal(Literal::Bool(true))));
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(false));
    }

    #[test]
    fn test_vm_neg() {
        let expr = Expr::Unary(UnaryOp::Neg, Box::new(Expr::Literal(Literal::Int(5))));
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Int(-5));
    }

    #[test]
    fn test_vm_conjunction_true() {
        let expr = Expr::Conjunction(vec![
            Expr::Literal(Literal::Bool(true)),
            Expr::Literal(Literal::Bool(true)),
        ]);
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(true));
    }

    #[test]
    fn test_vm_conjunction_false() {
        let expr = Expr::Conjunction(vec![
            Expr::Literal(Literal::Bool(true)),
            Expr::Literal(Literal::Bool(false)),
        ]);
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(false));
    }

    #[test]
    fn test_vm_disjunction_true() {
        let expr = Expr::Disjunction(vec![
            Expr::Literal(Literal::Bool(false)),
            Expr::Literal(Literal::Bool(true)),
        ]);
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(true));
    }

    #[test]
    fn test_vm_disjunction_false() {
        let expr = Expr::Disjunction(vec![
            Expr::Literal(Literal::Bool(false)),
            Expr::Literal(Literal::Bool(false)),
        ]);
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(false));
    }

    #[test]
    fn test_vm_implies_true_true() {
        let expr = Expr::Implies(
            Box::new(Expr::Literal(Literal::Bool(true))),
            Box::new(Expr::Literal(Literal::Bool(true))),
        );
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(true));
    }

    #[test]
    fn test_vm_implies_false_any() {
        let expr = Expr::Implies(
            Box::new(Expr::Literal(Literal::Bool(false))),
            Box::new(Expr::Literal(Literal::Bool(false))),
        );
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(true));
    }

    #[test]
    fn test_vm_implies_true_false() {
        let expr = Expr::Implies(
            Box::new(Expr::Literal(Literal::Bool(true))),
            Box::new(Expr::Literal(Literal::Bool(false))),
        );
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(false));
    }

    #[test]
    fn test_vm_if_then_else() {
        let expr = Expr::If {
            cond: Box::new(Expr::Literal(Literal::Bool(true))),
            then_branch: Box::new(Expr::Literal(Literal::Int(1))),
            else_branch: Some(Box::new(Expr::Literal(Literal::Int(2)))),
        };
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Int(1));

        let expr2 = Expr::If {
            cond: Box::new(Expr::Literal(Literal::Bool(false))),
            then_branch: Box::new(Expr::Literal(Literal::Int(1))),
            else_branch: Some(Box::new(Expr::Literal(Literal::Int(2)))),
        };
        assert_eq!(eval(&expr2).unwrap(), RuntimeValue::Int(2));
    }

    #[test]
    fn test_vm_let_binding() {
        // let x = 10 in x + 1
        let expr = Expr::Let {
            binding: crate::ast::Binding {
                pattern: Pattern::Ident("x".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            },
            value: Box::new(Expr::Literal(Literal::Int(10))),
            body: Box::new(Expr::Binary(
                Box::new(Expr::Ident("x".to_string())),
                BinOp::Add,
                Box::new(Expr::Literal(Literal::Int(1))),
            )),
        };
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Int(11));
    }

    #[test]
    fn test_vm_nested_let() {
        // let x = 3 in (let y = 4 in x * y)
        let expr = Expr::Let {
            binding: crate::ast::Binding {
                pattern: Pattern::Ident("x".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            },
            value: Box::new(Expr::Literal(Literal::Int(3))),
            body: Box::new(Expr::Let {
                binding: crate::ast::Binding {
                    pattern: Pattern::Ident("y".to_string()),
                    ty: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                },
                value: Box::new(Expr::Literal(Literal::Int(4))),
                body: Box::new(Expr::Binary(
                    Box::new(Expr::Ident("x".to_string())),
                    BinOp::Mul,
                    Box::new(Expr::Ident("y".to_string())),
                )),
            }),
        };
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Int(12));
    }

    #[test]
    fn test_vm_set_lit() {
        let expr = Expr::SetLit(vec![
            Expr::Literal(Literal::Int(1)),
            Expr::Literal(Literal::Int(2)),
            Expr::Literal(Literal::Int(3)),
        ]);
        let result = eval(&expr).unwrap();
        match result {
            RuntimeValue::Set(items) => assert_eq!(items.len(), 3),
            _ => panic!("expected Set"),
        }
    }

    #[test]
    fn test_vm_seq_lit() {
        let expr = Expr::SeqLit(vec![
            Expr::Literal(Literal::Int(10)),
            Expr::Literal(Literal::Int(20)),
        ]);
        let result = eval(&expr).unwrap();
        match result {
            RuntimeValue::Seq(items) => {
                assert_eq!(items.len(), 2);
                assert_eq!(items[0], RuntimeValue::Int(10));
                assert_eq!(items[1], RuntimeValue::Int(20));
            }
            _ => panic!("expected Seq"),
        }
    }

    #[test]
    fn test_vm_map_lit() {
        let expr = Expr::MapLit(vec![(
            Expr::Literal(Literal::Int(1)),
            Expr::Literal(Literal::Bool(true)),
        )]);
        let result = eval(&expr).unwrap();
        match result {
            RuntimeValue::Map(entries) => {
                assert_eq!(entries.len(), 1);
                assert_eq!(entries[&RuntimeValue::Int(1)], RuntimeValue::Bool(true));
            }
            _ => panic!("expected Map"),
        }
    }

    #[test]
    fn test_vm_empty_collections() {
        match eval(&Expr::SetEmpty).unwrap() {
            RuntimeValue::Set(s) => assert!(s.is_empty()),
            _ => panic!("expected Set"),
        }
        match eval(&Expr::SeqEmpty).unwrap() {
            RuntimeValue::Seq(s) => assert!(s.is_empty()),
            _ => panic!("expected Seq"),
        }
        match eval(&Expr::MapEmpty).unwrap() {
            RuntimeValue::Map(m) => assert!(m.is_empty()),
            _ => panic!("expected Map"),
        }
    }

    #[test]
    fn test_vm_struct_new() {
        let expr = Expr::Struct {
            name: Path::new(vec!["Point".to_string()]),
            fields: vec![
                ("x".to_string(), Expr::Literal(Literal::Int(1))),
                ("y".to_string(), Expr::Literal(Literal::Int(2))),
            ],
        };
        let result = eval(&expr).unwrap();
        assert_eq!(result.field("x"), Some(&RuntimeValue::Int(1)));
        assert_eq!(result.field("y"), Some(&RuntimeValue::Int(2)));
    }

    #[test]
    fn test_vm_field_access() {
        // Create struct then access field: (Point { x: 42, y: 0 }).x
        let expr = Expr::Field(
            Box::new(Expr::Struct {
                name: Path::new(vec!["Point".to_string()]),
                fields: vec![
                    ("x".to_string(), Expr::Literal(Literal::Int(42))),
                    ("y".to_string(), Expr::Literal(Literal::Int(0))),
                ],
            }),
            "x".to_string(),
        );
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Int(42));
    }

    #[test]
    fn test_vm_seq_index() {
        // seq![10, 20, 30][1]
        let expr = Expr::Index(
            Box::new(Expr::SeqLit(vec![
                Expr::Literal(Literal::Int(10)),
                Expr::Literal(Literal::Int(20)),
                Expr::Literal(Literal::Int(30)),
            ])),
            Box::new(Expr::Literal(Literal::Int(1))),
        );
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Int(20));
    }

    #[test]
    fn test_vm_iff() {
        let expr = Expr::Iff(
            Box::new(Expr::Literal(Literal::Bool(true))),
            Box::new(Expr::Literal(Literal::Bool(true))),
        );
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(true));

        let expr2 = Expr::Iff(
            Box::new(Expr::Literal(Literal::Bool(true))),
            Box::new(Expr::Literal(Literal::Bool(false))),
        );
        assert_eq!(eval(&expr2).unwrap(), RuntimeValue::Bool(false));
    }

    #[test]
    fn test_vm_binary_and_short_circuit() {
        let expr = Expr::Binary(
            Box::new(Expr::Literal(Literal::Bool(false))),
            BinOp::And,
            Box::new(Expr::Literal(Literal::Bool(true))),
        );
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(false));
    }

    #[test]
    fn test_vm_binary_or_short_circuit() {
        let expr = Expr::Binary(
            Box::new(Expr::Literal(Literal::Bool(true))),
            BinOp::Or,
            Box::new(Expr::Literal(Literal::Bool(false))),
        );
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(true));
    }

    #[test]
    fn test_vm_constant_value() {
        let expr = Expr::ConstantValue(RuntimeValue::String("hello".to_string()));
        assert_eq!(
            eval(&expr).unwrap(),
            RuntimeValue::String("hello".to_string())
        );
    }

    #[test]
    fn test_vm_view_passthrough() {
        let expr = Expr::View(Box::new(Expr::Literal(Literal::Int(7))));
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Int(7));
    }

    #[test]
    fn test_vm_method_call_len() {
        // seq![1, 2, 3].len()
        let expr = Expr::MethodCall {
            receiver: Box::new(Expr::SeqLit(vec![
                Expr::Literal(Literal::Int(1)),
                Expr::Literal(Literal::Int(2)),
                Expr::Literal(Literal::Int(3)),
            ])),
            method: "len".to_string(),
            args: vec![],
        };
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Nat(3));
    }

    #[test]
    fn test_vm_method_call_contains() {
        // set![1, 2, 3].contains(2)
        let expr = Expr::MethodCall {
            receiver: Box::new(Expr::SetLit(vec![
                Expr::Literal(Literal::Int(1)),
                Expr::Literal(Literal::Int(2)),
                Expr::Literal(Literal::Int(3)),
            ])),
            method: "contains".to_string(),
            args: vec![Expr::Literal(Literal::Int(2))],
        };
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Bool(true));
    }

    #[test]
    fn test_vm_complex_expression() {
        // let a = 5 in let b = 10 in if a < b { a + b } else { a - b }
        let expr = Expr::Let {
            binding: crate::ast::Binding {
                pattern: Pattern::Ident("a".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            },
            value: Box::new(Expr::Literal(Literal::Int(5))),
            body: Box::new(Expr::Let {
                binding: crate::ast::Binding {
                    pattern: Pattern::Ident("b".to_string()),
                    ty: None,
                    variable_mode: crate::ast::VariableMode::Exec,
                },
                value: Box::new(Expr::Literal(Literal::Int(10))),
                body: Box::new(Expr::If {
                    cond: Box::new(Expr::Lt(
                        Box::new(Expr::Ident("a".to_string())),
                        Box::new(Expr::Ident("b".to_string())),
                    )),
                    then_branch: Box::new(Expr::Binary(
                        Box::new(Expr::Ident("a".to_string())),
                        BinOp::Add,
                        Box::new(Expr::Ident("b".to_string())),
                    )),
                    else_branch: Some(Box::new(Expr::Binary(
                        Box::new(Expr::Ident("a".to_string())),
                        BinOp::Sub,
                        Box::new(Expr::Ident("b".to_string())),
                    ))),
                }),
            }),
        };
        assert_eq!(eval(&expr).unwrap(), RuntimeValue::Int(15));
    }
}
