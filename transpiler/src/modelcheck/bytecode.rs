//! Stack-based bytecode VM for fast expression evaluation.
//!
//! This module defines the instruction set and chunk representation for
//! compiling spec expressions into bytecode. The VM uses a simple
//! stack-machine model: operands are pushed onto the stack, operations
//! pop their inputs and push their result.
//!
//! Phase 38.22.1.b.i: Opcode enum and Chunk struct definitions.

use crate::ast::{BinOp, Path};
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
}
