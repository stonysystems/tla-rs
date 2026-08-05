//! Output formatting for generated code.
//!
//! This module handles pretty-printing of generated Verus exec functions
//! to properly formatted Rust source code.

use std::collections::HashMap;

use crate::translator::{ExecExpr, ExecFunction, ExecParameter, ExecType};

/// Configuration for code printing
#[derive(Debug, Clone)]
pub struct PrinterConfig {
    /// Indentation string (e.g., "    " or "\t")
    pub indent: String,
    /// Maximum line width before wrapping
    pub max_width: usize,
    /// Whether to include comments
    pub include_comments: bool,
    /// Extra fields to append to struct constructions.
    /// Key format: "TypeName.field_name", Value: "type = default_value"
    /// When a struct construction for TypeName is printed, any extra fields
    /// not already present will be appended with their default values.
    pub extra_fields: HashMap<String, String>,
}

impl Default for PrinterConfig {
    fn default() -> Self {
        Self {
            indent: "    ".to_string(),
            max_width: 100,
            include_comments: true,
            extra_fields: HashMap::new(),
        }
    }
}

/// Code printer for exec functions
pub struct Printer {
    config: PrinterConfig,
    output: String,
    current_indent: usize,
}

impl Printer {
    /// Create a new printer with the given configuration
    pub fn new(config: PrinterConfig) -> Self {
        Self {
            config,
            output: String::new(),
            current_indent: 0,
        }
    }

    /// Print an exec function to a string
    pub fn print_function(&mut self, func: &ExecFunction) -> String {
        self.output.clear();
        self.current_indent = 0;

        // For methods, open impl block
        if func.is_method {
            if let Some(ref recv_ty) = func.receiver_type {
                self.write(&format!("impl {} {{", recv_ty));
                self.newline();
                self.current_indent += 1;
            }
        }

        // Print function signature
        self.indent();
        self.print_signature(func);

        // Print requires
        if !func.requires.is_empty() {
            self.newline();
            self.indent();
            self.write("requires");
            self.newline();
            self.current_indent += 1;
            for req in &func.requires {
                self.indent();
                self.write(req);
                self.write(",");
                self.newline();
            }
            self.current_indent -= 1;
        }

        // Print ensures
        if !func.ensures.is_empty() {
            self.indent();
            self.write("ensures");
            self.newline();
            self.current_indent += 1;
            for ens in &func.ensures {
                self.indent();
                self.write(ens);
                self.write(",");
                self.newline();
            }
            self.current_indent -= 1;
        }

        // Print decreases (for recursive functions)
        if !func.decreases.is_empty() {
            self.indent();
            self.write("decreases");
            self.newline();
            self.current_indent += 1;
            for dec in &func.decreases {
                self.indent();
                self.write(dec);
                self.write(",");
                self.newline();
            }
            self.current_indent -= 1;
        }

        // Print body — for methods, transform struct returns into field assignments
        self.indent();
        self.write("{");
        self.newline();
        self.current_indent += 1;
        if func.is_method {
            // Emit ghost binding for old state
            self.indent();
            self.write("let ghost old_self = *old(self);");
            self.newline();
            // Phase 42.8.c.2.iii: a method whose receiver-typed output collapsed
            // the return type to `()` must not keep the functional tail, and its
            // proof blocks must read the updated `self` rather than the vanished
            // output binding.
            let returns_unit = matches!(&func.return_type, ExecType::Named(n) if n == "()");
            let method_body = Self::struct_to_field_assignments(&func.body, returns_unit);
            // If nothing still binds the output name, every remaining mention of
            // it refers to the state the assignments just wrote -- i.e. `self`.
            // The guard matters: renaming while `let result = ..` is still live
            // makes proof blocks read the *old* state, which is the mistake
            // recorded in 42.8.c.2.ii.
            let method_body = if returns_unit && !Self::binds_var(&method_body, "result") {
                Self::fix_ghost_refs_in_proofs(&method_body, "result")
            } else {
                method_body
            };
            self.print_expr(&method_body);
        } else {
            self.print_expr(&func.body);
        }
        self.current_indent -= 1;
        self.newline();
        self.indent();
        self.write("}");
        self.newline();

        // For methods, close impl block
        if func.is_method && func.receiver_type.is_some() {
            self.current_indent -= 1;
            self.write("}");
            self.newline();
        }

        std::mem::take(&mut self.output)
    }

    /// Print just an expression to a string (for testing/debugging)
    pub fn print_expr_to_string(&mut self, expr: &ExecExpr) -> String {
        self.output.clear();
        self.current_indent = 0;
        self.print_expr(expr);
        std::mem::take(&mut self.output)
    }

    /// Transform tail-position struct constructions into `self.field = expr;` assignments
    /// for `&mut self` method bodies. Recursively handles if/else branches and blocks.
    /// Whether any statement still binds `name` with a `let`.
    fn binds_var(expr: &ExecExpr, name: &str) -> bool {
        match expr {
            ExecExpr::Let { pattern, .. } => pattern == name,
            ExecExpr::Block(stmts) => stmts.iter().any(|s| Self::binds_var(s, name)),
            ExecExpr::If {
                then_branch,
                else_branch,
                ..
            } => {
                Self::binds_var(then_branch, name)
                    || else_branch
                        .as_ref()
                        .is_some_and(|e| Self::binds_var(e, name))
            }
            _ => false,
        }
    }

    /// Rewrite ghost references after the body was lifted to in-place updates.
    ///
    /// In the functional body the receiver param (already renamed to `self`)
    /// denotes the **pre** state and the output binding denotes the **post**
    /// state. Once the struct is lifted into field assignments those meanings
    /// swap: `self` is the post state and `*old(self)` -- bound as `old_self`
    /// -- is the pre state. So the substitution has to be simultaneous:
    ///
    /// ```text
    /// result.X  ->  self.X        (post state keeps its meaning)
    /// self.X    ->  old_self.X    (pre state moves to the ghost binding)
    /// ```
    ///
    /// Doing only the first half silently collapses both arguments of a lemma
    /// like `lemma_abstractify_clearnerstate_remove(old_m, m2, k)` onto the
    /// same value, whose precondition `m2@ =~= old_m@.remove(k)` is then
    /// unprovable.
    ///
    /// This applies **only inside proof contexts**. In exec position `self`
    /// before the assignments is genuinely the pre state, and rewriting it to
    /// the ghost `old_self` would not compile.
    fn swap_ghost_state_refs(text: &str, output: &str) -> String {
        const MARK: &str = "\u{0}post\u{0}";
        let staged = text.replace(&format!("{}.", output), MARK);
        let staged = staged.replace("self.", "old_self.");
        staged.replace(MARK, "self.")
    }

    fn fix_ghost_refs_in_proofs(expr: &ExecExpr, output: &str) -> ExecExpr {
        fn in_proof(expr: &ExecExpr, output: &str) -> ExecExpr {
            match expr {
                ExecExpr::Var(name) => ExecExpr::Var(Printer::swap_ghost_state_refs(name, output)),
                ExecExpr::Block(stmts) => {
                    ExecExpr::Block(stmts.iter().map(|s| in_proof(s, output)).collect())
                }
                ExecExpr::ProofBlock { stmts } => ExecExpr::ProofBlock {
                    stmts: stmts.iter().map(|s| in_proof(s, output)).collect(),
                },
                ExecExpr::Assert(inner) => ExecExpr::Assert(Box::new(in_proof(inner, output))),
                ExecExpr::Assume(inner) => ExecExpr::Assume(Box::new(in_proof(inner, output))),
                ExecExpr::Call { func, args } => ExecExpr::Call {
                    func: func.clone(),
                    args: args.iter().map(|a| in_proof(a, output)).collect(),
                },
                ExecExpr::Field(base, field) => {
                    ExecExpr::Field(Box::new(in_proof(base, output)), field.clone())
                }
                ExecExpr::If {
                    cond,
                    then_branch,
                    else_branch,
                } => ExecExpr::If {
                    cond: Box::new(in_proof(cond, output)),
                    then_branch: Box::new(in_proof(then_branch, output)),
                    else_branch: else_branch.as_ref().map(|e| Box::new(in_proof(e, output))),
                },
                other => other.clone(),
            }
        }

        match expr {
            ExecExpr::ProofBlock { .. } | ExecExpr::Assert(_) | ExecExpr::Assume(_) => {
                in_proof(expr, output)
            }
            ExecExpr::Block(stmts) => ExecExpr::Block(
                stmts
                    .iter()
                    .map(|s| Self::fix_ghost_refs_in_proofs(s, output))
                    .collect(),
            ),
            ExecExpr::If {
                cond,
                then_branch,
                else_branch,
            } => ExecExpr::If {
                cond: cond.clone(),
                then_branch: Box::new(Self::fix_ghost_refs_in_proofs(then_branch, output)),
                else_branch: else_branch
                    .as_ref()
                    .map(|e| Box::new(Self::fix_ghost_refs_in_proofs(e, output))),
            },
            other => other.clone(),
        }
    }

    /// `self.clone_up_to_view()` / `self.clone()` as a whole branch: the state
    /// is unchanged, which in a `&mut self` method means "do nothing".
    fn is_identity_self_clone(expr: &ExecExpr) -> bool {
        match expr {
            ExecExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                args.is_empty()
                    && (method == "clone_up_to_view" || method == "clone")
                    && matches!(receiver.as_ref(), ExecExpr::Var(v) if v == "self")
            }
            ExecExpr::Block(stmts) => stmts.len() == 1 && Self::is_identity_self_clone(&stmts[0]),
            _ => false,
        }
    }

    fn struct_to_field_assignments(expr: &ExecExpr, returns_unit: bool) -> ExecExpr {
        match expr {
            ExecExpr::Struct { fields, .. } => {
                // Convert each field to self.field = expr;
                let assignments: Vec<ExecExpr> = fields
                    .iter()
                    .map(|(name, value)| ExecExpr::Binary {
                        lhs: Box::new(ExecExpr::Field(
                            Box::new(ExecExpr::Var("self".to_string())),
                            name.clone(),
                        )),
                        op: "=".to_string(),
                        rhs: Box::new(value.clone()),
                    })
                    .collect();
                ExecExpr::Block(assignments)
            }
            ExecExpr::StructUpdate { fields, .. } => {
                // Only the explicitly changed fields get assignments
                let assignments: Vec<ExecExpr> = fields
                    .iter()
                    .map(|(name, value)| ExecExpr::Binary {
                        lhs: Box::new(ExecExpr::Field(
                            Box::new(ExecExpr::Var("self".to_string())),
                            name.clone(),
                        )),
                        op: "=".to_string(),
                        rhs: Box::new(value.clone()),
                    })
                    .collect();
                ExecExpr::Block(assignments)
            }
            ExecExpr::Block(stmts) if !stmts.is_empty() => {
                // Pattern: `let result = (Struct{...}, rest); ...proofs...; result`
                // Detect: last expr is Var(v) and an earlier Let(v, ...) has a transformable value
                if let Some(ExecExpr::Var(tail_var)) = stmts.last() {
                    if let Some(let_idx) = stmts.iter().position(
                        |s| matches!(s, ExecExpr::Let { pattern, .. } if pattern == tail_var),
                    ) {
                        if let ExecExpr::Let { value, .. } = &stmts[let_idx] {
                            let transformed =
                                Self::struct_to_field_assignments(value, returns_unit);
                            if !matches!(&transformed, v if Self::expr_eq(v, value)) {
                                // The Let value was transformed — restructure the block:
                                // 1. Statements before the Let (preserved)
                                // 2. Field assignments from struct extraction
                                // 3. Rebind result to remaining non-struct elements (if any)
                                // 4. Proof blocks + other statements (with index rewriting)
                                // 5. Trailing Var (for return value, if method has non-() return)
                                let struct_idx = Self::find_struct_in_expr(value);
                                let remaining_count = Self::count_non_struct_in_expr(value);
                                let mut new_stmts: Vec<ExecExpr> = stmts[..let_idx].to_vec();

                                match &transformed {
                                    ExecExpr::Block(inner) => {
                                        // Last element of inner is the remaining return value
                                        // Everything before it is field assignments
                                        if inner.len() > 1 {
                                            // Field assignments
                                            new_stmts
                                                .extend(inner[..inner.len() - 1].iter().cloned());
                                            // Rebind result to remaining value
                                            let remaining = &inner[inner.len() - 1];
                                            new_stmts.push(ExecExpr::Let {
                                                pattern: tail_var.clone(),
                                                ty: None,
                                                value: Box::new(remaining.clone()),
                                            });
                                        } else if inner.len() == 1 {
                                            // Only field assignments, no remaining return
                                            new_stmts.extend(inner.iter().cloned());
                                        }
                                    }
                                    _ => {
                                        // Single expression (assignments only)
                                        new_stmts.push(transformed);
                                    }
                                }

                                // Add remaining statements (proof blocks etc.) with index rewriting
                                for stmt in &stmts[let_idx + 1..stmts.len() - 1] {
                                    let rewritten = Self::rewrite_tuple_refs_in_expr(
                                        stmt,
                                        struct_idx,
                                        tail_var,
                                        remaining_count,
                                    );
                                    // The struct was lifted into `self`'s fields, so
                                    // anything still naming the output refers to the
                                    // new state -- which is `self`.
                                    // The ghost-reference swap happens once, at the
                                    // top level of the method body; doing it here as
                                    // well produced `old_old_self`.
                                    new_stmts.push(rewritten);
                                }
                                // Keep trailing var only when it is still returned.
                                if !returns_unit {
                                    new_stmts.push(stmts.last().unwrap().clone());
                                }
                                return ExecExpr::Block(new_stmts);
                            }
                        }
                    }
                }
                // Default: transform the last statement, keep the rest
                let mut new_stmts = stmts[..stmts.len() - 1].to_vec();
                let last = Self::struct_to_field_assignments(stmts.last().unwrap(), returns_unit);
                new_stmts.push(last);
                ExecExpr::Block(new_stmts)
            }
            ExecExpr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                // Transform both branches
                ExecExpr::If {
                    cond: cond.clone(),
                    then_branch: Box::new(
                        if returns_unit && Self::is_identity_self_clone(then_branch) {
                            ExecExpr::Block(Vec::new())
                        } else {
                            Self::struct_to_field_assignments(then_branch, returns_unit)
                        },
                    ),
                    else_branch: else_branch.as_ref().map(|e| {
                        Box::new(if returns_unit && Self::is_identity_self_clone(e) {
                            ExecExpr::Block(Vec::new())
                        } else {
                            Self::struct_to_field_assignments(e, returns_unit)
                        })
                    }),
                }
            }
            ExecExpr::Tuple(elems) => {
                // For multi-output methods: find the Struct/StructUpdate element,
                // convert it to field assignments, and return the remaining elements.
                let struct_idx = elems.iter().position(|e| {
                    matches!(e, ExecExpr::Struct { .. } | ExecExpr::StructUpdate { .. })
                });
                if let Some(idx) = struct_idx {
                    let struct_assignments =
                        Self::struct_to_field_assignments(&elems[idx], returns_unit);
                    let remaining: Vec<ExecExpr> = elems
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != idx)
                        .map(|(_, e)| e.clone())
                        .collect();
                    // Combine: field assignments block, then return remaining as expression
                    let mut stmts = match struct_assignments {
                        ExecExpr::Block(s) => s,
                        other => vec![other],
                    };
                    match remaining.len() {
                        0 => ExecExpr::Block(stmts),
                        1 => {
                            stmts.push(remaining.into_iter().next().unwrap());
                            ExecExpr::Block(stmts)
                        }
                        _ => {
                            stmts.push(ExecExpr::Tuple(remaining));
                            ExecExpr::Block(stmts)
                        }
                    }
                } else {
                    // No struct element found — leave as-is
                    expr.clone()
                }
            }
            // For other expressions (no struct at tail), leave unchanged
            other => other.clone(),
        }
    }

    /// Check if two ExecExpr are structurally equal (shallow comparison for optimization).
    fn expr_eq(a: &ExecExpr, b: &ExecExpr) -> bool {
        // Compare by debug format — sufficient for detecting no-op transforms
        format!("{:?}", a) == format!("{:?}", b)
    }

    /// Find the index of a Struct/StructUpdate element inside an expression.
    /// Returns Some(idx) if the expression is a Tuple with a struct element,
    /// or if it's a Block/nested expression containing a Tuple with a struct.
    fn find_struct_in_expr(expr: &ExecExpr) -> Option<usize> {
        match expr {
            ExecExpr::Tuple(elems) => elems
                .iter()
                .position(|e| matches!(e, ExecExpr::Struct { .. } | ExecExpr::StructUpdate { .. })),
            ExecExpr::Block(stmts) if !stmts.is_empty() => {
                Self::find_struct_in_expr(stmts.last().unwrap())
            }
            _ => None,
        }
    }

    /// Count non-struct elements in a Tuple expression (follows block tails).
    fn count_non_struct_in_expr(expr: &ExecExpr) -> usize {
        match expr {
            ExecExpr::Tuple(elems) => elems
                .iter()
                .filter(|e| !matches!(e, ExecExpr::Struct { .. } | ExecExpr::StructUpdate { .. }))
                .count(),
            ExecExpr::Block(stmts) if !stmts.is_empty() => {
                Self::count_non_struct_in_expr(stmts.last().unwrap())
            }
            _ => 0,
        }
    }

    /// Rewrite tuple index references in proof strings and other expressions.
    /// When the struct at `struct_idx` is extracted from a tuple, references like
    /// `result.0` (if struct_idx=0) become `self`, and remaining indices are renumbered.
    /// `remaining_count` is the number of non-struct tuple elements.
    fn rewrite_tuple_refs_in_expr(
        expr: &ExecExpr,
        struct_idx: Option<usize>,
        result_var: &str,
        remaining_count: usize,
    ) -> ExecExpr {
        let si = match struct_idx {
            Some(i) => i,
            None => return expr.clone(),
        };
        let rw = |s: &str| Self::rewrite_tuple_refs_in_string(s, si, result_var, remaining_count);
        let rw_expr = |e: &ExecExpr| {
            Self::rewrite_tuple_refs_in_expr(e, struct_idx, result_var, remaining_count)
        };
        match expr {
            ExecExpr::Var(s) => ExecExpr::Var(rw(s)),
            ExecExpr::Literal(s) => ExecExpr::Literal(rw(s)),
            ExecExpr::Assert(inner) => ExecExpr::Assert(Box::new(rw_expr(inner))),
            ExecExpr::Assume(inner) => ExecExpr::Assume(Box::new(rw_expr(inner))),
            ExecExpr::ProofBlock { stmts } => ExecExpr::ProofBlock {
                stmts: stmts.iter().map(rw_expr).collect(),
            },
            ExecExpr::Block(stmts) => ExecExpr::Block(stmts.iter().map(rw_expr).collect()),
            ExecExpr::Binary { lhs, op, rhs } => ExecExpr::Binary {
                lhs: Box::new(rw_expr(lhs)),
                op: op.clone(),
                rhs: Box::new(rw_expr(rhs)),
            },
            ExecExpr::Field(base, field) => ExecExpr::Field(Box::new(rw_expr(base)), field.clone()),
            ExecExpr::BroadcastUse(s) => ExecExpr::BroadcastUse(rw(s)),
            other => other.clone(),
        }
    }

    /// Rewrite tuple index references in a proof string.
    /// `result.{si}` → `self`, remaining indices renumbered.
    /// When `remaining_count == 1`, `result.{other_idx}` → `result` (no index).
    fn rewrite_tuple_refs_in_string(
        s: &str,
        struct_idx: usize,
        result_var: &str,
        remaining_count: usize,
    ) -> String {
        let mut out = s.to_string();
        // Replace struct index references with self
        out = out.replace(&format!("{}.{}@", result_var, struct_idx), "self@");
        out = out.replace(&format!("{}.{}.", result_var, struct_idx), "self.");
        // Handle bare result.{si} followed by non-alnum
        let struct_prefix = format!("{}.{}", result_var, struct_idx);
        let temp = out.clone();
        out = String::new();
        let mut chars = temp.char_indices().peekable();
        while let Some((idx, _)) = chars.peek() {
            let rest = &temp[*idx..];
            if rest.starts_with(&struct_prefix) {
                let after = rest.get(struct_prefix.len()..struct_prefix.len() + 1);
                let is_boundary = !after.is_some_and(|c| {
                    let c = c.chars().next().unwrap();
                    c.is_alphanumeric() || c == '_' || c == '.'
                });
                if is_boundary {
                    out.push_str("self");
                    for _ in 0..struct_prefix.len() {
                        chars.next();
                    }
                    continue;
                }
            }
            out.push(temp.as_bytes()[*idx] as char);
            chars.next();
        }

        // Renumber remaining indices using placeholders to avoid interference
        // First pass: replace old references with placeholders
        for old_idx in (0..10).rev() {
            if old_idx == struct_idx {
                continue;
            }
            let old_ref = format!("{}.{}", result_var, old_idx);
            let new_idx = if old_idx > struct_idx {
                old_idx - 1
            } else {
                old_idx
            };
            let placeholder = if remaining_count == 1 {
                "__RESULT_PLACEHOLDER__".to_string()
            } else {
                format!("__RESULT_PLACEHOLDER_{new_idx}__")
            };
            out = out.replace(&old_ref, &placeholder);
        }
        // Second pass: replace placeholders with final references
        if remaining_count == 1 {
            out = out.replace("__RESULT_PLACEHOLDER__", result_var);
        } else {
            for new_idx in 0..remaining_count {
                let placeholder = format!("__RESULT_PLACEHOLDER_{new_idx}__");
                let new_ref = format!("{}.{}", result_var, new_idx);
                out = out.replace(&placeholder, &new_ref);
            }
        }
        out
    }

    /// Print function signature
    fn print_signature(&mut self, func: &ExecFunction) {
        self.write("pub exec fn ");
        self.write(&func.name);
        self.write("(");

        // Print parameters — for methods, emit &mut self then non-self params
        let params: Vec<_> = if func.is_method {
            std::iter::once("&mut self".to_string())
                .chain(
                    func.params
                        .iter()
                        .filter(|p| !p.is_self)
                        .map(|p| self.format_param(p)),
                )
                .collect()
        } else {
            func.params.iter().map(|p| self.format_param(p)).collect()
        };
        self.write(&params.join(", "));

        self.write(")");

        // Emit return type: methods with () return skip it, all others emit it
        let skip_return = func.is_method && func.return_type == ExecType::Named("()".to_string());
        if !skip_return {
            self.write(" -> (result: ");
            self.write(&func.return_type.to_rust_string());
            self.write(")");
        }
    }

    /// Format a parameter
    fn format_param(&self, param: &ExecParameter) -> String {
        format!("{}: {}", param.name, param.ty.to_rust_string())
    }

    /// Print an expression
    fn print_expr(&mut self, expr: &ExecExpr) {
        match expr {
            ExecExpr::Block(stmts) => {
                for (i, stmt) in stmts.iter().enumerate() {
                    self.indent();
                    // When a non-empty Block appears as a statement inside another Block,
                    // wrap it in { } braces (used for HashMap insert to discard Option<V>).
                    // Empty blocks are rendered as nothing (just whitespace).
                    if let ExecExpr::Block(inner) = stmt {
                        if !inner.is_empty() {
                            self.write("{ ");
                            for (j, inner_stmt) in inner.iter().enumerate() {
                                self.print_expr(inner_stmt);
                                // Add semicolons after MethodCall statements to discard
                                // return values (e.g., HashMap::insert returns Option<V>).
                                // Let/Assume/etc. already print their own semicolons.
                                let inner_has_own_semi = matches!(
                                    inner_stmt,
                                    ExecExpr::Let { .. }
                                        | ExecExpr::Assume(_)
                                        | ExecExpr::Assert(_)
                                        | ExecExpr::BroadcastUse(_)
                                        | ExecExpr::GhostVar { .. }
                                );
                                let inner_is_last = j == inner.len() - 1;
                                if !inner_has_own_semi
                                    && (!inner_is_last
                                        || matches!(inner_stmt, ExecExpr::MethodCall { .. }))
                                {
                                    self.write("; ");
                                } else {
                                    self.write(" ");
                                }
                            }
                            self.write("}");
                        }
                    } else {
                        self.print_expr(stmt);
                    }
                    // Add semicolon after statements except the last one (return value)
                    // Some statements already have semicolons from their own printing
                    let is_last = i == stmts.len() - 1;
                    let has_own_semicolon = matches!(
                        stmt,
                        ExecExpr::Let { .. }
                            | ExecExpr::Assume(_)
                            | ExecExpr::Assert(_)
                            | ExecExpr::BroadcastUse(_)
                            | ExecExpr::GhostVar { .. }
                            | ExecExpr::Comment(_)
                            | ExecExpr::ProofBlock { .. }
                            | ExecExpr::ForInIter { .. }
                            | ExecExpr::WhileLoop { .. }
                            | ExecExpr::Block(_)
                            | ExecExpr::Break
                    );
                    if !is_last && !has_own_semicolon {
                        self.write(";");
                    }
                    self.newline();
                }
            }

            ExecExpr::Let { pattern, ty, value } => {
                self.write("let ");
                self.write(pattern);
                if let Some(ty) = ty {
                    self.write(": ");
                    self.write(&ty.to_rust_string());
                }
                self.write(" = ");
                // If value is a Block, wrap it in curly braces
                if matches!(value.as_ref(), ExecExpr::Block(_)) {
                    self.write("{");
                    self.newline();
                    self.current_indent += 1;
                    self.print_expr(value);
                    self.current_indent -= 1;
                    self.indent();
                    self.write("}");
                } else {
                    self.print_expr(value);
                }
                self.write(";");
            }

            ExecExpr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.write("if ");
                // If condition is a block expression, wrap it in braces
                if matches!(cond.as_ref(), ExecExpr::Block(_)) {
                    self.write("{");
                    self.newline();
                    self.current_indent += 1;
                    self.print_expr(cond);
                    self.current_indent -= 1;
                    self.indent();
                    self.write("}");
                } else {
                    self.print_expr(cond);
                }
                self.write(" {");
                self.newline();
                self.current_indent += 1;
                self.indent();
                self.print_expr(then_branch);
                self.current_indent -= 1;
                self.newline();
                self.indent();
                self.write("}");
                if let Some(else_expr) = else_branch {
                    self.write(" else {");
                    self.newline();
                    self.current_indent += 1;
                    self.indent();
                    self.print_expr(else_expr);
                    self.current_indent -= 1;
                    self.newline();
                    self.indent();
                    self.write("}");
                }
            }

            ExecExpr::Struct { name, fields } => {
                self.write(name);
                self.write(" {");
                self.newline();
                self.current_indent += 1;
                let existing_field_names: std::collections::HashSet<&str> =
                    fields.iter().map(|(n, _)| n.as_str()).collect();
                for (field_name, field_value) in fields {
                    self.indent();
                    self.write(field_name);
                    self.write(": ");
                    // A block-valued field initializer must be wrapped as an expression.
                    // Without braces we emit invalid syntax like `field: let x = ...; x`.
                    if matches!(field_value, ExecExpr::Block(_)) {
                        self.write("{");
                        self.newline();
                        self.current_indent += 1;
                        self.print_expr(field_value);
                        self.current_indent -= 1;
                        self.indent();
                        self.write("}");
                    } else {
                        self.print_expr(field_value);
                    }
                    self.write(",");
                    self.newline();
                }
                // Append extra fields from config that aren't already present
                let prefix = format!("{}.", name);
                let mut extra: Vec<(String, String)> = self
                    .config
                    .extra_fields
                    .iter()
                    .filter_map(|(key, value)| {
                        key.strip_prefix(&prefix)
                            .map(|field_name| (field_name.to_string(), value.clone()))
                    })
                    .filter(|(field_name, _)| !existing_field_names.contains(field_name.as_str()))
                    .collect();
                extra.sort_by(|(a, _), (b, _)| a.cmp(b));
                for (field_name, value) in &extra {
                    // Parse "type = default" format — use only the default value
                    let default_val = value
                        .split('=')
                        .nth(1)
                        .map(|s| s.trim())
                        .unwrap_or("Default::default()");
                    self.indent();
                    self.write(field_name);
                    self.write(": ");
                    self.write(default_val);
                    self.write(",");
                    self.newline();
                }
                self.current_indent -= 1;
                self.indent();
                self.write("}");
            }

            ExecExpr::Clone(inner) => {
                self.print_expr(inner);
                self.write(".clone()");
            }

            ExecExpr::Field(base, field) => {
                // Block sub-expressions need brace-wrapping (e.g., Arc-wrapped
                // field indexing: { let __arc_ref = &*s.log; __arc_ref[i] }.term)
                if matches!(base.as_ref(), ExecExpr::Block(_)) {
                    self.write("{");
                    self.print_expr(base);
                    self.write("}");
                } else {
                    self.print_expr(base);
                }
                self.write(".");
                self.write(field);
            }

            ExecExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                // Special case: .index(idx) in exec code should use bracket indexing
                // In Verus spec, .index() is valid, but in Rust exec code we use []
                if method == "index" && args.len() == 1 {
                    if matches!(receiver.as_ref(), ExecExpr::Block(_)) {
                        self.write("{");
                        self.print_expr(receiver);
                        self.write("}");
                    } else {
                        self.print_expr(receiver);
                    }
                    self.write("[");
                    self.print_expr(&args[0]);
                    self.write("]");
                } else {
                    if matches!(receiver.as_ref(), ExecExpr::Block(_)) {
                        self.write("{");
                        self.print_expr(receiver);
                        self.write("}");
                    } else {
                        self.print_expr(receiver);
                    }
                    self.write(".");
                    self.write(method);
                    self.write("(");
                    let args_str: Vec<_> = args
                        .iter()
                        .map(|a| {
                            let mut p = Printer::new(self.config.clone());
                            p.print_expr(a);
                            p.output
                        })
                        .collect();
                    self.write(&args_str.join(", "));
                    self.write(")");
                }
            }

            ExecExpr::Call { func, args } => {
                self.write(func);
                self.write("(");
                let args_str: Vec<_> = args
                    .iter()
                    .map(|a| {
                        let mut p = Printer::new(self.config.clone());
                        // Block args need brace-wrapping to form valid Rust expressions
                        if matches!(a, ExecExpr::Block(_)) {
                            p.write("{");
                            p.print_expr(a);
                            p.write("}");
                        } else {
                            p.print_expr(a);
                        }
                        p.output
                    })
                    .collect();
                self.write(&args_str.join(", "));
                self.write(")");
            }

            ExecExpr::Var(name) => {
                self.write(name);
            }

            ExecExpr::Literal(lit) => {
                self.write(lit);
            }

            ExecExpr::VecLit(elems) => {
                self.write("vec![");
                let elems_str: Vec<_> = elems
                    .iter()
                    .map(|e| {
                        let mut p = Printer::new(self.config.clone());
                        p.print_expr(e);
                        p.output
                    })
                    .collect();
                self.write(&elems_str.join(", "));
                self.write("]");
            }

            ExecExpr::Tuple(elems) => {
                self.write("(");
                let elems_str: Vec<_> = elems
                    .iter()
                    .map(|e| {
                        let mut p = Printer::new(self.config.clone());
                        p.print_expr(e);
                        p.output
                    })
                    .collect();
                self.write(&elems_str.join(", "));
                self.write(")");
            }

            ExecExpr::Return(value) => {
                self.write("return ");
                self.print_expr(value);
            }

            ExecExpr::Match { scrutinee, arms } => {
                self.write("match ");
                self.print_expr(scrutinee);
                self.write(" {");
                self.newline();
                self.current_indent += 1;
                for (pattern, body) in arms {
                    self.indent();
                    self.write(pattern);
                    self.write(" => ");
                    match body {
                        ExecExpr::Block(stmts) if stmts.is_empty() => {
                            self.write("{}");
                        }
                        ExecExpr::Block(_) => {
                            // Non-empty block: wrap in { } for multi-statement arms
                            self.write("{");
                            self.newline();
                            self.current_indent += 1;
                            self.print_expr(body);
                            self.current_indent -= 1;
                            self.indent();
                            self.write("}");
                        }
                        _ => {
                            self.print_expr(body);
                        }
                    }
                    self.write(",");
                    self.newline();
                }
                self.current_indent -= 1;
                self.indent();
                self.write("}");
            }

            ExecExpr::StructUpdate { name, base, fields } => {
                // Get the struct name from the base (if it's a clone of a var)
                let base_str = {
                    let mut p = Printer::new(self.config.clone());
                    p.print_expr(base);
                    p.output
                };

                // For struct update syntax: StructName { fields, ..base }
                self.write(name);
                self.write(" { ");
                for (field_name, field_value) in fields {
                    self.write(field_name);
                    self.write(": ");
                    self.print_expr(field_value);
                    self.write(", ");
                }
                self.write("..");
                self.write(&base_str);
                self.write(" }");
            }

            ExecExpr::Binary { lhs, op, rhs } => {
                // For assignments (used in proof blocks), don't wrap in parentheses
                if op == "=" {
                    self.print_expr(lhs);
                    self.write(" ");
                    self.write(op);
                    self.write(" ");
                    self.print_expr(rhs);
                } else {
                    self.write("(");
                    // Block sub-expressions need brace-wrapping to form valid
                    // Rust expressions (e.g., Arc-wrapped field indexing via
                    // `let __arc_ref` inside a binary condition).
                    if matches!(lhs.as_ref(), ExecExpr::Block(_)) {
                        self.write("{");
                        self.print_expr(lhs);
                        self.write("}");
                    } else {
                        self.print_expr(lhs);
                    }
                    self.write(" ");
                    self.write(op);
                    self.write(" ");
                    if matches!(rhs.as_ref(), ExecExpr::Block(_)) {
                        self.write("{");
                        self.print_expr(rhs);
                        self.write("}");
                    } else {
                        self.print_expr(rhs);
                    }
                    self.write(")");
                }
            }

            ExecExpr::Unary { op, expr } => {
                if op == "*" {
                    // Deref needs parens when used as a receiver: (*x).method()
                    self.write("(*");
                    self.print_expr(expr);
                    self.write(")");
                } else {
                    self.write(op);
                    self.print_expr(expr);
                }
            }

            ExecExpr::Range { start, end } => {
                self.write("(");
                self.print_expr(start);
                self.write("..");
                self.print_expr(end);
                self.write(")");
            }

            ExecExpr::Closure { params, body } => {
                self.write("|");
                self.write(&params.join(", "));
                self.write("| ");
                self.print_expr(body);
            }

            ExecExpr::Comment(text) => {
                self.write("// ");
                self.write(text);
            }

            ExecExpr::Cast(inner, target_type) => {
                self.write("(");
                self.print_expr(inner);
                self.write(" as ");
                self.write(target_type);
                self.write(")");
            }

            ExecExpr::MapUpdateWithInsert {
                source,
                key_var,
                filter,
                new_key,
            } => {
                // Generate: {
                //   let mut __result = source.iter().filter(|(k, _)| filter).cloned().collect::<HashMap<_, _>>();
                //   if filter_applies_to_new_key { __result.insert(new_key.clone(), __new_value); }
                //   __result
                // }
                // Note: The value (__new_value) needs to be set by the caller context
                // For now, generate a placeholder that will be replaced by MapConditionalValue
                self.write("{\n");
                self.current_indent += 1;
                self.indent();
                self.write("let mut __result = ");
                self.print_expr(source);
                self.write(".iter().filter(|(");
                self.write(key_var);
                self.write(", _)| ");
                self.print_expr(filter);
                self.write(").map(|(k, v)| (k.clone(), v.clone())).collect::<HashMap<_, _>>();\n");
                self.indent();
                self.write("// Insert new key if it passes filter\n");
                self.indent();
                self.write("if ");
                // Generate filter check for new_key by substituting key_var with new_key
                // This is a simplified version - ideally we'd substitute properly
                self.write("true /* ");
                self.print_expr(new_key);
                self.write(" passes filter */ {\n");
                self.current_indent += 1;
                self.indent();
                self.write("__result.insert(");
                self.print_expr(new_key);
                self.write(".clone(), __new_value.clone());\n");
                self.current_indent -= 1;
                self.indent();
                self.write("}\n");
                self.indent();
                self.write("__result\n");
                self.current_indent -= 1;
                self.indent();
                self.write("}");
            }

            // === Verus Loop Constructs ===
            ExecExpr::WhileLoop {
                cond,
                invariants,
                decreases,
                body,
            } => {
                self.write("while ");
                self.print_expr(cond);
                self.newline();
                // Generate invariants
                if !invariants.is_empty() {
                    self.indent();
                    self.write("invariant");
                    self.newline();
                    self.current_indent += 1;
                    for inv in invariants {
                        self.indent();
                        self.write(inv);
                        self.write(",");
                        self.newline();
                    }
                    self.current_indent -= 1;
                }
                // Generate decreases
                if let Some(dec) = decreases {
                    self.indent();
                    self.write("decreases ");
                    self.write(dec);
                    self.write(",");
                    self.newline();
                }
                // Generate body
                self.indent();
                self.write("{");
                self.newline();
                self.current_indent += 1;
                // Don't double-indent Block bodies (Block handles its own indentation)
                if !matches!(body.as_ref(), ExecExpr::Block(_)) {
                    self.indent();
                }
                self.print_expr(body);
                self.newline();
                self.current_indent -= 1;
                self.indent();
                self.write("}");
            }

            ExecExpr::ForInIter {
                var,
                iter_name,
                iter_source,
                invariants,
                body,
            } => {
                // For range-based loops, print direct `for i in 0..n` form.
                // `iter:iter_name` over ranges generates a RangeGhostIterator shape that
                // does not satisfy iterator traits in current Verus.
                let is_range_source = matches!(iter_source.as_ref(), ExecExpr::Range { .. });
                if is_range_source {
                    self.write("for ");
                    self.write(var);
                    self.write(" in ");
                    self.print_expr(iter_source);
                    self.newline();
                } else {
                    // Only generate iterator initialization if iter_source is not already a Var with the same name
                    // (avoids redundant "let x = x;")
                    let skip_binding =
                        matches!(iter_source.as_ref(), ExecExpr::Var(name) if name == iter_name);
                    if !skip_binding {
                        self.write("let ");
                        self.write(iter_name);
                        self.write(" = ");
                        self.print_expr(iter_source);
                        self.write(";");
                        self.newline();
                        self.indent();
                    }
                    // Generate: for var in iter:iter_name
                    self.write("for ");
                    self.write(var);
                    self.write(" in iter:");
                    self.write(iter_name);
                    self.newline();
                }
                // Generate invariants
                if !invariants.is_empty() {
                    self.indent();
                    self.write("invariant");
                    self.newline();
                    self.current_indent += 1;
                    for inv in invariants {
                        self.indent();
                        self.write(inv);
                        self.write(",");
                        self.newline();
                    }
                    self.current_indent -= 1;
                }
                // Generate body
                self.indent();
                self.write("{");
                self.newline();
                self.current_indent += 1;
                self.indent();
                self.print_expr(body);
                self.newline();
                self.current_indent -= 1;
                self.indent();
                self.write("}");
            }

            ExecExpr::GhostVar {
                name,
                ty,
                init,
                mutable,
            } => {
                self.write("let ghost ");
                if *mutable {
                    self.write("mut ");
                }
                self.write(name);
                self.write(": ");
                self.write(ty);
                self.write(" = ");
                self.print_expr(init);
                self.write(";");
            }

            ExecExpr::ProofBlock { stmts } => {
                // Verus proof blocks: proof { stmt; }
                self.write("proof {");
                self.newline();
                self.current_indent += 1;
                for stmt in stmts {
                    self.indent();
                    self.print_expr(stmt);
                    // Some statements already include their own semicolons
                    let has_own_semicolon = matches!(
                        stmt,
                        ExecExpr::Let { .. }
                            | ExecExpr::Assume(_)
                            | ExecExpr::Assert(_)
                            | ExecExpr::BroadcastUse(_)
                            | ExecExpr::GhostVar { .. }
                            | ExecExpr::Comment(_)
                            | ExecExpr::ProofBlock { .. }
                    );
                    if !has_own_semicolon {
                        self.write(";");
                    }
                    self.newline();
                }
                self.current_indent -= 1;
                self.indent();
                self.write("}");
            }

            ExecExpr::Assume(expr) => {
                self.write("assume(");
                self.print_expr(expr);
                self.write(");");
            }

            ExecExpr::Assert(expr) => {
                self.write("assert(");
                self.print_expr(expr);
                self.write(");");
            }

            ExecExpr::BroadcastUse(path) => {
                self.write("broadcast use ");
                self.write(path);
                self.write(";");
            }

            ExecExpr::Break => {
                self.write("break;");
            }

            ExecExpr::Matches {
                expr,
                pattern,
                is_struct_variant,
            } => {
                self.write("matches!(");
                self.print_expr(expr);
                self.write(", ");
                self.write(pattern);
                if *is_struct_variant {
                    self.write(" { .. }");
                }
                self.write(")");
            }

            ExecExpr::IsVariant { expr, variant } => {
                // Verus native syntax: expr is Variant
                // This works with -> syntax unlike matches!()
                // Note: variant may contain full path like "CUpperBound::CUpperBoundFinite"
                // but Verus `is` syntax expects just the variant name "CUpperBoundFinite"
                self.print_expr(expr);
                self.write(" is ");
                // Extract just the variant name if it contains ::
                let variant_name = if let Some(pos) = variant.rfind("::") {
                    &variant[pos + 2..]
                } else {
                    variant.as_str()
                };
                self.write(variant_name);
            }

            ExecExpr::ArrowAccess { base, field } => {
                // Verus arrow access syntax for enum variant fields: expr->field
                self.print_expr(base);
                self.write("->");
                self.write(field);
            }
        }
    }

    /// Write a string to output
    fn write(&mut self, s: &str) {
        self.output.push_str(s);
    }

    /// Write indentation
    fn indent(&mut self) {
        for _ in 0..self.current_indent {
            self.output.push_str(&self.config.indent);
        }
    }

    /// Write a newline
    fn newline(&mut self) {
        self.output.push('\n');
    }
}

impl Default for Printer {
    fn default() -> Self {
        Self::new(PrinterConfig::default())
    }
}

/// Print a function to a string with default configuration
pub fn print_function(func: &ExecFunction) -> String {
    let mut printer = Printer::default();
    printer.print_function(func)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::translator::ExecType;

    #[test]
    fn test_printer_basic() {
        let func = ExecFunction {
            name: "CTestFn".to_string(),
            params: vec![ExecParameter {
                name: "s".to_string(),
                ty: ExecType::Reference(Box::new(ExecType::Named("CState".to_string())), false),
                is_reference: true,
                is_self: false,
            }],
            return_type: ExecType::Named("CState".to_string()),
            requires: vec!["s.well_formed()".to_string()],
            ensures: vec!["result.well_formed()".to_string()],
            decreases: vec![],
            body: ExecExpr::Clone(Box::new(ExecExpr::Var("s".to_string()))),
            is_method: false,
            receiver_type: None,
        };

        let output = print_function(&func);
        assert!(output.contains("pub exec fn CTestFn"));
        assert!(output.contains("requires"));
        assert!(output.contains("ensures"));
    }

    #[test]
    fn test_print_decreases() {
        let func = ExecFunction {
            name: "CRecursiveFn".to_string(),
            params: vec![ExecParameter {
                name: "s".to_string(),
                ty: ExecType::Reference(
                    Box::new(ExecType::Vec(Box::new(ExecType::Named(
                        "CRequest".to_string(),
                    )))),
                    false,
                ),
                is_reference: true,
                is_self: false,
            }],
            return_type: ExecType::Vec(Box::new(ExecType::Named("CRequest".to_string()))),
            requires: vec!["s.valid()".to_string()],
            ensures: vec!["result.valid()".to_string()],
            decreases: vec!["s.len()".to_string()],
            body: ExecExpr::VecLit(vec![]),
            is_method: false,
            receiver_type: None,
        };

        let output = print_function(&func);
        assert!(output.contains("pub exec fn CRecursiveFn"));
        assert!(output.contains("decreases"));
        assert!(output.contains("s.len()"));
    }

    #[test]
    fn test_print_for_in_iter() {
        let mut printer = Printer::default();
        let expr = ExecExpr::ForInIter {
            var: "key".to_string(),
            iter_name: "m_keys".to_string(),
            iter_source: Box::new(ExecExpr::MethodCall {
                receiver: Box::new(ExecExpr::Var("votes".to_string())),
                method: "keys".to_string(),
                args: vec![],
            }),
            invariants: vec![
                "seen_keys.subset_of(votes@.dom())".to_string(),
                "forall |opn| result@.contains_key(opn) ==> opn >= threshold".to_string(),
            ],
            body: Box::new(ExecExpr::If {
                cond: Box::new(ExecExpr::Binary {
                    lhs: Box::new(ExecExpr::Var("*key".to_string())),
                    op: ">=".to_string(),
                    rhs: Box::new(ExecExpr::Var("threshold".to_string())),
                }),
                then_branch: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Var("result".to_string())),
                    method: "insert".to_string(),
                    args: vec![ExecExpr::Var("*key".to_string())],
                }),
                else_branch: None,
            }),
        };

        printer.print_expr(&expr);
        let output = printer.output;

        assert!(output.contains("let m_keys = votes.keys();"));
        assert!(output.contains("for key in iter:m_keys"));
        assert!(output.contains("invariant"));
        assert!(output.contains("seen_keys.subset_of(votes@.dom())"));
    }

    #[test]
    fn test_print_for_in_iter_range_source() {
        let mut printer = Printer::default();
        let expr = ExecExpr::ForInIter {
            var: "i".to_string(),
            iter_name: "iter".to_string(),
            iter_source: Box::new(ExecExpr::Range {
                start: Box::new(ExecExpr::Literal("0".to_string())),
                end: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Var("s".to_string())),
                    method: "len".to_string(),
                    args: vec![],
                }),
            }),
            invariants: vec!["i <= s.len()".to_string()],
            body: Box::new(ExecExpr::Block(vec![])),
        };

        printer.print_expr(&expr);
        let output = printer.output;

        assert!(output.contains("for i in (0..s.len())"));
        assert!(!output.contains("for i in iter:iter"));
        assert!(!output.contains("let iter ="));
    }

    #[test]
    fn test_print_ghost_var() {
        let mut printer = Printer::default();
        let expr = ExecExpr::GhostVar {
            name: "seen_keys".to_string(),
            ty: "Set::<COperationNumber>".to_string(),
            init: Box::new(ExecExpr::MethodCall {
                receiver: Box::new(ExecExpr::Var("Set".to_string())),
                method: "empty".to_string(),
                args: vec![],
            }),
            mutable: true,
        };

        printer.print_expr(&expr);
        let output = printer.output;

        assert!(output.contains("let ghost mut seen_keys"));
        assert!(output.contains("Set::<COperationNumber>"));
        assert!(output.contains("Set.empty()"));
    }

    #[test]
    fn test_print_proof_block() {
        let mut printer = Printer::default();
        let expr = ExecExpr::ProofBlock {
            stmts: vec![ExecExpr::Binary {
                lhs: Box::new(ExecExpr::Var("seen_keys".to_string())),
                op: "=".to_string(),
                rhs: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Var("seen_keys".to_string())),
                    method: "insert".to_string(),
                    args: vec![ExecExpr::Var("*key".to_string())],
                }),
            }],
        };

        printer.print_expr(&expr);
        let output = printer.output;

        // Proof blocks use spaced format: proof { stmt; }
        assert!(
            output.contains("proof {"),
            "Should use 'proof {{' with space, got: {}",
            output
        );
        assert!(output.contains("seen_keys = seen_keys.insert"));
        assert!(output.contains("}"), "Should close with }}");
    }

    #[test]
    fn test_print_assume_assert() {
        let mut printer = Printer::default();

        // Test assume
        printer.print_expr(&ExecExpr::Assume(Box::new(ExecExpr::Binary {
            lhs: Box::new(ExecExpr::Var("x".to_string())),
            op: ">".to_string(),
            rhs: Box::new(ExecExpr::Literal("0".to_string())),
        })));
        assert!(printer.output.contains("assume((x > 0));"));

        printer.output.clear();

        // Test assert
        printer.print_expr(&ExecExpr::Assert(Box::new(ExecExpr::Binary {
            lhs: Box::new(ExecExpr::Var("y".to_string())),
            op: "<".to_string(),
            rhs: Box::new(ExecExpr::Literal("10".to_string())),
        })));
        assert!(printer.output.contains("assert((y < 10));"));
    }

    #[test]
    fn test_print_broadcast_use() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::BroadcastUse(
            "vstd::std_specs::hash::group_hash_axioms".to_string(),
        ));
        assert!(printer
            .output
            .contains("broadcast use vstd::std_specs::hash::group_hash_axioms;"));
    }

    #[test]
    fn test_print_struct_field_block_wrapped() {
        let mut printer = Printer::default();
        let expr = ExecExpr::Struct {
            name: "S".to_string(),
            fields: vec![(
                "f".to_string(),
                ExecExpr::Block(vec![
                    ExecExpr::Let {
                        pattern: "x".to_string(),
                        ty: None,
                        value: Box::new(ExecExpr::Literal("1".to_string())),
                    },
                    ExecExpr::Var("x".to_string()),
                ]),
            )],
        };

        printer.print_expr(&expr);
        let output = printer.output;
        assert!(
            output.contains("f: {"),
            "block-valued struct fields must be wrapped in braces: {}",
            output
        );
        assert!(
            output.contains("let x = 1;"),
            "expected let binding in wrapped block"
        );
        assert!(output.contains("x"), "expected block tail expression");
    }

    #[test]
    fn test_print_struct_extra_fields() {
        let mut extra = HashMap::new();
        extra.insert(
            "CAcceptor.min_vote_opn".to_string(),
            "u64 = 0u64".to_string(),
        );
        extra.insert(
            "CAcceptor.extra_flag".to_string(),
            "bool = false".to_string(),
        );
        let config = PrinterConfig {
            extra_fields: extra,
            ..Default::default()
        };
        let mut printer = Printer::new(config);

        let expr = ExecExpr::Struct {
            name: "CAcceptor".to_string(),
            fields: vec![("max_bal".to_string(), ExecExpr::Literal("0".to_string()))],
        };

        printer.print_expr(&expr);
        let output = &printer.output;
        assert!(
            output.contains("max_bal: 0,"),
            "expected original field: {}",
            output
        );
        assert!(
            output.contains("extra_flag: false,"),
            "expected extra_flag: {}",
            output
        );
        assert!(
            output.contains("min_vote_opn: 0u64,"),
            "expected min_vote_opn: {}",
            output
        );
    }

    #[test]
    fn test_print_struct_extra_fields_not_duplicated() {
        let mut extra = HashMap::new();
        extra.insert(
            "CAcceptor.min_vote_opn".to_string(),
            "u64 = 0u64".to_string(),
        );
        let config = PrinterConfig {
            extra_fields: extra,
            ..Default::default()
        };
        let mut printer = Printer::new(config);

        // min_vote_opn is already present, so it should not be duplicated
        let expr = ExecExpr::Struct {
            name: "CAcceptor".to_string(),
            fields: vec![
                ("max_bal".to_string(), ExecExpr::Literal("0".to_string())),
                (
                    "min_vote_opn".to_string(),
                    ExecExpr::Literal("42".to_string()),
                ),
            ],
        };

        printer.print_expr(&expr);
        let output = &printer.output;
        assert!(
            output.contains("min_vote_opn: 42,"),
            "expected original min_vote_opn value: {}",
            output
        );
        // Count occurrences of "min_vote_opn" — should be exactly 1
        assert_eq!(
            output.matches("min_vote_opn").count(),
            1,
            "extra field should not be duplicated: {}",
            output
        );
    }

    #[test]
    fn test_print_struct_extra_fields_wrong_type_ignored() {
        let mut extra = HashMap::new();
        extra.insert("CProposer.extra_field".to_string(), "u64 = 0".to_string());
        let config = PrinterConfig {
            extra_fields: extra,
            ..Default::default()
        };
        let mut printer = Printer::new(config);

        // Struct is CAcceptor, not CProposer, so extra_field should not appear
        let expr = ExecExpr::Struct {
            name: "CAcceptor".to_string(),
            fields: vec![("max_bal".to_string(), ExecExpr::Literal("0".to_string()))],
        };

        printer.print_expr(&expr);
        let output = &printer.output;
        assert!(
            !output.contains("extra_field"),
            "extra_field should not appear for CAcceptor: {}",
            output
        );
    }

    #[test]
    fn test_print_var() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Var("x".to_string()));
        assert_eq!(printer.output, "x");
    }

    #[test]
    fn test_print_literal() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Literal("42".to_string()));
        assert_eq!(printer.output, "42");
    }

    #[test]
    fn test_print_clone() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Clone(Box::new(ExecExpr::Var("s".to_string()))));
        assert_eq!(printer.output, "s.clone()");
    }

    #[test]
    fn test_print_field() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Field(
            Box::new(ExecExpr::Var("s".to_string())),
            "bal".to_string(),
        ));
        assert_eq!(printer.output, "s.bal");
    }

    #[test]
    fn test_print_call() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Call {
            func: "foo".to_string(),
            args: vec![
                ExecExpr::Var("x".to_string()),
                ExecExpr::Literal("1".to_string()),
            ],
        });
        assert_eq!(printer.output, "foo(x, 1)");
    }

    #[test]
    fn test_print_method_call() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::MethodCall {
            receiver: Box::new(ExecExpr::Var("v".to_string())),
            method: "push".to_string(),
            args: vec![ExecExpr::Literal("1".to_string())],
        });
        assert_eq!(printer.output, "v.push(1)");
    }

    #[test]
    fn test_print_method_call_index() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::MethodCall {
            receiver: Box::new(ExecExpr::Var("v".to_string())),
            method: "index".to_string(),
            args: vec![ExecExpr::Literal("0".to_string())],
        });
        assert_eq!(printer.output, "v[0]");
    }

    #[test]
    fn test_print_vec_lit() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::VecLit(vec![
            ExecExpr::Literal("1".to_string()),
            ExecExpr::Literal("2".to_string()),
        ]));
        assert_eq!(printer.output, "vec![1, 2]");
    }

    #[test]
    fn test_print_tuple() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Tuple(vec![
            ExecExpr::Var("x".to_string()),
            ExecExpr::Var("y".to_string()),
        ]));
        assert_eq!(printer.output, "(x, y)");
    }

    #[test]
    fn test_print_return() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Return(Box::new(ExecExpr::Var(
            "result".to_string(),
        ))));
        assert_eq!(printer.output, "return result");
    }

    #[test]
    fn test_print_match_simple() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Match {
            scrutinee: Box::new(ExecExpr::Var("x".to_string())),
            arms: vec![
                ("A".to_string(), ExecExpr::Literal("1".to_string())),
                ("B".to_string(), ExecExpr::Literal("2".to_string())),
            ],
        });
        let output = &printer.output;
        assert!(
            output.contains("match x {"),
            "expected match header: {}",
            output
        );
        assert!(output.contains("A => 1,"), "expected arm A: {}", output);
        assert!(output.contains("B => 2,"), "expected arm B: {}", output);
    }

    #[test]
    fn test_print_struct_update() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::StructUpdate {
            name: "Name".to_string(),
            base: Box::new(ExecExpr::Var("base".to_string())),
            fields: vec![("field".to_string(), ExecExpr::Var("val".to_string()))],
        });
        let output = &printer.output;
        assert!(
            output.contains("Name {"),
            "expected struct name: {}",
            output
        );
        assert!(
            output.contains("field: val"),
            "expected field assignment: {}",
            output
        );
        assert!(
            output.contains("..base"),
            "expected base update syntax: {}",
            output
        );
    }

    #[test]
    fn test_print_binary_assignment() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Binary {
            lhs: Box::new(ExecExpr::Var("x".to_string())),
            op: "=".to_string(),
            rhs: Box::new(ExecExpr::Var("y".to_string())),
        });
        assert_eq!(printer.output, "x = y");
    }

    #[test]
    fn test_print_binary_comparison() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Binary {
            lhs: Box::new(ExecExpr::Var("x".to_string())),
            op: ">".to_string(),
            rhs: Box::new(ExecExpr::Var("y".to_string())),
        });
        assert_eq!(printer.output, "(x > y)");
    }

    #[test]
    fn test_print_unary() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Unary {
            op: "!".to_string(),
            expr: Box::new(ExecExpr::Var("x".to_string())),
        });
        assert_eq!(printer.output, "!x");
    }

    #[test]
    fn test_print_range() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Range {
            start: Box::new(ExecExpr::Literal("0".to_string())),
            end: Box::new(ExecExpr::Var("n".to_string())),
        });
        assert_eq!(printer.output, "(0..n)");
    }

    #[test]
    fn test_print_closure() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Closure {
            params: vec!["x".to_string()],
            body: Box::new(ExecExpr::Var("x".to_string())),
        });
        assert_eq!(printer.output, "|x| x");
    }

    #[test]
    fn test_print_comment() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Comment("hello".to_string()));
        assert_eq!(printer.output, "// hello");
    }

    #[test]
    fn test_print_cast() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Cast(
            Box::new(ExecExpr::Var("x".to_string())),
            "u64".to_string(),
        ));
        assert_eq!(printer.output, "(x as u64)");
    }

    #[test]
    fn test_print_break() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Break);
        assert_eq!(printer.output, "break;");
    }

    #[test]
    fn test_print_matches_variant() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Matches {
            expr: Box::new(ExecExpr::Var("expr".to_string())),
            pattern: "Pat".to_string(),
            is_struct_variant: true,
        });
        assert_eq!(printer.output, "matches!(expr, Pat { .. })");
    }

    #[test]
    fn test_print_is_variant() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::IsVariant {
            expr: Box::new(ExecExpr::Var("expr".to_string())),
            variant: "CEnum::Var1".to_string(),
        });
        assert_eq!(printer.output, "expr is Var1");
    }

    #[test]
    fn test_print_arrow_access() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::ArrowAccess {
            base: Box::new(ExecExpr::Var("base".to_string())),
            field: "field".to_string(),
        });
        assert_eq!(printer.output, "base->field");
    }

    #[test]
    fn test_print_while_loop_empty_invariants() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::WhileLoop {
            cond: Box::new(ExecExpr::Binary {
                lhs: Box::new(ExecExpr::Var("i".to_string())),
                op: "<".to_string(),
                rhs: Box::new(ExecExpr::Var("n".to_string())),
            }),
            invariants: vec![],
            decreases: None,
            body: Box::new(ExecExpr::Block(vec![])),
        });
        let output = &printer.output;
        assert!(
            output.contains("while (i < n)"),
            "expected while header: {}",
            output
        );
        assert!(
            !output.contains("invariant"),
            "empty invariants should produce no invariant line: {}",
            output
        );
    }

    #[test]
    fn test_print_let_with_type() {
        let mut printer = Printer::default();
        printer.print_expr(&ExecExpr::Let {
            pattern: "x".to_string(),
            ty: Some(ExecType::Named("u64".to_string())),
            value: Box::new(ExecExpr::Literal("42".to_string())),
        });
        assert_eq!(printer.output, "let x: u64 = 42;");
    }

    #[test]
    fn test_exec_function_is_method_field() {
        // Verify that ExecFunction with is_method=false prints as regular function
        let func = ExecFunction {
            name: "CTestMethod".to_string(),
            params: vec![
                ExecParameter {
                    name: "s".to_string(),
                    ty: ExecType::Reference(Box::new(ExecType::Named("CState".to_string())), false),
                    is_reference: true,
                    is_self: false,
                },
                ExecParameter {
                    name: "x".to_string(),
                    ty: ExecType::Named("u64".to_string()),
                    is_reference: false,
                    is_self: false,
                },
            ],
            return_type: ExecType::Named("CState".to_string()),
            requires: vec![],
            ensures: vec![],
            decreases: vec![],
            body: ExecExpr::Clone(Box::new(ExecExpr::Var("s".to_string()))),
            is_method: false,
            receiver_type: None,
        };

        let output = print_function(&func);
        // Regular function should have both params and no impl block
        assert!(output.contains("pub exec fn CTestMethod(s: &CState, x: u64)"));
        assert!(!output.contains("impl"));
        assert!(!output.contains("&mut self"));

        // Now test with is_method=true — should print as impl method
        // In the real pipeline, maybe_apply_mut_self sets return_type to ()
        // for single-output methods where the output IS the receiver type.
        let method_func = ExecFunction {
            is_method: true,
            receiver_type: Some("CState".to_string()),
            return_type: ExecType::Named("()".to_string()),
            params: vec![
                ExecParameter {
                    name: "s".to_string(),
                    ty: ExecType::Reference(Box::new(ExecType::Named("CState".to_string())), true),
                    is_reference: true,
                    is_self: true,
                },
                ExecParameter {
                    name: "x".to_string(),
                    ty: ExecType::Named("u64".to_string()),
                    is_reference: false,
                    is_self: false,
                },
            ],
            ..func
        };
        let method_output = print_function(&method_func);
        assert!(
            method_output.contains("impl CState {"),
            "method should be wrapped in impl block: {}",
            method_output
        );
        assert!(
            method_output.contains("&mut self, x: u64)"),
            "method should have &mut self and skip receiver param: {}",
            method_output
        );
        assert!(
            !method_output.contains("-> (result:"),
            "method should not have return type: {}",
            method_output
        );
        // impl block should be closed
        assert!(
            method_output.ends_with("}\n}\n"),
            "impl block should be closed: {:?}",
            method_output
        );
    }

    #[test]
    fn test_print_method_with_requires_ensures() {
        let func = ExecFunction {
            name: "CDoStep".to_string(),
            params: vec![
                ExecParameter {
                    name: "s".to_string(),
                    ty: ExecType::Reference(
                        Box::new(ExecType::Named("CReplica".to_string())),
                        true,
                    ),
                    is_reference: true,
                    is_self: true,
                },
                ExecParameter {
                    name: "msg".to_string(),
                    ty: ExecType::Reference(
                        Box::new(ExecType::Named("CMessage".to_string())),
                        false,
                    ),
                    is_reference: true,
                    is_self: false,
                },
            ],
            return_type: ExecType::Named("()".to_string()),
            requires: vec!["old(self).well_formed()".to_string()],
            ensures: vec!["self.well_formed()".to_string()],
            decreases: vec![],
            body: ExecExpr::Block(vec![]),
            is_method: true,
            receiver_type: Some("CReplica".to_string()),
        };

        let output = print_function(&func);
        // Verify impl block structure
        assert!(
            output.starts_with("impl CReplica {\n"),
            "output: {}",
            output
        );
        assert!(
            output.contains("pub exec fn CDoStep(&mut self, msg: &CMessage)"),
            "output: {}",
            output
        );
        assert!(output.contains("requires"), "output: {}", output);
        assert!(
            output.contains("old(self).well_formed()"),
            "output: {}",
            output
        );
        assert!(output.contains("ensures"), "output: {}", output);
        assert!(output.contains("self.well_formed()"), "output: {}", output);
        // No return type
        assert!(!output.contains("-> (result:"), "output: {}", output);
    }

    #[test]
    fn test_print_method_no_extra_params() {
        // Method with only self parameter (no extra args)
        let func = ExecFunction {
            name: "CInit".to_string(),
            params: vec![ExecParameter {
                name: "s".to_string(),
                ty: ExecType::Reference(Box::new(ExecType::Named("CState".to_string())), true),
                is_reference: true,
                is_self: true,
            }],
            return_type: ExecType::Named("CState".to_string()),
            requires: vec![],
            ensures: vec![],
            decreases: vec![],
            body: ExecExpr::Block(vec![]),
            is_method: true,
            receiver_type: Some("CState".to_string()),
        };

        let output = print_function(&func);
        assert!(
            output.contains("pub exec fn CInit(&mut self)"),
            "self-only method should have just &mut self: {}",
            output
        );
    }

    #[test]
    fn test_exec_parameter_is_self_field() {
        let self_param = ExecParameter {
            name: "self".to_string(),
            ty: ExecType::Reference(Box::new(ExecType::Named("CState".to_string())), true),
            is_reference: true,
            is_self: true,
        };
        assert!(self_param.is_self);

        let regular_param = ExecParameter {
            name: "packet".to_string(),
            ty: ExecType::Reference(Box::new(ExecType::Named("CPacket".to_string())), false),
            is_reference: true,
            is_self: false,
        };
        assert!(!regular_param.is_self);
    }

    #[test]
    fn test_method_body_struct_to_field_assignments() {
        // A method whose body is a struct construction should emit field assignments
        let func = ExecFunction {
            name: "CDoStep".to_string(),
            params: vec![
                ExecParameter {
                    name: "s".to_string(),
                    ty: ExecType::Reference(
                        Box::new(ExecType::Named("CReplica".to_string())),
                        true,
                    ),
                    is_reference: true,
                    is_self: true,
                },
                ExecParameter {
                    name: "val".to_string(),
                    ty: ExecType::Named("u64".to_string()),
                    is_reference: false,
                    is_self: false,
                },
            ],
            return_type: ExecType::Named("CReplica".to_string()),
            requires: vec![],
            ensures: vec![],
            decreases: vec![],
            body: ExecExpr::Struct {
                name: "CReplica".to_string(),
                fields: vec![
                    ("counter".to_string(), ExecExpr::Var("val".to_string())),
                    ("state".to_string(), ExecExpr::Literal("0u64".to_string())),
                ],
            },
            is_method: true,
            receiver_type: Some("CReplica".to_string()),
        };

        let output = print_function(&func);
        // Should have ghost old_self binding
        assert!(
            output.contains("let ghost old_self = *old(self);"),
            "method body should start with old_self binding: {}",
            output
        );
        // Should have field assignments instead of struct construction
        assert!(
            output.contains("self.counter = val"),
            "should emit self.counter = val: {}",
            output
        );
        assert!(
            output.contains("self.state = 0u64"),
            "should emit self.state = 0u64: {}",
            output
        );
        // Should NOT have struct field initialization syntax
        assert!(
            !output.contains("counter:"),
            "should not have struct field initialization: {}",
            output
        );
    }

    #[test]
    fn test_method_body_struct_update_to_field_assignments() {
        // StructUpdate should only emit assignments for changed fields
        let func = ExecFunction {
            name: "CIncrement".to_string(),
            params: vec![ExecParameter {
                name: "s".to_string(),
                ty: ExecType::Reference(Box::new(ExecType::Named("CState".to_string())), true),
                is_reference: true,
                is_self: true,
            }],
            return_type: ExecType::Named("CState".to_string()),
            requires: vec![],
            ensures: vec![],
            decreases: vec![],
            body: ExecExpr::StructUpdate {
                name: "CState".to_string(),
                base: Box::new(ExecExpr::Clone(Box::new(ExecExpr::Var("s".to_string())))),
                fields: vec![(
                    "counter".to_string(),
                    ExecExpr::Binary {
                        lhs: Box::new(ExecExpr::Var("self.counter".to_string())),
                        op: "+".to_string(),
                        rhs: Box::new(ExecExpr::Literal("1".to_string())),
                    },
                )],
            },
            is_method: true,
            receiver_type: Some("CState".to_string()),
        };

        let output = print_function(&func);
        // Only the changed field should be assigned
        assert!(
            output.contains("self.counter = "),
            "should assign changed field: {}",
            output
        );
        // Should not have struct update syntax
        assert!(
            !output.contains(".."),
            "should not have struct update ..base syntax: {}",
            output
        );
    }

    #[test]
    fn test_method_body_if_else_branches() {
        // Method body with if/else where each branch returns a struct
        let func = ExecFunction {
            name: "CStep".to_string(),
            params: vec![
                ExecParameter {
                    name: "s".to_string(),
                    ty: ExecType::Reference(Box::new(ExecType::Named("CState".to_string())), true),
                    is_reference: true,
                    is_self: true,
                },
                ExecParameter {
                    name: "flag".to_string(),
                    ty: ExecType::Named("bool".to_string()),
                    is_reference: false,
                    is_self: false,
                },
            ],
            return_type: ExecType::Named("CState".to_string()),
            requires: vec![],
            ensures: vec![],
            decreases: vec![],
            body: ExecExpr::If {
                cond: Box::new(ExecExpr::Var("flag".to_string())),
                then_branch: Box::new(ExecExpr::Struct {
                    name: "CState".to_string(),
                    fields: vec![("x".to_string(), ExecExpr::Literal("1".to_string()))],
                }),
                else_branch: Some(Box::new(ExecExpr::Struct {
                    name: "CState".to_string(),
                    fields: vec![("x".to_string(), ExecExpr::Literal("0".to_string()))],
                })),
            },
            is_method: true,
            receiver_type: Some("CState".to_string()),
        };

        let output = print_function(&func);
        // Both branches should have field assignments
        assert!(
            output.contains("self.x = 1"),
            "then branch should have field assignment: {}",
            output
        );
        assert!(
            output.contains("self.x = 0"),
            "else branch should have field assignment: {}",
            output
        );
    }

    #[test]
    fn test_method_body_block_with_lets_then_struct() {
        // Method body: let bindings followed by struct construction
        let func = ExecFunction {
            name: "CCompute".to_string(),
            params: vec![ExecParameter {
                name: "s".to_string(),
                ty: ExecType::Reference(Box::new(ExecType::Named("CState".to_string())), true),
                is_reference: true,
                is_self: true,
            }],
            return_type: ExecType::Named("CState".to_string()),
            requires: vec![],
            ensures: vec![],
            decreases: vec![],
            body: ExecExpr::Block(vec![
                ExecExpr::Let {
                    pattern: "tmp".to_string(),
                    ty: None,
                    value: Box::new(ExecExpr::Literal("42u64".to_string())),
                },
                ExecExpr::Struct {
                    name: "CState".to_string(),
                    fields: vec![("val".to_string(), ExecExpr::Var("tmp".to_string()))],
                },
            ]),
            is_method: true,
            receiver_type: Some("CState".to_string()),
        };

        let output = print_function(&func);
        // Let binding should be preserved
        assert!(
            output.contains("let tmp = 42u64;"),
            "let binding should be preserved: {}",
            output
        );
        // Last expression should be field assignment
        assert!(
            output.contains("self.val = tmp"),
            "struct construction should become field assignment: {}",
            output
        );
    }

    #[test]
    fn test_method_body_tuple_with_struct_extracts_assignments() {
        // Multi-output method: body is Tuple(Struct{...}, sent_packets)
        // Should become: self.field = val; sent_packets (as return)
        let func = ExecFunction {
            name: "CHandleMsg".to_string(),
            params: vec![
                ExecParameter {
                    name: "s".to_string(),
                    ty: ExecType::Reference(Box::new(ExecType::Named("CState".to_string())), true),
                    is_reference: true,
                    is_self: true,
                },
                ExecParameter {
                    name: "msg".to_string(),
                    ty: ExecType::Reference(
                        Box::new(ExecType::Named("CMessage".to_string())),
                        false,
                    ),
                    is_reference: true,
                    is_self: false,
                },
            ],
            return_type: ExecType::Named("Vec<CTPCMessage>".to_string()),
            requires: vec![],
            ensures: vec![],
            decreases: vec![],
            body: ExecExpr::Tuple(vec![
                ExecExpr::Struct {
                    name: "CState".to_string(),
                    fields: vec![
                        ("counter".to_string(), ExecExpr::Literal("1u64".to_string())),
                        ("flag".to_string(), ExecExpr::Literal("true".to_string())),
                    ],
                },
                ExecExpr::Var("sent_packets".to_string()),
            ]),
            is_method: true,
            receiver_type: Some("CState".to_string()),
        };

        let output = print_function(&func);
        // Should have field assignments
        assert!(
            output.contains("self.counter = 1u64"),
            "should have counter assignment: {}",
            output
        );
        assert!(
            output.contains("self.flag = true"),
            "should have flag assignment: {}",
            output
        );
        // Should return remaining tuple element
        assert!(
            output.contains("sent_packets"),
            "should return remaining tuple element: {}",
            output
        );
        // Should have return type in signature
        assert!(
            output.contains("-> (result: Vec<CTPCMessage>)"),
            "multi-output method should have return type: {}",
            output
        );
    }

    #[test]
    fn test_method_body_tuple_in_block_tail() {
        // Multi-output method where body is Block([let ..., Tuple(Struct, packets)])
        let func = ExecFunction {
            name: "CStep".to_string(),
            params: vec![ExecParameter {
                name: "s".to_string(),
                ty: ExecType::Reference(Box::new(ExecType::Named("CState".to_string())), true),
                is_reference: true,
                is_self: true,
            }],
            return_type: ExecType::Named("Vec<CMsg>".to_string()),
            requires: vec![],
            ensures: vec![],
            decreases: vec![],
            body: ExecExpr::Block(vec![
                ExecExpr::Let {
                    pattern: "pkts".to_string(),
                    ty: None,
                    value: Box::new(ExecExpr::Literal("Vec::new()".to_string())),
                },
                ExecExpr::Tuple(vec![
                    ExecExpr::StructUpdate {
                        name: "CState".to_string(),
                        base: Box::new(ExecExpr::Var("self".to_string())),
                        fields: vec![(
                            "counter".to_string(),
                            ExecExpr::Literal("0u64".to_string()),
                        )],
                    },
                    ExecExpr::Var("pkts".to_string()),
                ]),
            ]),
            is_method: true,
            receiver_type: Some("CState".to_string()),
        };

        let output = print_function(&func);
        // Let binding preserved
        assert!(
            output.contains("let pkts = Vec::new();"),
            "let binding should be preserved: {}",
            output
        );
        // Struct update → field assignment
        assert!(
            output.contains("self.counter = 0u64"),
            "struct update should become field assignment: {}",
            output
        );
        // Remaining element returned
        assert!(
            output.contains("pkts"),
            "should return remaining packets: {}",
            output
        );
    }

    #[test]
    fn test_method_signature_with_non_unit_return() {
        // Multi-output method should emit return type
        let func = ExecFunction {
            name: "CProcess".to_string(),
            params: vec![ExecParameter {
                name: "s".to_string(),
                ty: ExecType::Reference(Box::new(ExecType::Named("CState".to_string())), true),
                is_reference: true,
                is_self: true,
            }],
            return_type: ExecType::Tuple(vec![
                ExecType::Named("Vec<CMsg>".to_string()),
                ExecType::Named("u64".to_string()),
            ]),
            requires: vec![],
            ensures: vec![],
            decreases: vec![],
            body: ExecExpr::Tuple(vec![
                ExecExpr::Struct {
                    name: "CState".to_string(),
                    fields: vec![("x".to_string(), ExecExpr::Literal("1u64".to_string()))],
                },
                ExecExpr::Var("pkts".to_string()),
                ExecExpr::Literal("42u64".to_string()),
            ]),
            is_method: true,
            receiver_type: Some("CState".to_string()),
        };

        let output = print_function(&func);
        // Should have tuple return type
        assert!(
            output.contains("-> (result: (Vec<CMsg>, u64))"),
            "should emit tuple return type: {}",
            output
        );
        // Field assignment for struct
        assert!(
            output.contains("self.x = 1u64"),
            "should have field assignment: {}",
            output
        );
    }

    #[test]
    fn test_method_body_let_result_tuple_pattern() {
        // Body pattern: let result = (Struct{...}, vec); proof { assert(result.1@...) }; result
        // Should become: field assignments; let result = vec; proof { assert(result@...) }; result
        let func = ExecFunction {
            name: "CStep".to_string(),
            params: vec![ExecParameter {
                name: "s".to_string(),
                ty: ExecType::Reference(Box::new(ExecType::Named("CState".to_string())), true),
                is_reference: true,
                is_self: true,
            }],
            return_type: ExecType::Named("Vec<CMsg>".to_string()),
            requires: vec![],
            ensures: vec![],
            decreases: vec![],
            body: ExecExpr::Block(vec![
                ExecExpr::Let {
                    pattern: "result".to_string(),
                    ty: None,
                    value: Box::new(ExecExpr::Tuple(vec![
                        ExecExpr::Struct {
                            name: "CState".to_string(),
                            fields: vec![(
                                "counter".to_string(),
                                ExecExpr::Literal("1u64".to_string()),
                            )],
                        },
                        ExecExpr::Var("packets".to_string()),
                    ])),
                },
                ExecExpr::ProofBlock {
                    stmts: vec![ExecExpr::Assert(Box::new(ExecExpr::Var(
                        "result.1@.len() == 0".to_string(),
                    )))],
                },
                ExecExpr::Var("result".to_string()),
            ]),
            is_method: true,
            receiver_type: Some("CState".to_string()),
        };

        let output = print_function(&func);
        // Field assignment
        assert!(
            output.contains("self.counter = 1u64"),
            "struct should become field assignment: {}",
            output
        );
        // Result rebound to remaining element
        assert!(
            output.contains("let result = packets"),
            "result should be rebound to remaining vec: {}",
            output
        );
        // Proof block should reference result@ (not result.1@)
        assert!(
            output.contains("result@.len() == 0"),
            "proof should reference result@ not result.1@: {}",
            output
        );
        assert!(
            !output.contains("result.1@"),
            "should NOT have result.1@ reference: {}",
            output
        );
    }

    #[test]
    fn test_rewrite_tuple_refs_in_string() {
        // struct_idx=0, result_var="result", remaining_count=1
        let s = "result.1@.map(|i: int, p: CMsg| p@) =~= Seq::empty().push(result.1@[0]@)";
        let out = Printer::rewrite_tuple_refs_in_string(s, 0, "result", 1);
        assert_eq!(
            out, "result@.map(|i: int, p: CMsg| p@) =~= Seq::empty().push(result@[0]@)",
            "result.1 should become result when remaining_count=1"
        );

        // struct_idx=0, remaining_count=2 — renumber 1→0, 2→1
        let s2 = "f(result.0@, result.1@, result.2@)";
        let out2 = Printer::rewrite_tuple_refs_in_string(s2, 0, "result", 2);
        assert_eq!(out2, "f(self@, result.0@, result.1@)");
    }
}
