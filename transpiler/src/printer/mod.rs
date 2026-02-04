//! Output formatting for generated code.
//!
//! This module handles pretty-printing of generated Verus exec functions
//! to properly formatted Rust source code.

use crate::translator::{ExecExpr, ExecFunction, ExecParameter};

/// Configuration for code printing
#[derive(Debug, Clone)]
pub struct PrinterConfig {
    /// Indentation string (e.g., "    " or "\t")
    pub indent: String,
    /// Maximum line width before wrapping
    pub max_width: usize,
    /// Whether to include comments
    pub include_comments: bool,
}

impl Default for PrinterConfig {
    fn default() -> Self {
        Self {
            indent: "    ".to_string(),
            max_width: 100,
            include_comments: true,
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

        // Print function signature
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

        // Print body
        self.indent();
        self.write("{");
        self.newline();
        self.current_indent += 1;
        self.print_expr(&func.body);
        self.current_indent -= 1;
        self.newline();
        self.indent();
        self.write("}");
        self.newline();

        std::mem::take(&mut self.output)
    }

    /// Print just an expression to a string (for testing/debugging)
    pub fn print_expr_to_string(&mut self, expr: &ExecExpr) -> String {
        self.output.clear();
        self.current_indent = 0;
        self.print_expr(expr);
        std::mem::take(&mut self.output)
    }

    /// Print function signature
    fn print_signature(&mut self, func: &ExecFunction) {
        self.write("pub exec fn ");
        self.write(&func.name);
        self.write("(");

        // Print parameters
        let params: Vec<_> = func.params.iter().map(|p| self.format_param(p)).collect();
        self.write(&params.join(", "));

        self.write(") -> (result: ");
        self.write(&func.return_type.to_rust_string());
        self.write(")");
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
                    self.print_expr(stmt);
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
                self.print_expr(value);
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
                for (field_name, field_value) in fields {
                    self.indent();
                    self.write(field_name);
                    self.write(": ");
                    self.print_expr(field_value);
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
                self.print_expr(base);
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
                    self.print_expr(receiver);
                    self.write("[");
                    self.print_expr(&args[0]);
                    self.write("]");
                } else {
                    self.print_expr(receiver);
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
                        p.print_expr(a);
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
                    // Handle empty blocks specially - print {} instead of nothing
                    match body {
                        ExecExpr::Block(stmts) if stmts.is_empty() => {
                            self.write("{}");
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
                    self.print_expr(lhs);
                    self.write(" ");
                    self.write(op);
                    self.write(" ");
                    self.print_expr(rhs);
                    self.write(")");
                }
            }

            ExecExpr::Unary { op, expr } => {
                self.write(op);
                self.print_expr(expr);
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
            ExecExpr::ForInIter {
                var,
                iter_name,
                iter_source,
                invariants,
                body,
            } => {
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
                // Verus proof blocks: proof{stmt};
                self.write("proof{");
                // For single-statement proof blocks, keep it compact
                if stmts.len() == 1 {
                    self.print_expr(&stmts[0]);
                } else {
                    self.newline();
                    self.current_indent += 1;
                    for stmt in stmts {
                        self.indent();
                        self.print_expr(stmt);
                        self.newline();
                    }
                    self.current_indent -= 1;
                    self.indent();
                }
                self.write("};");
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
                self.print_expr(expr);
                self.write(" is ");
                self.write(variant);
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
            }],
            return_type: ExecType::Named("CState".to_string()),
            requires: vec!["s.well_formed()".to_string()],
            ensures: vec!["result.well_formed()".to_string()],
            decreases: vec![],
            body: ExecExpr::Clone(Box::new(ExecExpr::Var("s".to_string()))),
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
            }],
            return_type: ExecType::Vec(Box::new(ExecType::Named("CRequest".to_string()))),
            requires: vec!["s.valid()".to_string()],
            ensures: vec!["result.valid()".to_string()],
            decreases: vec!["s.len()".to_string()],
            body: ExecExpr::VecLit(vec![]),
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

        // For single-statement proof blocks, output is compact: proof{stmt};
        assert!(output.contains("proof{"));
        assert!(output.contains("seen_keys = seen_keys.insert"));
        assert!(output.contains("};"));
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
}
