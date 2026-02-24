//! Output formatting for generated code.
//!
//! This module handles pretty-printing of generated Verus exec functions
//! to properly formatted Rust source code.

use std::collections::HashMap;

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
}
