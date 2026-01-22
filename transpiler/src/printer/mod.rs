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

    /// Print function signature
    fn print_signature(&mut self, func: &ExecFunction) {
        self.write("pub exec fn ");
        self.write(&func.name);
        self.write("(");

        // Print parameters
        let params: Vec<_> = func
            .params
            .iter()
            .map(|p| self.format_param(p))
            .collect();
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
                for stmt in stmts {
                    self.indent();
                    self.print_expr(stmt);
                    self.newline();
                }
            }

            ExecExpr::Let { name, ty, value } => {
                self.write("let ");
                self.write(name);
                if let Some(ty) = ty {
                    self.write(": ");
                    self.write(&ty.to_rust_string());
                }
                self.write(" = ");
                self.print_expr(value);
                self.write(";");
            }

            ExecExpr::If { cond, then_branch, else_branch } => {
                self.write("if ");
                self.print_expr(cond);
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

            ExecExpr::MethodCall { receiver, method, args } => {
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
                    self.print_expr(body);
                    self.write(",");
                    self.newline();
                }
                self.current_indent -= 1;
                self.indent();
                self.write("}");
            }

            ExecExpr::StructUpdate { base, fields } => {
                // Get the struct name from the base (if it's a clone of a var)
                let base_str = {
                    let mut p = Printer::new(self.config.clone());
                    p.print_expr(base);
                    p.output
                };

                // For struct update, we need to figure out the type name
                // Since we're typically doing SomeType { fields, ..base }, we need the type
                self.write("{ ");
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
                self.write("(");
                self.print_expr(lhs);
                self.write(" ");
                self.write(op);
                self.write(" ");
                self.print_expr(rhs);
                self.write(")");
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
            body: ExecExpr::Clone(Box::new(ExecExpr::Var("s".to_string()))),
        };

        let output = print_function(&func);
        assert!(output.contains("pub exec fn CTestFn"));
        assert!(output.contains("requires"));
        assert!(output.contains("ensures"));
    }
}
