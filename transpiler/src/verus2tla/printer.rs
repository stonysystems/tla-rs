//! TLA+ pretty printer.
//!
//! Converts TLA+ AST to formatted text output.

use crate::tla::ast::{
    TlaBinOp, TlaConstantDecl, TlaExceptPath, TlaExpr, TlaInstance, TlaModule, TlaNumber,
    TlaOperator, TlaParam, TlaQuantBound, TlaTheorem, TlaUnaryOp,
};

/// Configuration for the TLA+ printer.
#[derive(Debug, Clone)]
pub struct TlaPrinterConfig {
    /// Indentation string (default: 4 spaces)
    pub indent: String,
    /// Maximum line width before wrapping (default: 80)
    pub max_line_width: usize,
    /// Whether to add comments for generated code
    pub add_generation_comments: bool,
}

impl Default for TlaPrinterConfig {
    fn default() -> Self {
        Self {
            indent: "    ".to_string(),
            max_line_width: 80,
            add_generation_comments: true,
        }
    }
}

/// TLA+ pretty printer.
pub struct TlaPrinter {
    config: TlaPrinterConfig,
}

impl TlaPrinter {
    /// Create a new TLA+ printer with default configuration.
    pub fn new() -> Self {
        Self {
            config: TlaPrinterConfig::default(),
        }
    }

    /// Create a new TLA+ printer with custom configuration.
    pub fn with_config(config: TlaPrinterConfig) -> Self {
        Self { config }
    }

    /// Print a complete TLA+ module.
    pub fn print_module(&self, module: &TlaModule) -> String {
        let mut output = String::new();

        // Module header
        let header_line = format!("---- MODULE {} ----", module.name);
        output.push_str(&header_line);
        output.push('\n');

        // Generation comment
        if self.config.add_generation_comments {
            output.push_str("\\* Auto-generated from Verus spec by verus2tla\n");
            output.push_str("\\* DO NOT EDIT MANUALLY\n");
        }
        output.push('\n');

        // EXTENDS
        if !module.extends.is_empty() {
            output.push_str("EXTENDS ");
            output.push_str(&module.extends.join(", "));
            output.push('\n');
            output.push('\n');
        }

        // CONSTANTS
        if !module.constants.is_empty() {
            output.push_str("CONSTANTS ");
            let const_names: Vec<String> = module
                .constants
                .iter()
                .map(|c| self.print_constant_decl(c))
                .collect();
            output.push_str(&const_names.join(", "));
            output.push('\n');
            output.push('\n');
        }

        // VARIABLES
        if !module.variables.is_empty() {
            output.push_str("VARIABLES ");
            output.push_str(&module.variables.join(", "));
            output.push('\n');
            output.push('\n');
        }

        // ASSUMPTIONS
        for assumption in &module.assumptions {
            output.push_str("ASSUME ");
            output.push_str(&self.print_expr(assumption, 0));
            output.push('\n');
            output.push('\n');
        }

        // INSTANCES
        for instance in &module.instances {
            output.push_str(&self.print_instance(instance));
            output.push('\n');
        }
        if !module.instances.is_empty() {
            output.push('\n');
        }

        // Operators
        for operator in &module.operators {
            output.push_str(&self.print_operator(operator));
            output.push('\n');
        }

        // Theorems
        for theorem in &module.theorems {
            output.push_str(&self.print_theorem(theorem));
            output.push('\n');
        }

        // Module footer
        output.push_str("====\n");

        output
    }

    /// Print a constant declaration.
    fn print_constant_decl(&self, constant: &TlaConstantDecl) -> String {
        if let Some(ref constraint) = constant.type_constraint {
            format!("{} \\in {}", constant.name, self.print_expr(constraint, 0))
        } else {
            constant.name.clone()
        }
    }

    /// Print a module instance.
    fn print_instance(&self, instance: &TlaInstance) -> String {
        let mut output = String::new();

        if instance.is_local {
            output.push_str("LOCAL ");
        }

        if let Some(ref name) = instance.local_name {
            output.push_str(name);
            output.push_str(" == ");
        }

        output.push_str("INSTANCE ");
        output.push_str(&instance.module_name);

        if !instance.substitutions.is_empty() {
            output.push_str(" WITH ");
            let subs: Vec<String> = instance
                .substitutions
                .iter()
                .map(|(name, expr)| format!("{} <- {}", name, self.print_expr(expr, 0)))
                .collect();
            output.push_str(&subs.join(", "));
        }

        output
    }

    /// Print an operator definition.
    pub fn print_operator(&self, operator: &TlaOperator) -> String {
        let mut output = String::new();

        // RECURSIVE declaration if needed
        if operator.is_recursive {
            output.push_str("RECURSIVE ");
            output.push_str(&operator.name);
            output.push('(');
            let underscores: Vec<&str> = operator.params.iter().map(|_| "_").collect();
            output.push_str(&underscores.join(", "));
            output.push_str(")\n");
        }

        // LOCAL prefix
        if operator.is_local {
            output.push_str("LOCAL ");
        }

        // Operator name and parameters
        output.push_str(&operator.name);
        if !operator.params.is_empty() {
            output.push('(');
            let params: Vec<String> = operator.params.iter().map(|p| self.print_param(p)).collect();
            output.push_str(&params.join(", "));
            output.push(')');
        }
        output.push_str(" ==\n");

        // Operator body with indentation
        let body = self.print_expr(&operator.body, 1);
        output.push_str(&body);
        output.push('\n');

        output
    }

    /// Print a parameter.
    fn print_param(&self, param: &TlaParam) -> String {
        if param.arity > 0 {
            // Higher-order parameter
            let underscores: Vec<&str> = (0..param.arity).map(|_| "_").collect();
            format!("{}({})", param.name, underscores.join(", "))
        } else {
            param.name.clone()
        }
    }

    /// Print a theorem.
    fn print_theorem(&self, theorem: &TlaTheorem) -> String {
        let mut output = String::new();

        output.push_str("THEOREM ");
        if let Some(ref name) = theorem.name {
            output.push_str(name);
            output.push_str(" == ");
        }
        output.push_str(&self.print_expr(&theorem.body, 0));
        output.push('\n');

        output
    }

    /// Print an expression with the given indentation level.
    pub fn print_expr(&self, expr: &TlaExpr, indent_level: usize) -> String {
        let indent = self.config.indent.repeat(indent_level);

        match expr {
            TlaExpr::Ident(name) => format!("{}{}", indent, name),

            TlaExpr::Prime(inner) => {
                let inner_str = self.print_expr_no_indent(inner);
                format!("{}{}'", indent, inner_str)
            }

            TlaExpr::Number(num) => format!("{}{}", indent, self.print_number(num)),

            TlaExpr::String(s) => format!("{}\"{}\"", indent, s),

            TlaExpr::Bool(b) => {
                if *b {
                    format!("{}TRUE", indent)
                } else {
                    format!("{}FALSE", indent)
                }
            }

            TlaExpr::BinOp { op, left, right } => {
                self.print_binop(op, left, right, indent_level)
            }

            TlaExpr::UnaryOp { op, operand } => {
                let op_str = self.print_unary_op(op);
                let operand_str = self.print_expr_no_indent(operand);
                format!("{}{}{}", indent, op_str, operand_str)
            }

            TlaExpr::OpApply { op, args } => {
                let op_str = self.print_expr_no_indent(op);
                if args.is_empty() {
                    format!("{}{}", indent, op_str)
                } else {
                    let args_str: Vec<String> =
                        args.iter().map(|a| self.print_expr_no_indent(a)).collect();
                    format!("{}{}({})", indent, op_str, args_str.join(", "))
                }
            }

            TlaExpr::FnApply { func, arg } => {
                let func_str = self.print_expr_no_indent(func);
                let arg_str = self.print_expr_no_indent(arg);
                format!("{}{}[{}]", indent, func_str, arg_str)
            }

            TlaExpr::SetEnum(elements) => {
                let elems: Vec<String> = elements
                    .iter()
                    .map(|e| self.print_expr_no_indent(e))
                    .collect();
                format!("{}{{{}}}", indent, elems.join(", "))
            }

            TlaExpr::SetFilter { var, set, filter } => {
                let set_str = self.print_expr_no_indent(set);
                let filter_str = self.print_expr_no_indent(filter);
                format!("{}{{{}\\in {} : {}}}", indent, var, set_str, filter_str)
            }

            TlaExpr::SetMap { expr, var, set } => {
                let expr_str = self.print_expr_no_indent(expr);
                let set_str = self.print_expr_no_indent(set);
                format!("{}{{{}:{} \\in {}}}", indent, expr_str, var, set_str)
            }

            TlaExpr::FnConstruct { var, domain, body } => {
                let domain_str = self.print_expr_no_indent(domain);
                let body_str = self.print_expr_no_indent(body);
                format!("{}[{} \\in {} |-> {}]", indent, var, domain_str, body_str)
            }

            TlaExpr::FnExcept { func, updates } => {
                let func_str = self.print_expr_no_indent(func);
                let updates_str: Vec<String> = updates
                    .iter()
                    .map(|u| {
                        let path_str: Vec<String> = u
                            .path
                            .iter()
                            .map(|p| match p {
                                TlaExceptPath::Index(e) => {
                                    format!("![{}]", self.print_expr_no_indent(e))
                                }
                                TlaExceptPath::Field(f) => format!("!.{}", f),
                            })
                            .collect();
                        let value_str = self.print_expr_no_indent(&u.value);
                        format!("{} = {}", path_str.join(""), value_str)
                    })
                    .collect();
                format!("{}[{} EXCEPT {}]", indent, func_str, updates_str.join(", "))
            }

            TlaExpr::Record(fields) => {
                if fields.is_empty() {
                    // Empty record - use a named constant or special syntax
                    // In TLA+, an "empty record" is typically a unit type
                    format!("{}<<>>", indent) // Using empty tuple as placeholder for empty struct
                } else {
                    let fields_str: Vec<String> = fields
                        .iter()
                        .map(|(name, expr)| {
                            format!("{} |-> {}", name, self.print_expr_no_indent(expr))
                        })
                        .collect();
                    format!("{}[{}]", indent, fields_str.join(", "))
                }
            }

            TlaExpr::RecordAccess { record, field } => {
                let record_str = self.print_expr_no_indent(record);
                format!("{}{}.{}", indent, record_str, field)
            }

            TlaExpr::Tuple(elements) => {
                let elems: Vec<String> = elements
                    .iter()
                    .map(|e| self.print_expr_no_indent(e))
                    .collect();
                format!("{}<<{}>>", indent, elems.join(", "))
            }

            TlaExpr::Forall { vars, body } => {
                self.print_quantifier("\\A", vars, body, indent_level)
            }

            TlaExpr::Exists { vars, body } => {
                self.print_quantifier("\\E", vars, body, indent_level)
            }

            TlaExpr::Choose { var, set, body } => {
                let body_str = self.print_expr_no_indent(body);
                if let Some(ref s) = set {
                    let set_str = self.print_expr_no_indent(s);
                    format!("{}CHOOSE {} \\in {} : {}", indent, var, set_str, body_str)
                } else {
                    format!("{}CHOOSE {} : {}", indent, var, body_str)
                }
            }

            TlaExpr::IfThenElse {
                cond,
                then_expr,
                else_expr,
            } => {
                let cond_str = self.print_expr_no_indent(cond);
                let then_str = self.print_expr_no_indent(then_expr);
                let else_str = self.print_expr_no_indent(else_expr);
                format!(
                    "{}IF {} THEN {} ELSE {}",
                    indent, cond_str, then_str, else_str
                )
            }

            TlaExpr::Case { arms, other } => {
                let mut output = format!("{}CASE ", indent);
                let arms_str: Vec<String> = arms
                    .iter()
                    .map(|(cond, result)| {
                        format!(
                            "{} -> {}",
                            self.print_expr_no_indent(cond),
                            self.print_expr_no_indent(result)
                        )
                    })
                    .collect();
                output.push_str(&arms_str.join("\n     [] "));
                if let Some(ref other_expr) = other {
                    output.push_str("\n     [] OTHER -> ");
                    output.push_str(&self.print_expr_no_indent(other_expr));
                }
                output
            }

            TlaExpr::LetIn { defs, body } => {
                let mut output = format!("{}LET ", indent);
                for (i, def) in defs.iter().enumerate() {
                    if i > 0 {
                        output.push_str(&self.config.indent);
                    }
                    output.push_str(&def.name);
                    if !def.params.is_empty() {
                        output.push('(');
                        let params: Vec<String> =
                            def.params.iter().map(|p| self.print_param(p)).collect();
                        output.push_str(&params.join(", "));
                        output.push(')');
                    }
                    output.push_str(" == ");
                    output.push_str(&self.print_expr_no_indent(&def.body));
                    output.push('\n');
                }
                output.push_str(&format!("{}IN ", indent));
                output.push_str(&self.print_expr_no_indent(body));
                output
            }

            TlaExpr::Unchanged(vars) => {
                let vars_str: Vec<String> = vars
                    .iter()
                    .map(|v| self.print_expr_no_indent(v))
                    .collect();
                if vars_str.len() == 1 {
                    format!("{}UNCHANGED {}", indent, vars_str[0])
                } else {
                    format!("{}UNCHANGED <<{}>>", indent, vars_str.join(", "))
                }
            }

            TlaExpr::Enabled(action) => {
                let action_str = self.print_expr_no_indent(action);
                format!("{}ENABLED {}", indent, action_str)
            }

            TlaExpr::Always(formula) => {
                let formula_str = self.print_expr_no_indent(formula);
                format!("{}[]{}", indent, formula_str)
            }

            TlaExpr::Eventually(formula) => {
                let formula_str = self.print_expr_no_indent(formula);
                format!("{}<>{}", indent, formula_str)
            }

            TlaExpr::LeadsTo { left, right } => {
                let left_str = self.print_expr_no_indent(left);
                let right_str = self.print_expr_no_indent(right);
                format!("{}{} ~> {}", indent, left_str, right_str)
            }

            TlaExpr::WeakFairness { vars, action } => {
                let vars_str = self.print_expr_no_indent(vars);
                let action_str = self.print_expr_no_indent(action);
                format!("{}WF_{}({})", indent, vars_str, action_str)
            }

            TlaExpr::StrongFairness { vars, action } => {
                let vars_str = self.print_expr_no_indent(vars);
                let action_str = self.print_expr_no_indent(action);
                format!("{}SF_{}({})", indent, vars_str, action_str)
            }
        }
    }

    /// Print an expression without leading indentation.
    fn print_expr_no_indent(&self, expr: &TlaExpr) -> String {
        let full = self.print_expr(expr, 0);
        full.trim_start().to_string()
    }

    /// Print a binary operation.
    fn print_binop(
        &self,
        op: &TlaBinOp,
        left: &TlaExpr,
        right: &TlaExpr,
        indent_level: usize,
    ) -> String {
        let indent = self.config.indent.repeat(indent_level);

        // Add parentheses around operands with lower precedence to avoid TLA+ precedence conflicts
        let left_str = self.print_with_precedence(left, op);
        let right_str = self.print_with_precedence(right, op);
        let op_str = self.print_binary_op(op);

        // For conjunction/disjunction at the top level (indent_level > 0), use multi-line format
        // When indent_level is 0, we're likely in an inline context, so keep single line
        if indent_level > 0 && matches!(op, TlaBinOp::And | TlaBinOp::Or) {
            let connector = if *op == TlaBinOp::And { "/\\" } else { "\\/" };

            // Check if operands are also and/or - if so, flatten
            let left_parts = self.flatten_connective(left, *op);
            let right_parts = self.flatten_connective(right, *op);

            if left_parts.len() + right_parts.len() > 2 {
                // Multi-line format for many conjuncts/disjuncts
                let all_parts: Vec<String> = left_parts
                    .into_iter()
                    .chain(right_parts.into_iter())
                    .collect();

                let lines: Vec<String> = all_parts
                    .iter()
                    .map(|p| format!("{}{} {}", indent, connector, p))
                    .collect();
                return lines.join("\n");
            }
        }

        format!("{}{} {} {}", indent, left_str, op_str, right_str)
    }

    /// Print an expression with parentheses if needed for precedence.
    /// TLA+ has strict precedence rules for logical operators.
    /// When printing a child with a conflicting operator, wrap it in parentheses.
    fn print_with_precedence(&self, expr: &TlaExpr, parent_op: &TlaBinOp) -> String {
        let inner = self.print_expr_no_indent(expr);

        // Check if we need parentheses due to precedence conflict
        let needs_parens = match expr {
            TlaExpr::BinOp { op: child_op, .. } => {
                // In TLA+, logical operators have different precedence:
                // /\ (highest) > \/ > => (same as \/) > <=> (same as =>)
                // When mixing any of these operators, we need parentheses to avoid conflicts
                self.needs_precedence_parens(parent_op, child_op)
            }
            _ => false,
        };

        if needs_parens {
            format!("({})", inner)
        } else {
            inner
        }
    }

    /// Determine if parentheses are needed when child_op appears under parent_op.
    fn needs_precedence_parens(&self, parent_op: &TlaBinOp, child_op: &TlaBinOp) -> bool {
        // List of logical operators that can conflict
        let is_logical = |op: &TlaBinOp| {
            matches!(
                op,
                TlaBinOp::And | TlaBinOp::Or | TlaBinOp::Implies | TlaBinOp::Iff
            )
        };

        // List of arithmetic operators that can conflict
        let is_arithmetic = |op: &TlaBinOp| {
            matches!(
                op,
                TlaBinOp::Plus | TlaBinOp::Minus | TlaBinOp::Times | TlaBinOp::Div | TlaBinOp::Mod
            )
        };

        // If both are logical operators and different, we need parens
        if is_logical(parent_op) && is_logical(child_op) && parent_op != child_op {
            return true;
        }

        // If both are arithmetic operators and different (except mul/div have same precedence), we may need parens
        if is_arithmetic(parent_op) && is_arithmetic(child_op) && parent_op != child_op {
            // In TLA+, + and - have lower precedence than *, /, %
            // So we need parens when mixing add/sub with mul/div/mod
            let is_add_sub =
                |op: &TlaBinOp| matches!(op, TlaBinOp::Plus | TlaBinOp::Minus);
            let is_mul_div_mod =
                |op: &TlaBinOp| matches!(op, TlaBinOp::Times | TlaBinOp::Div | TlaBinOp::Mod);

            if (is_add_sub(parent_op) && is_mul_div_mod(child_op))
                || (is_mul_div_mod(parent_op) && is_add_sub(child_op))
            {
                return true;
            }
        }

        // /\ and \/ specifically conflict
        matches!(
            (parent_op, child_op),
            (TlaBinOp::And, TlaBinOp::Or) | (TlaBinOp::Or, TlaBinOp::And)
        )
    }

    /// Flatten nested conjunctions or disjunctions.
    fn flatten_connective(&self, expr: &TlaExpr, target_op: TlaBinOp) -> Vec<String> {
        match expr {
            TlaExpr::BinOp { op, left, right } if *op == target_op => {
                let mut result = self.flatten_connective(left, target_op);
                result.extend(self.flatten_connective(right, target_op));
                result
            }
            _ => vec![self.print_expr_no_indent(expr)],
        }
    }

    /// Print a quantifier expression.
    fn print_quantifier(
        &self,
        quantifier: &str,
        vars: &[TlaQuantBound],
        body: &TlaExpr,
        indent_level: usize,
    ) -> String {
        let indent = self.config.indent.repeat(indent_level);
        let bounds: Vec<String> = vars.iter().map(|b| self.print_quant_bound(b)).collect();
        let body_str = self.print_expr_no_indent(body);
        format!("{}{} {} : {}", indent, quantifier, bounds.join(", "), body_str)
    }

    /// Print a quantifier bound.
    fn print_quant_bound(&self, bound: &TlaQuantBound) -> String {
        if let Some(ref set) = bound.set {
            format!("{} \\in {}", bound.var, self.print_expr_no_indent(set))
        } else {
            bound.var.clone()
        }
    }

    /// Convert a binary operator to its TLA+ string representation.
    fn print_binary_op(&self, op: &TlaBinOp) -> &'static str {
        match op {
            TlaBinOp::And => "/\\",
            TlaBinOp::Or => "\\/",
            TlaBinOp::Implies => "=>",
            TlaBinOp::Iff => "<=>",
            TlaBinOp::In => "\\in",
            TlaBinOp::NotIn => "\\notin",
            TlaBinOp::Subseteq => "\\subseteq",
            TlaBinOp::Cup => "\\cup",
            TlaBinOp::Cap => "\\cap",
            TlaBinOp::Setminus => "\\",
            TlaBinOp::CrossProd => "\\X",
            TlaBinOp::Plus => "+",
            TlaBinOp::Minus => "-",
            TlaBinOp::Times => "*",
            TlaBinOp::Div => "\\div",
            TlaBinOp::Mod => "%",
            TlaBinOp::Slash => "/",
            TlaBinOp::Caret => "^",
            TlaBinOp::DotDot => "..",
            TlaBinOp::Eq => "=",
            TlaBinOp::Neq => "#",
            TlaBinOp::Lt => "<",
            TlaBinOp::Gt => ">",
            TlaBinOp::Leq => "<=",
            TlaBinOp::Geq => ">=",
            TlaBinOp::Compose => "\\cdot",
        }
    }

    /// Convert a unary operator to its TLA+ string representation.
    fn print_unary_op(&self, op: &TlaUnaryOp) -> &'static str {
        match op {
            TlaUnaryOp::Not => "~",
            TlaUnaryOp::Subset => "SUBSET ",
            TlaUnaryOp::Union => "UNION ",
            TlaUnaryOp::Domain => "DOMAIN ",
            TlaUnaryOp::Neg => "-",
        }
    }

    /// Print a number literal.
    fn print_number(&self, num: &TlaNumber) -> String {
        match num {
            TlaNumber::Decimal(s) => s.clone(),
            TlaNumber::Binary(s) => format!("\\b{}", s),
            TlaNumber::Octal(s) => format!("\\o{}", s),
            TlaNumber::Hex(s) => format!("\\h{}", s),
        }
    }
}

impl Default for TlaPrinter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tla::ast::TlaExceptUpdate;

    #[test]
    fn test_print_simple_module() {
        let mut module = TlaModule::new("Test");
        module.extends = vec!["Integers".to_string(), "Sequences".to_string()];
        module.variables = vec!["x".to_string(), "y".to_string()];

        let printer = TlaPrinter::new();
        let output = printer.print_module(&module);

        assert!(output.contains("---- MODULE Test ----"));
        assert!(output.contains("EXTENDS Integers, Sequences"));
        assert!(output.contains("VARIABLES x, y"));
        assert!(output.contains("===="));
    }

    #[test]
    fn test_print_operator() {
        let op = TlaOperator::new(
            "Init",
            TlaExpr::binop(TlaBinOp::Eq, TlaExpr::ident("x"), TlaExpr::number(0)),
        );

        let printer = TlaPrinter::new();
        let output = printer.print_operator(&op);

        assert!(output.contains("Init =="));
        assert!(output.contains("x = 0"));
    }

    #[test]
    fn test_print_operator_with_params() {
        let op = TlaOperator::new(
            "Add",
            TlaExpr::binop(
                TlaBinOp::Plus,
                TlaExpr::ident("a"),
                TlaExpr::ident("b"),
            ),
        )
        .with_params(vec![TlaParam::new("a"), TlaParam::new("b")]);

        let printer = TlaPrinter::new();
        let output = printer.print_operator(&op);

        assert!(output.contains("Add(a, b) =="));
        assert!(output.contains("a + b"));
    }

    #[test]
    fn test_print_forall() {
        let expr = TlaExpr::Forall {
            vars: vec![TlaQuantBound::new("x", TlaExpr::ident("S"))],
            body: Box::new(TlaExpr::binop(
                TlaBinOp::Gt,
                TlaExpr::ident("x"),
                TlaExpr::number(0),
            )),
        };

        let printer = TlaPrinter::new();
        let output = printer.print_expr(&expr, 0);

        assert!(output.contains("\\A x \\in S : x > 0"));
    }

    #[test]
    fn test_print_record() {
        let expr = TlaExpr::Record(vec![
            ("a".to_string(), TlaExpr::number(1)),
            ("b".to_string(), TlaExpr::number(2)),
        ]);

        let printer = TlaPrinter::new();
        let output = printer.print_expr(&expr, 0);

        assert!(output.contains("[a |-> 1, b |-> 2]"));
    }

    #[test]
    fn test_print_tuple() {
        let expr = TlaExpr::Tuple(vec![
            TlaExpr::number(1),
            TlaExpr::number(2),
            TlaExpr::number(3),
        ]);

        let printer = TlaPrinter::new();
        let output = printer.print_expr(&expr, 0);

        assert!(output.contains("<<1, 2, 3>>"));
    }

    #[test]
    fn test_print_if_then_else() {
        let expr = TlaExpr::IfThenElse {
            cond: Box::new(TlaExpr::binop(
                TlaBinOp::Gt,
                TlaExpr::ident("x"),
                TlaExpr::number(0),
            )),
            then_expr: Box::new(TlaExpr::ident("x")),
            else_expr: Box::new(TlaExpr::unary(TlaUnaryOp::Neg, TlaExpr::ident("x"))),
        };

        let printer = TlaPrinter::new();
        let output = printer.print_expr(&expr, 0);

        assert!(output.contains("IF x > 0 THEN x ELSE -x"));
    }

    #[test]
    fn test_print_fn_construct() {
        let expr = TlaExpr::FnConstruct {
            var: "i".to_string(),
            domain: Box::new(TlaExpr::binop(
                TlaBinOp::DotDot,
                TlaExpr::number(1),
                TlaExpr::number(10),
            )),
            body: Box::new(TlaExpr::binop(
                TlaBinOp::Times,
                TlaExpr::ident("i"),
                TlaExpr::number(2),
            )),
        };

        let printer = TlaPrinter::new();
        let output = printer.print_expr(&expr, 0);

        // The DotDot operator adds spaces around ".."
        assert!(output.contains("[i \\in 1 .. 10 |-> i * 2]"));
    }

    #[test]
    fn test_print_fn_except() {
        let expr = TlaExpr::FnExcept {
            func: Box::new(TlaExpr::ident("f")),
            updates: vec![TlaExceptUpdate {
                path: vec![TlaExceptPath::Index(TlaExpr::ident("i"))],
                value: TlaExpr::number(42),
            }],
        };

        let printer = TlaPrinter::new();
        let output = printer.print_expr(&expr, 0);

        assert!(output.contains("[f EXCEPT ![i] = 42]"));
    }

    #[test]
    fn test_print_set_comprehension() {
        let expr = TlaExpr::SetFilter {
            var: "x".to_string(),
            set: Box::new(TlaExpr::ident("S")),
            filter: Box::new(TlaExpr::binop(
                TlaBinOp::Gt,
                TlaExpr::ident("x"),
                TlaExpr::number(0),
            )),
        };

        let printer = TlaPrinter::new();
        let output = printer.print_expr(&expr, 0);

        assert!(output.contains("{x\\in S : x > 0}"));
    }

    #[test]
    fn test_print_recursive_operator() {
        let op = TlaOperator::new(
            "Factorial",
            TlaExpr::IfThenElse {
                cond: Box::new(TlaExpr::binop(
                    TlaBinOp::Eq,
                    TlaExpr::ident("n"),
                    TlaExpr::number(0),
                )),
                then_expr: Box::new(TlaExpr::number(1)),
                else_expr: Box::new(TlaExpr::binop(
                    TlaBinOp::Times,
                    TlaExpr::ident("n"),
                    TlaExpr::OpApply {
                        op: Box::new(TlaExpr::ident("Factorial")),
                        args: vec![TlaExpr::binop(
                            TlaBinOp::Minus,
                            TlaExpr::ident("n"),
                            TlaExpr::number(1),
                        )],
                    },
                )),
            },
        )
        .with_params(vec![TlaParam::new("n")])
        .recursive();

        let printer = TlaPrinter::new();
        let output = printer.print_operator(&op);

        assert!(output.contains("RECURSIVE Factorial(_)"));
        assert!(output.contains("Factorial(n) =="));
    }

    #[test]
    fn test_print_primed() {
        let expr = TlaExpr::prime(TlaExpr::ident("x"));

        let printer = TlaPrinter::new();
        let output = printer.print_expr(&expr, 0);

        assert!(output.contains("x'"));
    }
}
