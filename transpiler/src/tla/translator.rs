//! TLA+ to Verus expression translator.
//!
//! This module translates TLA+ AST expressions to Verus code.

use crate::tla::ast::{TlaBinOp, TlaExceptPath, TlaExpr, TlaNumber, TlaQuantBound, TlaUnaryOp};

/// Configuration for the expression translator
#[derive(Debug, Clone)]
pub struct TranslatorConfig {
    /// Whether to generate spec (specification) or exec (executable) code
    pub is_spec: bool,
    /// Map TLA+ identifiers to Verus identifiers
    pub rename_map: std::collections::HashMap<String, String>,
}

impl Default for TranslatorConfig {
    fn default() -> Self {
        Self {
            is_spec: true,
            rename_map: std::collections::HashMap::new(),
        }
    }
}

impl TranslatorConfig {
    /// Create a new spec-mode configuration
    pub fn spec() -> Self {
        Self {
            is_spec: true,
            ..Default::default()
        }
    }

    /// Create a new exec-mode configuration
    pub fn exec() -> Self {
        Self {
            is_spec: false,
            ..Default::default()
        }
    }

    /// Add a rename mapping
    pub fn with_rename(mut self, from: impl Into<String>, to: impl Into<String>) -> Self {
        self.rename_map.insert(from.into(), to.into());
        self
    }
}

/// Translates TLA+ expressions to Verus code
pub struct ExprTranslator<'a> {
    config: &'a TranslatorConfig,
}

impl<'a> ExprTranslator<'a> {
    /// Create a new expression translator with the given configuration
    pub fn new(config: &'a TranslatorConfig) -> Self {
        Self { config }
    }

    /// Translate a TLA+ expression to a Verus code string
    pub fn translate(&self, expr: &TlaExpr) -> String {
        match expr {
            // Identifiers and literals
            TlaExpr::Ident(name) => self.translate_ident(name),
            TlaExpr::Prime(inner) => self.translate_prime(inner),
            TlaExpr::Number(num) => self.translate_number(num),
            TlaExpr::String(s) => self.translate_string(s),
            TlaExpr::Bool(b) => self.translate_bool(*b),

            // Operators
            TlaExpr::BinOp { op, left, right } => self.translate_binop(*op, left, right),
            TlaExpr::UnaryOp { op, operand } => self.translate_unary(*op, operand),

            // Function/operator application
            TlaExpr::OpApply { op, args } => self.translate_op_apply(op, args),
            TlaExpr::FnApply { func, arg } => self.translate_fn_apply(func, arg),

            // Sets
            TlaExpr::SetEnum(elements) => self.translate_set_enum(elements),
            TlaExpr::SetFilter { var, set, filter } => self.translate_set_filter(var, set, filter),
            TlaExpr::SetMap { expr, var, set } => self.translate_set_map(expr, var, set),

            // Functions
            TlaExpr::FnConstruct { var, domain, body } => {
                self.translate_fn_construct(var, domain, body)
            }
            TlaExpr::FnExcept { func, updates } => self.translate_fn_except(func, updates),

            // Records
            TlaExpr::Record(fields) => self.translate_record(fields),
            TlaExpr::RecordAccess { record, field } => self.translate_record_access(record, field),

            // Tuples
            TlaExpr::Tuple(elements) => self.translate_tuple(elements),

            // Quantifiers
            TlaExpr::Forall { vars, body } => self.translate_forall(vars, body),
            TlaExpr::Exists { vars, body } => self.translate_exists(vars, body),
            TlaExpr::Choose { var, set, body } => self.translate_choose(var, set, body),

            // Control flow
            TlaExpr::IfThenElse {
                cond,
                then_expr,
                else_expr,
            } => self.translate_if_then_else(cond, then_expr, else_expr),
            TlaExpr::Case { arms, other } => self.translate_case(arms, other),
            TlaExpr::LetIn { defs, body } => self.translate_let_in(defs, body),

            // Action operators
            TlaExpr::Unchanged(vars) => self.translate_unchanged(vars),
            TlaExpr::Enabled(action) => self.translate_enabled(action),

            // Temporal operators
            TlaExpr::Always(inner) => self.translate_always(inner),
            TlaExpr::Eventually(inner) => self.translate_eventually(inner),
            TlaExpr::LeadsTo { left, right } => self.translate_leads_to(left, right),
            TlaExpr::WeakFairness { vars, action } => self.translate_weak_fairness(vars, action),
            TlaExpr::StrongFairness { vars, action } => self.translate_strong_fairness(vars, action),
        }
    }

    // =========================================================================
    // Identifier and literal translation
    // =========================================================================

    fn translate_ident(&self, name: &str) -> String {
        // Check for rename mapping
        if let Some(renamed) = self.config.rename_map.get(name) {
            return renamed.clone();
        }

        // Standard TLA+ identifiers
        match name {
            "Nat" => "nat".to_string(),
            "Int" => "int".to_string(),
            "BOOLEAN" => "bool".to_string(),
            "TRUE" => "true".to_string(),
            "FALSE" => "false".to_string(),
            _ => name.to_string(),
        }
    }

    fn translate_prime(&self, inner: &TlaExpr) -> String {
        // Primed variables are output parameters, translated as `name_`
        match inner {
            TlaExpr::Ident(name) => format!("{}_", name),
            _ => {
                // Nested primed expression (unusual)
                format!("({})_", self.translate(inner))
            }
        }
    }

    fn translate_number(&self, num: &TlaNumber) -> String {
        match num {
            TlaNumber::Decimal(s) => s.clone(),
            TlaNumber::Binary(s) => format!("0b{}", s.strip_prefix("\\b").unwrap_or(s)),
            TlaNumber::Octal(s) => format!("0o{}", s.strip_prefix("\\o").unwrap_or(s)),
            TlaNumber::Hex(s) => format!("0x{}", s.strip_prefix("\\h").unwrap_or(s)),
        }
    }

    fn translate_string(&self, s: &str) -> String {
        format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
    }

    fn translate_bool(&self, b: bool) -> String {
        if b {
            "true".to_string()
        } else {
            "false".to_string()
        }
    }

    // =========================================================================
    // Binary operator translation (T5.1: Set operations)
    // =========================================================================

    fn translate_binop(&self, op: TlaBinOp, left: &TlaExpr, right: &TlaExpr) -> String {
        let left_str = self.translate(left);
        let right_str = self.translate(right);

        match op {
            // Logical operators
            TlaBinOp::And => format!("({} && {})", left_str, right_str),
            TlaBinOp::Or => format!("({} || {})", left_str, right_str),
            TlaBinOp::Implies => format!("({} ==> {})", left_str, right_str),
            TlaBinOp::Iff => format!("({} <==> {})", left_str, right_str),

            // Set operations (T5.1)
            TlaBinOp::In => format!("{}.contains({})", right_str, left_str),
            TlaBinOp::NotIn => format!("!{}.contains({})", right_str, left_str),
            TlaBinOp::Subseteq => format!("{}.subset_of({})", left_str, right_str),
            TlaBinOp::Cup => format!("{}.union({})", left_str, right_str),
            TlaBinOp::Cap => format!("{}.intersect({})", left_str, right_str),
            TlaBinOp::Setminus => format!("{}.difference({})", left_str, right_str),
            TlaBinOp::CrossProd => format!("{}.cartesian_product({})", left_str, right_str),

            // Arithmetic
            TlaBinOp::Plus => format!("({} + {})", left_str, right_str),
            TlaBinOp::Minus => format!("({} - {})", left_str, right_str),
            TlaBinOp::Times => format!("({} * {})", left_str, right_str),
            TlaBinOp::Div => format!("({} / {})", left_str, right_str),
            TlaBinOp::Mod => format!("({} % {})", left_str, right_str),
            TlaBinOp::Slash => format!("({} / {})", left_str, right_str),
            TlaBinOp::Caret => {
                // Exponentiation - use pow function
                format!("{}.pow({})", left_str, right_str)
            }
            TlaBinOp::DotDot => {
                // Range: a..b in TLA+ (inclusive) → Set::new(|x| a <= x <= b)
                format!("Set::new(|x: int| {} <= x && x <= {})", left_str, right_str)
            }

            // Comparison
            TlaBinOp::Eq => format!("({} == {})", left_str, right_str),
            TlaBinOp::Neq => format!("({} != {})", left_str, right_str),
            TlaBinOp::Lt => format!("({} < {})", left_str, right_str),
            TlaBinOp::Gt => format!("({} > {})", left_str, right_str),
            TlaBinOp::Leq => format!("({} <= {})", left_str, right_str),
            TlaBinOp::Geq => format!("({} >= {})", left_str, right_str),

            // Action composition
            TlaBinOp::Compose => {
                // Action composition is typically handled at a higher level
                format!("/* compose */ ({} && {})", left_str, right_str)
            }
        }
    }

    // =========================================================================
    // Unary operator translation
    // =========================================================================

    fn translate_unary(&self, op: TlaUnaryOp, operand: &TlaExpr) -> String {
        let operand_str = self.translate(operand);

        match op {
            TlaUnaryOp::Not => format!("!({})", operand_str),
            TlaUnaryOp::Neg => format!("-({})", operand_str),
            TlaUnaryOp::Subset => {
                // SUBSET S = power set
                format!("{}.powerset()", operand_str)
            }
            TlaUnaryOp::Union => {
                // UNION S = flatten/union of sets of sets
                format!("{}.flatten()", operand_str)
            }
            TlaUnaryOp::Domain => {
                // DOMAIN f = domain of function/map
                format!("{}.dom()", operand_str)
            }
        }
    }

    // =========================================================================
    // Set operations (T5.1)
    // =========================================================================

    fn translate_set_enum(&self, elements: &[TlaExpr]) -> String {
        if elements.is_empty() {
            return "Set::empty()".to_string();
        }

        let elem_strs: Vec<_> = elements.iter().map(|e| self.translate(e)).collect();
        format!("set![{}]", elem_strs.join(", "))
    }

    fn translate_set_filter(&self, var: &str, set: &TlaExpr, filter: &TlaExpr) -> String {
        // {x \in S : P(x)} → S.filter(|x| P(x))
        let set_str = self.translate(set);
        let filter_str = self.translate(filter);
        format!("{}.filter(|{}| {})", set_str, var, filter_str)
    }

    fn translate_set_map(&self, expr: &TlaExpr, var: &str, set: &TlaExpr) -> String {
        // {f(x) : x \in S} → S.map(|x| f(x))
        let set_str = self.translate(set);
        let expr_str = self.translate(expr);
        format!("{}.map(|{}| {})", set_str, var, expr_str)
    }

    // =========================================================================
    // Function/map operations (T5.2)
    // =========================================================================

    fn translate_fn_construct(
        &self,
        var: &str,
        domain: &TlaExpr,
        body: &TlaExpr,
    ) -> String {
        // [x \in S |-> f(x)] → Map::new(|x| f(x))
        let domain_str = self.translate(domain);
        let body_str = self.translate(body);
        format!("Map::new({}, |{}| {})", domain_str, var, body_str)
    }

    fn translate_fn_apply(&self, func: &TlaExpr, arg: &TlaExpr) -> String {
        // f[x] → f[x] or f.index(x)
        let func_str = self.translate(func);
        let arg_str = self.translate(arg);
        format!("{}[{}]", func_str, arg_str)
    }

    fn translate_fn_except(
        &self,
        func: &TlaExpr,
        updates: &[crate::tla::ast::TlaExceptUpdate],
    ) -> String {
        // [f EXCEPT ![i] = v] → f.insert(i, v)
        let mut result = self.translate(func);

        for update in updates {
            let value_str = self.translate(&update.value);

            // Build the path
            for path_elem in &update.path {
                match path_elem {
                    TlaExceptPath::Index(idx) => {
                        let idx_str = self.translate(idx);
                        result = format!("{}.insert({}, {})", result, idx_str, value_str);
                    }
                    TlaExceptPath::Field(field) => {
                        // Record field update
                        result = format!(
                            "{{ let mut tmp = {}; tmp.{} = {}; tmp }}",
                            result, field, value_str
                        );
                    }
                }
            }
        }

        result
    }

    // =========================================================================
    // Record and tuple operations
    // =========================================================================

    fn translate_record(&self, fields: &[(String, TlaExpr)]) -> String {
        let field_strs: Vec<_> = fields
            .iter()
            .map(|(name, value)| format!("{}: {}", name, self.translate(value)))
            .collect();
        format!("{{ {} }}", field_strs.join(", "))
    }

    fn translate_record_access(&self, record: &TlaExpr, field: &str) -> String {
        let record_str = self.translate(record);
        format!("{}.{}", record_str, field)
    }

    fn translate_tuple(&self, elements: &[TlaExpr]) -> String {
        // <<a, b, c>> → seq![a, b, c] (for sequences)
        // For tuples as actual tuples, use (a, b, c)
        let elem_strs: Vec<_> = elements.iter().map(|e| self.translate(e)).collect();
        format!("seq![{}]", elem_strs.join(", "))
    }

    // =========================================================================
    // Quantifier translation (T5.4)
    // =========================================================================

    fn translate_forall(&self, vars: &[TlaQuantBound], body: &TlaExpr) -> String {
        // \A x \in S : P(x) → forall |x| S.contains(x) ==> P(x)
        let body_str = self.translate(body);

        if vars.len() == 1 {
            let var = &vars[0];
            if let Some(set) = &var.set {
                let set_str = self.translate(set);
                format!(
                    "forall |{}| {}.contains({}) ==> {}",
                    var.var, set_str, var.var, body_str
                )
            } else {
                format!("forall |{}| {}", var.var, body_str)
            }
        } else {
            // Multiple bound variables
            let var_names: Vec<_> = vars.iter().map(|v| v.var.clone()).collect();
            let bounds: Vec<_> = vars
                .iter()
                .filter_map(|v| {
                    v.set.as_ref().map(|s| {
                        let set_str = self.translate(s);
                        format!("{}.contains({})", set_str, v.var)
                    })
                })
                .collect();

            if bounds.is_empty() {
                format!("forall |{}| {}", var_names.join(", "), body_str)
            } else {
                format!(
                    "forall |{}| ({}) ==> {}",
                    var_names.join(", "),
                    bounds.join(" && "),
                    body_str
                )
            }
        }
    }

    fn translate_exists(&self, vars: &[TlaQuantBound], body: &TlaExpr) -> String {
        // \E x \in S : P(x) → exists |x| S.contains(x) && P(x)
        let body_str = self.translate(body);

        if vars.len() == 1 {
            let var = &vars[0];
            if let Some(set) = &var.set {
                let set_str = self.translate(set);
                format!(
                    "exists |{}| {}.contains({}) && {}",
                    var.var, set_str, var.var, body_str
                )
            } else {
                format!("exists |{}| {}", var.var, body_str)
            }
        } else {
            // Multiple bound variables
            let var_names: Vec<_> = vars.iter().map(|v| v.var.clone()).collect();
            let bounds: Vec<_> = vars
                .iter()
                .filter_map(|v| {
                    v.set.as_ref().map(|s| {
                        let set_str = self.translate(s);
                        format!("{}.contains({})", set_str, v.var)
                    })
                })
                .collect();

            if bounds.is_empty() {
                format!("exists |{}| {}", var_names.join(", "), body_str)
            } else {
                format!(
                    "exists |{}| ({}) && {}",
                    var_names.join(", "),
                    bounds.join(" && "),
                    body_str
                )
            }
        }
    }

    fn translate_choose(&self, var: &str, set: &Option<Box<TlaExpr>>, body: &TlaExpr) -> String {
        // CHOOSE x \in S : P(x) → choose |x| S.contains(x) && P(x)
        let body_str = self.translate(body);

        if let Some(set_expr) = set {
            let set_str = self.translate(set_expr);
            format!(
                "choose |{}| {}.contains({}) && {}",
                var, set_str, var, body_str
            )
        } else {
            format!("choose |{}| {}", var, body_str)
        }
    }

    // =========================================================================
    // Function/operator application
    // =========================================================================

    fn translate_op_apply(&self, op: &TlaExpr, args: &[TlaExpr]) -> String {
        let op_str = self.translate(op);
        let arg_strs: Vec<_> = args.iter().map(|a| self.translate(a)).collect();

        // Check for standard library functions
        match op_str.as_str() {
            // Sequence operations (T5.3)
            "Append" if args.len() == 2 => {
                format!("{}.push({})", arg_strs[0], arg_strs[1])
            }
            "Head" if args.len() == 1 => {
                format!("{}[0]", arg_strs[0])
            }
            "Tail" if args.len() == 1 => {
                format!("{}.drop_first()", arg_strs[0])
            }
            "Len" if args.len() == 1 => {
                format!("{}.len()", arg_strs[0])
            }
            "SubSeq" if args.len() == 3 => {
                // TLA+ is 1-indexed, Verus is 0-indexed
                format!(
                    "{}.subrange({} - 1, {})",
                    arg_strs[0], arg_strs[1], arg_strs[2]
                )
            }

            // Set operations
            "Cardinality" if args.len() == 1 => {
                format!("{}.len()", arg_strs[0])
            }
            "IsFiniteSet" if args.len() == 1 => {
                format!("{}.finite()", arg_strs[0])
            }

            // Default: regular function call
            _ => format!("{}({})", op_str, arg_strs.join(", ")),
        }
    }

    // =========================================================================
    // Control flow
    // =========================================================================

    fn translate_if_then_else(
        &self,
        cond: &TlaExpr,
        then_expr: &TlaExpr,
        else_expr: &TlaExpr,
    ) -> String {
        let cond_str = self.translate(cond);
        let then_str = self.translate(then_expr);
        let else_str = self.translate(else_expr);

        format!("if {} {{ {} }} else {{ {} }}", cond_str, then_str, else_str)
    }

    fn translate_case(&self, arms: &[(TlaExpr, TlaExpr)], other: &Option<Box<TlaExpr>>) -> String {
        let mut result = String::new();

        for (i, (cond, expr)) in arms.iter().enumerate() {
            let cond_str = self.translate(cond);
            let expr_str = self.translate(expr);

            if i == 0 {
                result.push_str(&format!("if {} {{ {} }}", cond_str, expr_str));
            } else {
                result.push_str(&format!(" else if {} {{ {} }}", cond_str, expr_str));
            }
        }

        if let Some(other_expr) = other {
            let other_str = self.translate(other_expr);
            result.push_str(&format!(" else {{ {} }}", other_str));
        } else {
            // TLA+ CASE without OTHER is partial, which is unusual
            result.push_str(" else { /* no OTHER case */ panic!() }");
        }

        result
    }

    fn translate_let_in(&self, defs: &[crate::tla::ast::TlaOperator], body: &TlaExpr) -> String {
        let mut result = String::from("{\n");

        for def in defs {
            let body_str = self.translate(&def.body);
            if def.params.is_empty() {
                result.push_str(&format!("    let {} = {};\n", def.name, body_str));
            } else {
                let param_names: Vec<_> = def.params.iter().map(|p| p.name.clone()).collect();
                result.push_str(&format!(
                    "    let {} = |{}| {};\n",
                    def.name,
                    param_names.join(", "),
                    body_str
                ));
            }
        }

        let body_str = self.translate(body);
        result.push_str(&format!("    {}\n}}", body_str));

        result
    }

    // =========================================================================
    // Action operators (T5.5)
    // =========================================================================

    fn translate_unchanged(&self, vars: &[TlaExpr]) -> String {
        // UNCHANGED <<x, y>> → x_ == x && y_ == y
        let conditions: Vec<_> = vars
            .iter()
            .map(|v| {
                let v_str = self.translate(v);
                format!("{}_ == {}", v_str, v_str)
            })
            .collect();

        if conditions.is_empty() {
            "true".to_string()
        } else {
            format!("({})", conditions.join(" && "))
        }
    }

    fn translate_enabled(&self, action: &TlaExpr) -> String {
        // ENABLED A → check if action A is possible
        let action_str = self.translate(action);
        format!("/* ENABLED */ exists |_| {}", action_str)
    }

    // =========================================================================
    // Temporal operators
    // =========================================================================

    fn translate_always(&self, inner: &TlaExpr) -> String {
        let inner_str = self.translate(inner);
        format!("/* [] */ always({})", inner_str)
    }

    fn translate_eventually(&self, inner: &TlaExpr) -> String {
        let inner_str = self.translate(inner);
        format!("/* <> */ eventually({})", inner_str)
    }

    fn translate_leads_to(&self, left: &TlaExpr, right: &TlaExpr) -> String {
        let left_str = self.translate(left);
        let right_str = self.translate(right);
        format!("/* ~> */ leads_to({}, {})", left_str, right_str)
    }

    fn translate_weak_fairness(&self, vars: &TlaExpr, action: &TlaExpr) -> String {
        let vars_str = self.translate(vars);
        let action_str = self.translate(action);
        format!("/* WF */ weak_fairness({}, {})", vars_str, action_str)
    }

    fn translate_strong_fairness(&self, vars: &TlaExpr, action: &TlaExpr) -> String {
        let vars_str = self.translate(vars);
        let action_str = self.translate(action);
        format!("/* SF */ strong_fairness({}, {})", vars_str, action_str)
    }
}

/// Convenience function to translate an expression with default config
pub fn translate_expr(expr: &TlaExpr) -> String {
    let config = TranslatorConfig::default();
    let translator = ExprTranslator::new(&config);
    translator.translate(expr)
}

/// Convenience function to translate an expression with a custom config
pub fn translate_expr_with_config(expr: &TlaExpr, config: &TranslatorConfig) -> String {
    let translator = ExprTranslator::new(config);
    translator.translate(expr)
}

// =============================================================================
// Module Translation (T6)
// =============================================================================

use crate::tla::ast::{TlaModule, TlaOperator};
use crate::tla::types::{TlaType, TypeEnv, TypeInference};

/// Configuration for module translation
#[derive(Debug, Clone)]
pub struct ModuleConfig {
    /// Prefix for spec types/functions (e.g., "L" for LState, LInit)
    pub spec_prefix: String,
    /// Prefix for exec types/functions (e.g., "C" for CState, CInit)
    pub exec_prefix: String,
    /// State struct name (without prefix)
    pub state_name: String,
    /// Whether to generate View trait implementation
    pub generate_view: bool,
    /// Whether to add type annotations from TypeEnv
    pub use_inferred_types: bool,
}

impl Default for ModuleConfig {
    fn default() -> Self {
        Self {
            spec_prefix: "L".to_string(),
            exec_prefix: "C".to_string(),
            state_name: "State".to_string(),
            generate_view: true,
            use_inferred_types: true,
        }
    }
}

impl ModuleConfig {
    /// Get the spec state struct name
    pub fn spec_state_name(&self) -> String {
        format!("{}{}", self.spec_prefix, self.state_name)
    }

    /// Get the exec state struct name
    pub fn exec_state_name(&self) -> String {
        format!("{}{}", self.exec_prefix, self.state_name)
    }

    /// Get the spec function name for an operator
    pub fn spec_fn_name(&self, op_name: &str) -> String {
        format!("{}{}", self.spec_prefix, op_name)
    }
}

/// Translates a TLA+ module to Verus code
pub struct ModuleTranslator {
    /// Module configuration
    pub config: ModuleConfig,
    /// Expression translator configuration
    pub expr_config: TranslatorConfig,
    /// Inferred types (optional)
    pub type_env: Option<TypeEnv>,
}

impl Default for ModuleTranslator {
    fn default() -> Self {
        Self::new()
    }
}

impl ModuleTranslator {
    /// Create a new module translator with default configuration
    pub fn new() -> Self {
        Self {
            config: ModuleConfig::default(),
            expr_config: TranslatorConfig::spec(),
            type_env: None,
        }
    }

    /// Create a module translator with a specific configuration
    pub fn with_config(config: ModuleConfig) -> Self {
        Self {
            config,
            expr_config: TranslatorConfig::spec(),
            type_env: None,
        }
    }

    /// Set inferred types
    pub fn with_types(mut self, type_env: TypeEnv) -> Self {
        self.type_env = Some(type_env);
        self
    }

    /// Translate a TLA+ module to Verus code
    pub fn translate(&self, module: &TlaModule) -> String {
        let mut output = String::new();

        // Module header
        output.push_str(&self.generate_header(module));
        output.push('\n');

        // Imports based on EXTENDS
        output.push_str(&self.generate_imports(module));
        output.push('\n');

        // State struct
        output.push_str(&self.generate_state_struct(module));
        output.push('\n');

        // Spec functions for operators
        output.push_str(&self.generate_spec_functions(module));

        output
    }

    /// Generate module header comment
    fn generate_header(&self, module: &TlaModule) -> String {
        format!(
            "//! Generated from TLA+ module: {}\n//!\n//! This file was auto-generated by verus-transpiler.\n",
            module.name
        )
    }

    /// Generate import statements based on EXTENDS
    fn generate_imports(&self, module: &TlaModule) -> String {
        let mut imports = String::new();

        // Always include verus prelude
        imports.push_str("use vstd::prelude::*;\n");

        // Map TLA+ extends to Verus imports
        for ext in &module.extends {
            match ext.as_str() {
                "Naturals" | "Integers" => {
                    // These are built into Verus
                }
                "Sequences" => {
                    imports.push_str("use vstd::seq::*;\n");
                }
                "FiniteSets" => {
                    imports.push_str("use vstd::set::*;\n");
                }
                "TLC" => {
                    // TLC module has no direct Verus equivalent
                    imports.push_str("// TLC module (no Verus equivalent)\n");
                }
                _ => {
                    // Custom module - add as a comment
                    imports.push_str(&format!("// EXTENDS {} (custom module)\n", ext));
                }
            }
        }

        imports
    }

    /// Generate the state struct from VARIABLE declarations
    fn generate_state_struct(&self, module: &TlaModule) -> String {
        let mut output = String::new();
        let state_name = self.config.spec_state_name();

        // Open verus block
        output.push_str("verus! {\n\n");

        // State struct
        output.push_str(&format!("/// State for {} module\n", module.name));
        output.push_str("#[derive(Clone)]\n");
        output.push_str(&format!("pub struct {} {{\n", state_name));

        for var in &module.variables {
            let var_type = self.get_variable_type(var);
            output.push_str(&format!("    pub {}: {},\n", var, var_type));
        }

        output.push_str("}\n\n");

        // Constants as associated constants or generic parameters
        if !module.constants.is_empty() {
            output.push_str("/// Constants for the module\n");
            output.push_str(&format!("pub struct {}Constants {{\n", self.config.spec_prefix));
            for constant in &module.constants {
                let const_type = self.get_constant_type(&constant.name);
                output.push_str(&format!("    pub {}: {},\n", constant.name, const_type));
            }
            output.push_str("}\n\n");
        }

        output
    }

    /// Generate spec functions for operators
    fn generate_spec_functions(&self, module: &TlaModule) -> String {
        let mut output = String::new();
        let state_name = self.config.spec_state_name();
        let expr_translator = ExprTranslator::new(&self.expr_config);

        for op in &module.operators {
            output.push_str(&self.generate_spec_function(op, &state_name, &expr_translator));
            output.push('\n');
        }

        // Close verus block
        output.push_str("} // verus!\n");

        output
    }

    /// Generate a single spec function
    fn generate_spec_function(
        &self,
        op: &TlaOperator,
        state_name: &str,
        expr_translator: &ExprTranslator,
    ) -> String {
        let mut output = String::new();
        let fn_name = self.config.spec_fn_name(&op.name);

        // Detect if this is an action (uses primed variables)
        let is_action = self.operator_uses_primes(&op.body);

        // Build parameter list
        let mut params = Vec::new();

        // Add state parameter if operator references variables
        let refs_vars = self.operator_refs_variables(&op.body, &[]);
        if refs_vars {
            params.push(format!("s: {}", state_name));
            if is_action {
                params.push(format!("s_: {}", state_name));
            }
        }

        // Add operator parameters
        for param in &op.params {
            let param_type = self.get_param_type(&param.name);
            params.push(format!("{}: {}", param.name, param_type));
        }

        // Determine return type
        let return_type = self.get_operator_return_type(&op.name);

        // Generate function signature
        output.push_str(&format!("/// {} operator\n", op.name));
        if op.is_local {
            output.push_str("#[verifier(inline)]\n");
        }
        output.push_str(&format!(
            "pub open spec fn {}({}) -> {} {{\n",
            fn_name,
            params.join(", "),
            return_type
        ));

        // Generate body
        let body = expr_translator.translate(&op.body);
        output.push_str(&format!("    {}\n", body));

        output.push_str("}\n");

        output
    }

    /// Check if an expression uses primed variables
    fn operator_uses_primes(&self, expr: &TlaExpr) -> bool {
        match expr {
            TlaExpr::Prime(_) => true,
            TlaExpr::BinOp { left, right, .. } => {
                self.operator_uses_primes(left) || self.operator_uses_primes(right)
            }
            TlaExpr::UnaryOp { operand, .. } => self.operator_uses_primes(operand),
            TlaExpr::OpApply { op, args } => {
                self.operator_uses_primes(op) || args.iter().any(|a| self.operator_uses_primes(a))
            }
            TlaExpr::FnApply { func, arg } => {
                self.operator_uses_primes(func) || self.operator_uses_primes(arg)
            }
            TlaExpr::SetEnum(elements) => elements.iter().any(|e| self.operator_uses_primes(e)),
            TlaExpr::SetFilter { set, filter, .. } => {
                self.operator_uses_primes(set) || self.operator_uses_primes(filter)
            }
            TlaExpr::SetMap { expr, set, .. } => {
                self.operator_uses_primes(expr) || self.operator_uses_primes(set)
            }
            TlaExpr::FnConstruct { domain, body, .. } => {
                self.operator_uses_primes(domain) || self.operator_uses_primes(body)
            }
            TlaExpr::FnExcept { func, updates } => {
                self.operator_uses_primes(func)
                    || updates
                        .iter()
                        .any(|u| self.operator_uses_primes(&u.value))
            }
            TlaExpr::Record(fields) => fields.iter().any(|(_, e)| self.operator_uses_primes(e)),
            TlaExpr::RecordAccess { record, .. } => self.operator_uses_primes(record),
            TlaExpr::Tuple(elements) => elements.iter().any(|e| self.operator_uses_primes(e)),
            TlaExpr::Forall { body, .. } | TlaExpr::Exists { body, .. } => {
                self.operator_uses_primes(body)
            }
            TlaExpr::Choose { body, set, .. } => {
                self.operator_uses_primes(body)
                    || set.as_ref().is_some_and(|s| self.operator_uses_primes(s))
            }
            TlaExpr::IfThenElse {
                cond,
                then_expr,
                else_expr,
            } => {
                self.operator_uses_primes(cond)
                    || self.operator_uses_primes(then_expr)
                    || self.operator_uses_primes(else_expr)
            }
            TlaExpr::Case { arms, other } => {
                arms.iter()
                    .any(|(c, e)| self.operator_uses_primes(c) || self.operator_uses_primes(e))
                    || other.as_ref().is_some_and(|o| self.operator_uses_primes(o))
            }
            TlaExpr::LetIn { defs, body } => {
                defs.iter().any(|d| self.operator_uses_primes(&d.body))
                    || self.operator_uses_primes(body)
            }
            TlaExpr::Unchanged(_) => true, // UNCHANGED implies action
            TlaExpr::Enabled(inner) => self.operator_uses_primes(inner),
            TlaExpr::Always(inner) | TlaExpr::Eventually(inner) => self.operator_uses_primes(inner),
            TlaExpr::LeadsTo { left, right } => {
                self.operator_uses_primes(left) || self.operator_uses_primes(right)
            }
            TlaExpr::WeakFairness { action, .. } | TlaExpr::StrongFairness { action, .. } => {
                self.operator_uses_primes(action)
            }
            _ => false,
        }
    }

    /// Check if an expression references module variables (simplified check)
    fn operator_refs_variables(&self, _expr: &TlaExpr, _local_vars: &[String]) -> bool {
        // For now, assume operators that are not pure constant expressions reference state
        // A more sophisticated check would track variable references
        true
    }

    /// Get the Verus type for a variable
    fn get_variable_type(&self, var_name: &str) -> String {
        if let Some(env) = &self.type_env {
            if let Some(ty) = env.variables.get(var_name) {
                return ty.to_verus_type();
            }
        }
        // Default to spec type comment
        format!("/* {} type */ int", var_name)
    }

    /// Get the Verus type for a constant
    fn get_constant_type(&self, const_name: &str) -> String {
        if let Some(env) = &self.type_env {
            if let Some(ty) = env.constants.get(const_name) {
                return ty.to_verus_type();
            }
        }
        // Default to spec type comment
        format!("/* {} type */ int", const_name)
    }

    /// Get the Verus type for a parameter
    fn get_param_type(&self, _param_name: &str) -> String {
        // Parameters need type inference context
        "int".to_string()
    }

    /// Get the return type for an operator
    fn get_operator_return_type(&self, op_name: &str) -> String {
        if let Some(env) = &self.type_env {
            if let Some(ty) = env.operators.get(op_name) {
                // Extract return type from function type
                if let TlaType::Function { range, .. } = ty {
                    return range.to_verus_type();
                }
                return ty.to_verus_type();
            }
        }
        // Default: most operators return bool
        "bool".to_string()
    }
}

/// Translate a TLA+ module to Verus code
pub fn translate_module(module: &TlaModule) -> String {
    let translator = ModuleTranslator::new();
    translator.translate(module)
}

/// Translate a TLA+ module with type inference
pub fn translate_module_with_types(module: &TlaModule) -> String {
    let mut inference = TypeInference::new();
    let type_env = inference.infer_types(module);

    let translator = ModuleTranslator::new().with_types(type_env);
    translator.translate(module)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tla::ast::{TlaExpr, TlaBinOp, TlaQuantBound};
    use crate::tla::parser::parse_module;

    #[test]
    fn test_translate_identifiers() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        assert_eq!(translator.translate(&TlaExpr::ident("x")), "x");
        assert_eq!(translator.translate(&TlaExpr::ident("Nat")), "nat");
        assert_eq!(translator.translate(&TlaExpr::ident("TRUE")), "true");
    }

    #[test]
    fn test_translate_literals() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        assert_eq!(translator.translate(&TlaExpr::number(42)), "42");
        assert_eq!(translator.translate(&TlaExpr::bool(true)), "true");
        assert_eq!(translator.translate(&TlaExpr::bool(false)), "false");
        assert_eq!(translator.translate(&TlaExpr::string("hello")), "\"hello\"");
    }

    #[test]
    fn test_translate_set_membership() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        // x \in S → S.contains(x)
        let expr = TlaExpr::binop(TlaBinOp::In, TlaExpr::ident("x"), TlaExpr::ident("S"));
        assert_eq!(translator.translate(&expr), "S.contains(x)");

        // x \notin S → !S.contains(x)
        let expr = TlaExpr::binop(TlaBinOp::NotIn, TlaExpr::ident("x"), TlaExpr::ident("S"));
        assert_eq!(translator.translate(&expr), "!S.contains(x)");
    }

    #[test]
    fn test_translate_set_operations() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        // S \cup T → S.union(T)
        let expr = TlaExpr::binop(TlaBinOp::Cup, TlaExpr::ident("S"), TlaExpr::ident("T"));
        assert_eq!(translator.translate(&expr), "S.union(T)");

        // S \cap T → S.intersect(T)
        let expr = TlaExpr::binop(TlaBinOp::Cap, TlaExpr::ident("S"), TlaExpr::ident("T"));
        assert_eq!(translator.translate(&expr), "S.intersect(T)");

        // S \subseteq T → S.subset_of(T)
        let expr = TlaExpr::binop(TlaBinOp::Subseteq, TlaExpr::ident("S"), TlaExpr::ident("T"));
        assert_eq!(translator.translate(&expr), "S.subset_of(T)");

        // S \ T → S.difference(T)
        let expr = TlaExpr::binop(TlaBinOp::Setminus, TlaExpr::ident("S"), TlaExpr::ident("T"));
        assert_eq!(translator.translate(&expr), "S.difference(T)");
    }

    #[test]
    fn test_translate_set_enum() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        // {} → Set::empty()
        let expr = TlaExpr::SetEnum(vec![]);
        assert_eq!(translator.translate(&expr), "Set::empty()");

        // {1, 2, 3} → set![1, 2, 3]
        let expr = TlaExpr::SetEnum(vec![
            TlaExpr::number(1),
            TlaExpr::number(2),
            TlaExpr::number(3),
        ]);
        assert_eq!(translator.translate(&expr), "set![1, 2, 3]");
    }

    #[test]
    fn test_translate_set_filter() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        // {x \in S : x > 0} → S.filter(|x| x > 0)
        let expr = TlaExpr::SetFilter {
            var: "x".to_string(),
            set: Box::new(TlaExpr::ident("S")),
            filter: Box::new(TlaExpr::binop(
                TlaBinOp::Gt,
                TlaExpr::ident("x"),
                TlaExpr::number(0),
            )),
        };
        assert_eq!(translator.translate(&expr), "S.filter(|x| (x > 0))");
    }

    #[test]
    fn test_translate_set_map() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        // {x * 2 : x \in S} → S.map(|x| x * 2)
        let expr = TlaExpr::SetMap {
            expr: Box::new(TlaExpr::binop(
                TlaBinOp::Times,
                TlaExpr::ident("x"),
                TlaExpr::number(2),
            )),
            var: "x".to_string(),
            set: Box::new(TlaExpr::ident("S")),
        };
        assert_eq!(translator.translate(&expr), "S.map(|x| (x * 2))");
    }

    #[test]
    fn test_translate_forall() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        // \A x \in S : P(x) → forall |x| S.contains(x) ==> P(x)
        let expr = TlaExpr::Forall {
            vars: vec![TlaQuantBound::new("x", TlaExpr::ident("S"))],
            body: Box::new(TlaExpr::OpApply {
                op: Box::new(TlaExpr::ident("P")),
                args: vec![TlaExpr::ident("x")],
            }),
        };
        let result = translator.translate(&expr);
        assert!(result.contains("forall |x|"));
        assert!(result.contains("S.contains(x)"));
        assert!(result.contains("==>"));
    }

    #[test]
    fn test_translate_exists() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        // \E x \in S : P(x) → exists |x| S.contains(x) && P(x)
        let expr = TlaExpr::Exists {
            vars: vec![TlaQuantBound::new("x", TlaExpr::ident("S"))],
            body: Box::new(TlaExpr::OpApply {
                op: Box::new(TlaExpr::ident("P")),
                args: vec![TlaExpr::ident("x")],
            }),
        };
        let result = translator.translate(&expr);
        assert!(result.contains("exists |x|"));
        assert!(result.contains("S.contains(x)"));
        assert!(result.contains("&&"));
    }

    #[test]
    fn test_translate_unchanged() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        // UNCHANGED <<x, y>> → (x_ == x && y_ == y)
        let expr = TlaExpr::Unchanged(vec![TlaExpr::ident("x"), TlaExpr::ident("y")]);
        let result = translator.translate(&expr);
        assert!(result.contains("x_ == x"));
        assert!(result.contains("y_ == y"));
    }

    #[test]
    fn test_translate_prime() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        // x' → x_
        let expr = TlaExpr::prime(TlaExpr::ident("x"));
        assert_eq!(translator.translate(&expr), "x_");
    }

    #[test]
    fn test_translate_if_then_else() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        let expr = TlaExpr::IfThenElse {
            cond: Box::new(TlaExpr::binop(
                TlaBinOp::Gt,
                TlaExpr::ident("x"),
                TlaExpr::number(0),
            )),
            then_expr: Box::new(TlaExpr::ident("x")),
            else_expr: Box::new(TlaExpr::number(0)),
        };
        let result = translator.translate(&expr);
        assert!(result.contains("if"));
        assert!(result.contains("else"));
    }

    #[test]
    fn test_translate_fn_construct() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        // [x \in S |-> x + 1] → Map::new(S, |x| x + 1)
        let expr = TlaExpr::FnConstruct {
            var: "x".to_string(),
            domain: Box::new(TlaExpr::ident("S")),
            body: Box::new(TlaExpr::binop(
                TlaBinOp::Plus,
                TlaExpr::ident("x"),
                TlaExpr::number(1),
            )),
        };
        let result = translator.translate(&expr);
        assert!(result.contains("Map::new"));
        assert!(result.contains("|x|"));
    }

    #[test]
    fn test_translate_fn_apply() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        // f[x] → f[x]
        let expr = TlaExpr::FnApply {
            func: Box::new(TlaExpr::ident("f")),
            arg: Box::new(TlaExpr::ident("x")),
        };
        assert_eq!(translator.translate(&expr), "f[x]");
    }

    #[test]
    fn test_translate_sequence_ops() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        // Append(s, x) → s.push(x)
        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("Append")),
            args: vec![TlaExpr::ident("s"), TlaExpr::ident("x")],
        };
        assert_eq!(translator.translate(&expr), "s.push(x)");

        // Head(s) → s[0]
        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("Head")),
            args: vec![TlaExpr::ident("s")],
        };
        assert_eq!(translator.translate(&expr), "s[0]");

        // Tail(s) → s.drop_first()
        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("Tail")),
            args: vec![TlaExpr::ident("s")],
        };
        assert_eq!(translator.translate(&expr), "s.drop_first()");

        // Len(s) → s.len()
        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("Len")),
            args: vec![TlaExpr::ident("s")],
        };
        assert_eq!(translator.translate(&expr), "s.len()");
    }

    #[test]
    fn test_translate_domain() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        // DOMAIN f → f.dom()
        let expr = TlaExpr::unary(TlaUnaryOp::Domain, TlaExpr::ident("f"));
        assert_eq!(translator.translate(&expr), "f.dom()");
    }

    #[test]
    fn test_translate_from_parsed() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE x
            Init == x \in Nat /\ x = 0
            ====
        ";
        let module = parse_module(source).unwrap();
        let init_op = module
            .operators
            .iter()
            .find(|op| op.name == "Init")
            .unwrap();

        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);
        let result = translator.translate(&init_op.body);

        assert!(result.contains("nat.contains(x)"));
        assert!(result.contains("(x == 0)"));
    }

    #[test]
    fn test_translate_with_rename() {
        let config = TranslatorConfig::default().with_rename("old_name", "new_name");
        let translator = ExprTranslator::new(&config);

        assert_eq!(translator.translate(&TlaExpr::ident("old_name")), "new_name");
        assert_eq!(translator.translate(&TlaExpr::ident("other")), "other");
    }

    // Module translation tests (T6)
    #[test]
    fn test_module_config_defaults() {
        let config = ModuleConfig::default();
        assert_eq!(config.spec_prefix, "L");
        assert_eq!(config.exec_prefix, "C");
        assert_eq!(config.state_name, "State");
        assert_eq!(config.spec_state_name(), "LState");
        assert_eq!(config.exec_state_name(), "CState");
        assert_eq!(config.spec_fn_name("Init"), "LInit");
    }

    #[test]
    fn test_translate_simple_module() {
        let source = r"
            ---- MODULE Counter ----
            VARIABLE count
            Init == count = 0
            ====
        ";
        let module = parse_module(source).unwrap();
        let translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        // Should generate module header
        assert!(result.contains("Generated from TLA+ module: Counter"));

        // Should generate verus block
        assert!(result.contains("verus!"));

        // Should generate state struct
        assert!(result.contains("pub struct LState"));
        assert!(result.contains("pub count:"));

        // Should generate Init function
        assert!(result.contains("pub open spec fn LInit"));
    }

    #[test]
    fn test_translate_module_with_extends() {
        let source = r"
            ---- MODULE Test ----
            EXTENDS Naturals, Sequences
            VARIABLE x
            Init == x = 0
            ====
        ";
        let module = parse_module(source).unwrap();
        let translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        // Should generate imports
        assert!(result.contains("use vstd::prelude::*"));
        assert!(result.contains("use vstd::seq::*"));
    }

    #[test]
    fn test_translate_module_with_constants() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT N
            VARIABLE count
            Init == count \in Nat /\ count < N
            ====
        ";
        let module = parse_module(source).unwrap();
        let translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        // Should generate constants struct
        assert!(result.contains("LConstants"));
        assert!(result.contains("pub N:"));
    }

    #[test]
    fn test_translate_module_with_types() {
        let source = r"
            ---- MODULE Counter ----
            VARIABLE count
            Init == count \in Nat
            ====
        ";
        let module = parse_module(source).unwrap();
        let result = translate_module_with_types(&module);

        // Should generate state struct with inferred types
        assert!(result.contains("pub struct LState"));
        assert!(result.contains("count:"));
    }

    #[test]
    fn test_translate_action_operator() {
        let source = r"
            ---- MODULE Counter ----
            VARIABLE count
            Init == count = 0
            Increment == count' = count + 1
            ====
        ";
        let module = parse_module(source).unwrap();
        let translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        // Init should have single state parameter (no primes)
        assert!(result.contains("pub open spec fn LInit"));

        // Increment should have s and s_ parameters (uses primes)
        assert!(result.contains("pub open spec fn LIncrement"));
        // The function should reference primed variables
        assert!(result.contains("count_"));
    }

    #[test]
    fn test_translate_module_helper_operator() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE x
            Max(a, b) == IF a > b THEN a ELSE b
            Init == x = Max(1, 2)
            ====
        ";
        let module = parse_module(source).unwrap();
        let translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        // Should generate Max function with parameters
        assert!(result.contains("pub open spec fn LMax"));
        assert!(result.contains("a:"));
        assert!(result.contains("b:"));
    }

    #[test]
    fn test_module_translator_with_custom_config() {
        let config = ModuleConfig {
            spec_prefix: "Spec".to_string(),
            exec_prefix: "Exec".to_string(),
            state_name: "MyState".to_string(),
            ..Default::default()
        };

        let source = r"
            ---- MODULE Test ----
            VARIABLE x
            Init == x = 0
            ====
        ";
        let module = parse_module(source).unwrap();
        let translator = ModuleTranslator::with_config(config);
        let result = translator.translate(&module);

        // Should use custom prefix
        assert!(result.contains("pub struct SpecMyState"));
        assert!(result.contains("pub open spec fn SpecInit"));
    }

    #[test]
    fn test_operator_uses_primes() {
        let translator = ModuleTranslator::new();

        // Expression without primes
        let expr1 = TlaExpr::binop(TlaBinOp::Eq, TlaExpr::ident("x"), TlaExpr::number(0));
        assert!(!translator.operator_uses_primes(&expr1));

        // Expression with primes
        let expr2 = TlaExpr::binop(
            TlaBinOp::Eq,
            TlaExpr::prime(TlaExpr::ident("x")),
            TlaExpr::number(1),
        );
        assert!(translator.operator_uses_primes(&expr2));

        // UNCHANGED implies primes
        let expr3 = TlaExpr::Unchanged(vec![TlaExpr::ident("x")]);
        assert!(translator.operator_uses_primes(&expr3));
    }

    #[test]
    fn test_translate_module_convenience() {
        let source = r"
            ---- MODULE Simple ----
            VARIABLE x
            Init == x = 0
            ====
        ";
        let module = parse_module(source).unwrap();

        // Test convenience function
        let result = translate_module(&module);
        assert!(result.contains("LState"));
        assert!(result.contains("LInit"));
    }
}
