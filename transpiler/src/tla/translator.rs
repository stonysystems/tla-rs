//! TLA+ to Verus expression translator.
//!
//! This module translates TLA+ AST expressions to Verus code.

use crate::tla::ast::{TlaBinOp, TlaExceptPath, TlaExpr, TlaNumber, TlaQuantBound, TlaUnaryOp};
/// Make a field name safe for Rust (handle keywords like `type`)
fn safe_field_name(name: &str) -> String {
    match name {
        "type" | "fn" | "let" | "mut" | "ref" | "self" | "super" | "crate" | "mod" | "use"
        | "pub" | "struct" | "enum" | "trait" | "impl" | "where" | "async" | "await" | "match"
        | "if" | "else" | "for" | "while" | "loop" | "return" | "break" | "continue" | "move"
        | "box" | "in" | "as" | "const" | "static" | "extern" | "unsafe" | "dyn" | "abstract"
        | "become" | "do" | "final" | "macro" | "override" | "priv" | "typeof" | "unsized"
        | "virtual" | "yield" => format!("r#{}", name),
        _ => name.to_string(),
    }
}

/// True when an identifier looks like a symbolic atom from generated TLA+ specs
/// (for example enum-like tags such as `Idle`, `Prepare`, `Follower`).
fn is_symbolic_atom_name(name: &str) -> bool {
    if name.len() <= 1 {
        return false;
    }
    if matches!(
        name,
        "Append" | "Len" | "SubSeq" | "Cardinality" | "IsFiniteSet"
    ) {
        return false;
    }
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    first.is_ascii_uppercase() && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Deterministically lower symbolic atoms to integer literals so generated D1
/// specs remain Verus-compilable without requiring out-of-module declarations.
fn symbolic_atom_to_int_literal(name: &str) -> String {
    // 64-bit FNV-1a for stable cross-run mapping.
    let mut hash: u64 = 0xcbf29ce484222325;
    for b in name.as_bytes() {
        hash ^= *b as u64;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    // Keep values readable and avoid tiny literals like 0/1.
    let value = (hash % 9_000_000_000) + 1_000_000_000;
    format!("{value}int")
}

fn is_generated_placeholder_ident(name: &str) -> bool {
    matches!(
        name,
        "new_state"
            | "reply"
            | "restStates"
            | "restReplies"
            | "states"
            | "replies"
            | "earnerState"
    )
}

fn is_builtin_op_name(name: &str) -> bool {
    matches!(
        name,
        "Append"
            | "update"
            | "skip"
            | "drop_first"
            | "drop_last"
            | "Head"
            | "Tail"
            | "Last"
            | "Len"
            | "SubSeq"
            | "Cardinality"
            | "IsFiniteSet"
            | "Seq"
            | "Set"
            | "Map"
    )
}

fn looks_like_external_operator_name(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    first.is_ascii_uppercase() || name.chars().any(|c| c.is_ascii_uppercase())
}

fn is_constructor_style_type_set_expr(expr: &TlaExpr) -> bool {
    match expr {
        TlaExpr::FnSet { .. } => true,
        TlaExpr::OpApply { op, .. } => {
            matches!(
                op.as_ref(),
                TlaExpr::Ident(name) if name == "Seq" || name == "Set" || name == "Map"
            )
        }
        _ => false,
    }
}

fn is_builtin_type_token_ident(name: &str) -> bool {
    matches!(name, "Nat" | "Int" | "BOOLEAN")
}

fn is_rendered_int_literal(s: &str) -> bool {
    let trimmed = s.trim();
    let Some(num) = trimmed.strip_suffix("int") else {
        return false;
    };
    !num.is_empty() && num.chars().all(|c| c.is_ascii_digit())
}

fn rendered_looks_like_set_int(rendered: &str) -> bool {
    let trimmed = rendered.trim();
    trimmed.starts_with("Set::<int>::")
        || trimmed.contains(".union(")
        || trimmed.contains(".intersect(")
        || trimmed.contains(".difference(")
        || trimmed.contains(".subset_of(")
}

fn rendered_looks_like_seq_int(rendered: &str) -> bool {
    let trimmed = rendered.trim();
    trimmed.starts_with("Seq::<int>::")
        || trimmed.contains(".push(")
        || trimmed.contains(".drop_first(")
        || trimmed.contains(".subrange(")
        || trimmed.contains(".update(")
        || trimmed.contains(".skip(")
}

/// Configuration for the expression translator
#[derive(Debug, Clone)]
pub struct TranslatorConfig {
    /// Whether to generate spec (specification) or exec (executable) code
    pub is_spec: bool,
    /// Map TLA+ identifiers to Verus identifiers
    pub rename_map: std::collections::HashMap<String, String>,
    /// Module variable names (for qualifying as `s.field` / `s_.field`)
    pub variable_names: std::collections::HashSet<String>,
    /// Module constant names (for qualifying as `c.field`)
    pub constant_names: std::collections::HashSet<String>,
    /// Module operator names mapped to whether they are actions (use primed vars)
    pub operator_info: std::collections::HashMap<String, OperatorKind>,
    /// Module operator names mapped to explicit parameter arity from source.
    pub operator_arity: std::collections::HashMap<String, usize>,
    /// Prefix for spec function names (e.g. "L")
    pub spec_prefix: String,
    /// Mapping from sorted field names to generated struct name for record types.
    /// Key: sorted, comma-joined field names; Value: struct name (e.g. "LMessage")
    pub record_structs: std::collections::HashMap<String, String>,
    /// All field names in the merged record struct (sorted), empty if no records
    pub record_all_fields: Vec<String>,
    /// Variable names whose type is Set<Record> (need record-typed empty set)
    pub record_set_vars: std::collections::HashSet<String>,
    /// Field name → Verus type for record struct fields (inferred from AST)
    pub record_field_types: std::collections::HashMap<String, String>,
    /// Normalize unresolved external refs in generated spec output to keep D1 compilable.
    pub normalize_unknown_external_refs: bool,
    /// Per-operator identifier type hints (typically parameter types) for local coercion.
    pub identifier_type_hints: std::collections::HashMap<String, String>,
    /// Per-module constants-field type hints for `c.<Field>` access coercion in generated D1.
    pub constant_field_type_hints: std::collections::HashMap<String, String>,
}

/// Classification of a TLA+ operator for code generation
#[derive(Debug, Clone, PartialEq)]
pub enum OperatorKind {
    /// Predicate on current state only (e.g., Init, TypeOK)
    Predicate,
    /// Action that relates current and next state (uses primed variables)
    Action,
    /// Constant operator — does not reference state variables (e.g., Follower == "follower")
    ConstantOp,
}

impl Default for TranslatorConfig {
    fn default() -> Self {
        Self {
            is_spec: true,
            rename_map: std::collections::HashMap::new(),
            variable_names: std::collections::HashSet::new(),
            constant_names: std::collections::HashSet::new(),
            operator_info: std::collections::HashMap::new(),
            operator_arity: std::collections::HashMap::new(),
            spec_prefix: String::new(),
            record_structs: std::collections::HashMap::new(),
            record_all_fields: Vec::new(),
            record_set_vars: std::collections::HashSet::new(),
            record_field_types: std::collections::HashMap::new(),
            normalize_unknown_external_refs: false,
            identifier_type_hints: std::collections::HashMap::new(),
            constant_field_type_hints: std::collections::HashMap::new(),
        }
    }
}

impl TranslatorConfig {
    /// Create a new spec-mode configuration
    pub fn spec() -> Self {
        Self {
            is_spec: true,
            normalize_unknown_external_refs: true,
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
            TlaExpr::FnSet { domain, range } => {
                // [Domain -> Range] = set of all functions from Domain to Range
                let domain_str = self.translate(domain);
                let range_str = self.translate(range);
                format!("Map::<{}, {}>", domain_str, range_str)
            }

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
            TlaExpr::StrongFairness { vars, action } => {
                self.translate_strong_fairness(vars, action)
            }
        }
    }

    fn translate_value_context_expr(&self, expr: &TlaExpr) -> String {
        if self.config.normalize_unknown_external_refs {
            let is_generated_d1_context = self.is_generated_d1_context();
            match expr {
                TlaExpr::Ident(name) => {
                    if is_builtin_type_token_ident(name) {
                        return "arbitrary()".to_string();
                    }
                    if is_generated_d1_context && self.config.operator_info.contains_key(name) {
                        return "arbitrary()".to_string();
                    }
                }
                TlaExpr::OpApply { op, .. } => {
                    if is_generated_d1_context {
                        if let TlaExpr::Ident(name) = op.as_ref() {
                            if self.config.operator_info.contains_key(name) {
                                return "arbitrary()".to_string();
                            }
                        }
                    }
                }
                TlaExpr::SetEnum(_)
                | TlaExpr::SetFilter { .. }
                | TlaExpr::SetMap { .. }
                | TlaExpr::FnConstruct { .. }
                | TlaExpr::FnSet { .. }
                | TlaExpr::Tuple(_) => {
                    if is_generated_d1_context {
                        return "arbitrary()".to_string();
                    }
                }
                TlaExpr::UnaryOp { op, .. }
                    if matches!(op, TlaUnaryOp::Subset | TlaUnaryOp::Union | TlaUnaryOp::Domain) =>
                {
                    if is_generated_d1_context {
                        return "arbitrary()".to_string();
                    }
                }
                _ => {}
            }
            if is_constructor_style_type_set_expr(expr) {
                return "arbitrary()".to_string();
            }
        }
        self.translate(expr)
    }

    fn is_generated_d1_context(&self) -> bool {
        self.config.normalize_unknown_external_refs && self.config.variable_names.is_empty()
    }

    fn coerce_untyped_arbitrary_int(&self, rendered: &str) -> String {
        if self.is_generated_d1_context() && rendered == "arbitrary()" {
            "arbitrary::<int>()".to_string()
        } else {
            rendered.to_string()
        }
    }

    fn coerce_untyped_arbitrary_set_int(&self, rendered: &str) -> String {
        if self.is_generated_d1_context() && rendered == "arbitrary()" {
            "Set::<int>::empty()".to_string()
        } else {
            rendered.to_string()
        }
    }

    fn coerce_untyped_arbitrary_bool(&self, rendered: &str) -> String {
        if self.is_generated_d1_context() && rendered == "arbitrary()" {
            "arbitrary::<bool>()".to_string()
        } else {
            rendered.to_string()
        }
    }

    fn coerce_untyped_arbitrary_seq_int(&self, rendered: &str) -> String {
        if self.is_generated_d1_context() && rendered == "arbitrary()" {
            "arbitrary::<Seq<int>>()".to_string()
        } else {
            rendered.to_string()
        }
    }

    fn coerce_untyped_arbitrary_from_type_hint(&self, rendered: &str, hint: &str) -> String {
        if !self.is_generated_d1_context() || rendered != "arbitrary()" {
            return rendered.to_string();
        }
        match hint.trim() {
            "Seq<int>" => "arbitrary::<Seq<int>>()".to_string(),
            "Set<int>" => "arbitrary::<Set<int>>()".to_string(),
            _ => rendered.to_string(),
        }
    }

    fn constant_field_type_hint<'b>(&'b self, expr: &TlaExpr) -> Option<&'b str> {
        let field_name = match expr {
            TlaExpr::Ident(name) => {
                if let Some(field_name) = name.strip_prefix("c.") {
                    field_name
                } else if self.config.constant_names.contains(name.as_str()) {
                    name.as_str()
                } else {
                    return None;
                }
            }
            TlaExpr::RecordAccess { record, field } => {
                if matches!(record.as_ref(), TlaExpr::Ident(name) if name == "c") {
                    field.as_str()
                } else {
                    return None;
                }
            }
            _ => return None,
        };
        self.config
            .constant_field_type_hints
            .get(field_name)
            .map(|s| s.as_str())
    }

    fn coerce_boolish_numeric_literal(&self, rendered: &str, expr: &TlaExpr) -> String {
        // In D1 spec translation, fallback normalization can leave `0`/`1` in logical
        // positions; Verus requires booleans there.
        if !self.config.normalize_unknown_external_refs {
            return rendered.to_string();
        }
        match expr {
            TlaExpr::Number(TlaNumber::Decimal(s)) if s == "0" => "false".to_string(),
            TlaExpr::Number(TlaNumber::Decimal(s)) if s == "1" => "true".to_string(),
            _ => match rendered.trim() {
                "0" | "0int" => "false".to_string(),
                "1" | "1int" => "true".to_string(),
                _ => rendered.to_string(),
            },
        }
    }

    fn expr_is_boolish(&self, expr: &TlaExpr) -> bool {
        match expr {
            TlaExpr::Bool(_) => true,
            TlaExpr::Ident(name) => name == "TRUE" || name == "FALSE",
            TlaExpr::UnaryOp {
                op: TlaUnaryOp::Not, ..
            } => true,
            TlaExpr::BinOp { op, .. } => matches!(
                op,
                TlaBinOp::And
                    | TlaBinOp::Or
                    | TlaBinOp::Implies
                    | TlaBinOp::Iff
                    | TlaBinOp::In
                    | TlaBinOp::NotIn
                    | TlaBinOp::Subseteq
                    | TlaBinOp::Eq
                    | TlaBinOp::Neq
                    | TlaBinOp::Lt
                    | TlaBinOp::Gt
                    | TlaBinOp::Leq
                    | TlaBinOp::Geq
            ),
            TlaExpr::Forall { .. }
            | TlaExpr::Exists { .. }
            | TlaExpr::Choose { .. }
            | TlaExpr::Enabled(_)
            | TlaExpr::Always(_)
            | TlaExpr::Eventually(_)
            | TlaExpr::LeadsTo { .. }
            | TlaExpr::WeakFairness { .. }
            | TlaExpr::StrongFairness { .. }
            | TlaExpr::Unchanged(_) => true,
            TlaExpr::IfThenElse {
                then_expr,
                else_expr,
                ..
            } => self.expr_is_boolish(then_expr) && self.expr_is_boolish(else_expr),
            TlaExpr::LetIn { body, .. } => self.expr_is_boolish(body),
            _ => false,
        }
    }

    fn expr_is_numericish(&self, expr: &TlaExpr) -> bool {
        match expr {
            TlaExpr::Number(_) => true,
            TlaExpr::UnaryOp {
                op: TlaUnaryOp::Neg, ..
            } => true,
            TlaExpr::BinOp { op, .. } => matches!(
                op,
                TlaBinOp::Plus
                    | TlaBinOp::Minus
                    | TlaBinOp::Times
                    | TlaBinOp::Div
                    | TlaBinOp::Mod
                    | TlaBinOp::Slash
                    | TlaBinOp::Caret
            ),
            TlaExpr::IfThenElse {
                then_expr,
                else_expr,
                ..
            } => self.expr_is_numericish(then_expr) && self.expr_is_numericish(else_expr),
            TlaExpr::LetIn { body, .. } => self.expr_is_numericish(body),
            _ => false,
        }
    }

    fn expr_is_tupleish(&self, expr: &TlaExpr) -> bool {
        match expr {
            TlaExpr::Tuple(_) => true,
            TlaExpr::IfThenElse {
                then_expr,
                else_expr,
                ..
            } => self.expr_is_tupleish(then_expr) && self.expr_is_tupleish(else_expr),
            TlaExpr::LetIn { body, .. } => self.expr_is_tupleish(body),
            _ => false,
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
            _ => {
                // Qualify module variables with s.
                if self.config.variable_names.contains(name) {
                    return format!("s.{}", name);
                }
                // Qualify module constants with c.
                if self.config.constant_names.contains(name) {
                    return format!("c.{}", name);
                }
                // Reference to a module operator: add prefix and pass state args
                if let Some(kind) = self.config.operator_info.get(name) {
                    let arity = self.config.operator_arity.get(name).copied().unwrap_or(0);
                    // Only auto-call bare operator identifiers when they are nullary.
                    // For parameterized operators, keep value-context behavior (e.g. symbolic tags).
                    if arity > 0 {
                        if self.config.normalize_unknown_external_refs
                            && is_symbolic_atom_name(name)
                        {
                            return symbolic_atom_to_int_literal(name);
                        }
                        return format!("{}{}", self.config.spec_prefix, name);
                    }
                    let prefixed = format!("{}{}", self.config.spec_prefix, name);
                    let has_constants = !self.config.constant_names.is_empty();
                    return match kind {
                        OperatorKind::Action if has_constants => {
                            format!("{}(s, s_, c)", prefixed)
                        }
                        OperatorKind::Action => format!("{}(s, s_)", prefixed),
                        OperatorKind::Predicate if has_constants => {
                            format!("{}(s, c)", prefixed)
                        }
                        OperatorKind::Predicate => format!("{}(s)", prefixed),
                        OperatorKind::ConstantOp if has_constants => {
                            format!("{}(c)", prefixed)
                        }
                        OperatorKind::ConstantOp => format!("{}()", prefixed),
                    };
                }
                if self.config.normalize_unknown_external_refs
                    && is_generated_placeholder_ident(name)
                {
                    return "arbitrary()".to_string();
                }
                if is_symbolic_atom_name(name) {
                    return symbolic_atom_to_int_literal(name);
                }
                name.to_string()
            }
        }
    }

    fn translate_prime(&self, inner: &TlaExpr) -> String {
        // Primed variables reference the next-state struct field
        match inner {
            TlaExpr::Ident(name) => {
                if self.config.variable_names.contains(name.as_str()) {
                    format!("s_.{}", name)
                } else {
                    format!("{}_", name)
                }
            }
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
        // In Verus spec mode, "str" is &str but we need Seq<char>.
        // Use "str"@ to convert &str to Seq<char>.
        let escaped = s.replace('\\', "\\\\").replace('"', "\\\"");
        if self.config.is_spec {
            format!("\"{}\"@", escaped)
        } else {
            format!("\"{}\"", escaped)
        }
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
        // Special handling for Eq/Neq with empty sets and record struct types
        if matches!(op, TlaBinOp::Eq | TlaBinOp::Neq) && !self.config.record_set_vars.is_empty() {
            let is_empty_set =
                |e: &TlaExpr| matches!(e, TlaExpr::SetEnum(elems) if elems.is_empty());
            let is_record_set_var = |e: &TlaExpr| {
                // Check if expression references a variable with Set<Record> type
                matches!(e, TlaExpr::Ident(n) if self.config.record_set_vars.contains(n))
                    || matches!(e, TlaExpr::Prime(inner) if matches!(inner.as_ref(), TlaExpr::Ident(n) if self.config.record_set_vars.contains(n)))
            };

            if is_empty_set(right) && is_record_set_var(left) {
                // Get the struct name to determine the empty set type
                if let Some(struct_name) = self.config.record_structs.values().next() {
                    let left_str = self.translate(left);
                    let op_str = if matches!(op, TlaBinOp::Eq) {
                        "=="
                    } else {
                        "!="
                    };
                    return format!("({} {} Set::<{}>::empty())", left_str, op_str, struct_name);
                }
            }
            if is_empty_set(left) && is_record_set_var(right) {
                if let Some(struct_name) = self.config.record_structs.values().next() {
                    let right_str = self.translate(right);
                    let op_str = if matches!(op, TlaBinOp::Eq) {
                        "=="
                    } else {
                        "!="
                    };
                    return format!("(Set::<{}>::empty() {} {})", struct_name, op_str, right_str);
                }
            }
        }

        let mut left_str = self.translate(left);
        let mut right_str = self.translate(right);

        if self.is_generated_d1_context() && matches!(op, TlaBinOp::Eq | TlaBinOp::Neq) {
            let coerce_int = |s: &mut String| {
                if s == "arbitrary()" {
                    *s = "arbitrary::<int>()".to_string();
                }
            };
            let coerce_set = |s: &mut String| {
                if s == "arbitrary()" {
                    *s = "Set::<int>::empty()".to_string();
                }
            };

            if matches!(left, TlaExpr::Number(_)) {
                coerce_int(&mut right_str);
            }
            if matches!(right, TlaExpr::Number(_)) {
                coerce_int(&mut left_str);
            }
            if is_rendered_int_literal(&left_str) {
                coerce_int(&mut right_str);
            }
            if is_rendered_int_literal(&right_str) {
                coerce_int(&mut left_str);
            }
            if matches!(left, TlaExpr::SetEnum(_)) {
                coerce_set(&mut right_str);
            }
            if matches!(right, TlaExpr::SetEnum(_)) {
                coerce_set(&mut left_str);
            }
            if rendered_looks_like_set_int(&left_str) {
                coerce_set(&mut right_str);
            }
            if rendered_looks_like_set_int(&right_str) {
                coerce_set(&mut left_str);
            }
            if rendered_looks_like_seq_int(&left_str) {
                right_str = self.coerce_untyped_arbitrary_seq_int(&right_str);
            }
            if rendered_looks_like_seq_int(&right_str) {
                left_str = self.coerce_untyped_arbitrary_seq_int(&left_str);
            }
            if let TlaExpr::Ident(name) = right {
                if let Some(hint) = self.config.identifier_type_hints.get(name) {
                    left_str = self.coerce_untyped_arbitrary_from_type_hint(&left_str, hint);
                }
            }
            if let TlaExpr::Ident(name) = left {
                if let Some(hint) = self.config.identifier_type_hints.get(name) {
                    right_str = self.coerce_untyped_arbitrary_from_type_hint(&right_str, hint);
                }
            }
            if let Some(hint) = self.constant_field_type_hint(left) {
                right_str = self.coerce_untyped_arbitrary_from_type_hint(&right_str, hint);
            }
            if let Some(hint) = self.constant_field_type_hint(right) {
                left_str = self.coerce_untyped_arbitrary_from_type_hint(&left_str, hint);
            }

            if self.expr_is_boolish(left) {
                right_str = self.coerce_untyped_arbitrary_bool(&right_str);
            }
            if self.expr_is_boolish(right) {
                left_str = self.coerce_untyped_arbitrary_bool(&left_str);
            }
            if self.expr_is_numericish(left) {
                coerce_int(&mut right_str);
            }
            if self.expr_is_numericish(right) {
                coerce_int(&mut left_str);
            }
            if matches!(left, TlaExpr::Tuple(_)) {
                right_str = self.coerce_untyped_arbitrary_seq_int(&right_str);
            }
            if matches!(right, TlaExpr::Tuple(_)) {
                left_str = self.coerce_untyped_arbitrary_seq_int(&left_str);
            }
            if matches!(left, TlaExpr::Ident(name) if name == "c")
                && !self.config.constant_names.is_empty()
                && right_str == "arbitrary()"
            {
                right_str = "arbitrary::<LConstants>()".to_string();
            }
            if matches!(right, TlaExpr::Ident(name) if name == "c")
                && !self.config.constant_names.is_empty()
                && left_str == "arbitrary()"
            {
                left_str = "arbitrary::<LConstants>()".to_string();
            }
            if left_str == "arbitrary()" && right_str == "arbitrary()" {
                left_str = "arbitrary::<int>()".to_string();
                right_str = "arbitrary::<int>()".to_string();
            }
        }

        match op {
            // Logical operators
            TlaBinOp::And => format!(
                "({} && {})",
                self.coerce_boolish_numeric_literal(&left_str, left),
                self.coerce_boolish_numeric_literal(&right_str, right)
            ),
            TlaBinOp::Or => format!(
                "({} || {})",
                self.coerce_boolish_numeric_literal(&left_str, left),
                self.coerce_boolish_numeric_literal(&right_str, right)
            ),
            TlaBinOp::Implies => format!(
                "({} ==> {})",
                self.coerce_boolish_numeric_literal(&left_str, left),
                self.coerce_boolish_numeric_literal(&right_str, right)
            ),
            TlaBinOp::Iff => format!(
                "({} <==> {})",
                self.coerce_boolish_numeric_literal(&left_str, left),
                self.coerce_boolish_numeric_literal(&right_str, right)
            ),

            // Set operations (T5.1)
            TlaBinOp::In => {
                // x \in Nat → x >= 0, x \in Int → true, x \in BOOLEAN → true
                match right {
                    TlaExpr::Ident(name) if name == "Nat" || name == "Int" || name == "BOOLEAN" => {
                        match name.as_str() {
                            "Nat" => format!("({} >= 0)", left_str),
                            _ => "true".to_string(),
                        }
                    }
                    // Constructor-style type sets (Seq(...), Set(...), Map(...), [D -> R]) are
                    // type-level in Verus and cannot be called as runtime set constructors.
                    _ if is_constructor_style_type_set_expr(right) => "true".to_string(),
                    _ => {
                        if self.config.normalize_unknown_external_refs {
                            if let TlaExpr::UnaryOp {
                                op: TlaUnaryOp::Not,
                                operand,
                            } = left
                            {
                                return format!(
                                    "!{}.contains({})",
                                    self.coerce_untyped_arbitrary_set_int(&right_str),
                                    self.coerce_untyped_arbitrary_int(&self.translate(operand))
                                );
                            }
                            if self.is_generated_d1_context() {
                                if let Some(inner) =
                                    left_str.strip_prefix("!(").and_then(|s| s.strip_suffix(')'))
                                {
                                    return format!(
                                        "!{}.contains({})",
                                        self.coerce_untyped_arbitrary_set_int(&right_str),
                                        self.coerce_untyped_arbitrary_int(inner)
                                    );
                                }
                            }
                        }
                        format!(
                            "{}.contains({})",
                            self.coerce_untyped_arbitrary_set_int(&right_str),
                            self.coerce_untyped_arbitrary_int(&left_str)
                        )
                    }
                }
            }
            TlaBinOp::NotIn => match right {
                TlaExpr::Ident(name) if name == "Nat" || name == "Int" || name == "BOOLEAN" => {
                    match name.as_str() {
                        "Nat" => format!("({} < 0)", left_str),
                        _ => "false".to_string(),
                    }
                }
                _ if is_constructor_style_type_set_expr(right) => "false".to_string(),
                _ => format!(
                    "!{}.contains({})",
                    self.coerce_untyped_arbitrary_set_int(&right_str),
                    self.coerce_untyped_arbitrary_int(&left_str)
                ),
            },
            TlaBinOp::Subseteq => format!(
                "{}.subset_of({})",
                self.coerce_untyped_arbitrary_set_int(&left_str),
                self.coerce_untyped_arbitrary_set_int(&right_str)
            ),
            TlaBinOp::Cup => format!(
                "{}.union({})",
                self.coerce_untyped_arbitrary_set_int(&left_str),
                self.coerce_untyped_arbitrary_set_int(&right_str)
            ),
            TlaBinOp::Cap => format!(
                "{}.intersect({})",
                self.coerce_untyped_arbitrary_set_int(&left_str),
                self.coerce_untyped_arbitrary_set_int(&right_str)
            ),
            TlaBinOp::Setminus => format!(
                "{}.difference({})",
                self.coerce_untyped_arbitrary_set_int(&left_str),
                self.coerce_untyped_arbitrary_set_int(&right_str)
            ),
            TlaBinOp::CrossProd => format!(
                "{}.cartesian_product({})",
                self.coerce_untyped_arbitrary_set_int(&left_str),
                self.coerce_untyped_arbitrary_set_int(&right_str)
            ),

            // Arithmetic
            TlaBinOp::Plus => format!(
                "({} + {})",
                self.coerce_untyped_arbitrary_int(&left_str),
                self.coerce_untyped_arbitrary_int(&right_str)
            ),
            TlaBinOp::Minus => format!(
                "({} - {})",
                self.coerce_untyped_arbitrary_int(&left_str),
                self.coerce_untyped_arbitrary_int(&right_str)
            ),
            TlaBinOp::Times => format!(
                "({} * {})",
                self.coerce_untyped_arbitrary_int(&left_str),
                self.coerce_untyped_arbitrary_int(&right_str)
            ),
            TlaBinOp::Div => format!(
                "({} / {})",
                self.coerce_untyped_arbitrary_int(&left_str),
                self.coerce_untyped_arbitrary_int(&right_str)
            ),
            TlaBinOp::Mod => format!(
                "({} % {})",
                self.coerce_untyped_arbitrary_int(&left_str),
                self.coerce_untyped_arbitrary_int(&right_str)
            ),
            TlaBinOp::Slash => format!(
                "({} / {})",
                self.coerce_untyped_arbitrary_int(&left_str),
                self.coerce_untyped_arbitrary_int(&right_str)
            ),
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
            TlaBinOp::Lt => format!(
                "({} < {})",
                self.coerce_untyped_arbitrary_int(&left_str),
                self.coerce_untyped_arbitrary_int(&right_str)
            ),
            TlaBinOp::Gt => format!(
                "({} > {})",
                self.coerce_untyped_arbitrary_int(&left_str),
                self.coerce_untyped_arbitrary_int(&right_str)
            ),
            TlaBinOp::Leq => format!(
                "({} <= {})",
                self.coerce_untyped_arbitrary_int(&left_str),
                self.coerce_untyped_arbitrary_int(&right_str)
            ),
            TlaBinOp::Geq => format!(
                "({} >= {})",
                self.coerce_untyped_arbitrary_int(&left_str),
                self.coerce_untyped_arbitrary_int(&right_str)
            ),

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
            // Verus cannot infer the type parameter for Set::empty().
            // Default to int since TLA+ sets are untyped and int is the common element type.
            return "Set::<int>::empty()".to_string();
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

    fn translate_fn_construct(&self, var: &str, domain: &TlaExpr, body: &TlaExpr) -> String {
        // [x \in S |-> f(x)] → Map::new(|x| f(x))
        let domain_str = self.translate(domain);
        let body_str = self.translate(body);
        format!("Map::new({}, |{}| {})", domain_str, var, body_str)
    }

    fn translate_fn_apply(&self, func: &TlaExpr, arg: &TlaExpr) -> String {
        // f[x] → f[x] or f.index(x)
        let func_str = self.translate(func);
        let func_str = self.coerce_untyped_arbitrary_seq_int(&func_str);
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
        // Check if we have a named struct for this record shape
        let mut sorted_names: Vec<_> = fields.iter().map(|(n, _)| n.as_str()).collect();
        sorted_names.sort();
        let key = sorted_names.join(",");

        if let Some(struct_name) = self.config.record_structs.get(&key) {
            // Build field assignments, filling in defaults for missing fields
            let present: std::collections::HashSet<&str> =
                fields.iter().map(|(n, _)| n.as_str()).collect();
            let mut all_field_strs: Vec<String> = Vec::new();

            for all_field in &self.config.record_all_fields {
                let safe_name = safe_field_name(all_field);
                if let Some((_, value)) = fields.iter().find(|(n, _)| n == all_field) {
                    let expected_ty = self
                        .config
                        .record_field_types
                        .get(all_field)
                        .map(|s| s.as_str())
                        .unwrap_or("int");
                    let normalized_expected_ty = expected_ty
                        .chars()
                        .filter(|c| !c.is_whitespace())
                        .collect::<String>();
                    let expected_is_int_like = normalized_expected_ty == "int"
                        || normalized_expected_ty == "nat"
                        || normalized_expected_ty.ends_with("*/int")
                        || normalized_expected_ty.ends_with("*/nat");
                    let mut rendered_value = self.translate_value_context_expr(value);
                    if self.config.normalize_unknown_external_refs
                        && expected_is_int_like
                        && rendered_value.starts_with("c.")
                    {
                        rendered_value = "arbitrary::<int>()".to_string();
                    }
                    all_field_strs.push(format!("{}: {}", safe_name, rendered_value));
                } else if !present.contains(all_field.as_str()) {
                    // Default value for missing fields (type-aware)
                    let default_val = match self
                        .config
                        .record_field_types
                        .get(all_field)
                        .map(|s| s.as_str())
                    {
                        Some("Seq<char>") => "\"\"@",
                        _ => "0int",
                    };
                    all_field_strs.push(format!("{}: {}", safe_name, default_val));
                }
            }

            format!("{} {{ {} }}", struct_name, all_field_strs.join(", "))
        } else {
            let field_strs: Vec<_> = fields
                .iter()
                .map(|(name, value)| {
                    format!(
                        "{}: {}",
                        safe_field_name(name),
                        self.translate_value_context_expr(value)
                    )
                })
                .collect();
            format!("{{ {} }}", field_strs.join(", "))
        }
    }

    fn translate_record_access(&self, record: &TlaExpr, field: &str) -> String {
        if self.config.normalize_unknown_external_refs {
            // For generated D1 specs, unknown/local record roots (e.g. request.client, ps.replicas)
            // frequently become scalar placeholders. Emit an untyped placeholder directly to avoid
            // field-on-scalar compile failures while preserving known module state/constant roots.
            if let TlaExpr::Ident(name) = record {
                if self.config.variable_names.is_empty()
                    && (name == "s" || name == "s_" || name == "c")
                {
                    return "arbitrary()".to_string();
                }
                let is_known_module_root = self.config.variable_names.contains(name.as_str())
                    || self.config.constant_names.contains(name.as_str())
                    || name == "s"
                    || name == "s_"
                    || name == "c";
                if !is_known_module_root {
                    return "arbitrary()".to_string();
                }
            } else if self.config.variable_names.is_empty()
                && matches!(record, TlaExpr::RecordAccess { .. })
            {
                return "arbitrary()".to_string();
            }
        }
        let record_str = self.translate(record);
        format!("{}.{}", record_str, safe_field_name(field))
    }

    fn translate_tuple(&self, elements: &[TlaExpr]) -> String {
        if elements.is_empty() {
            return "Seq::<int>::empty()".to_string();
        }
        if self.is_generated_d1_context()
            && elements
                .iter()
                .any(|e| matches!(e, TlaExpr::Record(_) | TlaExpr::Tuple(_)))
        {
            return "arbitrary()".to_string();
        }
        // <<a, b, c>> → seq![a, b, c] (for sequences)
        // For tuples as actual tuples, use (a, b, c)
        let elem_strs: Vec<_> = elements.iter().map(|e| self.translate(e)).collect();
        if self.is_generated_d1_context()
            && elements.len() > 1
            && elem_strs.iter().all(|s| s == "arbitrary()")
        {
            return "arbitrary()".to_string();
        }
        format!("seq![{}]", elem_strs.join(", "))
    }

    // =========================================================================
    // Quantifier translation (T5.4)
    // =========================================================================

    fn translate_quantifier_bound(&self, var: &str, set: &TlaExpr) -> Option<String> {
        match set {
            // Int/BOOLEAN are universal in TLA+; no explicit bound needed in Verus quantifier guard.
            TlaExpr::Ident(name) if name == "Int" || name == "BOOLEAN" => None,
            // Nat is modeled as int with non-negativity guard.
            TlaExpr::Ident(name) if name == "Nat" => Some(format!("({var} >= 0)")),
            // Constructor-style type sets are type-level and should not be emitted as value calls.
            _ if is_constructor_style_type_set_expr(set) => None,
            _ => {
                let set_str = self.translate(set);
                Some(format!("{}.contains({})", set_str, var))
            }
        }
    }

    fn translate_forall(&self, vars: &[TlaQuantBound], body: &TlaExpr) -> String {
        // \A x \in S : P(x) → forall |x| S.contains(x) ==> P(x)
        let body_str = self.translate(body);

        if vars.len() == 1 {
            let var = &vars[0];
            if let Some(set) = &var.set {
                if let Some(bound) = self.translate_quantifier_bound(&var.var, set) {
                    format!("forall |{}| {} ==> {}", var.var, bound, body_str)
                } else {
                    format!("forall |{}| {}", var.var, body_str)
                }
            } else {
                format!("forall |{}| {}", var.var, body_str)
            }
        } else {
            // Multiple bound variables
            let var_names: Vec<_> = vars.iter().map(|v| v.var.clone()).collect();
            let bounds: Vec<_> = vars
                .iter()
                .filter_map(|v| {
                    v.set
                        .as_ref()
                        .and_then(|s| self.translate_quantifier_bound(&v.var, s))
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
                if let Some(bound) = self.translate_quantifier_bound(&var.var, set) {
                    format!("exists |{}| {} && {}", var.var, bound, body_str)
                } else {
                    format!("exists |{}| {}", var.var, body_str)
                }
            } else {
                format!("exists |{}| {}", var.var, body_str)
            }
        } else {
            // Multiple bound variables
            let var_names: Vec<_> = vars.iter().map(|v| v.var.clone()).collect();
            let bounds: Vec<_> = vars
                .iter()
                .filter_map(|v| {
                    v.set
                        .as_ref()
                        .and_then(|s| self.translate_quantifier_bound(&v.var, s))
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
        // Module operator calls need special handling:
        // - avoid producing double-call forms like `LFoo(...)(...)`
        // - inject implicit state/constants args when source omitted them
        if let TlaExpr::Ident(op_name) = op {
            if let Some(kind) = self.config.operator_info.get(op_name) {
                let declared_arity = self
                    .config
                    .operator_arity
                    .get(op_name)
                    .copied()
                    .unwrap_or(args.len());
                if args.is_empty() && declared_arity > 0 {
                    if self.config.normalize_unknown_external_refs
                        && is_symbolic_atom_name(op_name)
                    {
                        return symbolic_atom_to_int_literal(op_name);
                    }
                    return format!("{}{}", self.config.spec_prefix, op_name);
                }
                let prefixed = format!("{}{}", self.config.spec_prefix, op_name);
                let has_constants = !self.config.constant_names.is_empty();

                let implicit_args: Vec<&str> = match (kind, has_constants) {
                    (OperatorKind::Action, true) => vec!["s", "s_", "c"],
                    (OperatorKind::Action, false) => vec!["s", "s_"],
                    (OperatorKind::Predicate, true) => vec!["s", "c"],
                    (OperatorKind::Predicate, false) => vec!["s"],
                    (OperatorKind::ConstantOp, true) => vec!["c"],
                    (OperatorKind::ConstantOp, false) => Vec::new(),
                };
                let explicit_args: Vec<String> = args.iter().map(|a| self.translate(a)).collect();
                let explicit_starts_with_implicit = explicit_args
                    .iter()
                    .take(implicit_args.len())
                    .map(|s| s.as_str())
                    .eq(implicit_args.iter().copied());
                let call_args: Vec<String> = if explicit_starts_with_implicit {
                    explicit_args
                } else {
                    implicit_args
                        .iter()
                        .map(|s| s.to_string())
                        .chain(explicit_args)
                        .collect()
                };

                return format!("{}({})", prefixed, call_args.join(", "));
            }
        }

        let arg_strs: Vec<_> = args.iter().map(|a| self.translate(a)).collect();
        // In operator-call position, keep identifier operators as identifiers to
        // avoid symbolic-atom lowering turning call heads into integer literals.
        let op_str = match op {
            TlaExpr::Ident(name) => self
                .config
                .rename_map
                .get(name)
                .cloned()
                .unwrap_or_else(|| name.clone()),
            _ => self.translate(op),
        };

        // Check for standard library functions
        match op_str.as_str() {
            // Sequence operations (T5.3)
            "Append" if args.len() == 2 => {
                let seq = self.coerce_untyped_arbitrary_seq_int(&arg_strs[0]);
                format!("{}.push({})", seq, arg_strs[1])
            }
            "update" if args.len() == 3 => {
                let seq = self.coerce_untyped_arbitrary_seq_int(&arg_strs[0]);
                format!("{}.update({}, {})", seq, arg_strs[1], arg_strs[2])
            }
            "skip" if args.len() == 2 => {
                let seq = self.coerce_untyped_arbitrary_seq_int(&arg_strs[0]);
                format!("{}.skip({})", seq, arg_strs[1])
            }
            "drop_first" if args.len() == 1 => {
                let seq = self.coerce_untyped_arbitrary_seq_int(&arg_strs[0]);
                format!("{}.drop_first()", seq)
            }
            "drop_last" if args.len() == 1 => {
                let seq = self.coerce_untyped_arbitrary_seq_int(&arg_strs[0]);
                format!("{}.subrange(0, {}.len() - 1)", seq, seq)
            }
            "Head" if args.len() == 1 => {
                let seq = self.coerce_untyped_arbitrary_seq_int(&arg_strs[0]);
                format!("{}[0]", seq)
            }
            "Tail" if args.len() == 1 => {
                let seq = self.coerce_untyped_arbitrary_seq_int(&arg_strs[0]);
                format!("{}.drop_first()", seq)
            }
            "Last" if args.len() == 1 => {
                let seq = self.coerce_untyped_arbitrary_seq_int(&arg_strs[0]);
                format!("{}[{}.len() - 1]", seq, seq)
            }
            "Len" if args.len() == 1 => {
                let seq = self.coerce_untyped_arbitrary_seq_int(&arg_strs[0]);
                if self.is_generated_d1_context() {
                    format!("({}.len() as int)", seq)
                } else {
                    format!("{}.len()", seq)
                }
            }
            "SubSeq" if args.len() == 3 => {
                // TLA+ is 1-indexed, Verus is 0-indexed
                let seq = self.coerce_untyped_arbitrary_seq_int(&arg_strs[0]);
                format!(
                    "{}.subrange({} - 1, {})",
                    seq, arg_strs[1], arg_strs[2]
                )
            }

            // Set operations
            "Cardinality" if args.len() == 1 => {
                let set = self.coerce_untyped_arbitrary_set_int(&arg_strs[0]);
                format!("{}.len()", set)
            }
            "IsFiniteSet" if args.len() == 1 => {
                let set = self.coerce_untyped_arbitrary_set_int(&arg_strs[0]);
                format!("{}.finite()", set)
            }

            // Default: regular function call
            _ => {
                if self.config.normalize_unknown_external_refs {
                    if let TlaExpr::Ident(name) = op {
                        if !self.config.operator_info.contains_key(name)
                            && !self.config.rename_map.contains_key(name)
                            && !is_builtin_op_name(name)
                            && looks_like_external_operator_name(name)
                        {
                            return "arbitrary()".to_string();
                        }
                    }
                }
                format!("{}({})", op_str, arg_strs.join(", "))
            }
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
        if self.is_generated_d1_context() {
            let mixed_bool_numeric = (self.expr_is_boolish(then_expr)
                && self.expr_is_numericish(else_expr))
                || (self.expr_is_numericish(then_expr) && self.expr_is_boolish(else_expr));
            let tupleish_branches =
                self.expr_is_tupleish(then_expr) && self.expr_is_tupleish(else_expr);
            if mixed_bool_numeric || tupleish_branches {
                return "arbitrary()".to_string();
            }
        }

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
                if self.is_generated_d1_context() && body_str == "arbitrary()" {
                    let ty = if self.expr_is_boolish(&def.body) {
                        "bool"
                    } else {
                        "int"
                    };
                    result.push_str(&format!("    let {}: {} = {};\n", def.name, ty, body_str));
                } else {
                    result.push_str(&format!("    let {} = {};\n", def.name, body_str));
                }
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
        // UNCHANGED <<x, y>> → s_.x == s.x && s_.y == s.y
        let conditions: Vec<_> = vars
            .iter()
            .map(|v| match v {
                TlaExpr::Ident(name) if self.config.variable_names.contains(name.as_str()) => {
                    format!("s_.{} == s.{}", name, name)
                }
                _ => {
                    let v_str = self.translate(v);
                    format!("{}_ == {}", v_str, v_str)
                }
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

fn operator_has_explicit_next_state_param(op: &TlaOperator) -> bool {
    op.params.iter().any(|param| param.name == "s_")
}

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

#[derive(Debug, Default, Clone, Copy)]
struct UsageHintEvidence {
    set_membership: bool,
    set_element_usage: bool,
    seq_len: bool,
    seq_index_like: bool,
    map_domain: bool,
    map_index_like: bool,
    scalar_usage: bool,
}

impl UsageHintEvidence {
    fn merge(self, other: Self) -> Self {
        Self {
            set_membership: self.set_membership || other.set_membership,
            set_element_usage: self.set_element_usage || other.set_element_usage,
            seq_len: self.seq_len || other.seq_len,
            seq_index_like: self.seq_index_like || other.seq_index_like,
            map_domain: self.map_domain || other.map_domain,
            map_index_like: self.map_index_like || other.map_index_like,
            scalar_usage: self.scalar_usage || other.scalar_usage,
        }
    }

    fn to_hint(self) -> Option<&'static str> {
        if self.map_domain && self.map_index_like && !self.scalar_usage {
            Some("Map<int, int>")
        } else if self.seq_len && self.seq_index_like && !self.scalar_usage {
            Some("Seq<int>")
        } else if self.set_membership {
            Some("Set<int>")
        } else if self.set_element_usage {
            Some("int")
        } else if self.scalar_usage {
            Some("int")
        } else {
            None
        }
    }
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
    pub fn translate(&mut self, module: &TlaModule) -> String {
        // Pre-pass: collect record shapes and set up struct mappings
        self.collect_record_shapes(module);

        let mut output = String::new();

        // Module header
        output.push_str(&self.generate_header(module));
        output.push('\n');

        // Imports based on EXTENDS
        output.push_str(&self.generate_imports(module));
        output.push('\n');

        // State struct (includes record struct definitions)
        output.push_str(&self.generate_state_struct(module));
        output.push('\n');

        // Spec functions for operators
        output.push_str(&self.generate_spec_functions(module));

        output
    }

    /// Collect all record shapes from the module and assign struct names.
    /// All record shapes are merged into a single struct (union of all fields)
    /// since TLA+ records with different field sets can go into the same collection.
    fn collect_record_shapes(&mut self, module: &TlaModule) {
        let mut all_field_names: std::collections::BTreeSet<String> =
            std::collections::BTreeSet::new();
        let mut per_record_keys: Vec<String> = Vec::new();
        let mut string_fields: std::collections::HashSet<String> = std::collections::HashSet::new();

        // Build set of operators that return string values (body is a TlaExpr::String)
        let mut string_ops: std::collections::HashSet<String> = std::collections::HashSet::new();
        for op in &module.operators {
            if matches!(&op.body, TlaExpr::String(_)) {
                string_ops.insert(op.name.clone());
            }
        }

        // Walk all operator bodies to find Record expressions
        for op in &module.operators {
            self.collect_records_from_expr_fields(
                &op.body,
                &mut all_field_names,
                &mut per_record_keys,
                &mut string_fields,
                &string_ops,
            );
        }

        if all_field_names.is_empty() {
            return;
        }

        // Create a single struct name for all record shapes
        let prefix = &self.config.spec_prefix;
        let struct_name = format!("{}Record", prefix);

        // Map every unique record key to the same struct name
        for key in &per_record_keys {
            self.expr_config
                .record_structs
                .insert(key.clone(), struct_name.clone());
        }
        // Also map the full set of all fields (for the variable type)
        let all_fields_vec: Vec<String> = all_field_names.iter().cloned().collect();
        let all_key: String = all_fields_vec.join(",");
        self.expr_config
            .record_structs
            .insert(all_key, struct_name.clone());
        self.expr_config.record_all_fields = all_fields_vec;

        // Store inferred field types (string fields → Seq<char>, rest → int)
        for field_name in &all_field_names {
            if string_fields.contains(field_name) {
                self.expr_config
                    .record_field_types
                    .insert(field_name.clone(), "Seq<char>".to_string());
            } else {
                self.expr_config
                    .record_field_types
                    .insert(field_name.clone(), "int".to_string());
            }
        }

        // Identify variables with Set<Record> type
        if let Some(env) = &self.type_env {
            for (var_name, ty) in &env.variables {
                if Self::type_contains_record(ty) {
                    self.expr_config.record_set_vars.insert(var_name.clone());
                }
            }
        }
    }

    /// Check if a type contains a Record type (used to detect Set<Record> variables)
    fn type_contains_record(ty: &TlaType) -> bool {
        match ty {
            TlaType::Record(_) => true,
            TlaType::Set(elem) => Self::type_contains_record(elem),
            TlaType::Seq(elem) => Self::type_contains_record(elem),
            TlaType::Map { key, value } => {
                Self::type_contains_record(key) || Self::type_contains_record(value)
            }
            _ => false,
        }
    }

    /// Check if an expression produces a string type (directly, via operator call, or via ident ref)
    fn expr_is_string(expr: &TlaExpr, string_ops: &std::collections::HashSet<String>) -> bool {
        match expr {
            TlaExpr::String(_) => true,
            TlaExpr::Ident(name) => string_ops.contains(name),
            TlaExpr::OpApply { op, .. } => {
                if let TlaExpr::Ident(name) = op.as_ref() {
                    string_ops.contains(name)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// Walk an expression tree to collect record field names, per-record keys, and field types
    fn collect_records_from_expr_fields(
        &self,
        expr: &TlaExpr,
        all_fields: &mut std::collections::BTreeSet<String>,
        keys: &mut Vec<String>,
        string_fields: &mut std::collections::HashSet<String>,
        string_ops: &std::collections::HashSet<String>,
    ) {
        match expr {
            TlaExpr::Record(fields) => {
                let mut sorted_names: Vec<_> = fields.iter().map(|(n, _)| n.clone()).collect();
                sorted_names.sort();
                let key = sorted_names.join(",");
                if !keys.contains(&key) {
                    keys.push(key);
                }
                for name in &sorted_names {
                    all_fields.insert(name.clone());
                }
                // Check field value types and recurse
                for (name, value) in fields {
                    if Self::expr_is_string(value, string_ops) {
                        string_fields.insert(name.clone());
                    }
                    self.collect_records_from_expr_fields(
                        value,
                        all_fields,
                        keys,
                        string_fields,
                        string_ops,
                    );
                }
            }
            TlaExpr::Prime(inner)
            | TlaExpr::UnaryOp { operand: inner, .. }
            | TlaExpr::Enabled(inner)
            | TlaExpr::Always(inner)
            | TlaExpr::Eventually(inner) => {
                self.collect_records_from_expr_fields(
                    inner,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
            }
            TlaExpr::BinOp { left, right, .. } | TlaExpr::LeadsTo { left, right } => {
                self.collect_records_from_expr_fields(
                    left,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
                self.collect_records_from_expr_fields(
                    right,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
            }
            TlaExpr::OpApply { op, args } => {
                self.collect_records_from_expr_fields(
                    op,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
                for arg in args {
                    self.collect_records_from_expr_fields(
                        arg,
                        all_fields,
                        keys,
                        string_fields,
                        string_ops,
                    );
                }
            }
            TlaExpr::FnApply { func, arg } => {
                self.collect_records_from_expr_fields(
                    func,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
                self.collect_records_from_expr_fields(
                    arg,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
            }
            TlaExpr::IfThenElse {
                cond,
                then_expr,
                else_expr,
            } => {
                self.collect_records_from_expr_fields(
                    cond,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
                self.collect_records_from_expr_fields(
                    then_expr,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
                self.collect_records_from_expr_fields(
                    else_expr,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
            }
            TlaExpr::SetEnum(elements) | TlaExpr::Tuple(elements) | TlaExpr::Unchanged(elements) => {
                for element in elements {
                    self.collect_records_from_expr_fields(
                        element,
                        all_fields,
                        keys,
                        string_fields,
                        string_ops,
                    );
                }
            }
            TlaExpr::SetFilter { set, filter, .. } => {
                self.collect_records_from_expr_fields(
                    set,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
                self.collect_records_from_expr_fields(
                    filter,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
            }
            TlaExpr::SetMap { expr, set, .. } => {
                self.collect_records_from_expr_fields(
                    expr,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
                self.collect_records_from_expr_fields(
                    set,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
            }
            TlaExpr::FnConstruct { domain, body, .. } => {
                self.collect_records_from_expr_fields(
                    domain,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
                self.collect_records_from_expr_fields(
                    body,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
            }
            TlaExpr::FnExcept { func, updates } => {
                self.collect_records_from_expr_fields(
                    func,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
                for update in updates {
                    for path in &update.path {
                        if let TlaExceptPath::Index(index) = path {
                            self.collect_records_from_expr_fields(
                                index,
                                all_fields,
                                keys,
                                string_fields,
                                string_ops,
                            );
                        }
                    }
                    self.collect_records_from_expr_fields(
                        &update.value,
                        all_fields,
                        keys,
                        string_fields,
                        string_ops,
                    );
                }
            }
            TlaExpr::FnSet { domain, range } => {
                self.collect_records_from_expr_fields(
                    domain,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
                self.collect_records_from_expr_fields(
                    range,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
            }
            TlaExpr::RecordAccess { record, .. } => {
                self.collect_records_from_expr_fields(
                    record,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
            }
            TlaExpr::Forall { vars, body } | TlaExpr::Exists { vars, body } => {
                for quant_bound in vars {
                    if let Some(set_expr) = &quant_bound.set {
                        self.collect_records_from_expr_fields(
                            set_expr,
                            all_fields,
                            keys,
                            string_fields,
                            string_ops,
                        );
                    }
                }
                self.collect_records_from_expr_fields(
                    body,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
            }
            TlaExpr::Choose { set, body, .. } => {
                if let Some(set_expr) = set {
                    self.collect_records_from_expr_fields(
                        set_expr,
                        all_fields,
                        keys,
                        string_fields,
                        string_ops,
                    );
                }
                self.collect_records_from_expr_fields(
                    body,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
            }
            TlaExpr::Case { arms, other } => {
                for (condition, body) in arms {
                    self.collect_records_from_expr_fields(
                        condition,
                        all_fields,
                        keys,
                        string_fields,
                        string_ops,
                    );
                    self.collect_records_from_expr_fields(
                        body,
                        all_fields,
                        keys,
                        string_fields,
                        string_ops,
                    );
                }
                if let Some(other_expr) = other {
                    self.collect_records_from_expr_fields(
                        other_expr,
                        all_fields,
                        keys,
                        string_fields,
                        string_ops,
                    );
                }
            }
            TlaExpr::LetIn { defs, body } => {
                for def in defs {
                    self.collect_records_from_expr_fields(
                        &def.body,
                        all_fields,
                        keys,
                        string_fields,
                        string_ops,
                    );
                }
                self.collect_records_from_expr_fields(
                    body,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
            }
            TlaExpr::WeakFairness { vars, action } | TlaExpr::StrongFairness { vars, action } => {
                self.collect_records_from_expr_fields(
                    vars,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
                self.collect_records_from_expr_fields(
                    action,
                    all_fields,
                    keys,
                    string_fields,
                    string_ops,
                );
            }
            _ => {}
        }
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

        // Generate record struct definitions (for TLA+ record/message types)
        if !self.expr_config.record_structs.is_empty() {
            self.generate_record_structs(module, &mut output);
        }

        // State struct (spec-only, no derive Clone — Verus doesn't support it for nat/int fields)
        output.push_str(&format!("/// State for {} module\n", module.name));
        output.push_str(&format!("pub struct {} {{\n", state_name));

        for var in &module.variables {
            let var_type = self.get_variable_type(var);
            output.push_str(&format!("    pub {}: {},\n", var, var_type));
        }

        output.push_str("}\n\n");

        // Constants as associated constants or generic parameters
        if !module.constants.is_empty() {
            output.push_str("/// Constants for the module\n");
            output.push_str(&format!(
                "pub struct {}Constants {{\n",
                self.config.spec_prefix
            ));
            for constant in &module.constants {
                let const_type = self.get_constant_type(module, &constant.name);
                output.push_str(&format!("    pub {}: {},\n", constant.name, const_type));
            }
            output.push_str("}\n\n");
        }

        output
    }

    /// Generate struct definitions for TLA+ record types.
    /// Since all record shapes map to a single merged struct, we generate one struct
    /// with the union of all fields. Field types default to `int`.
    fn generate_record_structs(&self, module: &TlaModule, output: &mut String) {
        // Collect all unique struct names (should be just one since we merge)
        let mut struct_names: std::collections::BTreeSet<String> =
            std::collections::BTreeSet::new();
        for name in self.expr_config.record_structs.values() {
            struct_names.insert(name.clone());
        }

        // Merge all field names from all record shapes
        let mut all_field_names: std::collections::BTreeSet<String> =
            std::collections::BTreeSet::new();
        for key in self.expr_config.record_structs.keys() {
            for field_name in key.split(',') {
                all_field_names.insert(field_name.to_string());
            }
        }

        for struct_name in &struct_names {
            output.push_str(&format!("/// Record type for {} module\n", module.name));
            output.push_str(&format!("pub struct {} {{\n", struct_name));

            for field_name in &all_field_names {
                let safe_name = safe_field_name(field_name);
                let field_type = self
                    .expr_config
                    .record_field_types
                    .get(field_name)
                    .map(|s| s.as_str())
                    .unwrap_or("int");
                output.push_str(&format!("    pub {}: {},\n", safe_name, field_type));
            }

            output.push_str("}\n\n");
        }
    }

    /// Generate spec functions for operators
    fn generate_spec_functions(&self, module: &TlaModule) -> String {
        let mut output = String::new();
        let state_name = self.config.spec_state_name();
        let module_var_names: std::collections::HashSet<String> =
            module.variables.iter().cloned().collect();

        // Build module-aware expression translator config
        let mut config = self.expr_config.clone();
        config.variable_names = module.variables.iter().cloned().collect();
        config.constant_names = module.constants.iter().map(|c| c.name.clone()).collect();
        config.spec_prefix = self.config.spec_prefix.clone();
        // Classify operators as actions vs predicates vs constants (multi-pass)
        // Pass 1: direct prime usage + variable reference check
        for op in &module.operators {
            config.operator_arity.insert(op.name.clone(), op.params.len());
            let op_param_names: Vec<String> = op.params.iter().map(|p| p.name.clone()).collect();
            let kind = if op.name.eq_ignore_ascii_case("init") {
                OperatorKind::Predicate
            } else if self.operator_uses_primes(&op.body)
                || operator_has_explicit_next_state_param(op)
            {
                OperatorKind::Action
            } else if !self.operator_refs_declared_variables(
                &op.body,
                &op_param_names,
                &module_var_names,
            ) {
                OperatorKind::ConstantOp
            } else {
                OperatorKind::Predicate
            };
            config.operator_info.insert(op.name.clone(), kind);
        }
        // Pass 2: propagate operator kinds through references
        // If operator A references operator B which is Action, then A is also Action
        // If a ConstantOp references a Predicate or Action, promote it accordingly
        let op_names: Vec<String> = module.operators.iter().map(|o| o.name.clone()).collect();
        let mut changed = true;
        while changed {
            changed = false;
            for op in &module.operators {
                if op.name.eq_ignore_ascii_case("init") {
                    continue;
                }
                let current = config.operator_info.get(&op.name).cloned();
                match current {
                    Some(OperatorKind::Predicate) => {
                        if self.expr_refs_action_operators(
                            &op.body,
                            &config.operator_info,
                            &op_names,
                        ) {
                            config
                                .operator_info
                                .insert(op.name.clone(), OperatorKind::Action);
                            changed = true;
                        }
                    }
                    Some(OperatorKind::ConstantOp) => {
                        // Promote ConstantOp to Action if it references Action operators
                        if self.expr_refs_action_operators(
                            &op.body,
                            &config.operator_info,
                            &op_names,
                        ) {
                            config
                                .operator_info
                                .insert(op.name.clone(), OperatorKind::Action);
                            changed = true;
                        } else if self.expr_refs_predicate_operators(
                            &op.body,
                            &config.operator_info,
                            &op_names,
                        ) {
                            config
                                .operator_info
                                .insert(op.name.clone(), OperatorKind::Predicate);
                            changed = true;
                        }
                    }
                    _ => {}
                }
            }
        }
        let expr_translator = ExprTranslator::new(&config);

        for op in &module.operators {
            output.push_str(&self.generate_spec_function(
                op,
                &state_name,
                &expr_translator,
                module,
                &module_var_names,
            ));
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
        module: &TlaModule,
        module_var_names: &std::collections::HashSet<String>,
    ) -> String {
        let mut output = String::new();
        let fn_name = self.config.spec_fn_name(&op.name);
        let mut identifier_type_hints = std::collections::HashMap::<String, String>::new();
        let mut constant_field_type_hints = std::collections::HashMap::<String, String>::new();
        for constant in &module.constants {
            let constant_ty = self.get_constant_type(module, &constant.name);
            constant_field_type_hints.insert(constant.name.clone(), constant_ty.clone());
            let safe_name = safe_field_name(&constant.name);
            if safe_name != constant.name {
                constant_field_type_hints.insert(safe_name, constant_ty);
            }
        }

        // Detect if this is an action (uses primed variables, directly or transitively)
        let is_action =
            expr_translator.config.operator_info.get(&op.name) == Some(&OperatorKind::Action);
        let is_strict_init = op.name.eq_ignore_ascii_case("init");

        // Build parameter list
        let mut params = Vec::new();
        let mut used_param_names = std::collections::HashSet::<String>::new();

        // Add state parameter if operator references variables (directly or transitively)
        let op_param_names: Vec<String> = op.params.iter().map(|p| p.name.clone()).collect();
        let refs_vars =
            self.operator_refs_declared_variables(&op.body, &op_param_names, module_var_names);
        // Actions always get s and s_ params (they transitively reference state through sub-operators)
        if refs_vars || is_action {
            params.push(format!("s: {}", state_name));
            used_param_names.insert("s".to_string());
            identifier_type_hints.insert("s".to_string(), state_name.to_string());
            if is_action && !is_strict_init {
                params.push(format!("s_: {}", state_name));
                used_param_names.insert("s_".to_string());
                identifier_type_hints.insert("s_".to_string(), state_name.to_string());
            }
        }

        // Add constants parameter if module has constants
        // (simpler than per-function tracking; all functions get c to allow operator cross-references)
        if !module.constants.is_empty() {
            let const_struct = format!("{}Constants", self.config.spec_prefix);
            params.push(format!("c: {}", const_struct));
            used_param_names.insert("c".to_string());
            identifier_type_hints.insert("c".to_string(), const_struct);
        }

        // Add operator parameters
        for (param_idx, param) in op.params.iter().enumerate() {
            // D1 round-trip can emit explicit params named s/s_/c even though those are
            // already auto-injected; skip duplicates to keep signatures parseable.
            if used_param_names.contains(&param.name) {
                continue;
            }
            let param_type =
                self.get_param_type(op, param_idx, &param.name, module.variables.is_empty());
            params.push(format!("{}: {}", param.name, param_type));
            identifier_type_hints.insert(param.name.clone(), param_type.clone());
            used_param_names.insert(param.name.clone());
        }

        // Determine return type
        let mut return_type = self.get_operator_return_type(&op.name);
        if module.variables.is_empty() && (return_type == "int" || return_type == "()") {
            if let Some(inferred_return_ty) =
                self.infer_generated_d1_return_type_from_expr(&op.body, &identifier_type_hints)
            {
                return_type = inferred_return_ty;
            }
        }

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
        let mut function_expr_config = expr_translator.config.clone();
        function_expr_config
            .identifier_type_hints
            .extend(identifier_type_hints);
        function_expr_config
            .constant_field_type_hints
            .extend(constant_field_type_hints);
        let function_expr_translator = ExprTranslator::new(&function_expr_config);
        let body = function_expr_translator.translate(&op.body);
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
                    || updates.iter().any(|u| self.operator_uses_primes(&u.value))
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

    /// Check if an expression references any operator classified as Action
    fn expr_refs_action_operators(
        &self,
        expr: &TlaExpr,
        operator_info: &std::collections::HashMap<String, OperatorKind>,
        _op_names: &[String],
    ) -> bool {
        match expr {
            TlaExpr::Ident(name) => operator_info.get(name) == Some(&OperatorKind::Action),
            TlaExpr::BinOp { left, right, .. } => {
                self.expr_refs_action_operators(left, operator_info, _op_names)
                    || self.expr_refs_action_operators(right, operator_info, _op_names)
            }
            TlaExpr::UnaryOp { operand, .. } => {
                self.expr_refs_action_operators(operand, operator_info, _op_names)
            }
            TlaExpr::OpApply { op, args } => {
                self.expr_refs_action_operators(op, operator_info, _op_names)
                    || args
                        .iter()
                        .any(|a| self.expr_refs_action_operators(a, operator_info, _op_names))
            }
            _ => false,
        }
    }

    /// Check if an expression references Predicate or Action operators (needs state params)
    fn expr_refs_predicate_operators(
        &self,
        expr: &TlaExpr,
        operator_info: &std::collections::HashMap<String, OperatorKind>,
        _op_names: &[String],
    ) -> bool {
        match expr {
            TlaExpr::Ident(name) => matches!(
                operator_info.get(name),
                Some(&OperatorKind::Predicate) | Some(&OperatorKind::Action)
            ),
            TlaExpr::BinOp { left, right, .. } => {
                self.expr_refs_predicate_operators(left, operator_info, _op_names)
                    || self.expr_refs_predicate_operators(right, operator_info, _op_names)
            }
            TlaExpr::UnaryOp { operand, .. } => {
                self.expr_refs_predicate_operators(operand, operator_info, _op_names)
            }
            TlaExpr::OpApply { op, args } => {
                self.expr_refs_predicate_operators(op, operator_info, _op_names)
                    || args
                        .iter()
                        .any(|a| self.expr_refs_predicate_operators(a, operator_info, _op_names))
            }
            _ => false,
        }
    }

    /// Check if an expression references declared module variables.
    /// Unlike `operator_refs_variables`, this does not treat every unknown
    /// non-local identifier as a state variable when type info is absent.
    fn operator_refs_declared_variables(
        &self,
        expr: &TlaExpr,
        local_vars: &[String],
        module_vars: &std::collections::HashSet<String>,
    ) -> bool {
        use crate::tla::ast::TlaExpr;
        match expr {
            TlaExpr::Ident(name) => !local_vars.contains(name) && module_vars.contains(name),
            TlaExpr::Prime(_) => true, // Primed variables always reference state
            TlaExpr::Number(_) | TlaExpr::String(_) | TlaExpr::Bool(_) => false,
            TlaExpr::BinOp { left, right, .. } => {
                self.operator_refs_declared_variables(left, local_vars, module_vars)
                    || self.operator_refs_declared_variables(right, local_vars, module_vars)
            }
            TlaExpr::UnaryOp { operand, .. } => {
                self.operator_refs_declared_variables(operand, local_vars, module_vars)
            }
            TlaExpr::OpApply { op, args } => {
                let op_refs_vars = match op.as_ref() {
                    // Operator names are not module state variables.
                    TlaExpr::Ident(_) => false,
                    _ => self.operator_refs_declared_variables(op, local_vars, module_vars),
                };
                op_refs_vars
                    || args
                        .iter()
                        .any(|a| self.operator_refs_declared_variables(a, local_vars, module_vars))
            }
            TlaExpr::FnApply { func, arg } => {
                self.operator_refs_declared_variables(func, local_vars, module_vars)
                    || self.operator_refs_declared_variables(arg, local_vars, module_vars)
            }
            TlaExpr::SetEnum(elems) => elems
                .iter()
                .any(|e| self.operator_refs_declared_variables(e, local_vars, module_vars)),
            TlaExpr::SetFilter { var, set, filter } => {
                let mut locals = local_vars.to_vec();
                locals.push(var.clone());
                self.operator_refs_declared_variables(set, local_vars, module_vars)
                    || self.operator_refs_declared_variables(filter, &locals, module_vars)
            }
            TlaExpr::SetMap { expr: e, var, set } => {
                let mut locals = local_vars.to_vec();
                locals.push(var.clone());
                self.operator_refs_declared_variables(set, local_vars, module_vars)
                    || self.operator_refs_declared_variables(e, &locals, module_vars)
            }
            TlaExpr::FnConstruct { var, domain, body } => {
                let mut locals = local_vars.to_vec();
                locals.push(var.clone());
                self.operator_refs_declared_variables(domain, local_vars, module_vars)
                    || self.operator_refs_declared_variables(body, &locals, module_vars)
            }
            TlaExpr::FnExcept { func, updates } => {
                self.operator_refs_declared_variables(func, local_vars, module_vars)
                    || updates.iter().any(|u| {
                        self.operator_refs_declared_variables(&u.value, local_vars, module_vars)
                    })
            }
            TlaExpr::Record(fields) => fields
                .iter()
                .any(|(_, v)| self.operator_refs_declared_variables(v, local_vars, module_vars)),
            TlaExpr::RecordAccess { record, .. } => {
                self.operator_refs_declared_variables(record, local_vars, module_vars)
            }
            TlaExpr::Enabled(inner) | TlaExpr::Always(inner) | TlaExpr::Eventually(inner) => {
                self.operator_refs_declared_variables(inner, local_vars, module_vars)
            }
            TlaExpr::Tuple(elems) => elems
                .iter()
                .any(|e| self.operator_refs_declared_variables(e, local_vars, module_vars)),
            TlaExpr::IfThenElse {
                cond,
                then_expr,
                else_expr,
            } => {
                self.operator_refs_declared_variables(cond, local_vars, module_vars)
                    || self.operator_refs_declared_variables(then_expr, local_vars, module_vars)
                    || self.operator_refs_declared_variables(else_expr, local_vars, module_vars)
            }
            TlaExpr::Case { arms, other } => {
                arms.iter().any(|(cond, body)| {
                    self.operator_refs_declared_variables(cond, local_vars, module_vars)
                        || self.operator_refs_declared_variables(body, local_vars, module_vars)
                }) || other.as_ref().is_some_and(|e| {
                    self.operator_refs_declared_variables(e, local_vars, module_vars)
                })
            }
            TlaExpr::Forall { vars, body } | TlaExpr::Exists { vars, body } => {
                let mut locals = local_vars.to_vec();
                for qb in vars {
                    locals.push(qb.var.clone());
                }
                vars.iter().any(|qb| {
                    qb.set.as_ref().is_some_and(|s| {
                        self.operator_refs_declared_variables(s, local_vars, module_vars)
                    })
                }) || self.operator_refs_declared_variables(body, &locals, module_vars)
            }
            TlaExpr::Choose { var, set, body } => {
                let mut locals = local_vars.to_vec();
                locals.push(var.clone());
                set.as_ref().is_some_and(|s| {
                    self.operator_refs_declared_variables(s, local_vars, module_vars)
                }) || self.operator_refs_declared_variables(body, &locals, module_vars)
            }
            TlaExpr::LetIn { defs, body } => {
                let mut locals = local_vars.to_vec();
                for def in defs {
                    locals.push(def.name.clone());
                }
                defs.iter().any(|d| {
                    self.operator_refs_declared_variables(&d.body, local_vars, module_vars)
                }) || self.operator_refs_declared_variables(body, &locals, module_vars)
            }
            TlaExpr::LeadsTo { left, right } => {
                self.operator_refs_declared_variables(left, local_vars, module_vars)
                    || self.operator_refs_declared_variables(right, local_vars, module_vars)
            }
            TlaExpr::WeakFairness { vars, action } | TlaExpr::StrongFairness { vars, action } => {
                self.operator_refs_declared_variables(vars, local_vars, module_vars)
                    || self.operator_refs_declared_variables(action, local_vars, module_vars)
            }
            TlaExpr::Unchanged(vars) => vars
                .iter()
                .any(|v| self.operator_refs_declared_variables(v, local_vars, module_vars)),
            _ => false,
        }
    }

    /// Get the Verus type for a variable
    fn get_variable_type(&self, var_name: &str) -> String {
        if let Some(env) = &self.type_env {
            if let Some(ty) = env.variables.get(var_name) {
                return ty.to_verus_type_with_records(&self.expr_config.record_structs);
            }
        }
        // Default to spec type comment
        format!("/* {} type */ int", var_name)
    }

    /// Get the Verus type for a constant
    fn get_constant_type(&self, module: &TlaModule, const_name: &str) -> String {
        let generated_d1_context =
            self.expr_config.normalize_unknown_external_refs && module.variables.is_empty();
        if let Some(env) = &self.type_env {
            if let Some(ty) = env.constants.get(const_name) {
                let inferred = ty.to_verus_type_with_records(&self.expr_config.record_structs);
                if inferred != "int" {
                    return inferred;
                }
                if generated_d1_context {
                    if let Some(hint) =
                        self.infer_constant_type_hint_from_module_usage(module, const_name)
                    {
                        return hint.to_string();
                    }
                }
                return inferred;
            }
        }
        if generated_d1_context {
            if let Some(hint) = self.infer_constant_type_hint_from_module_usage(module, const_name)
            {
                return hint.to_string();
            }
        }
        // Default to spec type comment
        format!("/* {} type */ int", const_name)
    }

    /// Get the Verus type for a parameter
    fn get_param_type(
        &self,
        op: &TlaOperator,
        param_index: usize,
        param_name: &str,
        generated_d1_context: bool,
    ) -> String {
        let usage_hint = if self.expr_config.normalize_unknown_external_refs && generated_d1_context
        {
            self.infer_identifier_type_hint_from_usage(&op.body, param_name)
        } else {
            None
        };

        if let Some(env) = &self.type_env {
            if let Some(TlaType::Function { domain, .. }) = env.operators.get(&op.name) {
                let param_ty = match domain.as_ref() {
                    TlaType::Tuple(elements) => elements.get(param_index),
                    _ if param_index == 0 => Some(domain.as_ref()),
                    _ => None,
                };
                if let Some(param_ty) = param_ty {
                    let inferred =
                        param_ty.to_verus_type_with_records(&self.expr_config.record_structs);
                    if inferred != "int" {
                        if generated_d1_context
                            && inferred == "bool"
                            && usage_hint == Some("int")
                        {
                            return "int".to_string();
                        }
                        return inferred;
                    }
                    if let Some(hint) = usage_hint {
                        return hint.to_string();
                    }
                    return inferred;
                }
            }
        }
        if let Some(hint) = usage_hint {
            return hint.to_string();
        }
        // Fallback when inference is unavailable or unresolved.
        let _ = param_name;
        "int".to_string()
    }

    fn infer_constant_type_hint_from_module_usage(
        &self,
        module: &TlaModule,
        const_name: &str,
    ) -> Option<&'static str> {
        let mut evidence = UsageHintEvidence::default();
        for op in &module.operators {
            evidence = evidence.merge(self.collect_identifier_usage_evidence(&op.body, const_name));
        }
        evidence.to_hint()
    }

    fn infer_identifier_type_hint_from_usage(
        &self,
        expr: &TlaExpr,
        ident_name: &str,
    ) -> Option<&'static str> {
        self.collect_identifier_usage_evidence(expr, ident_name)
            .to_hint()
    }

    fn collect_identifier_usage_evidence(
        &self,
        expr: &TlaExpr,
        ident_name: &str,
    ) -> UsageHintEvidence {
        let is_target_ident = |node: &TlaExpr| match node {
            TlaExpr::Ident(name) => name == ident_name,
            _ => false,
        };

        match expr {
            TlaExpr::BinOp { op, left, right } => {
                let mut evidence = self
                    .collect_identifier_usage_evidence(left, ident_name)
                    .merge(self.collect_identifier_usage_evidence(right, ident_name));
                let left_is_target = is_target_ident(left);
                let right_is_target = is_target_ident(right);
                if matches!(op, TlaBinOp::In | TlaBinOp::NotIn) && is_target_ident(right) {
                    evidence.set_membership = true;
                }
                if matches!(op, TlaBinOp::In | TlaBinOp::NotIn) && is_target_ident(left) {
                    evidence.set_element_usage = true;
                }
                if left_is_target || right_is_target {
                    match op {
                        TlaBinOp::Plus
                        | TlaBinOp::Minus
                        | TlaBinOp::Times
                        | TlaBinOp::Div
                        | TlaBinOp::Mod
                        | TlaBinOp::Lt
                        | TlaBinOp::Leq
                        | TlaBinOp::Gt
                        | TlaBinOp::Geq => {
                            evidence.scalar_usage = true;
                        }
                        TlaBinOp::Eq | TlaBinOp::Neq => {
                            let other = if left_is_target {
                                right.as_ref()
                            } else {
                                left.as_ref()
                            };
                            if matches!(
                                other,
                                TlaExpr::Number(_) | TlaExpr::Bool(_) | TlaExpr::String(_)
                            ) {
                                evidence.scalar_usage = true;
                            }
                        }
                        _ => {}
                    }
                }
                evidence
            }
            TlaExpr::UnaryOp { op, operand } => {
                let mut evidence = self.collect_identifier_usage_evidence(operand, ident_name);
                if matches!(op, TlaUnaryOp::Domain) && is_target_ident(operand) {
                    evidence.map_domain = true;
                } else if matches!(op, TlaUnaryOp::Neg) && is_target_ident(operand) {
                    evidence.scalar_usage = true;
                }
                evidence
            }
            TlaExpr::OpApply { op, args } => {
                let mut evidence = self.collect_identifier_usage_evidence(op, ident_name);
                for arg in args {
                    evidence = evidence.merge(self.collect_identifier_usage_evidence(arg, ident_name));
                }

                let op_name = match op.as_ref() {
                    TlaExpr::Ident(name) => Some(name.as_str()),
                    _ => None,
                };
                let first_is_target = args.first().is_some_and(is_target_ident);
                if first_is_target {
                    match op_name {
                        Some("Cardinality" | "IsFiniteSet") => {
                            evidence.set_membership = true;
                        }
                        Some("Len") => {
                            evidence.seq_len = true;
                        }
                        Some("DOMAIN") => {
                            evidence.map_domain = true;
                        }
                        Some("skip" | "drop_first" | "Tail" | "SubSeq" | "Append" | "Head"
                        | "update") => {
                            evidence.seq_index_like = true;
                        }
                        _ => {}
                    }
                }
                evidence
            }
            TlaExpr::FnApply { func, arg } => {
                let mut evidence = self
                    .collect_identifier_usage_evidence(func, ident_name)
                    .merge(self.collect_identifier_usage_evidence(arg, ident_name));
                if is_target_ident(func) {
                    evidence.seq_index_like = true;
                    evidence.map_index_like = true;
                }
                evidence
            }
            TlaExpr::SetFilter { set, filter, .. } => {
                let mut evidence = self
                    .collect_identifier_usage_evidence(set, ident_name)
                    .merge(self.collect_identifier_usage_evidence(filter, ident_name));
                if is_target_ident(set) {
                    evidence.set_membership = true;
                }
                evidence
            }
            TlaExpr::SetMap { expr, set, .. } => {
                let mut evidence = self
                    .collect_identifier_usage_evidence(expr, ident_name)
                    .merge(self.collect_identifier_usage_evidence(set, ident_name));
                if is_target_ident(set) {
                    evidence.set_membership = true;
                }
                evidence
            }
            TlaExpr::FnConstruct { domain, body, .. } => self
                .collect_identifier_usage_evidence(domain, ident_name)
                .merge(self.collect_identifier_usage_evidence(body, ident_name)),
            TlaExpr::FnExcept { func, updates } => {
                let mut evidence = self.collect_identifier_usage_evidence(func, ident_name);
                if is_target_ident(func) {
                    evidence.map_index_like = true;
                }
                for update in updates {
                    evidence = evidence
                        .merge(self.collect_identifier_usage_evidence(&update.value, ident_name));
                }
                evidence
            }
            TlaExpr::Forall { vars, body } | TlaExpr::Exists { vars, body } => {
                let mut evidence = self.collect_identifier_usage_evidence(body, ident_name);
                for bound in vars {
                    if let Some(set) = &bound.set {
                        evidence =
                            evidence.merge(self.collect_identifier_usage_evidence(set, ident_name));
                        if is_target_ident(set) {
                            evidence.set_membership = true;
                        }
                    }
                }
                evidence
            }
            TlaExpr::Choose { set, body, .. } => {
                let mut evidence = self.collect_identifier_usage_evidence(body, ident_name);
                if let Some(set) = set {
                    evidence = evidence.merge(self.collect_identifier_usage_evidence(set, ident_name));
                    if is_target_ident(set) {
                        evidence.set_membership = true;
                    }
                }
                evidence
            }
            TlaExpr::IfThenElse {
                cond,
                then_expr,
                else_expr,
            } => self
                .collect_identifier_usage_evidence(cond, ident_name)
                .merge(self.collect_identifier_usage_evidence(then_expr, ident_name))
                .merge(self.collect_identifier_usage_evidence(else_expr, ident_name)),
            TlaExpr::Case { arms, other } => {
                let mut evidence = UsageHintEvidence::default();
                for (cond, arm_body) in arms {
                    evidence = evidence
                        .merge(self.collect_identifier_usage_evidence(cond, ident_name))
                        .merge(self.collect_identifier_usage_evidence(arm_body, ident_name));
                }
                if let Some(other_expr) = other {
                    evidence =
                        evidence.merge(self.collect_identifier_usage_evidence(other_expr, ident_name));
                }
                evidence
            }
            TlaExpr::LetIn { defs, body } => {
                let mut evidence = self.collect_identifier_usage_evidence(body, ident_name);
                for def in defs {
                    evidence =
                        evidence.merge(self.collect_identifier_usage_evidence(&def.body, ident_name));
                }
                evidence
            }
            TlaExpr::SetEnum(elements) | TlaExpr::Tuple(elements) | TlaExpr::Unchanged(elements) => {
                let mut evidence = UsageHintEvidence::default();
                for element in elements {
                    if is_target_ident(element) {
                        evidence.set_element_usage = true;
                    }
                    evidence =
                        evidence.merge(self.collect_identifier_usage_evidence(element, ident_name));
                }
                evidence
            }
            TlaExpr::Record(fields) => {
                let mut evidence = UsageHintEvidence::default();
                for (_, value) in fields {
                    if is_target_ident(value) {
                        evidence.scalar_usage = true;
                    }
                    evidence = evidence.merge(self.collect_identifier_usage_evidence(value, ident_name));
                }
                evidence
            }
            TlaExpr::RecordAccess { record, .. }
            | TlaExpr::Prime(record)
            | TlaExpr::Enabled(record)
            | TlaExpr::Always(record)
            | TlaExpr::Eventually(record) => {
                self.collect_identifier_usage_evidence(record, ident_name)
            }
            TlaExpr::LeadsTo { left, right } => self
                .collect_identifier_usage_evidence(left, ident_name)
                .merge(self.collect_identifier_usage_evidence(right, ident_name)),
            TlaExpr::WeakFairness { vars, action } | TlaExpr::StrongFairness { vars, action } => self
                .collect_identifier_usage_evidence(vars, ident_name)
                .merge(self.collect_identifier_usage_evidence(action, ident_name)),
            _ => UsageHintEvidence::default(),
        }
    }

    /// Get the return type for an operator
    fn get_operator_return_type(&self, op_name: &str) -> String {
        if let Some(env) = &self.type_env {
            if let Some(ty) = env.operators.get(op_name) {
                // Extract return type from function type
                if let TlaType::Function { range, .. } = ty {
                    return range.to_verus_type_with_records(&self.expr_config.record_structs);
                }
                return ty.to_verus_type_with_records(&self.expr_config.record_structs);
            }
        }
        // Default: most operators return bool
        "bool".to_string()
    }

    fn infer_generated_d1_return_type_from_expr(
        &self,
        expr: &TlaExpr,
        identifier_type_hints: &std::collections::HashMap<String, String>,
    ) -> Option<String> {
        match expr {
            TlaExpr::Ident(name) => identifier_type_hints.get(name).cloned(),
            TlaExpr::Prime(inner)
            | TlaExpr::Enabled(inner)
            | TlaExpr::Always(inner)
            | TlaExpr::Eventually(inner) => {
                self.infer_generated_d1_return_type_from_expr(inner, identifier_type_hints)
            }
            TlaExpr::IfThenElse {
                then_expr,
                else_expr,
                ..
            } => {
                let lhs =
                    self.infer_generated_d1_return_type_from_expr(then_expr, identifier_type_hints);
                let rhs =
                    self.infer_generated_d1_return_type_from_expr(else_expr, identifier_type_hints);
                if lhs.is_some() && lhs == rhs {
                    lhs
                } else if lhs.is_some()
                    && rhs.is_none()
                    && matches!(lhs.as_deref(), Some("Seq<int>" | "Set<int>"))
                {
                    lhs
                } else if rhs.is_some()
                    && lhs.is_none()
                    && matches!(rhs.as_deref(), Some("Seq<int>" | "Set<int>"))
                {
                    rhs
                } else {
                    None
                }
            }
            TlaExpr::LetIn { body, .. } => {
                self.infer_generated_d1_return_type_from_expr(body, identifier_type_hints)
            }
            TlaExpr::SetEnum(_) => Some("Set<int>".to_string()),
            TlaExpr::Tuple(_) => Some("Seq<int>".to_string()),
            TlaExpr::BinOp { op, left, right } => match op {
                TlaBinOp::Cup | TlaBinOp::Cap | TlaBinOp::Setminus => Some("Set<int>".to_string()),
                TlaBinOp::Plus => {
                    let lhs =
                        self.infer_generated_d1_return_type_from_expr(left, identifier_type_hints);
                    let rhs =
                        self.infer_generated_d1_return_type_from_expr(right, identifier_type_hints);
                    if matches!(lhs.as_deref(), Some("Seq<int>"))
                        || matches!(rhs.as_deref(), Some("Seq<int>"))
                    {
                        Some("Seq<int>".to_string())
                    } else {
                        None
                    }
                }
                _ => None,
            },
            TlaExpr::OpApply { op, .. } => match op.as_ref() {
                TlaExpr::Ident(name) => match name.as_str() {
                    "SubSeq" | "Append" | "Tail" | "drop_first" | "drop_last" | "skip"
                    | "update" => Some("Seq<int>".to_string()),
                    "DOMAIN" | "SetUnion" | "SetIntersect" | "SetMinus" => {
                        Some("Set<int>".to_string())
                    }
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }
}

/// Translate a TLA+ module to Verus code
pub fn translate_module(module: &TlaModule) -> String {
    let mut translator = ModuleTranslator::new();
    translator.translate(module)
}

/// Translate a TLA+ module with type inference
pub fn translate_module_with_types(module: &TlaModule) -> String {
    let mut inference = TypeInference::new();
    let type_env = inference.infer_types(module);

    let mut translator = ModuleTranslator::new().with_types(type_env);
    translator.translate(module)
}

// =============================================================================
// Mode Annotation Generation (T6.4)
// =============================================================================

// Re-export the canonical ParameterMode from the AST module
pub use crate::ast::ParameterMode;

/// Mode annotation for an operator
#[derive(Debug, Clone)]
pub struct OperatorModes {
    /// Operator name
    pub name: String,
    /// Mode for each parameter
    pub modes: Vec<ParameterMode>,
    /// Optional description
    pub description: Option<String>,
    /// Whether this is a helper function (non-bool return type)
    pub is_helper: bool,
}

impl OperatorModes {
    /// Create a new operator mode annotation
    pub fn new(name: impl Into<String>, modes: Vec<ParameterMode>) -> Self {
        Self {
            name: name.into(),
            modes,
            description: None,
            is_helper: false,
        }
    }

    /// Mark as helper function
    pub fn as_helper(mut self) -> Self {
        self.is_helper = true;
        self
    }

    /// Add a description
    pub fn with_description(mut self, desc: impl Into<String>) -> Self {
        self.description = Some(desc.into());
        self
    }

    /// Format as automan annotation line
    pub fn to_automan_line(&self) -> String {
        let modes_str: Vec<_> = self.modes.iter().map(|m| m.to_string()).collect();
        let prefix = if self.is_helper {
            "    helper "
        } else {
            "    "
        };
        if let Some(desc) = &self.description {
            format!(
                "{}{}({});  // {}",
                prefix,
                self.name,
                modes_str.join(", "),
                desc
            )
        } else {
            format!("{}{}({});", prefix, self.name, modes_str.join(", "))
        }
    }
}

/// Generates mode annotations for a TLA+ module
pub struct ModeAnnotationGenerator {
    /// Module configuration (for prefixes)
    pub config: ModuleConfig,
}

impl Default for ModeAnnotationGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl ModeAnnotationGenerator {
    /// Create a new mode annotation generator
    pub fn new() -> Self {
        Self {
            config: ModuleConfig::default(),
        }
    }

    /// Create with custom configuration
    pub fn with_config(config: ModuleConfig) -> Self {
        Self { config }
    }

    /// Generate mode annotations for a TLA+ module
    pub fn generate(&self, module: &TlaModule) -> String {
        let mut output = String::new();
        let module_name = &module.name;
        let mut inference = TypeInference::new();
        let inferred = inference.infer_types(module);
        let resolved = inference.resolve_with_fallback(&inferred);
        let refs_helper = ModuleTranslator::new().with_types(resolved);

        // Pre-compute transitive action classification (same logic as ModuleTranslator)
        let mut operator_info: std::collections::HashMap<String, OperatorKind> =
            std::collections::HashMap::new();
        for op in &module.operators {
            let kind = if op.name.eq_ignore_ascii_case("init") {
                OperatorKind::Predicate
            } else if self.operator_uses_primes(&op.body)
                || operator_has_explicit_next_state_param(op)
            {
                OperatorKind::Action
            } else if !Self::body_refs_variables(&op.body, &module.variables) {
                OperatorKind::ConstantOp
            } else {
                OperatorKind::Predicate
            };
            operator_info.insert(op.name.clone(), kind);
        }
        // Propagate operator kinds through references
        let mut changed = true;
        while changed {
            changed = false;
            for op in &module.operators {
                if op.name.eq_ignore_ascii_case("init") {
                    continue;
                }
                let current = operator_info.get(&op.name).cloned();
                match current {
                    Some(OperatorKind::Predicate) => {
                        if Self::expr_refs_action_ops(&op.body, &operator_info) {
                            operator_info.insert(op.name.clone(), OperatorKind::Action);
                            changed = true;
                        }
                    }
                    Some(OperatorKind::ConstantOp) => {
                        if Self::expr_refs_action_ops(&op.body, &operator_info) {
                            operator_info.insert(op.name.clone(), OperatorKind::Action);
                            changed = true;
                        } else if Self::expr_refs_predicate_ops(&op.body, &operator_info) {
                            operator_info.insert(op.name.clone(), OperatorKind::Predicate);
                            changed = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        // Header
        output.push_str(&format!("// Mode annotations for {}.rs\n", module_name));
        output
            .push_str("// Format: FunctionName(mode1, mode2, ...) where + = input, - = output\n\n");

        // Module block
        output.push_str(&format!("module {} {{\n", module_name));

        // Generate annotations for each operator
        for op in &module.operators {
            let annotation = self.analyze_operator(op, module, &operator_info, &refs_helper);
            output.push_str(&annotation.to_automan_line());
            output.push('\n');
        }

        output.push_str("}\n");

        output
    }

    /// Check if an expression references any action operator (static helper)
    fn expr_refs_action_ops(
        expr: &TlaExpr,
        operator_info: &std::collections::HashMap<String, OperatorKind>,
    ) -> bool {
        match expr {
            TlaExpr::Ident(name) => operator_info.get(name) == Some(&OperatorKind::Action),
            TlaExpr::BinOp { left, right, .. } => {
                Self::expr_refs_action_ops(left, operator_info)
                    || Self::expr_refs_action_ops(right, operator_info)
            }
            TlaExpr::UnaryOp { operand, .. } => Self::expr_refs_action_ops(operand, operator_info),
            TlaExpr::OpApply { op, args } => {
                Self::expr_refs_action_ops(op, operator_info)
                    || args
                        .iter()
                        .any(|a| Self::expr_refs_action_ops(a, operator_info))
            }
            _ => false,
        }
    }

    fn expr_refs_predicate_ops(
        expr: &TlaExpr,
        operator_info: &std::collections::HashMap<String, OperatorKind>,
    ) -> bool {
        match expr {
            TlaExpr::Ident(name) => matches!(
                operator_info.get(name),
                Some(&OperatorKind::Predicate) | Some(&OperatorKind::Action)
            ),
            TlaExpr::BinOp { left, right, .. } => {
                Self::expr_refs_predicate_ops(left, operator_info)
                    || Self::expr_refs_predicate_ops(right, operator_info)
            }
            TlaExpr::UnaryOp { operand, .. } => {
                Self::expr_refs_predicate_ops(operand, operator_info)
            }
            TlaExpr::OpApply { op, args } => {
                Self::expr_refs_predicate_ops(op, operator_info)
                    || args
                        .iter()
                        .any(|a| Self::expr_refs_predicate_ops(a, operator_info))
            }
            _ => false,
        }
    }

    /// Analyze an operator to determine parameter modes
    fn analyze_operator(
        &self,
        op: &TlaOperator,
        module: &TlaModule,
        operator_info: &std::collections::HashMap<String, OperatorKind>,
        refs_helper: &ModuleTranslator,
    ) -> OperatorModes {
        let fn_name = self.config.spec_fn_name(&op.name);
        let mut modes = Vec::new();
        let mut desc_parts: Vec<String> = Vec::new();
        let mut used_param_names = std::collections::HashSet::<String>::new();

        // Check if this is an action (uses primed variables, directly or transitively)
        let is_action = operator_info.get(&op.name) == Some(&OperatorKind::Action);

        // Determine modes based on operator pattern.
        // Use strict init check: operator name must be exactly "Init" (case-insensitive)
        // to avoid false positives like "InitiateProbe" which is an action, not an init.
        let is_strict_init = op.name.eq_ignore_ascii_case("init");

        // Check if operator body references any module variables (constant operators skip s param)
        // Keep this in lock-step with spec signature generation.
        let op_param_names: Vec<String> = op.params.iter().map(|p| p.name.clone()).collect();
        let module_var_names: std::collections::HashSet<String> =
            module.variables.iter().cloned().collect();
        let refs_vars = refs_helper.operator_refs_declared_variables(
            &op.body,
            &op_param_names,
            &module_var_names,
        );

        if is_strict_init {
            // Init operators: state is output only
            modes.push(ParameterMode::Output);
            desc_parts.push("s is output (initialized state)".to_string());
            used_param_names.insert("s".to_string());
        } else if is_action {
            // Action operators: s is input, s_ is output
            modes.push(ParameterMode::Input);
            desc_parts.push("s is input (current state)".to_string());
            used_param_names.insert("s".to_string());
            modes.push(ParameterMode::Output);
            desc_parts.push("s_ is output (next state)".to_string());
            used_param_names.insert("s_".to_string());
        } else if refs_vars {
            // Pure predicates: state is input
            modes.push(ParameterMode::Input);
            desc_parts.push("s is input (state to check)".to_string());
            used_param_names.insert("s".to_string());
        }
        // else: constant operator — no state parameter

        // Add constants parameter if module has constants
        if !module.constants.is_empty() {
            modes.push(ParameterMode::Input);
            desc_parts.push("c is input (constants)".to_string());
            used_param_names.insert("c".to_string());
        }

        // Add modes for explicit parameters - typically inputs
        for param in &op.params {
            // D1 round-trip may emit explicit params named s/s_/c even though those are
            // already auto-injected in generated signatures.
            if used_param_names.contains(&param.name) {
                continue;
            }
            // Check if parameter appears on left side of primed assignment (output)
            // For simplicity, treat all explicit params as inputs
            modes.push(ParameterMode::Input);
            desc_parts.push(format!("{} is input", param.name));
            used_param_names.insert(param.name.clone());
        }

        // Detect helper functions: operators that return non-boolean values
        // (e.g., Follower == "follower", Phase1a == "Phase1a")
        let is_helper = !is_action && !is_strict_init && Self::body_returns_non_bool(&op.body);

        let result = OperatorModes::new(fn_name, modes).with_description(desc_parts.join(", "));
        if is_helper {
            result.as_helper()
        } else {
            result
        }
    }

    /// Check if an expression body references any module state variables
    fn body_refs_variables(expr: &TlaExpr, variables: &[String]) -> bool {
        match expr {
            TlaExpr::Ident(name) => variables.contains(name),
            TlaExpr::Prime(_) => true,
            TlaExpr::Number(_) | TlaExpr::String(_) | TlaExpr::Bool(_) => false,
            TlaExpr::BinOp { left, right, .. } => {
                Self::body_refs_variables(left, variables)
                    || Self::body_refs_variables(right, variables)
            }
            TlaExpr::UnaryOp { operand, .. } => Self::body_refs_variables(operand, variables),
            TlaExpr::OpApply { op, args } => {
                Self::body_refs_variables(op, variables)
                    || args.iter().any(|a| Self::body_refs_variables(a, variables))
            }
            TlaExpr::FnApply { func, arg } => {
                Self::body_refs_variables(func, variables)
                    || Self::body_refs_variables(arg, variables)
            }
            TlaExpr::SetEnum(elems) => elems
                .iter()
                .any(|e| Self::body_refs_variables(e, variables)),
            TlaExpr::Record(fields) => fields
                .iter()
                .any(|(_, v)| Self::body_refs_variables(v, variables)),
            TlaExpr::RecordAccess { record, .. } => Self::body_refs_variables(record, variables),
            TlaExpr::Tuple(elems) => elems
                .iter()
                .any(|e| Self::body_refs_variables(e, variables)),
            _ => {
                // Conservative: assume unknown expressions might reference variables
                true
            }
        }
    }

    /// Check if an expression body returns a non-boolean value (string, number, etc.)
    fn body_returns_non_bool(expr: &TlaExpr) -> bool {
        match expr {
            TlaExpr::String(_) | TlaExpr::Number(_) => true,
            TlaExpr::SetEnum(_) | TlaExpr::Record(_) | TlaExpr::Tuple(_) => true,
            TlaExpr::IfThenElse {
                then_expr,
                else_expr,
                ..
            } => Self::body_returns_non_bool(then_expr) || Self::body_returns_non_bool(else_expr),
            _ => false,
        }
    }

    /// Check if an expression uses primed variables (same as ModuleTranslator)
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
                    || updates.iter().any(|u| self.operator_uses_primes(&u.value))
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
            TlaExpr::Unchanged(_) => true,
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
}

/// Generate mode annotations for a TLA+ module
pub fn generate_mode_annotations(module: &TlaModule) -> String {
    let generator = ModeAnnotationGenerator::new();
    generator.generate(module)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tla::ast::{TlaBinOp, TlaExpr, TlaQuantBound, TlaUnaryOp};
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
        assert_eq!(
            translator.translate(&TlaExpr::string("hello")),
            "\"hello\"@"
        );
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
    fn test_translate_in_with_not_operand_normalizes_to_not_contains_in_spec_mode() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::In,
            TlaExpr::unary(TlaUnaryOp::Not, TlaExpr::ident("x")),
            TlaExpr::ident("S"),
        );

        assert_eq!(translator.translate(&expr), "!S.contains(x)");
    }

    #[test]
    fn test_translate_in_with_rendered_not_operand_normalizes_in_generated_d1_context() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::In,
            TlaExpr::ident("!(opn)"),
            TlaExpr::unary(TlaUnaryOp::Domain, TlaExpr::ident("votes_")),
        );

        assert_eq!(translator.translate(&expr), "!votes_.dom().contains(opn)");
    }

    #[test]
    fn test_translate_in_with_rendered_not_operand_preserves_non_generated_context() {
        let mut config = TranslatorConfig::spec();
        config.variable_names.insert("x".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::In,
            TlaExpr::ident("!(opn)"),
            TlaExpr::unary(TlaUnaryOp::Domain, TlaExpr::ident("votes_")),
        );

        assert_eq!(translator.translate(&expr), "votes_.dom().contains(!(opn))");
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

        // {} → Set::<int>::empty()
        let expr = TlaExpr::SetEnum(vec![]);
        assert_eq!(translator.translate(&expr), "Set::<int>::empty()");

        // {1, 2, 3} → set![1, 2, 3]
        let expr = TlaExpr::SetEnum(vec![
            TlaExpr::number(1),
            TlaExpr::number(2),
            TlaExpr::number(3),
        ]);
        assert_eq!(translator.translate(&expr), "set![1, 2, 3]");
    }

    #[test]
    fn test_translate_empty_tuple_emits_typed_empty_seq() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);
        assert_eq!(translator.translate(&TlaExpr::Tuple(vec![])), "Seq::<int>::empty()");
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
    fn test_translate_quantifier_bounds_for_builtin_sets() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        let forall_int = TlaExpr::Forall {
            vars: vec![TlaQuantBound::new("x", TlaExpr::ident("Int"))],
            body: Box::new(TlaExpr::ident("P")),
        };
        let out_forall_int = translator.translate(&forall_int);
        assert!(out_forall_int.contains("forall |x| P"));
        assert!(!out_forall_int.contains("int.contains"));

        let exists_nat = TlaExpr::Exists {
            vars: vec![TlaQuantBound::new("x", TlaExpr::ident("Nat"))],
            body: Box::new(TlaExpr::ident("Q")),
        };
        let out_exists_nat = translator.translate(&exists_nat);
        assert!(out_exists_nat.contains("exists |x| (x >= 0) && Q"));

        let exists_seq = TlaExpr::Exists {
            vars: vec![TlaQuantBound::new(
                "p",
                TlaExpr::OpApply {
                    op: Box::new(TlaExpr::ident("Seq")),
                    args: vec![TlaExpr::ident("Packet")],
                },
            )],
            body: Box::new(TlaExpr::ident("R")),
        };
        let out_exists_seq = translator.translate(&exists_seq);
        assert!(out_exists_seq.contains("exists |p| R"));
        assert!(!out_exists_seq.contains("Seq(Packet).contains"));
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
    fn test_generated_d1_fn_apply_coerces_untyped_arbitrary_receiver_to_seq() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::FnApply {
            func: Box::new(TlaExpr::ident("states")),
            arg: Box::new(TlaExpr::number(0)),
        };
        assert_eq!(translator.translate(&expr), "arbitrary::<Seq<int>>()[0]");
    }

    #[test]
    fn test_non_generated_fn_apply_preserves_untyped_arbitrary_receiver() {
        let mut config = TranslatorConfig::spec();
        config.variable_names.insert("x".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::FnApply {
            func: Box::new(TlaExpr::ident("states")),
            arg: Box::new(TlaExpr::number(0)),
        };
        assert_eq!(translator.translate(&expr), "arbitrary()[0]");
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

        // update(s, i, x) → s.update(i, x)
        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("update")),
            args: vec![TlaExpr::ident("s"), TlaExpr::ident("i"), TlaExpr::ident("x")],
        };
        assert_eq!(translator.translate(&expr), "s.update(i, x)");

        // skip(s, 1) → s.skip(1)
        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("skip")),
            args: vec![TlaExpr::ident("s"), TlaExpr::number(1)],
        };
        assert_eq!(translator.translate(&expr), "s.skip(1)");

        // drop_first(s) → s.drop_first()
        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("drop_first")),
            args: vec![TlaExpr::ident("s")],
        };
        assert_eq!(translator.translate(&expr), "s.drop_first()");

        // drop_last(s) → s.subrange(0, s.len() - 1)
        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("drop_last")),
            args: vec![TlaExpr::ident("s")],
        };
        assert_eq!(translator.translate(&expr), "s.subrange(0, s.len() - 1)");

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

        // Last(s) → s[s.len() - 1]
        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("Last")),
            args: vec![TlaExpr::ident("s")],
        };
        assert_eq!(translator.translate(&expr), "s[s.len() - 1]");
    }

    #[test]
    fn test_generated_d1_len_coerces_untyped_arbitrary_receiver_to_seq() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("Len")),
            args: vec![TlaExpr::ident("states")],
        };
        assert_eq!(
            translator.translate(&expr),
            "(arbitrary::<Seq<int>>().len() as int)"
        );
    }

    #[test]
    fn test_translate_op_apply_module_operator_injects_implicit_state_args() {
        let mut config = TranslatorConfig::default();
        config.spec_prefix = "L".to_string();
        config.constant_names.insert("N".to_string());
        config
            .operator_info
            .insert("Helper".to_string(), OperatorKind::Predicate);
        let translator = ExprTranslator::new(&config);

        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("Helper")),
            args: vec![TlaExpr::number(1)],
        };
        assert_eq!(translator.translate(&expr), "LHelper(s, c, 1)");
    }

    #[test]
    fn test_translate_op_apply_module_operator_avoids_double_call_when_state_explicit() {
        let mut config = TranslatorConfig::default();
        config.spec_prefix = "L".to_string();
        config.constant_names.insert("N".to_string());
        config
            .operator_info
            .insert("Step".to_string(), OperatorKind::Action);
        let translator = ExprTranslator::new(&config);

        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("Step")),
            args: vec![
                TlaExpr::ident("s"),
                TlaExpr::ident("s_"),
                TlaExpr::ident("c"),
                TlaExpr::ident("x"),
            ],
        };
        assert_eq!(translator.translate(&expr), "LStep(s, s_, c, x)");
    }

    #[test]
    fn test_translate_op_apply_parameterized_operator_without_args_in_value_context() {
        let mut config = TranslatorConfig::spec();
        config.spec_prefix = "L".to_string();
        config.constant_names.insert("N".to_string());
        config
            .operator_info
            .insert("PrePrepare".to_string(), OperatorKind::Action);
        config.operator_arity.insert("PrePrepare".to_string(), 5);
        let translator = ExprTranslator::new(&config);

        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("PrePrepare")),
            args: vec![],
        };
        assert_eq!(
            translator.translate(&expr),
            symbolic_atom_to_int_literal("PrePrepare")
        );
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

        assert!(result.contains("(x >= 0)"));
        assert!(result.contains("(x == 0)"));
    }

    #[test]
    fn test_translate_with_rename() {
        let config = TranslatorConfig::default().with_rename("old_name", "new_name");
        let translator = ExprTranslator::new(&config);

        assert_eq!(
            translator.translate(&TlaExpr::ident("old_name")),
            "new_name"
        );
        assert_eq!(translator.translate(&TlaExpr::ident("other")), "other");
    }

    #[test]
    fn test_translate_unknown_symbolic_atom_to_stable_int_literal() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);
        let out = translator.translate(&TlaExpr::ident("Idle"));
        assert_eq!(out, symbolic_atom_to_int_literal("Idle"));
        assert!(out.ends_with("int"));
    }

    #[test]
    fn test_translate_head_identifier_as_symbolic_atom_when_not_applied() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);
        let out = translator.translate(&TlaExpr::ident("Head"));
        assert_eq!(out, symbolic_atom_to_int_literal("Head"));
    }

    #[test]
    fn test_translate_unknown_uppercase_operator_call_head_is_not_lowered() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("Seq")),
            args: vec![TlaExpr::ident("x")],
        };
        assert_eq!(translator.translate(&expr), "Seq(x)");
    }

    #[test]
    fn test_translate_unknown_lowercase_identifier_is_preserved() {
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);
        assert_eq!(translator.translate(&TlaExpr::ident("new_state")), "new_state");
    }

    #[test]
    fn test_translate_placeholder_identifier_fallback_in_spec_mode() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        assert_eq!(translator.translate(&TlaExpr::ident("new_state")), "arbitrary()");
        assert_eq!(translator.translate(&TlaExpr::ident("earnerState")), "arbitrary()");
    }

    #[test]
    fn test_translate_record_normalizes_builtin_type_tokens_in_value_context_spec_mode() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::Record(vec![
            ("a".to_string(), TlaExpr::ident("Int")),
            ("b".to_string(), TlaExpr::ident("Nat")),
            ("c".to_string(), TlaExpr::ident("BOOLEAN")),
        ]);
        let out = translator.translate(&expr);
        assert!(out.contains("a: arbitrary()"));
        assert!(out.contains("b: arbitrary()"));
        assert!(out.contains("c: arbitrary()"));
        assert!(!out.contains("a: int"));
        assert!(!out.contains("b: nat"));
        assert!(!out.contains("c: bool"));
    }

    #[test]
    fn test_translate_record_normalizes_constructor_style_type_sets_in_value_context_spec_mode() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::Record(vec![
            (
                "seq_field".to_string(),
                TlaExpr::OpApply {
                    op: Box::new(TlaExpr::ident("Seq")),
                    args: vec![TlaExpr::ident("T")],
                },
            ),
            (
                "map_field".to_string(),
                TlaExpr::OpApply {
                    op: Box::new(TlaExpr::ident("Map")),
                    args: vec![TlaExpr::ident("K"), TlaExpr::ident("V")],
                },
            ),
            (
                "fnset_field".to_string(),
                TlaExpr::FnSet {
                    domain: Box::new(TlaExpr::ident("D")),
                    range: Box::new(TlaExpr::ident("R")),
                },
            ),
        ]);
        let out = translator.translate(&expr);
        assert!(out.contains("seq_field: arbitrary()"));
        assert!(out.contains("map_field: arbitrary()"));
        assert!(out.contains("fnset_field: arbitrary()"));
        assert!(!out.contains("seq_field: Seq("));
        assert!(!out.contains("map_field: Map("));
        assert!(!out.contains("fnset_field: Map::<"));
    }

    #[test]
    fn test_translate_record_normalizes_module_operator_calls_in_value_context_spec_mode() {
        let mut config = TranslatorConfig::spec();
        config
            .operator_info
            .insert("OutstandingOperation".to_string(), OperatorKind::Predicate);
        config
            .operator_arity
            .insert("OutstandingOperation".to_string(), 1);
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::Record(vec![(
            "outstanding".to_string(),
            TlaExpr::OpApply {
                op: Box::new(TlaExpr::ident("OutstandingOperation")),
                args: vec![TlaExpr::ident("c")],
            },
        )]);
        let out = translator.translate(&expr);
        assert!(out.contains("outstanding: arbitrary()"));
        assert!(!out.contains("OutstandingOperation("));
    }

    #[test]
    fn test_translate_record_normalizes_module_operator_ident_in_value_context_spec_mode() {
        let mut config = TranslatorConfig::spec();
        config
            .operator_info
            .insert("Phase".to_string(), OperatorKind::ConstantOp);
        config.operator_arity.insert("Phase".to_string(), 0);
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::Record(vec![(
            "phase".to_string(),
            TlaExpr::ident("Phase"),
        )]);
        let out = translator.translate(&expr);
        assert!(out.contains("phase: arbitrary()"));
        assert!(!out.contains("LPhase"));
    }

    #[test]
    fn test_translate_record_preserves_module_operator_ident_when_module_has_state_vars() {
        let mut config = TranslatorConfig::spec();
        config.variable_names.insert("x".to_string());
        config
            .operator_info
            .insert("Phase".to_string(), OperatorKind::ConstantOp);
        config.operator_arity.insert("Phase".to_string(), 0);
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::Record(vec![(
            "phase".to_string(),
            TlaExpr::ident("Phase"),
        )]);
        let out = translator.translate(&expr);
        assert!(out.contains("phase: Phase()"));
        assert!(!out.contains("phase: arbitrary()"));
    }

    #[test]
    fn test_translate_record_normalizes_subset_unary_in_value_context_spec_mode() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::Record(vec![(
            "domain".to_string(),
            TlaExpr::UnaryOp {
                op: TlaUnaryOp::Subset,
                operand: Box::new(TlaExpr::ident("Int")),
            },
        )]);
        let out = translator.translate(&expr);
        assert!(out.contains("domain: arbitrary()"));
        assert!(!out.contains(".powerset()"));
    }

    #[test]
    fn test_translate_record_access_fallback_for_reserved_roots_without_variable_decls() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);

        let root_access = TlaExpr::RecordAccess {
            record: Box::new(TlaExpr::ident("s")),
            field: "foo".to_string(),
        };
        assert_eq!(translator.translate(&root_access), "arbitrary()");

        let nested_access = TlaExpr::RecordAccess {
            record: Box::new(TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("c")),
                field: "cfg".to_string(),
            }),
            field: "value".to_string(),
        };
        assert_eq!(translator.translate(&nested_access), "arbitrary()");
    }

    #[test]
    fn test_translate_record_access_preserves_when_variables_are_known() {
        let mut config = TranslatorConfig::spec();
        config.variable_names.insert("x".to_string());
        let translator = ExprTranslator::new(&config);
        let access = TlaExpr::RecordAccess {
            record: Box::new(TlaExpr::ident("x")),
            field: "value".to_string(),
        };
        assert_eq!(translator.translate(&access), "s.x.value");
    }

    #[test]
    fn test_translate_record_access_fallback_for_unknown_identifier_roots() {
        let mut config = TranslatorConfig::spec();
        config.variable_names.insert("known_state".to_string());
        let translator = ExprTranslator::new(&config);

        let unknown_root_access = TlaExpr::RecordAccess {
            record: Box::new(TlaExpr::ident("request")),
            field: "client".to_string(),
        };
        assert_eq!(translator.translate(&unknown_root_access), "arbitrary()");
    }

    #[test]
    fn test_generated_d1_binop_coerces_untyped_arbitrary_to_int_for_arithmetic() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::Plus,
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "seqno".to_string(),
            },
            TlaExpr::number(1),
        );
        assert_eq!(translator.translate(&expr), "(arbitrary::<int>() + 1)");
    }

    #[test]
    fn test_generated_d1_binop_coerces_untyped_arbitrary_set_receiver_for_membership() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::In,
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "id".to_string(),
            },
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("pending")),
                field: "requests".to_string(),
            },
        );
        assert_eq!(
            translator.translate(&expr),
            "Set::<int>::empty().contains(arbitrary::<int>())"
        );
    }

    #[test]
    fn test_non_generated_context_does_not_coerce_untyped_arbitrary_in_arithmetic() {
        let mut config = TranslatorConfig::spec();
        config.variable_names.insert("known_state".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::Plus,
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "seqno".to_string(),
            },
            TlaExpr::number(1),
        );
        assert_eq!(translator.translate(&expr), "(arbitrary() + 1)");
    }

    #[test]
    fn test_generated_d1_logical_ops_coerce_boolish_numeric_literals() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(TlaBinOp::And, TlaExpr::number(0), TlaExpr::bool(true));
        assert_eq!(translator.translate(&expr), "(false && true)");
    }

    #[test]
    fn test_logical_ops_coerce_boolish_numeric_literals_with_known_vars() {
        let mut config = TranslatorConfig::spec();
        config.variable_names.insert("known_state".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(TlaBinOp::And, TlaExpr::number(0), TlaExpr::bool(true));
        assert_eq!(translator.translate(&expr), "(false && true)");
    }

    #[test]
    fn test_exec_mode_does_not_coerce_boolish_numeric_literals() {
        let config = TranslatorConfig::exec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(TlaBinOp::And, TlaExpr::number(0), TlaExpr::bool(true));
        assert_eq!(translator.translate(&expr), "(0 && true)");
    }

    #[test]
    fn test_generated_d1_tuple_with_record_falls_back_to_arbitrary() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::Tuple(vec![
            TlaExpr::number(1),
            TlaExpr::Record(vec![("x".to_string(), TlaExpr::number(2))]),
        ]);
        assert_eq!(translator.translate(&expr), "arbitrary()");
    }

    #[test]
    fn test_generated_d1_tuple_all_arbitrary_elements_falls_back_to_arbitrary() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::Tuple(vec![
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "left".to_string(),
            },
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "right".to_string(),
            },
        ]);
        assert_eq!(translator.translate(&expr), "arbitrary()");
    }

    #[test]
    fn test_non_generated_context_tuple_with_record_preserves_sequence_translation() {
        let mut config = TranslatorConfig::spec();
        config.variable_names.insert("known_state".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::Tuple(vec![
            TlaExpr::number(1),
            TlaExpr::Record(vec![("x".to_string(), TlaExpr::number(2))]),
        ]);
        assert_eq!(translator.translate(&expr), "seq![1, { x: 2 }]");
    }

    #[test]
    fn test_generated_d1_if_with_mixed_bool_numeric_branches_falls_back_to_arbitrary() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::IfThenElse {
            cond: Box::new(TlaExpr::ident("cond")),
            then_expr: Box::new(TlaExpr::number(1)),
            else_expr: Box::new(TlaExpr::bool(false)),
        };
        assert_eq!(translator.translate(&expr), "arbitrary()");
    }

    #[test]
    fn test_non_generated_context_if_with_mixed_bool_numeric_branches_is_preserved() {
        let mut config = TranslatorConfig::spec();
        config.variable_names.insert("known_state".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::IfThenElse {
            cond: Box::new(TlaExpr::ident("cond")),
            then_expr: Box::new(TlaExpr::number(1)),
            else_expr: Box::new(TlaExpr::bool(false)),
        };
        assert_eq!(translator.translate(&expr), "if cond { 1 } else { false }");
    }

    #[test]
    fn test_generated_d1_if_with_tupleish_branches_falls_back_to_arbitrary() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::IfThenElse {
            cond: Box::new(TlaExpr::bool(true)),
            then_expr: Box::new(TlaExpr::Tuple(vec![TlaExpr::number(1)])),
            else_expr: Box::new(TlaExpr::LetIn {
                defs: vec![],
                body: Box::new(TlaExpr::Tuple(vec![])),
            }),
        };
        assert_eq!(translator.translate(&expr), "arbitrary()");
    }

    #[test]
    fn test_generated_d1_eq_coerces_arbitrary_to_bool_from_peer() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::Eq,
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "ok".to_string(),
            },
            TlaExpr::bool(true),
        );
        assert_eq!(translator.translate(&expr), "(arbitrary::<bool>() == true)");
    }

    #[test]
    fn test_generated_d1_eq_coerces_arbitrary_to_seq_from_tuple_peer() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::Eq,
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "batch".to_string(),
            },
            TlaExpr::Tuple(vec![]),
        );
        assert_eq!(
            translator.translate(&expr),
            "(arbitrary::<Seq<int>>() == Seq::<int>::empty())"
        );
    }

    #[test]
    fn test_generated_d1_eq_coerces_arbitrary_to_set_from_rendered_union_peer() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::Eq,
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "members".to_string(),
            },
            TlaExpr::binop(
                TlaBinOp::Cup,
                TlaExpr::SetEnum(vec![]),
                TlaExpr::SetEnum(vec![TlaExpr::number(1)]),
            ),
        );
        assert_eq!(
            translator.translate(&expr),
            "(Set::<int>::empty() == Set::<int>::empty().union(set![1]))"
        );
    }

    #[test]
    fn test_generated_d1_eq_coerces_arbitrary_to_seq_from_rendered_append_peer() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::Eq,
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "batch".to_string(),
            },
            TlaExpr::OpApply {
                op: Box::new(TlaExpr::ident("Append")),
                args: vec![TlaExpr::Tuple(vec![]), TlaExpr::number(1)],
            },
        );
        assert_eq!(
            translator.translate(&expr),
            "(arbitrary::<Seq<int>>() == Seq::<int>::empty().push(1))"
        );
    }

    #[test]
    fn test_generated_d1_eq_coerces_arbitrary_from_identifier_type_hint_seq() {
        let mut config = TranslatorConfig::spec();
        config
            .identifier_type_hints
            .insert("sent_packets".to_string(), "Seq<int>".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::Eq,
            TlaExpr::ident("sent_packets"),
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "packets".to_string(),
            },
        );
        assert_eq!(
            translator.translate(&expr),
            "(sent_packets == arbitrary::<Seq<int>>())"
        );
    }

    #[test]
    fn test_generated_d1_eq_coerces_arbitrary_from_identifier_type_hint_set() {
        let mut config = TranslatorConfig::spec();
        config
            .identifier_type_hints
            .insert("S".to_string(), "Set<int>".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::Eq,
            TlaExpr::ident("S"),
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "members".to_string(),
            },
        );
        assert_eq!(
            translator.translate(&expr),
            "(S == arbitrary::<Set<int>>())"
        );
    }

    #[test]
    fn test_generated_d1_eq_coerces_arbitrary_from_constant_field_type_hint_set() {
        let mut config = TranslatorConfig::spec();
        config.constant_names.insert("Request".to_string());
        config
            .constant_field_type_hints
            .insert("Request".to_string(), "Set<int>".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::Eq,
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "payload".to_string(),
            },
            TlaExpr::Ident("Request".to_string()),
        );
        assert_eq!(
            translator.translate(&expr),
            "(arbitrary::<Set<int>>() == c.Request)"
        );
    }

    #[test]
    fn test_generated_d1_neq_coerces_arbitrary_from_constant_field_type_hint_seq() {
        let mut config = TranslatorConfig::spec();
        config
            .constant_field_type_hints
            .insert("RequestBatch".to_string(), "Seq<int>".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::Neq,
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "batch".to_string(),
            },
            TlaExpr::Ident("c.RequestBatch".to_string()),
        );
        assert_eq!(
            translator.translate(&expr),
            "(arbitrary::<Seq<int>>() != c.RequestBatch)"
        );
    }

    #[test]
    fn test_non_generated_eq_preserves_constant_field_hint_coercion() {
        let mut config = TranslatorConfig::spec();
        config.variable_names.insert("known_state".to_string());
        config
            .constant_field_type_hints
            .insert("Request".to_string(), "Set<int>".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::Eq,
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "payload".to_string(),
            },
            TlaExpr::Ident("c.Request".to_string()),
        );
        assert_eq!(translator.translate(&expr), "(arbitrary() == c.Request)");
    }

    #[test]
    fn test_generated_d1_eq_coerces_arbitrary_to_lconstants_for_c_peer() {
        let mut config = TranslatorConfig::spec();
        config.constant_names.insert("N".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(
            TlaBinOp::Eq,
            TlaExpr::RecordAccess {
                record: Box::new(TlaExpr::ident("request")),
                field: "cfg".to_string(),
            },
            TlaExpr::ident("c"),
        );
        assert_eq!(translator.translate(&expr), "(arbitrary::<LConstants>() == c)");
    }

    #[test]
    fn test_generated_d1_eq_coerces_arbitrary_to_int_from_symbolic_literal_peer() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(TlaBinOp::Eq, TlaExpr::ident("new_state"), TlaExpr::ident("Idle"));
        let out = translator.translate(&expr);
        assert!(out.starts_with("(arbitrary::<int>() == "));
        assert!(out.ends_with("int)"));
    }

    #[test]
    fn test_generated_d1_eq_coerces_double_untyped_arbitrary_to_int() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(TlaBinOp::Eq, TlaExpr::ident("new_state"), TlaExpr::ident("reply"));
        assert_eq!(
            translator.translate(&expr),
            "(arbitrary::<int>() == arbitrary::<int>())"
        );
    }

    #[test]
    fn test_non_generated_eq_preserves_double_untyped_arbitrary() {
        let mut config = TranslatorConfig::spec();
        config.variable_names.insert("known_state".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::binop(TlaBinOp::Eq, TlaExpr::ident("new_state"), TlaExpr::ident("reply"));
        assert_eq!(translator.translate(&expr), "(arbitrary() == arbitrary())");
    }

    #[test]
    fn test_generated_d1_let_in_types_untyped_arbitrary_binding() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::LetIn {
            defs: vec![crate::tla::ast::TlaOperator::new(
                "unused_0",
                TlaExpr::RecordAccess {
                    record: Box::new(TlaExpr::ident("request")),
                    field: "client".to_string(),
                },
            )],
            body: Box::new(TlaExpr::number(0)),
        };
        let out = translator.translate(&expr);
        assert!(out.contains("let unused_0: int = arbitrary();"));
    }

    #[test]
    fn test_non_generated_context_let_in_preserves_untyped_binding() {
        let mut config = TranslatorConfig::spec();
        config.variable_names.insert("known_state".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::LetIn {
            defs: vec![crate::tla::ast::TlaOperator::new(
                "unused_0",
                TlaExpr::RecordAccess {
                    record: Box::new(TlaExpr::ident("request")),
                    field: "client".to_string(),
                },
            )],
            body: Box::new(TlaExpr::number(0)),
        };
        let out = translator.translate(&expr);
        assert!(out.contains("let unused_0 = arbitrary();"));
        assert!(!out.contains("let unused_0: int = arbitrary();"));
    }

    #[test]
    fn test_translate_unknown_external_operator_call_fallback_in_spec_mode() {
        let config = TranslatorConfig::spec();
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::OpApply {
            op: Box::new(TlaExpr::ident("ProposerInit")),
            args: vec![TlaExpr::ident("p"), TlaExpr::ident("c")],
        };
        assert_eq!(translator.translate(&expr), "arbitrary()");
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
        let mut translator = ModuleTranslator::new();
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
        let mut translator = ModuleTranslator::new();
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
        let mut translator = ModuleTranslator::new();
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
    fn test_record_return_types_use_named_struct_not_anonymous_record_type() {
        let source = r"
            ---- MODULE Types ----
            LState == [tm_state |-> 0, rm_prepared |-> {}]
            ====
        ";
        let module = parse_module(source).unwrap();
        let result = translate_module_with_types(&module);

        assert!(
            result.contains("pub struct LRecord"),
            "Expected generated named record struct, got:\n{}",
            result
        );
        assert!(
            result.contains("pub open spec fn LLState() -> LRecord"),
            "Expected operator return type to use LRecord (with prefixed operator name), got:\n{}",
            result
        );
        assert!(
            !result.contains("pub open spec fn LLState() -> {"),
            "Anonymous record return type should not be emitted, got:\n{}",
            result
        );
    }

    #[test]
    fn test_record_shapes_found_inside_let_tuple_for_named_record_emission() {
        let source = r"
            ---- MODULE StateMachine ----
            HandleRequest(state, request) ==
                LET reply == 0
                IN <<state, [client |-> request, seqno |-> 1, reply |-> reply]>>
            ====
        ";
        let module = parse_module(source).unwrap();
        let result = translate_module_with_types(&module);

        assert!(
            result.contains("pub struct LRecord"),
            "Expected generated named record struct for nested record literal, got:\n{}",
            result
        );
        assert!(
            result.contains("pub open spec fn LHandleRequest"),
            "Expected translated operator function, got:\n{}",
            result
        );
        assert!(
            result.contains("-> (int, LRecord)"),
            "Expected tuple return type to use named record struct, got:\n{}",
            result
        );
        assert!(
            result.contains("LRecord {"),
            "Expected record literal in body to use named struct construction, got:\n{}",
            result
        );
        assert!(
            !result.contains("-> (int, {"),
            "Anonymous record return type should not appear in tuple return types, got:\n{}",
            result
        );
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
        let mut translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        // Init should have single state parameter (no primes)
        assert!(result.contains("pub open spec fn LInit"));

        // Increment should have s and s_ parameters (uses primes)
        assert!(result.contains("pub open spec fn LIncrement"));
        // The function body should reference s_.count (qualified primed variable)
        assert!(
            result.contains("s_.count"),
            "Expected s_.count in output, got:\n{}",
            result
        );
    }

    #[test]
    fn test_translate_skips_duplicate_reserved_params_in_init_signature() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT N
            VARIABLE x
            Init(s, c) == x = N
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        assert!(
            result.contains("pub open spec fn LInit(s: LState, c: LConstants) -> bool"),
            "Init signature should include exactly one s and one c, got:\n{}",
            result
        );
        assert!(
            !result.contains("LInit(s: LState, c: LConstants, s: int"),
            "Init signature should not include duplicate s param, got:\n{}",
            result
        );
        assert!(
            !result.contains("c: LConstants, c: int"),
            "Init signature should not include duplicate c param, got:\n{}",
            result
        );
    }

    #[test]
    fn test_translate_init_is_not_promoted_to_action_via_symbolic_action_token() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT N
            VARIABLE x
            Step(s, s_, c, delta) == s_.x = x + delta
            Init(s, c) == x = Step
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        assert!(
            result.contains("pub open spec fn LInit(s: LState, c: LConstants) -> bool"),
            "Init should not gain s_ via transitive action classification, got:\n{}",
            result
        );
        assert!(
            !result.contains("pub open spec fn LInit(s: LState, s_: LState, c: LConstants)"),
            "Init must remain non-action signature, got:\n{}",
            result
        );
    }

    #[test]
    fn test_translate_skips_duplicate_reserved_params_in_action_signature() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT N
            VARIABLE x
            Step(s, s_, c, delta) == x' = x + delta
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        assert!(
            result.contains(
                "pub open spec fn LStep(s: LState, s_: LState, c: LConstants, delta: int) -> bool"
            ),
            "Action signature should retain only non-reserved explicit params, got:\n{}",
            result
        );
        assert!(
            !result.contains("s_: LState, c: LConstants, s: int"),
            "Action signature should not include duplicate s param, got:\n{}",
            result
        );
        assert!(
            !result.contains("s_: LState, c: LConstants, s_: int"),
            "Action signature should not include duplicate s_ param, got:\n{}",
            result
        );
    }

    #[test]
    fn test_translate_explicit_s_param_without_primes_is_action() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT N
            VARIABLE x
            Step(s, s_, c, delta) == s_.x = x + delta
            Next(s, s_, c) == Step(s, s_, c, 1)
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        assert!(
            result.contains(
                "pub open spec fn LStep(s: LState, s_: LState, c: LConstants, delta: int) -> bool"
            ),
            "Explicit s_ parameter should classify operator as action, got:\n{}",
            result
        );
        assert!(
            result.contains("LStep(s, s_, c, 1)"),
            "Action calls should not duplicate implicit state/constants args, got:\n{}",
            result
        );
    }

    #[test]
    fn test_translate_param_named_s_is_not_treated_as_module_state() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT UpperBound
            BoundRequestSequence(s, lengthBound) ==
                IF 0 <= lengthBound /\ lengthBound < Len(s)
                THEN SubSeq(s, 0, lengthBound)
                ELSE s
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        assert!(
            result.contains(
                "pub open spec fn LBoundRequestSequence(c: LConstants, s: Seq<int>, lengthBound: int)"
            ),
            "Parameterized helper should keep explicit s param (Seq<int>) and avoid injected state s, got:\n{}",
            result
        );
        assert!(
            !result.contains("LBoundRequestSequence(s: LState"),
            "Parameterized helper should not inject state param for explicit local s, got:\n{}",
            result
        );
    }

    #[test]
    fn test_generated_d1_return_type_uses_seq_shape_for_bound_request_sequence() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT UpperBound
            BoundRequestSequence(s, lengthBound) ==
                IF 0 <= lengthBound /\ lengthBound < Len(s)
                THEN SubSeq(s, 0, lengthBound)
                ELSE s
            ====
        ";
        let module = parse_module(source).unwrap();
        let output = translate_module_with_types(&module);

        assert!(
            output.contains(
                "pub open spec fn LBoundRequestSequence(c: LConstants, s: Seq<int>, lengthBound: int) -> Seq<int>"
            ),
            "Expected Seq<int> return type for BoundRequestSequence shape, got:\n{}",
            output
        );
    }

    #[test]
    fn test_generated_d1_return_type_uses_seq_shape_for_recursive_if_with_one_sided_hint() {
        let source = r"
            ---- MODULE Test ----
            RECURSIVE KeepSeq(_, _)
            KeepSeq(s, n) ==
                IF n = 0
                THEN <<>>
                ELSE KeepSeq(s, n)
            ====
        ";
        let module = parse_module(source).unwrap();
        let output = translate_module_with_types(&module);

        assert!(
            output.contains("pub open spec fn LKeepSeq(s: int, n: int) -> Seq<int>"),
            "Expected Seq<int> return type for recursive IF with one-sided seq hint, got:\n{}",
            output
        );
    }

    #[test]
    fn test_generated_d1_return_type_uses_seq_shape_for_recursive_concat_expression() {
        let source = r"
            ---- MODULE Test ----
            RECURSIVE ConcatSelf(_)
            ConcatSelf(s) ==
                <<s[0]>> + ConcatSelf(s)
            ====
        ";
        let module = parse_module(source).unwrap();
        let output = translate_module_with_types(&module);

        assert!(
            output.contains("pub open spec fn LConcatSelf(s: int) -> Seq<int>"),
            "Expected Seq<int> return type for recursive sequence-concat expression, got:\n{}",
            output
        );
    }

    #[test]
    fn test_translate_parameterized_operator_ident_in_value_context_is_not_autocalled() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT N
            VARIABLE x
            PrePrepare(s, s_, c, delta) == s_.x = x + delta
            Tag(s, s_, c) == x = PrePrepare
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        assert!(
            !result.contains("x == LPrePrepare(s, s_, c)"),
            "Parameterized operator identifier in value context should not be auto-called, got:\n{}",
            result
        );
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
        let mut translator = ModuleTranslator::new();
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
        let mut translator = ModuleTranslator::with_config(config);
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

    // Mode annotation tests (T6.4)
    #[test]
    fn test_parameter_mode_display() {
        assert_eq!(format!("{}", ParameterMode::Input), "+");
        assert_eq!(format!("{}", ParameterMode::Output), "-");
    }

    #[test]
    fn test_operator_modes_to_automan() {
        let modes = OperatorModes::new("LInit", vec![ParameterMode::Output]);
        assert!(modes.to_automan_line().contains("LInit(-)"));

        let modes = OperatorModes::new("LNext", vec![ParameterMode::Input, ParameterMode::Output])
            .with_description("s is input, s_ is output");
        let line = modes.to_automan_line();
        assert!(line.contains("LNext(+, -)"));
        assert!(line.contains("s is input, s_ is output"));
    }

    #[test]
    fn test_generate_mode_annotations_simple() {
        let source = r"
            ---- MODULE Counter ----
            VARIABLE count
            Init == count = 0
            Increment == count' = count + 1
            ====
        ";
        let module = parse_module(source).unwrap();
        let result = generate_mode_annotations(&module);

        // Should have module block
        assert!(result.contains("module Counter"));

        // Init should have output mode (state is created)
        assert!(result.contains("LInit"));

        // Increment should have input and output modes (action)
        assert!(result.contains("LIncrement"));
    }

    #[test]
    fn test_generate_mode_annotations_with_params() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE x
            Max(a, b) == IF a > b THEN a ELSE b
            Init == x = Max(1, 2)
            ====
        ";
        let module = parse_module(source).unwrap();
        let result = generate_mode_annotations(&module);

        // Max has state + 2 params (all inputs for helper)
        assert!(result.contains("LMax"));
    }

    #[test]
    fn test_generate_mode_annotations_explicit_s_param_without_primes() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT N
            VARIABLE x
            Step(s, s_, c, delta) == s_.x = x + delta
            ====
        ";
        let module = parse_module(source).unwrap();
        let result = generate_mode_annotations(&module);

        assert!(
            result.contains("LStep(+, -, +, +);"),
            "Explicit s_ parameter should produce action modes (+, -, +, +), got:\n{}",
            result
        );
    }

    #[test]
    fn test_mode_annotations_param_named_s_is_not_auto_state_input() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT UpperBound
            BoundRequestSequence(s, lengthBound) ==
                IF 0 <= lengthBound /\ lengthBound < Len(s)
                THEN SubSeq(s, 0, lengthBound)
                ELSE s
            ====
        ";
        let module = parse_module(source).unwrap();
        let result = generate_mode_annotations(&module);

        assert!(
            result.contains("LBoundRequestSequence(+, +, +);"),
            "Param-only helper should have modes for (c, s, lengthBound) without injected state/s_, got:\n{}",
            result
        );
        assert!(
            !result.contains("LBoundRequestSequence(+, +, +, +);"),
            "Param-only helper should not gain an extra auto state parameter, got:\n{}",
            result
        );
    }

    #[test]
    fn test_mode_annotation_generator_with_config() {
        let config = ModuleConfig {
            spec_prefix: "Spec".to_string(),
            ..Default::default()
        };
        let generator = ModeAnnotationGenerator::with_config(config);

        let source = r"
            ---- MODULE Test ----
            VARIABLE x
            Init == x = 0
            ====
        ";
        let module = parse_module(source).unwrap();
        let result = generator.generate(&module);

        // Should use custom prefix
        assert!(result.contains("SpecInit"));
    }

    #[test]
    fn test_mode_annotation_action_detection() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE x, y
            TypeOK == x \in Nat /\ y \in Nat
            Step == x' = x + 1 /\ y' = y
            ====
        ";
        let module = parse_module(source).unwrap();
        let generator = ModeAnnotationGenerator::new();
        let result = generator.generate(&module);

        // TypeOK has no primes - pure predicate
        // Step has primes - action with s and s_
        assert!(result.contains("LTypeOK"));
        assert!(result.contains("LStep"));
    }

    #[test]
    fn test_mode_annotation_unchanged() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE x, y
            OnlyXChanges == x' = x + 1 /\ UNCHANGED y
            ====
        ";
        let module = parse_module(source).unwrap();
        let result = generate_mode_annotations(&module);

        // UNCHANGED implies action, so should have input and output state
        assert!(result.contains("LOnlyXChanges"));
        // Should be an action (has primes via UNCHANGED)
        assert!(result.contains("+, -"));
    }

    #[test]
    fn test_mode_annotation_init_name_not_confused_with_action() {
        // Operators with "init" in name but primed variables should be treated as actions,
        // not init operators. Only exact "Init" should be treated as init.
        let source = r"
            ---- MODULE Test ----
            VARIABLE x, y
            Init == x = 0 /\ y = 0
            InitiateProbe == x = 0 /\ x' = 1 /\ y' = y
            InitState == x' = 0 /\ y' = 0
            ====
        ";
        let module = parse_module(source).unwrap();
        let result = generate_mode_annotations(&module);

        // Init (exact match, no primes) -> output only
        assert!(
            result.contains("LInit(-);"),
            "Init should be output-only, got:\n{}",
            result
        );

        // InitiateProbe (has primes, name contains init) -> action (input + output)
        assert!(
            result.contains("LInitiateProbe(+, -);"),
            "InitiateProbe should be action (input + output), got:\n{}",
            result
        );

        // InitState (has primes, name contains init) -> action (input + output)
        assert!(
            result.contains("LInitState(+, -);"),
            "InitState should be action (input + output), got:\n{}",
            result
        );
    }

    #[test]
    fn test_variable_qualification() {
        // Variables should be qualified with s. and primed with s_.
        let source = r"
            ---- MODULE Test ----
            VARIABLE x
            Init == x = 0
            Inc == x' = x + 1
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        assert!(
            result.contains("s.x == 0"),
            "Variable x should be qualified as s.x, got:\n{}",
            result
        );
        assert!(
            result.contains("s_.x == (s.x + 1)"),
            "Primed x' should be s_.x and x should be s.x, got:\n{}",
            result
        );
    }

    #[test]
    fn test_constant_qualification() {
        // Constants should be qualified with c. and a constants parameter added
        let source = r"
            ---- MODULE Test ----
            CONSTANT N
            VARIABLE x
            Init == x = N
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        assert!(
            result.contains("c: LConstants"),
            "Functions should have c: LConstants parameter, got:\n{}",
            result
        );
        assert!(
            result.contains("s.x == c.N"),
            "Constant N should be qualified as c.N, got:\n{}",
            result
        );
    }

    #[test]
    fn test_parameter_type_uses_inferred_operator_domain() {
        let source = r"
            ---- MODULE Test ----
            Foo(S) == \A x \in S : x \in Nat
            ====
        ";
        let module = parse_module(source).unwrap();
        let output = translate_module_with_types(&module);

        assert!(
            output.contains("pub open spec fn LFoo(S: Set<int>) -> bool"),
            "Expected inferred set parameter type in signature, got:\n{}",
            output
        );
    }

    #[test]
    fn test_parameter_type_does_not_force_seq_from_len_usage() {
        let source = r"
            ---- MODULE Test ----
            Foo(xs) == Len(xs) >= 0
            ====
        ";
        let module = parse_module(source).unwrap();
        let output = translate_module_with_types(&module);

        assert!(
            output.contains("pub open spec fn LFoo(xs: int) -> bool"),
            "Expected fallback int param (no aggressive Seq inference), got:\n{}",
            output
        );
    }

    #[test]
    fn test_parameter_type_does_not_force_map_from_domain_usage() {
        let source = r"
            ---- MODULE Test ----
            Foo(m) == DOMAIN m = {}
            ====
        ";
        let module = parse_module(source).unwrap();
        let output = translate_module_with_types(&module);

        assert!(
            output.contains("pub open spec fn LFoo(m: int) -> bool"),
            "Expected fallback int param (no aggressive Map inference), got:\n{}",
            output
        );
    }

    #[test]
    fn test_parameter_type_infers_seq_from_len_and_index_usage() {
        let source = r"
            ---- MODULE Test ----
            Foo(xs) == /\ Len(xs) >= 0
                       /\ xs[0] = 0
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let output = translator.translate(&module);

        assert!(
            output.contains("pub open spec fn LFoo(xs: Seq<int>) -> bool"),
            "Expected Seq hint from combined len/index usage, got:\n{}",
            output
        );
    }

    #[test]
    fn test_parameter_type_infers_map_from_domain_and_index_usage() {
        let source = r"
            ---- MODULE Test ----
            Foo(m) == /\ DOMAIN m = {}
                      /\ m[0] = 0
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let output = translator.translate(&module);

        assert!(
            output.contains("pub open spec fn LFoo(m: Map<int, int>) -> bool"),
            "Expected Map hint from combined domain/index usage, got:\n{}",
            output
        );
    }

    #[test]
    fn test_generated_d1_param_type_overrides_inferred_bool_for_set_element_usage() {
        let op = TlaOperator::new(
            "Foo",
            TlaExpr::binop(TlaBinOp::In, TlaExpr::ident("x"), TlaExpr::ident("S")),
        )
        .with_params(vec![
            crate::tla::ast::TlaParam::new("x"),
            crate::tla::ast::TlaParam::new("S"),
        ]);
        let mut translator = ModuleTranslator::new();
        let mut env = TypeEnv::new();
        env.set_operator(
            "Foo",
            TlaType::function(
                TlaType::tuple(vec![TlaType::Bool, TlaType::set(TlaType::Int)]),
                TlaType::Bool,
            ),
        );
        translator.type_env = Some(env);

        assert_eq!(translator.get_param_type(&op, 0, "x", true), "int");
        assert_eq!(translator.get_param_type(&op, 1, "S", true), "Set<int>");
    }

    #[test]
    fn test_non_generated_param_type_keeps_inferred_bool_without_override() {
        let op = TlaOperator::new(
            "Foo",
            TlaExpr::binop(TlaBinOp::In, TlaExpr::ident("x"), TlaExpr::ident("S")),
        )
        .with_params(vec![
            crate::tla::ast::TlaParam::new("x"),
            crate::tla::ast::TlaParam::new("S"),
        ]);
        let mut translator = ModuleTranslator::new();
        let mut env = TypeEnv::new();
        env.set_operator(
            "Foo",
            TlaType::function(
                TlaType::tuple(vec![TlaType::Bool, TlaType::set(TlaType::Int)]),
                TlaType::Bool,
            ),
        );
        translator.type_env = Some(env);

        assert_eq!(translator.get_param_type(&op, 0, "x", false), "bool");
    }

    #[test]
    fn test_generated_d1_param_type_overrides_inferred_bool_for_scalar_usage() {
        let op = TlaOperator::new(
            "Foo",
            TlaExpr::binop(TlaBinOp::Gt, TlaExpr::ident("x"), TlaExpr::number(0)),
        )
        .with_params(vec![crate::tla::ast::TlaParam::new("x")]);
        let mut translator = ModuleTranslator::new();
        let mut env = TypeEnv::new();
        env.set_operator(
            "Foo",
            TlaType::function(TlaType::Bool, TlaType::Bool),
        );
        translator.type_env = Some(env);

        assert_eq!(translator.get_param_type(&op, 0, "x", true), "int");
    }

    #[test]
    fn test_constant_type_hint_uses_set_membership_usage_without_type_env() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT S
            Foo(x) == x \in S
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let output = translator.translate(&module);

        assert!(
            output.contains("pub S: Set<int>,"),
            "Expected Set hint for constant S from membership usage, got:\n{}",
            output
        );
    }

    #[test]
    fn test_generated_d1_module_translation_coerces_eq_from_constant_field_hint() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT Request
            IsRequestSet(x) == x \in Request
            Foo == request.payload = c.Request
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let output = translator.translate(&module);

        assert!(
            output.contains("pub Request: Set<int>,"),
            "Expected Request constant to infer Set<int>, got:\n{}",
            output
        );
        assert!(
            output.contains("(arbitrary::<Set<int>>() == arbitrary())"),
            "Expected generated-D1 Eq coercion from c.Request type hint, got:\n{}",
            output
        );
    }

    #[test]
    fn test_constant_type_hint_keeps_set_membership_hint_with_scalar_conflict() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT N
            Foo(x) == /\ x \in N
                      /\ N = 0
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let output = translator.translate(&module);

        assert!(
            output.contains("pub N: Set<int>,"),
            "Expected set-membership hint to win even with scalar conflict, got:\n{}",
            output
        );
    }

    #[test]
    fn test_generated_d1_record_int_field_normalizes_c_field_value_to_arbitrary_int() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT OperationNumber
            IsValidOpn(op) == op \in OperationNumber
            Foo == [log_truncation_point |-> c.OperationNumber]
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let output = translator.translate(&module);

        assert!(
            output.contains("log_truncation_point: arbitrary()"),
            "Expected generated-D1 reserved-root fallback to normalize c.field value to arbitrary(), got:\n{}",
            output
        );
    }

    #[test]
    fn test_record_int_field_normalizes_c_field_value_with_variables_present() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE x
            Foo == [log_truncation_point |-> c.OperationNumber]
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let output = translator.translate(&module);

        assert!(
            output.contains("log_truncation_point: arbitrary::<int>()"),
            "Expected int field with c.field value to normalize even when variables are present, got:\n{}",
            output
        );
    }

    #[test]
    fn test_record_int_field_preserves_non_c_value() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE x
            Foo == [constants |-> x]
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let output = translator.translate(&module);

        assert!(
            output.contains("constants: s.x"),
            "Expected non-c int field value to be preserved, got:\n{}",
            output
        );
    }

    #[test]
    fn test_record_int_field_normalizes_dotted_c_ident_value() {
        let mut config = TranslatorConfig::spec();
        config
            .record_structs
            .insert("log_truncation_point".to_string(), "LRecord".to_string());
        config.record_all_fields = vec!["log_truncation_point".to_string()];
        config
            .record_field_types
            .insert("log_truncation_point".to_string(), "int".to_string());
        let translator = ExprTranslator::new(&config);
        let expr = TlaExpr::Record(vec![(
            "log_truncation_point".to_string(),
            TlaExpr::Ident("c.OperationNumber".to_string()),
        )]);

        let out = translator.translate(&expr);
        assert!(
            out.contains("log_truncation_point: arbitrary::<int>()"),
            "Expected dotted c.ident to normalize for int record field, got:\n{}",
            out
        );
    }

    #[test]
    fn test_operator_cross_reference() {
        // Operator references should add L prefix and pass state args
        let source = r"
            ---- MODULE Test ----
            VARIABLE x
            Inc == x' = x + 1
            Dec == x' = x - 1
            Next == Inc \/ Dec
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        // Next references Inc and Dec, which are actions
        assert!(
            result.contains("LInc(s, s_)"),
            "Next body should reference LInc(s, s_), got:\n{}",
            result
        );
        assert!(
            result.contains("LDec(s, s_)"),
            "Next body should reference LDec(s, s_), got:\n{}",
            result
        );
        // Next should also be classified as an action (transitive)
        assert!(
            result.contains("fn LNext(s: LState, s_: LState)"),
            "Next should have s_ parameter (transitive action), got:\n{}",
            result
        );
    }

    #[test]
    fn test_in_nat_translation() {
        // x \in Nat should become (x >= 0), not nat.contains(x)
        let config = TranslatorConfig::default();
        let translator = ExprTranslator::new(&config);

        let expr = TlaExpr::binop(TlaBinOp::In, TlaExpr::ident("x"), TlaExpr::ident("Nat"));
        assert_eq!(translator.translate(&expr), "(x >= 0)");

        // x \in Int should become true
        let expr = TlaExpr::binop(TlaBinOp::In, TlaExpr::ident("x"), TlaExpr::ident("Int"));
        assert_eq!(translator.translate(&expr), "true");

        // x \notin Nat should become (x < 0)
        let expr = TlaExpr::binop(TlaBinOp::NotIn, TlaExpr::ident("x"), TlaExpr::ident("Nat"));
        assert_eq!(translator.translate(&expr), "(x < 0)");

        // x \in Seq(T) should be treated as constructor-style type membership guard (erased)
        let expr = TlaExpr::binop(
            TlaBinOp::In,
            TlaExpr::ident("x"),
            TlaExpr::OpApply {
                op: Box::new(TlaExpr::ident("Seq")),
                args: vec![TlaExpr::ident("T")],
            },
        );
        assert_eq!(translator.translate(&expr), "true");

        // x \notin Seq(T) should erase to false.
        let expr = TlaExpr::binop(
            TlaBinOp::NotIn,
            TlaExpr::ident("x"),
            TlaExpr::OpApply {
                op: Box::new(TlaExpr::ident("Seq")),
                args: vec![TlaExpr::ident("T")],
            },
        );
        assert_eq!(translator.translate(&expr), "false");
    }

    #[test]
    fn test_unchanged_with_module_context() {
        // UNCHANGED <<x, y>> should produce s_.x == s.x && s_.y == s.y
        let source = r"
            ---- MODULE Test ----
            VARIABLE x, y
            NoChange == UNCHANGED <<x, y>>
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut translator = ModuleTranslator::new();
        let result = translator.translate(&module);

        assert!(
            result.contains("s_.x == s.x"),
            "UNCHANGED x should produce s_.x == s.x, got:\n{}",
            result
        );
        assert!(
            result.contains("s_.y == s.y"),
            "UNCHANGED y should produce s_.y == s.y, got:\n{}",
            result
        );
    }

    #[test]
    fn test_type_var_fallback_to_int() {
        // Unresolved TypeVars should render as int, not T0/T1
        let source = r"
            ---- MODULE Test ----
            CONSTANT N
            VARIABLE x
            Init == x = N
            ====
        ";
        let module = parse_module(source).unwrap();
        let mut inference = TypeInference::new();
        let env = inference.infer_types(&module);
        let resolved = inference.resolve_with_fallback(&env);

        let mut translator = ModuleTranslator::new().with_types(resolved);
        let result = translator.translate(&module);

        // Should not contain T0, T1, etc.
        assert!(
            !result.contains("T0") && !result.contains("T1"),
            "Output should not contain unresolved type variables, got:\n{}",
            result
        );
        // Constants should have concrete types
        assert!(
            result.contains("pub N: int") || result.contains("pub N: nat"),
            "Constant N should have concrete type, got:\n{}",
            result
        );
    }

    #[test]
    fn test_mode_annotation_with_constants() {
        // Mode annotations should include c parameter when module has constants
        let source = r"
            ---- MODULE Test ----
            CONSTANT N
            VARIABLE x
            Init == x = 0
            Inc == x' = x + 1
            ====
        ";
        let module = parse_module(source).unwrap();
        let result = generate_mode_annotations(&module);

        // Init should have output + constants
        assert!(
            result.contains("LInit(-, +);"),
            "Init with constants should be (-, +), got:\n{}",
            result
        );
        // Inc should have input + output + constants
        assert!(
            result.contains("LInc(+, -, +);"),
            "Action with constants should be (+, -, +), got:\n{}",
            result
        );
    }

    #[test]
    fn test_mode_annotation_skips_duplicate_reserved_params() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT N
            VARIABLE x
            Step(s, s_, c, delta) == x' = x + delta
            Next(s, s_, c) == Step(s, s_, c, 1)
            ====
        ";
        let module = parse_module(source).unwrap();
        let result = generate_mode_annotations(&module);

        assert!(
            result.contains("LStep(+, -, +, +);"),
            "Step should only include one s/s_/c plus explicit delta, got:\n{}",
            result
        );
        assert!(
            result.contains("LNext(+, -, +);"),
            "Next should only include one s/s_/c after dedup, got:\n{}",
            result
        );
    }

    #[test]
    fn test_mode_annotation_param_counts_match_generated_signatures_for_param_only_predicate() {
        let source = r"
            ---- MODULE Dist ----
            CONSTANT K
            Foo(ps) == ps = K
            ====
        ";
        let module = parse_module(source).unwrap();
        let spec = translate_module_with_types(&module);
        let modes = generate_mode_annotations(&module);

        let signature_param_count = |code: &str, fn_name: &str| -> usize {
            let marker = format!("pub open spec fn {}(", fn_name);
            let start = code.find(&marker).expect("missing function signature") + marker.len();
            let rest = &code[start..];
            let end = rest.find(')').expect("missing signature close paren");
            let params = rest[..end].trim();
            if params.is_empty() {
                0
            } else {
                params.split(',').count()
            }
        };
        let annotation_param_count = |code: &str, fn_name: &str| -> usize {
            let marker = format!("{}(", fn_name);
            let start = code.find(&marker).expect("missing mode annotation") + marker.len();
            let rest = &code[start..];
            let end = rest.find(')').expect("missing mode close paren");
            let params = rest[..end].trim();
            if params.is_empty() {
                0
            } else {
                params.split(',').count()
            }
        };

        assert_eq!(
            signature_param_count(&spec, "LFoo"),
            annotation_param_count(&modes, "LFoo"),
            "LFoo annotation arity should match generated signature.\nSpec:\n{}\nModes:\n{}",
            spec,
            modes
        );
    }
}
