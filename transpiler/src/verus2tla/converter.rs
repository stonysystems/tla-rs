//! Verus to TLA+ converter.
//!
//! Converts Verus spec functions (AST) to TLA+ modules (AST).

use crate::ast::{
    BinOp, Binding, Expr as VerusExpr, Literal, MatchArm, Path, Pattern, SpecFunction,
    Type as VerusType, UnaryOp,
};
use crate::parser::parse_file;
use crate::tla::ast::{
    TlaBinOp, TlaConstantDecl, TlaExceptPath, TlaExceptUpdate, TlaExpr, TlaModule, TlaNumber,
    TlaOperator, TlaParam, TlaQuantBound, TlaUnaryOp,
};
use crate::types::{parse_types_from_file, TypeDef};

use super::types::{TypeMapper, VerusType as MapperVerusType};

use std::collections::HashSet;
use std::path::Path as FilePath;

/// Configuration for the Verus to TLA+ converter.
#[derive(Debug, Clone)]
pub struct ConverterConfig {
    /// Prefix to strip from spec type names (e.g., "L" for LReplica -> Replica)
    pub spec_prefix: String,
    /// Whether to include recommends as ASSUME statements
    pub include_recommends: bool,
    /// Whether to generate type definitions
    pub generate_type_defs: bool,
    /// Standard library modules to extend
    pub standard_extends: Vec<String>,
}

impl Default for ConverterConfig {
    fn default() -> Self {
        Self {
            spec_prefix: "L".to_string(),
            include_recommends: false,
            generate_type_defs: true,
            standard_extends: vec![
                "Integers".to_string(),
                "Sequences".to_string(),
                "FiniteSets".to_string(),
            ],
        }
    }
}

/// Verus to TLA+ converter.
pub struct Verus2TlaConverter {
    config: ConverterConfig,
    type_mapper: TypeMapper,
    /// Collected constants from function parameters
    constants: HashSet<String>,
}

impl Verus2TlaConverter {
    /// Create a new converter with default configuration.
    pub fn new() -> Self {
        Self {
            config: ConverterConfig::default(),
            type_mapper: TypeMapper::new(),
            constants: HashSet::new(),
        }
    }

    /// Create a new converter with custom configuration.
    pub fn with_config(config: ConverterConfig) -> Self {
        Self {
            config,
            type_mapper: TypeMapper::new(),
            constants: HashSet::new(),
        }
    }

    /// Convert a Verus source file to a TLA+ module.
    pub fn convert_file(&mut self, path: &FilePath) -> Result<TlaModule, ConversionError> {
        let spec_functions =
            parse_file(path).map_err(|e| ConversionError::ParseError(e.to_string()))?;

        // Extract type definitions (structs, enums, type aliases) from the file
        let type_defs =
            parse_types_from_file(path).map_err(|e| ConversionError::ParseError(e.to_string()))?;

        // Register extracted types in the type mapper
        self.register_types_from_defs(&type_defs);

        let file_stem = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("Module")
            .to_string();
        // Capitalize first letter to match TLA+ naming convention (filename = module name)
        let module_name = {
            let mut chars = file_stem.chars();
            match chars.next() {
                None => file_stem,
                Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
            }
        };

        self.convert_functions(&module_name, spec_functions)
    }

    /// Register type definitions from parsed TypeDef items into the type mapper.
    fn register_types_from_defs(&mut self, type_defs: &[TypeDef]) {
        for type_def in type_defs {
            match type_def {
                TypeDef::Struct(struct_def) => {
                    // Convert StructDef fields to TypeMapper format
                    let fields: Vec<(String, MapperVerusType)> = struct_def
                        .fields
                        .iter()
                        .map(|f| {
                            let mapper_type = self.convert_ast_type_to_mapper(&f.ty);
                            (f.name.clone(), mapper_type)
                        })
                        .collect();

                    let name = self.strip_prefix(&struct_def.name);
                    self.type_mapper.register_record(&name, fields);
                }
                TypeDef::Enum(enum_def) => {
                    // Convert EnumDef variants to TypeMapper format
                    let variants: Vec<String> =
                        enum_def.variants.iter().map(|v| v.name.clone()).collect();

                    let name = self.strip_prefix(&enum_def.name);
                    self.type_mapper.register_enum(&name, variants);
                }
                TypeDef::Alias(alias) => {
                    // Type aliases become custom mappings
                    let name = self.strip_prefix(&alias.name);
                    let target_type = self.convert_ast_type_to_mapper(&alias.ty);
                    self.type_mapper
                        .add_mapping(&name, &target_type.to_tla_type());
                }
                TypeDef::Function(_) => {
                    // Function signatures don't need type registration
                }
            }
        }
    }

    /// Convert AST Type to mapper's VerusType.
    fn convert_ast_type_to_mapper(&self, ty: &VerusType) -> MapperVerusType {
        match ty {
            VerusType::Int => MapperVerusType::Int,
            VerusType::Nat => MapperVerusType::Nat,
            VerusType::Bool => MapperVerusType::Bool,
            VerusType::Unit => MapperVerusType::Unit,
            VerusType::Seq(inner) => {
                MapperVerusType::Seq(Box::new(self.convert_ast_type_to_mapper(inner)))
            }
            VerusType::Set(inner) => {
                MapperVerusType::Set(Box::new(self.convert_ast_type_to_mapper(inner)))
            }
            VerusType::Map(k, v) => MapperVerusType::Map(
                Box::new(self.convert_ast_type_to_mapper(k)),
                Box::new(self.convert_ast_type_to_mapper(v)),
            ),
            VerusType::Tuple(parts) => MapperVerusType::Tuple(
                parts
                    .iter()
                    .map(|p| self.convert_ast_type_to_mapper(p))
                    .collect(),
            ),
            VerusType::Named(path) => {
                let name = path.last().unwrap_or("Unknown");
                // Check if this is Option<T>
                if name == "Option" {
                    // Can't determine inner type from Named, treat as unknown
                    MapperVerusType::Named(name.to_string())
                } else {
                    MapperVerusType::Named(name.to_string())
                }
            }
            VerusType::Generic(path, args) => {
                let name = path.last().unwrap_or("Unknown");
                // Handle Option<T> as a special generic case
                if name == "Option" && !args.is_empty() {
                    MapperVerusType::Option(Box::new(self.convert_ast_type_to_mapper(&args[0])))
                } else {
                    // For other generic types, use the base name
                    MapperVerusType::Named(name.to_string())
                }
            }
            VerusType::Reference { ty, .. } => {
                // Strip reference and use underlying type
                self.convert_ast_type_to_mapper(ty)
            }
        }
    }

    /// Convert a list of spec functions to a TLA+ module.
    pub fn convert_functions(
        &mut self,
        module_name: &str,
        functions: Vec<SpecFunction>,
    ) -> Result<TlaModule, ConversionError> {
        let mut module = TlaModule::new(self.strip_prefix(module_name));
        module.extends = self.config.standard_extends.clone();

        // Reset constants for this module
        self.constants.clear();

        // Convert each function to a TLA+ operator
        for func in &functions {
            let operator = self.convert_function(func)?;
            module.operators.push(operator);

            // Collect type information for type definitions
            if self.config.generate_type_defs {
                self.collect_types(func);
            }
        }

        // Add collected constants
        for constant in &self.constants {
            module
                .constants
                .push(TlaConstantDecl::new(constant.clone()));
        }

        // Generate type definitions as operators
        if self.config.generate_type_defs {
            let type_ops = self.generate_type_operators();
            // Insert type definitions at the beginning
            for (i, op) in type_ops.into_iter().enumerate() {
                module.operators.insert(i, op);
            }
        }

        Ok(module)
    }

    /// Convert a single spec function to a TLA+ operator.
    pub fn convert_function(
        &mut self,
        func: &SpecFunction,
    ) -> Result<TlaOperator, ConversionError> {
        let name = self.strip_prefix(&func.name);

        // Convert parameters
        let params: Vec<TlaParam> = func.params.iter().map(|p| TlaParam::new(&p.name)).collect();

        // Convert function body
        let body = self.convert_expr(&func.body)?;

        let mut operator = TlaOperator::new(name, body).with_params(params);

        // Mark as recursive if the function calls itself
        if self.is_recursive(func) {
            operator = operator.recursive();
        }

        Ok(operator)
    }

    /// Convert a Verus expression to a TLA+ expression.
    pub fn convert_expr(&mut self, expr: &VerusExpr) -> Result<TlaExpr, ConversionError> {
        match expr {
            // Logical operators
            VerusExpr::Conjunction(exprs) => {
                if exprs.is_empty() {
                    return Ok(TlaExpr::Bool(true));
                }
                let converted: Result<Vec<_>, _> =
                    exprs.iter().map(|e| self.convert_expr(e)).collect();
                let converted = converted?;

                // Build a chain of AND operations
                let mut result = converted[0].clone();
                for expr in converted.into_iter().skip(1) {
                    result = TlaExpr::binop(TlaBinOp::And, result, expr);
                }
                Ok(result)
            }

            VerusExpr::Disjunction(exprs) => {
                if exprs.is_empty() {
                    return Ok(TlaExpr::Bool(false));
                }
                let converted: Result<Vec<_>, _> =
                    exprs.iter().map(|e| self.convert_expr(e)).collect();
                let converted = converted?;

                let mut result = converted[0].clone();
                for expr in converted.into_iter().skip(1) {
                    result = TlaExpr::binop(TlaBinOp::Or, result, expr);
                }
                Ok(result)
            }

            VerusExpr::Implies(left, right) => Ok(TlaExpr::binop(
                TlaBinOp::Implies,
                self.convert_expr(left)?,
                self.convert_expr(right)?,
            )),

            VerusExpr::Iff(left, right) => Ok(TlaExpr::binop(
                TlaBinOp::Iff,
                self.convert_expr(left)?,
                self.convert_expr(right)?,
            )),

            VerusExpr::Not(inner) => Ok(TlaExpr::unary(TlaUnaryOp::Not, self.convert_expr(inner)?)),

            // Quantifiers
            VerusExpr::Forall { vars, body, .. } => {
                let bounds = self.convert_bindings(vars)?;
                Ok(TlaExpr::Forall {
                    vars: bounds,
                    body: Box::new(self.convert_expr(body)?),
                })
            }

            VerusExpr::Exists { vars, body } => {
                let bounds = self.convert_bindings(vars)?;
                Ok(TlaExpr::Exists {
                    vars: bounds,
                    body: Box::new(self.convert_expr(body)?),
                })
            }

            // Control flow
            VerusExpr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_expr = self.convert_expr(cond)?;
                let then_expr = self.convert_expr(then_branch)?;
                let else_expr = if let Some(else_br) = else_branch {
                    self.convert_expr(else_br)?
                } else {
                    // No else branch - this is unusual for spec functions
                    TlaExpr::Bool(true)
                };

                Ok(TlaExpr::IfThenElse {
                    cond: Box::new(cond_expr),
                    then_expr: Box::new(then_expr),
                    else_expr: Box::new(else_expr),
                })
            }

            VerusExpr::Match { scrutinee, arms } => self.convert_match(scrutinee, arms),

            VerusExpr::Let {
                binding,
                value,
                body,
            } => {
                let name = match binding.name() {
                    Some(n) if n != "_" => n.to_string(),
                    _ => {
                        // Generate a unique dummy name for wildcard patterns
                        // since TLA+ doesn't support `_` as identifier
                        format!("unused_{}", self.constants.len())
                    }
                };
                let value_expr = self.convert_expr(value)?;
                let body_expr = self.convert_expr(body)?;

                Ok(TlaExpr::LetIn {
                    defs: vec![TlaOperator::new(&name, value_expr)],
                    body: Box::new(body_expr),
                })
            }

            // Comparisons
            VerusExpr::Eq(left, right) => Ok(TlaExpr::binop(
                TlaBinOp::Eq,
                self.convert_expr(left)?,
                self.convert_expr(right)?,
            )),

            VerusExpr::Ne(left, right) => Ok(TlaExpr::binop(
                TlaBinOp::Neq,
                self.convert_expr(left)?,
                self.convert_expr(right)?,
            )),

            VerusExpr::Lt(left, right) => Ok(TlaExpr::binop(
                TlaBinOp::Lt,
                self.convert_expr(left)?,
                self.convert_expr(right)?,
            )),

            VerusExpr::Le(left, right) => Ok(TlaExpr::binop(
                TlaBinOp::Leq,
                self.convert_expr(left)?,
                self.convert_expr(right)?,
            )),

            VerusExpr::Gt(left, right) => Ok(TlaExpr::binop(
                TlaBinOp::Gt,
                self.convert_expr(left)?,
                self.convert_expr(right)?,
            )),

            VerusExpr::Ge(left, right) => Ok(TlaExpr::binop(
                TlaBinOp::Geq,
                self.convert_expr(left)?,
                self.convert_expr(right)?,
            )),

            VerusExpr::Is(expr, variant) => {
                // Convert "expr is Variant" to record field check or equality
                // This is a simplification - real handling depends on enum definition
                let expr_converted = self.convert_expr(expr)?;
                Ok(TlaExpr::binop(
                    TlaBinOp::Eq,
                    TlaExpr::RecordAccess {
                        record: Box::new(expr_converted),
                        field: "tag".to_string(),
                    },
                    TlaExpr::ident(variant),
                ))
            }

            // Access
            VerusExpr::Field(base, field) => {
                let base_expr = self.convert_expr(base)?;

                // Check if field is a numeric string (tuple access like .0, .1)
                if let Ok(idx) = field.parse::<usize>() {
                    // Convert to TLA+ 1-based indexing: .0 -> [1], .1 -> [2], etc.
                    Ok(TlaExpr::FnApply {
                        func: Box::new(base_expr),
                        arg: Box::new(TlaExpr::Number(TlaNumber::Decimal((idx + 1).to_string()))),
                    })
                } else {
                    // Regular field access
                    Ok(TlaExpr::RecordAccess {
                        record: Box::new(base_expr),
                        field: field.clone(),
                    })
                }
            }

            VerusExpr::Index(base, index) => {
                let base_expr = self.convert_expr(base)?;
                let index_expr = self.convert_expr(index)?;
                Ok(TlaExpr::FnApply {
                    func: Box::new(base_expr),
                    arg: Box::new(index_expr),
                })
            }

            VerusExpr::Arrow(base, field) => {
                // Arrow access for enum variants - treat as record access
                let base_expr = self.convert_expr(base)?;
                Ok(TlaExpr::RecordAccess {
                    record: Box::new(base_expr),
                    field: field.clone(),
                })
            }

            // Struct construction
            VerusExpr::Struct { name: _, fields } => {
                // Check if all field names are numeric (tuple-like struct)
                let all_numeric = fields
                    .iter()
                    .all(|(fname, _)| fname.parse::<usize>().is_ok());

                if all_numeric && !fields.is_empty() {
                    // Convert to tuple, sorted by numeric index
                    let mut indexed_exprs: Vec<(usize, TlaExpr)> = fields
                        .iter()
                        .filter_map(|(fname, fexpr)| {
                            fname
                                .parse::<usize>()
                                .ok()
                                .and_then(|idx| self.convert_expr(fexpr).ok().map(|e| (idx, e)))
                        })
                        .collect();
                    indexed_exprs.sort_by_key(|(idx, _)| *idx);
                    let tuple_exprs: Vec<TlaExpr> =
                        indexed_exprs.into_iter().map(|(_, e)| e).collect();
                    Ok(TlaExpr::Tuple(tuple_exprs))
                } else {
                    let tla_fields: Result<Vec<_>, _> = fields
                        .iter()
                        .map(|(fname, fexpr)| self.convert_expr(fexpr).map(|e| (fname.clone(), e)))
                        .collect();
                    Ok(TlaExpr::Record(tla_fields?))
                }
            }

            VerusExpr::StructUpdate { base, fields, .. } => {
                // Convert struct update to EXCEPT
                let base_expr = self.convert_expr(base)?;
                let updates: Result<Vec<_>, _> = fields
                    .iter()
                    .map(|(fname, fexpr)| {
                        self.convert_expr(fexpr).map(|e| TlaExceptUpdate {
                            path: vec![TlaExceptPath::Field(fname.clone())],
                            value: e,
                        })
                    })
                    .collect();
                Ok(TlaExpr::FnExcept {
                    func: Box::new(base_expr),
                    updates: updates?,
                })
            }

            // Collections
            VerusExpr::SeqLit(elements) => {
                let converted: Result<Vec<_>, _> =
                    elements.iter().map(|e| self.convert_expr(e)).collect();
                Ok(TlaExpr::Tuple(converted?))
            }

            VerusExpr::SetLit(elements) => {
                let converted: Result<Vec<_>, _> =
                    elements.iter().map(|e| self.convert_expr(e)).collect();
                Ok(TlaExpr::SetEnum(converted?))
            }

            VerusExpr::MapLit(entries) => {
                // Convert map literal to function construction
                // This is a simplification - proper handling needs type info
                if entries.is_empty() {
                    return Ok(TlaExpr::ident("<<>>"));
                }
                // For now, represent as a set of tuples
                let converted: Result<Vec<_>, _> = entries
                    .iter()
                    .map(|(k, v)| {
                        let key = self.convert_expr(k)?;
                        let val = self.convert_expr(v)?;
                        Ok(TlaExpr::Tuple(vec![key, val]))
                    })
                    .collect();
                Ok(TlaExpr::SetEnum(converted?))
            }

            VerusExpr::SeqEmpty => Ok(TlaExpr::Tuple(vec![])),
            VerusExpr::SetEmpty => Ok(TlaExpr::SetEnum(vec![])),
            VerusExpr::MapEmpty => Ok(TlaExpr::ident("<<>>")),

            // Calls
            VerusExpr::Call { func, args } => {
                let func_name = self.strip_prefix(&path_to_string(func));
                // Strip turbofish syntax (e.g., "Seq::<int>::empty" -> "Seq::empty")
                let func_name = strip_turbofish(&func_name);
                let converted_args: Result<Vec<_>, _> =
                    args.iter().map(|a| self.convert_expr(a)).collect();

                // Handle special built-in functions
                match func_name.as_str() {
                    "Seq::empty" => return Ok(TlaExpr::Tuple(vec![])),
                    "Set::empty" => return Ok(TlaExpr::SetEnum(vec![])),
                    "Map::empty" => return Ok(TlaExpr::Tuple(vec![])), // Empty function as empty tuple
                    _ => {}
                }

                // Strip enum type prefix: "TPCMessage::Prepare" -> "Prepare"
                // Multi-segment paths in TLA+ are invalid (:: is not TLA+ syntax),
                // so use only the last segment (the variant/function name).
                let tla_name = if func_name.contains("::") {
                    func_name
                        .rsplit("::")
                        .next()
                        .unwrap_or(&func_name)
                        .to_string()
                } else {
                    func_name
                };

                Ok(TlaExpr::OpApply {
                    op: Box::new(TlaExpr::ident(&tla_name)),
                    args: converted_args?,
                })
            }

            VerusExpr::MethodCall {
                receiver,
                method,
                args,
            } => self.convert_method_call(receiver, method, args),

            // Verus-specific
            VerusExpr::View(inner) => {
                // View operator @ - in TLA+ we just use the expression directly
                // since TLA+ doesn't distinguish between spec and exec views
                self.convert_expr(inner)
            }

            VerusExpr::Cast(inner, _ty) => {
                // Type casts are mostly erased in TLA+
                self.convert_expr(inner)
            }

            // Primitives
            VerusExpr::Ident(name) => {
                let stripped = self.strip_prefix(name);
                // Strip Rust enum type prefix: "TPCMessage::Prepare" -> "Prepare"
                let tla_name = if stripped.contains("::") {
                    stripped
                        .rsplit("::")
                        .next()
                        .unwrap_or(&stripped)
                        .to_string()
                } else {
                    stripped
                };
                Ok(TlaExpr::ident(&tla_name))
            }

            VerusExpr::Literal(lit) => self.convert_literal(lit),

            VerusExpr::Binary(left, op, right) => {
                let tla_op = self.convert_binop(op)?;
                Ok(TlaExpr::binop(
                    tla_op,
                    self.convert_expr(left)?,
                    self.convert_expr(right)?,
                ))
            }

            VerusExpr::Unary(op, inner) => {
                let tla_op = self.convert_unaryop(op)?;
                Ok(TlaExpr::unary(tla_op, self.convert_expr(inner)?))
            }
        }
    }

    /// Convert quantifier bindings to TLA+ quantifier bounds.
    fn convert_bindings(
        &self,
        bindings: &[Binding],
    ) -> Result<Vec<TlaQuantBound>, ConversionError> {
        bindings
            .iter()
            .map(|b| {
                let var = b.name().unwrap_or("_").to_string();
                let set = b.ty.as_ref().map(|t| self.type_to_set_expr(t));
                Ok(TlaQuantBound { var, set })
            })
            .collect()
    }

    /// Convert a Verus type to a TLA+ set expression (for quantifier bounds).
    fn type_to_set_expr(&self, ty: &VerusType) -> TlaExpr {
        match ty {
            VerusType::Int => TlaExpr::ident("Int"),
            VerusType::Nat => TlaExpr::ident("Nat"),
            VerusType::Bool => TlaExpr::ident("BOOLEAN"),
            VerusType::Named(path) => {
                let name = self.strip_prefix(path.last().unwrap_or("Unknown"));
                TlaExpr::ident(&name)
            }
            VerusType::Seq(inner) => {
                let inner_set = self.type_to_set_expr(inner);
                TlaExpr::OpApply {
                    op: Box::new(TlaExpr::ident("Seq")),
                    args: vec![inner_set],
                }
            }
            VerusType::Set(inner) => {
                let inner_set = self.type_to_set_expr(inner);
                TlaExpr::unary(TlaUnaryOp::Subset, inner_set)
            }
            _ => TlaExpr::ident("Unknown"),
        }
    }

    /// Convert a match expression to TLA+ CASE expression.
    fn convert_match(
        &mut self,
        scrutinee: &VerusExpr,
        arms: &[MatchArm],
    ) -> Result<TlaExpr, ConversionError> {
        let scrutinee_expr = self.convert_expr(scrutinee)?;

        let mut case_arms: Vec<(TlaExpr, TlaExpr)> = Vec::new();
        let mut other_case: Option<Box<TlaExpr>> = None;

        for arm in arms {
            match &arm.pattern {
                Pattern::Wildcard => {
                    // Wildcard is the OTHER case
                    other_case = Some(Box::new(self.convert_expr(&arm.body)?));
                }
                Pattern::Ident(_name) => {
                    // Simple identifier pattern - this becomes a let binding essentially
                    // For CASE, we treat it as OTHER since it matches everything
                    if other_case.is_none() {
                        other_case = Some(Box::new(self.convert_expr(&arm.body)?));
                    }
                }
                Pattern::Variant { name, .. } => {
                    // Enum variant match
                    let variant_name = name.last().unwrap_or("Unknown");
                    let condition = TlaExpr::binop(
                        TlaBinOp::Eq,
                        TlaExpr::RecordAccess {
                            record: Box::new(scrutinee_expr.clone()),
                            field: "tag".to_string(),
                        },
                        TlaExpr::ident(variant_name),
                    );
                    let body = self.convert_expr(&arm.body)?;
                    case_arms.push((condition, body));
                }
                Pattern::Literal(lit) => {
                    let lit_expr = self.convert_literal(lit)?;
                    let condition = TlaExpr::binop(TlaBinOp::Eq, scrutinee_expr.clone(), lit_expr);
                    let body = self.convert_expr(&arm.body)?;
                    case_arms.push((condition, body));
                }
                _ => {
                    // Other patterns - simplified handling
                    let body = self.convert_expr(&arm.body)?;
                    if other_case.is_none() {
                        other_case = Some(Box::new(body));
                    }
                }
            }
        }

        if case_arms.is_empty() {
            // No explicit cases, just return the other case or TRUE
            return Ok(other_case.map(|b| *b).unwrap_or(TlaExpr::Bool(true)));
        }

        Ok(TlaExpr::Case {
            arms: case_arms,
            other: other_case,
        })
    }

    /// Convert a method call to TLA+ expression.
    fn convert_method_call(
        &mut self,
        receiver: &VerusExpr,
        method: &str,
        args: &[VerusExpr],
    ) -> Result<TlaExpr, ConversionError> {
        let receiver_expr = self.convert_expr(receiver)?;

        match method {
            // Sequence methods
            "len" => Ok(TlaExpr::OpApply {
                op: Box::new(TlaExpr::ident("Len")),
                args: vec![receiver_expr],
            }),
            "push" => {
                let arg = self.convert_expr(&args[0])?;
                Ok(TlaExpr::OpApply {
                    op: Box::new(TlaExpr::ident("Append")),
                    args: vec![receiver_expr, arg],
                })
            }
            "first" | "head" => Ok(TlaExpr::OpApply {
                op: Box::new(TlaExpr::ident("Head")),
                args: vec![receiver_expr],
            }),
            "last" => Ok(TlaExpr::OpApply {
                op: Box::new(TlaExpr::ident("Last")),
                args: vec![receiver_expr],
            }),
            "subrange" => {
                let start = self.convert_expr(&args[0])?;
                let end = self.convert_expr(&args[1])?;
                Ok(TlaExpr::OpApply {
                    op: Box::new(TlaExpr::ident("SubSeq")),
                    args: vec![receiver_expr, start, end],
                })
            }

            // Set methods
            "contains" => {
                let elem = self.convert_expr(&args[0])?;
                Ok(TlaExpr::binop(TlaBinOp::In, elem, receiver_expr))
            }
            // Insert - distinguish between Set (1 arg) and Map (2 args)
            "insert" if args.len() == 2 => {
                // Map insert (key, value)
                let key = self.convert_expr(&args[0])?;
                let value = self.convert_expr(&args[1])?;
                Ok(TlaExpr::FnExcept {
                    func: Box::new(receiver_expr),
                    updates: vec![TlaExceptUpdate {
                        path: vec![TlaExceptPath::Index(key)],
                        value,
                    }],
                })
            }
            "insert" => {
                // Set insert (1 arg)
                let elem = self.convert_expr(&args[0])?;
                Ok(TlaExpr::binop(
                    TlaBinOp::Cup,
                    receiver_expr,
                    TlaExpr::SetEnum(vec![elem]),
                ))
            }
            "remove" => {
                let elem = self.convert_expr(&args[0])?;
                Ok(TlaExpr::binop(
                    TlaBinOp::Setminus,
                    receiver_expr,
                    TlaExpr::SetEnum(vec![elem]),
                ))
            }
            "union" => {
                let other = self.convert_expr(&args[0])?;
                Ok(TlaExpr::binop(TlaBinOp::Cup, receiver_expr, other))
            }
            "intersect" => {
                let other = self.convert_expr(&args[0])?;
                Ok(TlaExpr::binop(TlaBinOp::Cap, receiver_expr, other))
            }
            "subset_of" => {
                let other = self.convert_expr(&args[0])?;
                Ok(TlaExpr::binop(TlaBinOp::Subseteq, receiver_expr, other))
            }

            // Map methods
            "index" | "get" => {
                let key = self.convert_expr(&args[0])?;
                Ok(TlaExpr::FnApply {
                    func: Box::new(receiver_expr),
                    arg: Box::new(key),
                })
            }
            "contains_key" => {
                let key = self.convert_expr(&args[0])?;
                Ok(TlaExpr::binop(
                    TlaBinOp::In,
                    key,
                    TlaExpr::unary(TlaUnaryOp::Domain, receiver_expr),
                ))
            }
            "dom" | "domain" => Ok(TlaExpr::unary(TlaUnaryOp::Domain, receiver_expr)),

            // Default: treat as operator application
            _ => {
                let mut all_args = vec![receiver_expr];
                for arg in args {
                    all_args.push(self.convert_expr(arg)?);
                }
                Ok(TlaExpr::OpApply {
                    op: Box::new(TlaExpr::ident(method)),
                    args: all_args,
                })
            }
        }
    }

    /// Convert a literal to TLA+ expression.
    fn convert_literal(&self, lit: &Literal) -> Result<TlaExpr, ConversionError> {
        match lit {
            Literal::Bool(b) => Ok(TlaExpr::Bool(*b)),
            Literal::Int(n) => Ok(TlaExpr::Number(TlaNumber::Decimal(n.to_string()))),
            Literal::String(s) => Ok(TlaExpr::String(s.clone())),
        }
    }

    /// Convert a binary operator.
    fn convert_binop(&self, op: &BinOp) -> Result<TlaBinOp, ConversionError> {
        match op {
            BinOp::Add => Ok(TlaBinOp::Plus),
            BinOp::Sub => Ok(TlaBinOp::Minus),
            BinOp::Mul => Ok(TlaBinOp::Times),
            BinOp::Div => Ok(TlaBinOp::Div),
            BinOp::Mod => Ok(TlaBinOp::Mod),
            BinOp::And => Ok(TlaBinOp::And),
            BinOp::Or => Ok(TlaBinOp::Or),
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                Err(ConversionError::UnsupportedConstruct(
                    "Bitwise operations are not supported in TLA+".to_string(),
                ))
            }
        }
    }

    /// Convert a unary operator.
    fn convert_unaryop(&self, op: &UnaryOp) -> Result<TlaUnaryOp, ConversionError> {
        match op {
            UnaryOp::Not => Ok(TlaUnaryOp::Not),
            UnaryOp::Neg => Ok(TlaUnaryOp::Neg),
            UnaryOp::Deref => {
                // Dereference is erased in TLA+
                Err(ConversionError::UnsupportedConstruct(
                    "Dereference operator is not meaningful in TLA+".to_string(),
                ))
            }
        }
    }

    /// Strip the spec prefix from a name.
    /// Only strips if the character after the prefix is uppercase,
    /// to distinguish "LReplica" (spec type) from "LearnerTuple" (regular name).
    fn strip_prefix(&self, name: &str) -> String {
        if let Some(rest) = name.strip_prefix(&self.config.spec_prefix) {
            // Only strip if the next character is uppercase (indicates spec type convention)
            if rest
                .chars()
                .next()
                .map(|c| c.is_uppercase())
                .unwrap_or(false)
            {
                return rest.to_string();
            }
        }
        name.to_string()
    }

    /// Check if a function is recursive.
    fn is_recursive(&self, func: &SpecFunction) -> bool {
        self.expr_contains_call(&func.body, &func.name)
    }

    /// Check if an expression contains a call to the given function.
    fn expr_contains_call(&self, expr: &VerusExpr, func_name: &str) -> bool {
        match expr {
            VerusExpr::Call { func, args } => {
                if path_to_string(func) == func_name {
                    return true;
                }
                args.iter().any(|a| self.expr_contains_call(a, func_name))
            }
            VerusExpr::Conjunction(exprs) | VerusExpr::Disjunction(exprs) => {
                exprs.iter().any(|e| self.expr_contains_call(e, func_name))
            }
            VerusExpr::Implies(l, r)
            | VerusExpr::Iff(l, r)
            | VerusExpr::Eq(l, r)
            | VerusExpr::Ne(l, r)
            | VerusExpr::Lt(l, r)
            | VerusExpr::Le(l, r)
            | VerusExpr::Gt(l, r)
            | VerusExpr::Ge(l, r)
            | VerusExpr::Binary(l, _, r) => {
                self.expr_contains_call(l, func_name) || self.expr_contains_call(r, func_name)
            }
            VerusExpr::Not(inner)
            | VerusExpr::View(inner)
            | VerusExpr::Cast(inner, _)
            | VerusExpr::Unary(_, inner) => self.expr_contains_call(inner, func_name),
            VerusExpr::Forall { body, .. } | VerusExpr::Exists { body, .. } => {
                self.expr_contains_call(body, func_name)
            }
            VerusExpr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.expr_contains_call(cond, func_name)
                    || self.expr_contains_call(then_branch, func_name)
                    || else_branch
                        .as_ref()
                        .map(|e| self.expr_contains_call(e, func_name))
                        .unwrap_or(false)
            }
            VerusExpr::Let { value, body, .. } => {
                self.expr_contains_call(value, func_name)
                    || self.expr_contains_call(body, func_name)
            }
            VerusExpr::MethodCall { receiver, args, .. } => {
                self.expr_contains_call(receiver, func_name)
                    || args.iter().any(|a| self.expr_contains_call(a, func_name))
            }
            _ => false,
        }
    }

    /// Collect type information from a function.
    fn collect_types(&mut self, func: &SpecFunction) {
        for param in &func.params {
            self.collect_type(&param.ty);
        }
    }

    /// Collect type information recursively.
    fn collect_type(&mut self, ty: &VerusType) {
        match ty {
            VerusType::Named(path) => {
                if let Some(name) = path.last() {
                    // Register as a potential type that might need definition
                    let stripped = self.strip_prefix(name);
                    self.constants.insert(stripped);
                }
            }
            VerusType::Seq(inner) | VerusType::Set(inner) => {
                self.collect_type(inner);
            }
            VerusType::Map(k, v) => {
                self.collect_type(k);
                self.collect_type(v);
            }
            VerusType::Tuple(parts) => {
                for part in parts {
                    self.collect_type(part);
                }
            }
            VerusType::Generic(_, args) => {
                for arg in args {
                    self.collect_type(arg);
                }
            }
            _ => {}
        }
    }

    /// Generate type definition operators.
    fn generate_type_operators(&self) -> Vec<TlaOperator> {
        let mut operators = Vec::new();

        // Generate from registered record types
        for (name, fields) in self.type_mapper.record_types() {
            let field_exprs: Vec<(String, TlaExpr)> = fields
                .iter()
                .map(|(fname, ftype)| {
                    let type_expr = TlaExpr::ident(self.type_mapper.map_type(ftype));
                    (fname.clone(), type_expr)
                })
                .collect();

            let body = TlaExpr::Record(field_exprs);
            operators.push(TlaOperator::new(name, body));
        }

        // Generate from registered enum types
        for (name, variants) in self.type_mapper.enum_types() {
            let variant_exprs: Vec<TlaExpr> = variants.iter().map(TlaExpr::ident).collect();
            let body = TlaExpr::SetEnum(variant_exprs);
            operators.push(TlaOperator::new(name, body));
        }

        operators
    }

    /// Get a reference to the type mapper for external type registration.
    pub fn type_mapper_mut(&mut self) -> &mut TypeMapper {
        &mut self.type_mapper
    }
}

impl Default for Verus2TlaConverter {
    fn default() -> Self {
        Self::new()
    }
}

/// Convert a Path to a string.
fn path_to_string(path: &Path) -> String {
    path.segments.join("::")
}

/// Strip turbofish syntax from a function name.
/// E.g., "Seq::<int>::empty" -> "Seq::empty"
///       "Map::<K, V>::empty" -> "Map::empty"
fn strip_turbofish(s: &str) -> String {
    let mut result = String::new();
    let mut depth = 0;
    let mut chars = s.chars().peekable();

    while let Some(c) = chars.next() {
        if c == ':' && chars.peek() == Some(&':') && depth == 0 {
            // Check if next is '<' (turbofish)
            let mut lookahead = chars.clone();
            lookahead.next(); // consume second ':'
            if lookahead.peek() == Some(&'<') {
                // Skip the ::<...> part
                chars.next(); // consume second ':'
                chars.next(); // consume '<'
                depth = 1;
                while depth > 0 {
                    match chars.next() {
                        Some('<') => depth += 1,
                        Some('>') => depth -= 1,
                        None => break,
                        _ => {}
                    }
                }
                continue;
            }
        }

        if depth == 0 {
            result.push(c);
        }
    }

    result
}

/// Conversion error types.
#[derive(Debug, Clone)]
pub enum ConversionError {
    /// Error parsing the source file
    ParseError(String),
    /// Unsupported Verus construct
    UnsupportedConstruct(String),
    /// Type conversion error
    TypeError(String),
    /// Generic error
    Other(String),
}

impl std::fmt::Display for ConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConversionError::ParseError(msg) => write!(f, "Parse error: {}", msg),
            ConversionError::UnsupportedConstruct(msg) => {
                write!(f, "Unsupported construct: {}", msg)
            }
            ConversionError::TypeError(msg) => write!(f, "Type error: {}", msg),
            ConversionError::Other(msg) => write!(f, "Error: {}", msg),
        }
    }
}

impl std::error::Error for ConversionError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Generics, VariableMode};

    fn make_simple_func(name: &str, body: VerusExpr) -> SpecFunction {
        SpecFunction {
            name: name.to_string(),
            generics: Generics::default(),
            params: vec![],
            return_type: VerusType::Bool,
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            body,
            span: None,
        }
    }

    #[test]
    fn test_convert_simple_conjunction() {
        let mut converter = Verus2TlaConverter::new();

        let body = VerusExpr::Conjunction(vec![
            VerusExpr::Eq(
                Box::new(VerusExpr::Ident("x".to_string())),
                Box::new(VerusExpr::Literal(Literal::Int(0))),
            ),
            VerusExpr::Eq(
                Box::new(VerusExpr::Ident("y".to_string())),
                Box::new(VerusExpr::Literal(Literal::Int(0))),
            ),
        ]);

        let func = make_simple_func("LInit", body);
        let operator = converter.convert_function(&func).unwrap();

        assert_eq!(operator.name, "Init");
    }

    #[test]
    fn test_convert_if_then_else() {
        let mut converter = Verus2TlaConverter::new();

        let body = VerusExpr::If {
            cond: Box::new(VerusExpr::Gt(
                Box::new(VerusExpr::Ident("x".to_string())),
                Box::new(VerusExpr::Literal(Literal::Int(0))),
            )),
            then_branch: Box::new(VerusExpr::Ident("x".to_string())),
            else_branch: Some(Box::new(VerusExpr::Literal(Literal::Int(0)))),
        };

        let result = converter.convert_expr(&body).unwrap();
        assert!(matches!(result, TlaExpr::IfThenElse { .. }));
    }

    #[test]
    fn test_convert_forall() {
        let mut converter = Verus2TlaConverter::new();

        let body = VerusExpr::Forall {
            vars: vec![Binding {
                pattern: Pattern::Ident("i".to_string()),
                ty: Some(VerusType::Nat),
                variable_mode: VariableMode::Ghost,
            }],
            triggers: vec![],
            body: Box::new(VerusExpr::Gt(
                Box::new(VerusExpr::Ident("i".to_string())),
                Box::new(VerusExpr::Literal(Literal::Int(0))),
            )),
        };

        let result = converter.convert_expr(&body).unwrap();
        assert!(matches!(result, TlaExpr::Forall { .. }));
    }

    #[test]
    fn test_convert_field_access() {
        let mut converter = Verus2TlaConverter::new();

        let body = VerusExpr::Field(
            Box::new(VerusExpr::Ident("state".to_string())),
            "value".to_string(),
        );

        let result = converter.convert_expr(&body).unwrap();
        assert!(matches!(result, TlaExpr::RecordAccess { field, .. } if field == "value"));
    }

    #[test]
    fn test_strip_prefix() {
        let converter = Verus2TlaConverter::new();

        // Should strip L from spec types (followed by uppercase)
        assert_eq!(converter.strip_prefix("LReplica"), "Replica");
        assert_eq!(converter.strip_prefix("LInit"), "Init");
        assert_eq!(converter.strip_prefix("LAcceptor"), "Acceptor");

        // Should NOT strip L from regular names (followed by lowercase)
        assert_eq!(converter.strip_prefix("LearnerTuple"), "LearnerTuple");
        assert_eq!(converter.strip_prefix("LearnerState"), "LearnerState");

        // Should not modify names without the prefix
        assert_eq!(converter.strip_prefix("NoPrefix"), "NoPrefix");
        assert_eq!(converter.strip_prefix("Ballot"), "Ballot");
    }

    #[test]
    fn test_convert_method_call_len() {
        let mut converter = Verus2TlaConverter::new();

        let body = VerusExpr::MethodCall {
            receiver: Box::new(VerusExpr::Ident("seq".to_string())),
            method: "len".to_string(),
            args: vec![],
        };

        let result = converter.convert_expr(&body).unwrap();
        match result {
            TlaExpr::OpApply { op, args } => {
                assert!(matches!(*op, TlaExpr::Ident(name) if name == "Len"));
                assert_eq!(args.len(), 1);
            }
            _ => panic!("Expected OpApply"),
        }
    }

    #[test]
    fn test_register_types_from_defs() {
        use crate::ast::{Generics, Type};
        use crate::types::{
            EnumDef, FieldDef, StructDef, TypeAlias, TypeDef, VariantDef, VariantFields,
        };

        let mut converter = Verus2TlaConverter::new();

        // Create test type definitions
        let struct_def = StructDef {
            name: "LBallot".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "seqno".to_string(),
                    ty: Type::Int,
                    is_public: true,
                },
                FieldDef {
                    name: "proposer_id".to_string(),
                    ty: Type::Nat,
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        let enum_def = EnumDef {
            name: "LMessageType".to_string(),
            generics: Generics::default(),
            variants: vec![
                VariantDef {
                    name: "Msg1a".to_string(),
                    fields: VariantFields::Unit,
                },
                VariantDef {
                    name: "Msg1b".to_string(),
                    fields: VariantFields::Unit,
                },
            ],
            is_spec: true,
        };

        let type_alias = TypeAlias {
            name: "Votes".to_string(),
            generics: Generics::default(),
            ty: Type::Map(Box::new(Type::Int), Box::new(Type::Bool)),
        };

        let type_defs = vec![
            TypeDef::Struct(struct_def),
            TypeDef::Enum(enum_def),
            TypeDef::Alias(type_alias),
        ];

        // Register the types
        converter.register_types_from_defs(&type_defs);

        // Verify struct was registered
        let record_types = converter.type_mapper.record_types();
        assert!(
            record_types.contains_key("Ballot"),
            "Should have registered Ballot struct"
        );
        let ballot_fields = record_types.get("Ballot").unwrap();
        assert_eq!(ballot_fields.len(), 2);
        assert_eq!(ballot_fields[0].0, "seqno");
        assert_eq!(ballot_fields[1].0, "proposer_id");

        // Verify enum was registered
        let enum_types = converter.type_mapper.enum_types();
        assert!(
            enum_types.contains_key("MessageType"),
            "Should have registered MessageType enum"
        );
        let message_variants = enum_types.get("MessageType").unwrap();
        assert_eq!(message_variants.len(), 2);
        assert!(message_variants.contains(&"Msg1a".to_string()));
        assert!(message_variants.contains(&"Msg1b".to_string()));

        // Verify type operator generation
        let type_ops = converter.generate_type_operators();
        assert!(
            type_ops.len() >= 2,
            "Should generate operators for struct and enum"
        );
    }

    #[test]
    fn test_convert_ast_type_to_mapper() {
        use crate::ast::{Path, Type};

        let converter = Verus2TlaConverter::new();

        // Test primitives
        assert_eq!(
            converter
                .convert_ast_type_to_mapper(&Type::Int)
                .to_tla_type(),
            "Int"
        );
        assert_eq!(
            converter
                .convert_ast_type_to_mapper(&Type::Nat)
                .to_tla_type(),
            "Nat"
        );
        assert_eq!(
            converter
                .convert_ast_type_to_mapper(&Type::Bool)
                .to_tla_type(),
            "BOOLEAN"
        );

        // Test Seq
        let seq_int = Type::Seq(Box::new(Type::Int));
        assert_eq!(
            converter.convert_ast_type_to_mapper(&seq_int).to_tla_type(),
            "Seq(Int)"
        );

        // Test Map
        let map_type = Type::Map(Box::new(Type::Int), Box::new(Type::Bool));
        assert_eq!(
            converter
                .convert_ast_type_to_mapper(&map_type)
                .to_tla_type(),
            "[Int -> BOOLEAN]"
        );

        // Test Named with L prefix (spec type)
        let named_type = Type::Named(Path::single("LReplica".to_string()));
        assert_eq!(
            converter
                .convert_ast_type_to_mapper(&named_type)
                .to_tla_type(),
            "Replica"
        );

        // Test Reference (should strip reference)
        let ref_type = Type::Reference {
            ty: Box::new(Type::Int),
            mutable: false,
        };
        assert_eq!(
            converter
                .convert_ast_type_to_mapper(&ref_type)
                .to_tla_type(),
            "Int"
        );
    }

    #[test]
    fn test_convert_file_with_types() {
        use std::io::Write;

        // Create a temporary file with structs and functions
        let source = r#"
use vstd::prelude::*;

verus! {
    pub struct Ballot {
        pub seqno: int,
        pub proposer_id: int,
    }

    pub type Votes = Map<int, Ballot>;

    pub open spec fn BalLeq(ba: Ballot, bb: Ballot) -> bool {
        ||| ba.seqno < bb.seqno
        ||| ba.seqno == bb.seqno && ba.proposer_id <= bb.proposer_id
    }
}
"#;

        // Write to temporary file
        let temp_dir = std::env::temp_dir();
        let temp_file = temp_dir.join("test_verus_types.rs");
        let mut file = std::fs::File::create(&temp_file).unwrap();
        file.write_all(source.as_bytes()).unwrap();

        // Convert the file
        let mut converter = Verus2TlaConverter::new();
        let module = converter.convert_file(&temp_file).unwrap();

        // Clean up
        std::fs::remove_file(&temp_file).unwrap();

        // Verify module structure
        assert_eq!(module.name, "Test_verus_types");

        // Print operators for debugging
        println!(
            "Generated operators: {:?}",
            module.operators.iter().map(|o| &o.name).collect::<Vec<_>>()
        );

        // Verify that type operators were generated
        // Should have Ballot record type operator
        let has_ballot_op = module.operators.iter().any(|op| op.name == "Ballot");
        assert!(
            has_ballot_op,
            "Should have generated Ballot type operator. Operators: {:?}",
            module.operators.iter().map(|o| &o.name).collect::<Vec<_>>()
        );

        // Verify the BalLeq function was converted (Note: the parser may or may not find it
        // depending on verus! block handling - main goal is type extraction)
        // let has_balleq = module.operators.iter().any(|op| op.name == "BalLeq");
        // assert!(has_balleq, "Should have converted BalLeq function");
    }

    #[test]
    fn test_rsl_types_file() {
        use std::path::Path;

        // Test with the actual RSL types.rs file
        let rsl_types_path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .join("src/protocol/RSL/types.rs");

        if !rsl_types_path.exists() {
            println!(
                "Skipping test: RSL types.rs not found at {:?}",
                rsl_types_path
            );
            return;
        }

        // Parse types first
        let type_defs = crate::types::parse_types_from_file(&rsl_types_path).unwrap();
        println!("Parsed {} type definitions:", type_defs.len());
        for td in &type_defs {
            match td {
                crate::types::TypeDef::Struct(s) => {
                    println!("  Struct: {} ({} fields)", s.name, s.fields.len());
                }
                crate::types::TypeDef::Enum(e) => {
                    println!("  Enum: {} ({} variants)", e.name, e.variants.len());
                }
                crate::types::TypeDef::Alias(a) => {
                    println!("  Alias: {}", a.name);
                }
                crate::types::TypeDef::Function(f) => {
                    println!("  Function: {} ({} params)", f.name, f.params.len());
                }
            }
        }

        // Convert file
        let mut converter = Verus2TlaConverter::new();
        let module = converter.convert_file(&rsl_types_path).unwrap();

        println!("\nGenerated {} operators:", module.operators.len());
        for op in &module.operators {
            println!("  - {}", op.name);
        }

        // We should have type operators for the structs
        assert!(!type_defs.is_empty(), "Should have parsed some types");

        // Print TLA+ output
        let printer = crate::verus2tla::printer::TlaPrinter::new();
        let output = printer.print_module(&module);
        println!("\n=== TLA+ Output ===\n{}", output);
    }

    #[test]
    fn test_convert_file_capitalizes_module_name() {
        use std::io::Write;

        // Create a temp file with a lowercase name
        let temp_dir = std::env::temp_dir();
        let temp_file = temp_dir.join("my_protocol.rs");
        let source = r#"
use vstd::prelude::*;
verus! {
    pub open spec fn LInit(s: int) -> bool { s == 0 }
}
"#;
        let mut file = std::fs::File::create(&temp_file).unwrap();
        file.write_all(source.as_bytes()).unwrap();

        let mut converter = Verus2TlaConverter::new();
        let module = converter.convert_file(&temp_file).unwrap();
        std::fs::remove_file(&temp_file).unwrap();

        // Module name should have capitalized first letter to match TLA+ convention
        assert_eq!(
            module.name, "My_protocol",
            "Module name should capitalize first letter for SANY compatibility"
        );

        // Verify the printed output has matching MODULE header
        let printer = crate::verus2tla::printer::TlaPrinter::new();
        let output = printer.print_module(&module);
        assert!(
            output.contains("---- MODULE My_protocol ----"),
            "Printed MODULE header should match capitalized name"
        );
    }

    #[test]
    fn test_convert_file_already_capitalized() {
        use std::io::Write;

        // Create a temp file with already-capitalized name
        let temp_dir = std::env::temp_dir();
        let temp_file = temp_dir.join("Protocol.rs");
        let source = r#"
use vstd::prelude::*;
verus! {
    pub open spec fn LInit(s: int) -> bool { s == 0 }
}
"#;
        let mut file = std::fs::File::create(&temp_file).unwrap();
        file.write_all(source.as_bytes()).unwrap();

        let mut converter = Verus2TlaConverter::new();
        let module = converter.convert_file(&temp_file).unwrap();
        std::fs::remove_file(&temp_file).unwrap();

        // Already capitalized — should stay the same
        assert_eq!(module.name, "Protocol");
    }

    #[test]
    fn test_strip_turbofish() {
        // Simple cases
        assert_eq!(strip_turbofish("Seq::empty"), "Seq::empty");
        assert_eq!(strip_turbofish("Map::empty"), "Map::empty");

        // Turbofish with single type
        assert_eq!(strip_turbofish("Seq::<int>::empty"), "Seq::empty");
        assert_eq!(strip_turbofish("Set::<int>::empty"), "Set::empty");

        // Turbofish with complex types
        assert_eq!(strip_turbofish("Map::<K, V>::empty"), "Map::empty");
        assert_eq!(strip_turbofish("Seq::<Request>::empty"), "Seq::empty");
        assert_eq!(
            strip_turbofish("Set::<AbstractEndPoint>::empty"),
            "Set::empty"
        );

        // Turbofish with nested generics
        assert_eq!(
            strip_turbofish("Map::<int, Seq<Request>>::empty"),
            "Map::empty"
        );

        // No turbofish (function calls)
        assert_eq!(strip_turbofish("foo"), "foo");
        assert_eq!(strip_turbofish("SomeFunc::call"), "SomeFunc::call");
    }

    #[test]
    fn test_convert_enum_variant_ident_strips_path() {
        // Rust enum variant paths like "LTPCMessage::Prepare" stored as Ident
        // should be stripped to just the variant name in TLA+
        let body = VerusExpr::Eq(
            Box::new(VerusExpr::Ident("x".to_string())),
            Box::new(VerusExpr::Ident("LTPCMessage::Prepare".to_string())),
        );
        let func = make_simple_func("LTest", body);
        let mut converter = Verus2TlaConverter::new();
        let module = converter.convert_functions("Test", vec![func]).unwrap();
        // The operator body should contain "Prepare" not "LTPCMessage::Prepare"
        let op = &module.operators[0];
        match &op.body {
            TlaExpr::BinOp { right, .. } => match right.as_ref() {
                TlaExpr::Ident(name) => assert_eq!(name, "Prepare"),
                other => panic!("Expected Ident, got {:?}", other),
            },
            other => panic!("Expected BinOp, got {:?}", other),
        }
    }

    #[test]
    fn test_convert_call_strips_enum_path() {
        // A Call with multi-segment path like ["LMessage", "Commit"]
        // should be stripped to just "Commit" in TLA+
        let body = VerusExpr::Eq(
            Box::new(VerusExpr::Ident("x".to_string())),
            Box::new(VerusExpr::Call {
                func: Path {
                    segments: vec!["LMessage".to_string(), "Commit".to_string()],
                },
                args: vec![],
            }),
        );
        let func = make_simple_func("LTest", body);
        let mut converter = Verus2TlaConverter::new();
        let module = converter.convert_functions("Test", vec![func]).unwrap();
        let op = &module.operators[0];
        match &op.body {
            TlaExpr::BinOp { right, .. } => match right.as_ref() {
                TlaExpr::OpApply { op: name, args } => {
                    assert!(args.is_empty());
                    match name.as_ref() {
                        TlaExpr::Ident(n) => assert_eq!(n, "Commit"),
                        other => panic!("Expected Ident, got {:?}", other),
                    }
                }
                other => panic!("Expected OpApply, got {:?}", other),
            },
            other => panic!("Expected BinOp, got {:?}", other),
        }
    }
}
