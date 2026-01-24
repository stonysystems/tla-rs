//! Code generation for exec functions.
//!
//! This module transforms validated spec predicates into executable Rust/Verus
//! functions with proper proof linkage.

use crate::ast::{Expr, ParameterMode, Type};
use crate::error::{TranspileError, TranspileResult};
use crate::moder::AnnotatedFunction;
use std::collections::HashMap;

/// Configuration for code generation
#[derive(Debug, Clone)]
pub struct TranslatorConfig {
    /// Prefix for spec types (e.g., "L")
    pub spec_prefix: String,
    /// Prefix for exec types (e.g., "C")
    pub exec_prefix: String,
    /// Type remapping (spec type -> exec type)
    pub type_remapping: HashMap<String, String>,
    /// Whether to generate abstraction functions
    pub generate_abstraction_fns: bool,
    /// Whether to generate validity predicates
    pub generate_validity_predicates: bool,
}

impl Default for TranslatorConfig {
    fn default() -> Self {
        Self {
            spec_prefix: "L".to_string(),
            exec_prefix: "C".to_string(),
            type_remapping: HashMap::new(),
            generate_abstraction_fns: true,
            generate_validity_predicates: true,
        }
    }
}

/// Generated exec function
#[derive(Debug, Clone)]
pub struct ExecFunction {
    /// Function name (e.g., "CAcceptorProcess1a")
    pub name: String,
    /// Parameters (with exec types)
    pub params: Vec<ExecParameter>,
    /// Return type (tuple of outputs)
    pub return_type: ExecType,
    /// Requires clauses
    pub requires: Vec<String>,
    /// Ensures clauses (linking to spec)
    pub ensures: Vec<String>,
    /// Function body
    pub body: ExecExpr,
}

/// Parameter for exec function
#[derive(Debug, Clone)]
pub struct ExecParameter {
    pub name: String,
    pub ty: ExecType,
    pub is_reference: bool,
}

/// Type for exec code
#[derive(Debug, Clone)]
pub enum ExecType {
    Named(String),
    Generic(String, Vec<ExecType>),
    Tuple(Vec<ExecType>),
    Vec(Box<ExecType>),
    HashMap(Box<ExecType>, Box<ExecType>),
    Reference(Box<ExecType>, bool), // (type, mutable)
}

impl ExecType {
    /// Convert to Rust type string
    pub fn to_rust_string(&self) -> String {
        match self {
            ExecType::Named(name) => name.clone(),
            ExecType::Generic(name, args) => {
                let args_str: Vec<_> = args.iter().map(|a| a.to_rust_string()).collect();
                format!("{}<{}>", name, args_str.join(", "))
            }
            ExecType::Tuple(types) => {
                let types_str: Vec<_> = types.iter().map(|t| t.to_rust_string()).collect();
                format!("({})", types_str.join(", "))
            }
            ExecType::Vec(inner) => format!("Vec<{}>", inner.to_rust_string()),
            ExecType::HashMap(k, v) => {
                format!("HashMap<{}, {}>", k.to_rust_string(), v.to_rust_string())
            }
            ExecType::Reference(inner, mutable) => {
                if *mutable {
                    format!("&mut {}", inner.to_rust_string())
                } else {
                    format!("&{}", inner.to_rust_string())
                }
            }
        }
    }
}

/// Expression for exec code
#[derive(Debug, Clone)]
pub enum ExecExpr {
    /// Block of statements
    Block(Vec<ExecExpr>),
    /// Let binding
    Let {
        /// Pattern as a string (e.g., "x" or "(a, b)")
        pattern: String,
        ty: Option<ExecType>,
        value: Box<ExecExpr>,
    },
    /// If expression
    If {
        cond: Box<ExecExpr>,
        then_branch: Box<ExecExpr>,
        else_branch: Option<Box<ExecExpr>>,
    },
    /// Match expression
    Match {
        scrutinee: Box<ExecExpr>,
        arms: Vec<(String, ExecExpr)>, // (pattern, body)
    },
    /// Struct construction
    Struct {
        name: String,
        fields: Vec<(String, ExecExpr)>,
    },
    /// Struct update (..base syntax)
    StructUpdate {
        name: String,
        base: Box<ExecExpr>,
        fields: Vec<(String, ExecExpr)>,
    },
    /// Clone call
    Clone(Box<ExecExpr>),
    /// Field access
    Field(Box<ExecExpr>, String),
    /// Method call
    MethodCall {
        receiver: Box<ExecExpr>,
        method: String,
        args: Vec<ExecExpr>,
    },
    /// Function call
    Call { func: String, args: Vec<ExecExpr> },
    /// Binary operation
    Binary {
        lhs: Box<ExecExpr>,
        op: String,
        rhs: Box<ExecExpr>,
    },
    /// Unary operation
    Unary { op: String, expr: Box<ExecExpr> },
    /// Variable reference
    Var(String),
    /// Literal
    Literal(String),
    /// Vec literal
    VecLit(Vec<ExecExpr>),
    /// Tuple
    Tuple(Vec<ExecExpr>),
    /// Return statement
    Return(Box<ExecExpr>),
    /// Range expression (start..end)
    Range {
        start: Box<ExecExpr>,
        end: Box<ExecExpr>,
    },
    /// Closure expression (|params| body)
    Closure {
        params: Vec<String>,
        body: Box<ExecExpr>,
    },
    /// Comment (for documentation or TODO markers)
    Comment(String),
    /// Type cast (expr as Type)
    Cast(Box<ExecExpr>, String),
}

/// Context for expression transformation
pub struct TransformContext<'a> {
    pub config: &'a TranslatorConfig,
    pub output_params: Vec<String>,
    pub input_params: Vec<String>,
    /// Maps output parameter names to their types (for struct name derivation)
    pub output_types: HashMap<String, Type>,
}

impl<'a> TransformContext<'a> {
    pub fn is_output(&self, name: &str) -> bool {
        self.output_params.contains(&name.to_string())
    }

    /// Get the struct name for an output parameter from its type
    pub fn get_output_struct_name(&self, name: &str) -> Option<String> {
        self.output_types.get(name).and_then(|ty| match ty {
            Type::Named(path) => path.last().map(|s| s.to_string()),
            _ => None,
        })
    }
}

/// Code translator
pub struct Translator {
    config: TranslatorConfig,
}

impl Translator {
    /// Create a new translator with the given configuration
    pub fn new(config: TranslatorConfig) -> Self {
        Self { config }
    }

    /// Translate an annotated spec function to an exec function
    pub fn translate(&self, func: &AnnotatedFunction) -> TranspileResult<ExecFunction> {
        if !func.is_functionalizable {
            return Err(TranspileError::CodeGen {
                message: format!(
                    "Function '{}' cannot be functionalized: {}",
                    func.spec_fn.name,
                    func.non_functionalizable_reason
                        .as_deref()
                        .unwrap_or("unknown reason")
                ),
                span: None, // TODO: Convert proc_macro2::Span to miette::SourceSpan
            });
        }

        // Generate exec function name
        let exec_name = self.translate_name(&func.spec_fn.name);

        // Translate parameters
        let (params, output_names) = self.translate_params(func)?;

        // Build return type (tuple of outputs)
        let return_type = self.build_return_type(func)?;

        // Build requires clauses
        let requires = self.build_requires(func);

        // Build ensures clauses
        let ensures = self.build_ensures(func, &output_names);

        // Build output types map for struct name derivation
        let output_types: HashMap<String, Type> = func
            .spec_fn
            .params
            .iter()
            .zip(&func.param_modes)
            .filter(|(_, m)| **m == ParameterMode::Output)
            .map(|(p, _)| (p.name.clone(), p.ty.clone()))
            .collect();

        // Transform function body
        let ctx = TransformContext {
            config: &self.config,
            output_params: output_names,
            input_params: func
                .spec_fn
                .params
                .iter()
                .zip(&func.param_modes)
                .filter(|(_, m)| **m == ParameterMode::Input)
                .map(|(p, _)| p.name.clone())
                .collect(),
            output_types,
        };
        let body = self.transform_expr(&func.spec_fn.body, &ctx)?;

        Ok(ExecFunction {
            name: exec_name,
            params,
            return_type,
            requires,
            ensures,
            body,
        })
    }

    /// Translate spec name to exec name (L* -> C*)
    fn translate_name(&self, spec_name: &str) -> String {
        if spec_name.starts_with(&self.config.spec_prefix) {
            format!(
                "{}{}",
                self.config.exec_prefix,
                &spec_name[self.config.spec_prefix.len()..]
            )
        } else {
            format!("{}{}", self.config.exec_prefix, spec_name)
        }
    }

    /// Derive nested struct name from field name
    /// e.g., "max_bal" -> "CBallot" (assuming Ballot is the type)
    /// Falls back to PascalCase: "max_bal" -> "CMaxBal"
    fn derive_nested_struct_name(&self, field_name: &str) -> String {
        // Convert snake_case to PascalCase and add exec prefix
        let pascal_case: String = field_name
            .split('_')
            .map(|s| {
                let mut chars = s.chars();
                match chars.next() {
                    Some(c) => c.to_uppercase().chain(chars).collect::<String>(),
                    None => String::new(),
                }
            })
            .collect();
        format!("{}{}", self.config.exec_prefix, pascal_case)
    }

    /// Translate spec type to exec type
    fn translate_type(&self, ty: &Type) -> ExecType {
        match ty {
            Type::Named(path) => {
                let name = path.last().unwrap_or("Unknown");
                if let Some(remapped) = self.config.type_remapping.get(name) {
                    ExecType::Named(remapped.clone())
                } else {
                    ExecType::Named(self.translate_name(name))
                }
            }
            Type::Generic(path, args) => {
                let name = path.last().unwrap_or("Unknown");
                let translated_args: Vec<_> = args.iter().map(|a| self.translate_type(a)).collect();
                ExecType::Generic(self.translate_name(name), translated_args)
            }
            Type::Seq(inner) => ExecType::Vec(Box::new(self.translate_type(inner))),
            Type::Map(k, v) => ExecType::HashMap(
                Box::new(self.translate_type(k)),
                Box::new(self.translate_type(v)),
            ),
            Type::Tuple(types) => {
                ExecType::Tuple(types.iter().map(|t| self.translate_type(t)).collect())
            }
            Type::Reference { ty, mutable } => {
                ExecType::Reference(Box::new(self.translate_type(ty)), *mutable)
            }
            Type::Bool => ExecType::Named("bool".to_string()),
            Type::Int => ExecType::Named("i64".to_string()),
            Type::Nat => ExecType::Named("u64".to_string()),
            Type::Unit => ExecType::Named("()".to_string()),
            Type::Set(inner) => {
                ExecType::Generic("HashSet".to_string(), vec![self.translate_type(inner)])
            }
        }
    }

    /// Translate parameters
    fn translate_params(
        &self,
        func: &AnnotatedFunction,
    ) -> TranspileResult<(Vec<ExecParameter>, Vec<String>)> {
        let mut params = Vec::new();
        let mut output_names = Vec::new();

        for (param, mode) in func.spec_fn.params.iter().zip(&func.param_modes) {
            match mode {
                ParameterMode::Input => {
                    params.push(ExecParameter {
                        name: param.name.clone(),
                        ty: ExecType::Reference(Box::new(self.translate_type(&param.ty)), false),
                        is_reference: true,
                    });
                }
                ParameterMode::Output => {
                    output_names.push(param.name.clone());
                    // Output params are not in the function signature,
                    // they become part of the return type
                }
            }
        }

        Ok((params, output_names))
    }

    /// Build return type from output parameters
    fn build_return_type(&self, func: &AnnotatedFunction) -> TranspileResult<ExecType> {
        let output_types: Vec<_> = func
            .spec_fn
            .params
            .iter()
            .zip(&func.param_modes)
            .filter(|(_, m)| **m == ParameterMode::Output)
            .map(|(p, _)| self.translate_type(&p.ty))
            .collect();

        match output_types.len() {
            0 => Ok(ExecType::Named("()".to_string())),
            1 => Ok(output_types.into_iter().next().unwrap()),
            _ => Ok(ExecType::Tuple(output_types)),
        }
    }

    /// Build requires clauses
    fn build_requires(&self, func: &AnnotatedFunction) -> Vec<String> {
        let mut requires = Vec::new();

        // Add well_formed requirements for input params
        for (param, mode) in func.spec_fn.params.iter().zip(&func.param_modes) {
            if *mode == ParameterMode::Input {
                requires.push(format!("{}.well_formed()", param.name));
            }
        }

        requires
    }

    /// Build ensures clauses linking to spec
    fn build_ensures(&self, func: &AnnotatedFunction, output_names: &[String]) -> Vec<String> {
        let mut ensures = Vec::new();

        // Add well_formed ensures for outputs
        for (i, name) in output_names.iter().enumerate() {
            let accessor = if output_names.len() == 1 {
                "result".to_string()
            } else {
                format!("result.{}", i)
            };
            ensures.push(format!("{}.well_formed()", accessor));
            let _ = name; // Suppress warning
        }

        // Add linkage to original spec predicate
        let spec_call = self.build_spec_call(func, output_names);
        ensures.push(spec_call);

        ensures
    }

    /// Build call to spec predicate for ensures clause
    fn build_spec_call(&self, func: &AnnotatedFunction, output_names: &[String]) -> String {
        let args: Vec<_> = func
            .spec_fn
            .params
            .iter()
            .zip(&func.param_modes)
            .map(|(param, mode)| match mode {
                ParameterMode::Input => format!("{}@", param.name),
                ParameterMode::Output => {
                    let output_idx = output_names
                        .iter()
                        .position(|n| n == &param.name)
                        .unwrap_or(0);
                    if output_names.len() == 1 {
                        "result@".to_string()
                    } else {
                        format!("result.{}@", output_idx)
                    }
                }
            })
            .collect();

        format!("{}({})", func.spec_fn.name, args.join(", "))
    }

    /// Transform a spec expression to an exec expression (public interface)
    pub fn transform_expr_public(
        &self,
        expr: &Expr,
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        self.transform_expr(expr, ctx)
    }

    /// Transform a spec expression to an exec expression
    fn transform_expr(&self, expr: &Expr, ctx: &TransformContext) -> TranspileResult<ExecExpr> {
        match expr {
            Expr::Literal(lit) => Ok(ExecExpr::Literal(self.format_literal(lit))),

            Expr::Ident(name) => Ok(ExecExpr::Var(name.clone())),

            Expr::Field(base, field) => {
                let base_expr = self.transform_expr(base, ctx)?;
                Ok(ExecExpr::Field(Box::new(base_expr), field.clone()))
            }

            Expr::Index(base, idx) => {
                let base_expr = self.transform_expr(base, ctx)?;
                let idx_expr = self.transform_expr(idx, ctx)?;
                Ok(ExecExpr::MethodCall {
                    receiver: Box::new(base_expr),
                    method: "index".to_string(),
                    args: vec![idx_expr],
                })
            }

            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_expr = self.transform_expr(cond, ctx)?;
                let then_expr = self.transform_expr(then_branch, ctx)?;
                let else_expr = else_branch
                    .as_ref()
                    .map(|e| self.transform_expr(e, ctx))
                    .transpose()?;
                Ok(ExecExpr::If {
                    cond: Box::new(cond_expr),
                    then_branch: Box::new(then_expr),
                    else_branch: else_expr.map(Box::new),
                })
            }

            Expr::Conjunction(exprs) => {
                // Check if this is a struct construction pattern (s_.f1 == e1 &&& s_.f2 == e2)
                if let Some(struct_expr) = self.try_extract_struct_construction(exprs, ctx)? {
                    return Ok(struct_expr);
                }

                // Check if we have multiple output assignments that should be wrapped as a tuple
                let (output_exprs, other_exprs) = self.categorize_output_assignments(exprs, ctx)?;

                if output_exprs.len() > 1 {
                    // Multiple outputs should be returned as a tuple
                    // Sort by output parameter order if possible
                    let sorted_outputs = self.sort_outputs_by_param_order(&output_exprs, ctx);

                    if other_exprs.is_empty() {
                        // Just the tuple
                        Ok(ExecExpr::Tuple(sorted_outputs))
                    } else {
                        // Other expressions + tuple return
                        let mut block = other_exprs;
                        block.push(ExecExpr::Tuple(sorted_outputs));
                        Ok(ExecExpr::Block(block))
                    }
                } else if output_exprs.len() == 1 {
                    // Single output - extract the ExecExpr from the tuple
                    let (_, single_output) = output_exprs.into_iter().next().unwrap();
                    if other_exprs.is_empty() {
                        Ok(single_output)
                    } else {
                        let mut block = other_exprs;
                        block.push(single_output);
                        Ok(ExecExpr::Block(block))
                    }
                } else {
                    // No outputs detected, transform as block
                    let stmts: TranspileResult<Vec<_>> =
                        exprs.iter().map(|e| self.transform_expr(e, ctx)).collect();
                    Ok(ExecExpr::Block(stmts?))
                }
            }

            Expr::Eq(lhs, rhs) => self.transform_equality(lhs, rhs, ctx),

            Expr::Call { func, args } => {
                let translated_args: TranspileResult<Vec<_>> =
                    args.iter().map(|a| self.transform_expr(a, ctx)).collect();
                let func_name = func.last().unwrap_or("unknown");
                Ok(ExecExpr::Call {
                    func: self.translate_name(func_name),
                    args: translated_args?,
                })
            }

            Expr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let recv_expr = self.transform_expr(receiver, ctx)?;
                let translated_args: TranspileResult<Vec<_>> =
                    args.iter().map(|a| self.transform_expr(a, ctx)).collect();
                Ok(ExecExpr::MethodCall {
                    receiver: Box::new(recv_expr),
                    method: method.clone(),
                    args: translated_args?,
                })
            }

            Expr::Let {
                binding,
                value,
                body,
            } => {
                let value_expr = self.transform_expr(value, ctx)?;
                let body_expr = self.transform_expr(body, ctx)?;
                let pattern_str = self.format_binding_pattern(&binding.pattern);
                Ok(ExecExpr::Block(vec![
                    ExecExpr::Let {
                        pattern: pattern_str,
                        ty: None,
                        value: Box::new(value_expr),
                    },
                    body_expr,
                ]))
            }

            Expr::Match { scrutinee, arms } => {
                let scrut_expr = self.transform_expr(scrutinee, ctx)?;
                let mut translated_arms = Vec::new();
                for arm in arms {
                    let pattern = self.format_pattern(&arm.pattern);
                    let body = self.transform_expr(&arm.body, ctx)?;
                    translated_arms.push((pattern, body));
                }
                Ok(ExecExpr::Match {
                    scrutinee: Box::new(scrut_expr),
                    arms: translated_arms,
                })
            }

            Expr::View(inner) => {
                // @ operator - in exec code, this is typically just the value
                // For exec types, we don't need the view in most cases
                self.transform_expr(inner, ctx)
            }

            Expr::Arrow(base, field) => {
                // -> operator (enum variant field access)
                // In exec code: base.get_field() or match-based access
                let base_expr = self.transform_expr(base, ctx)?;
                Ok(ExecExpr::MethodCall {
                    receiver: Box::new(base_expr),
                    method: format!("get_{}", field),
                    args: vec![],
                })
            }

            Expr::Struct { name, fields } => {
                let exec_name = self.translate_name(name.last().unwrap_or("Unknown"));
                let translated_fields: TranspileResult<Vec<_>> = fields
                    .iter()
                    .map(|(fname, fexpr)| {
                        let expr = self.transform_expr(fexpr, ctx)?;
                        Ok((fname.clone(), expr))
                    })
                    .collect();
                Ok(ExecExpr::Struct {
                    name: exec_name,
                    fields: translated_fields?,
                })
            }

            Expr::StructUpdate { base, fields, name } => {
                let base_expr = self.transform_expr(base, ctx)?;
                let translated_fields: TranspileResult<Vec<_>> = fields
                    .iter()
                    .map(|(fname, fexpr)| {
                        let expr = self.transform_expr(fexpr, ctx)?;
                        Ok((fname.clone(), expr))
                    })
                    .collect();
                // Use provided name if available, otherwise try to derive from base
                let struct_name = if let Some(n) = name {
                    self.translate_name(n.last().unwrap_or("Unknown"))
                } else {
                    "Unknown".to_string()
                };
                Ok(ExecExpr::StructUpdate {
                    name: struct_name,
                    base: Box::new(base_expr),
                    fields: translated_fields?,
                })
            }

            // Binary operators from Expr::Binary
            Expr::Binary(lhs, op, rhs) => {
                let op_str = match op {
                    crate::ast::BinOp::Add => "+",
                    crate::ast::BinOp::Sub => "-",
                    crate::ast::BinOp::Mul => "*",
                    crate::ast::BinOp::Div => "/",
                    crate::ast::BinOp::Mod => "%",
                    crate::ast::BinOp::And => "&&",
                    crate::ast::BinOp::Or => "||",
                    crate::ast::BinOp::BitAnd => "&",
                    crate::ast::BinOp::BitOr => "|",
                    crate::ast::BinOp::BitXor => "^",
                    crate::ast::BinOp::Shl => "<<",
                    crate::ast::BinOp::Shr => ">>",
                };
                self.transform_binary_op(lhs, rhs, op_str, ctx)
            }

            // Comparison operators as dedicated AST nodes
            Expr::Lt(lhs, rhs) => self.transform_binary_op(lhs, rhs, "<", ctx),
            Expr::Le(lhs, rhs) => self.transform_binary_op(lhs, rhs, "<=", ctx),
            Expr::Gt(lhs, rhs) => self.transform_binary_op(lhs, rhs, ">", ctx),
            Expr::Ge(lhs, rhs) => self.transform_binary_op(lhs, rhs, ">=", ctx),
            Expr::Ne(lhs, rhs) => self.transform_binary_op(lhs, rhs, "!=", ctx),

            // Enum variant check: expr is VariantName
            Expr::Is(inner, variant) => {
                let inner_expr = self.transform_expr(inner, ctx)?;
                Ok(ExecExpr::Binary {
                    lhs: Box::new(inner_expr),
                    op: "is".to_string(),
                    rhs: Box::new(ExecExpr::Var(variant.clone())),
                })
            }

            // Unary operators
            Expr::Not(inner) => {
                let inner_expr = self.transform_expr(inner, ctx)?;
                Ok(ExecExpr::Unary {
                    op: "!".to_string(),
                    expr: Box::new(inner_expr),
                })
            }

            Expr::Unary(op, inner) => {
                let inner_expr = self.transform_expr(inner, ctx)?;
                let op_str = match op {
                    crate::ast::UnaryOp::Not => "!",
                    crate::ast::UnaryOp::Neg => "-",
                    crate::ast::UnaryOp::Deref => "*",
                };
                Ok(ExecExpr::Unary {
                    op: op_str.to_string(),
                    expr: Box::new(inner_expr),
                })
            }

            Expr::Implies(lhs, rhs) => {
                // a ==> b is equivalent to !a || b
                let lhs_expr = self.transform_expr(lhs, ctx)?;
                let rhs_expr = self.transform_expr(rhs, ctx)?;
                Ok(ExecExpr::Binary {
                    lhs: Box::new(ExecExpr::Unary {
                        op: "!".to_string(),
                        expr: Box::new(lhs_expr),
                    }),
                    op: "||".to_string(),
                    rhs: Box::new(rhs_expr),
                })
            }

            Expr::Iff(lhs, rhs) => {
                // a <==> b is equivalent to (a ==> b) && (b ==> a), which is (!a || b) && (!b || a)
                // But for exec code, we just use ==
                let lhs_expr = self.transform_expr(lhs, ctx)?;
                let rhs_expr = self.transform_expr(rhs, ctx)?;
                Ok(ExecExpr::Binary {
                    lhs: Box::new(lhs_expr),
                    op: "==".to_string(),
                    rhs: Box::new(rhs_expr),
                })
            }

            Expr::Disjunction(exprs) => {
                // Transform ||| to chain of ||
                if exprs.is_empty() {
                    return Ok(ExecExpr::Literal("false".to_string()));
                }
                let mut result = self.transform_expr(&exprs[0], ctx)?;
                for e in &exprs[1..] {
                    let next = self.transform_expr(e, ctx)?;
                    result = ExecExpr::Binary {
                        lhs: Box::new(result),
                        op: "||".to_string(),
                        rhs: Box::new(next),
                    };
                }
                Ok(result)
            }

            Expr::SeqEmpty => Ok(ExecExpr::VecLit(vec![])),

            Expr::SetEmpty => Ok(ExecExpr::MethodCall {
                receiver: Box::new(ExecExpr::Var("HashSet".to_string())),
                method: "new".to_string(),
                args: vec![],
            }),

            Expr::MapEmpty => Ok(ExecExpr::MethodCall {
                receiver: Box::new(ExecExpr::Var("HashMap".to_string())),
                method: "new".to_string(),
                args: vec![],
            }),

            Expr::SetLit(elems) => {
                // Generate HashSet::from([...])
                let translated: TranspileResult<Vec<_>> =
                    elems.iter().map(|e| self.transform_expr(e, ctx)).collect();
                Ok(ExecExpr::Call {
                    func: "HashSet::from".to_string(),
                    args: vec![ExecExpr::VecLit(translated?)],
                })
            }

            Expr::MapLit(pairs) => {
                // Generate HashMap::from([...])
                let translated: TranspileResult<Vec<_>> = pairs
                    .iter()
                    .map(|(k, v)| {
                        let key = self.transform_expr(k, ctx)?;
                        let val = self.transform_expr(v, ctx)?;
                        Ok(ExecExpr::Tuple(vec![key, val]))
                    })
                    .collect();
                Ok(ExecExpr::Call {
                    func: "HashMap::from".to_string(),
                    args: vec![ExecExpr::VecLit(translated?)],
                })
            }

            Expr::SeqLit(elems) => {
                let translated: TranspileResult<Vec<_>> =
                    elems.iter().map(|e| self.transform_expr(e, ctx)).collect();
                Ok(ExecExpr::VecLit(translated?))
            }

            Expr::Forall { vars, body, .. } => {
                // Try to match to a known template using the checker module
                use crate::checker::TemplateMatcher;

                if let Some(template) = TemplateMatcher::match_template(expr) {
                    self.translate_quantifier_template(&template, ctx)
                } else {
                    Err(TranspileError::UnsupportedPattern {
                        message: format!(
                            "Forall quantifier with vars {:?} doesn't match any known template",
                            vars.iter().map(|v| &v.pattern).collect::<Vec<_>>()
                        ),
                        span: None,
                        help: Some(format!(
                            "Body structure: {:?}. Consider restructuring to match a known pattern.",
                            std::mem::discriminant(body.as_ref())
                        )),
                    })
                }
            }

            Expr::Exists { vars, body, .. } => {
                // Try to translate exists quantifier to .any() or .iter().any()
                // Common pattern: exists |x| container.contains(x) && pred(x)
                // Translates to: container.iter().any(|x| pred(x))

                if vars.len() != 1 {
                    return Err(TranspileError::UnsupportedPattern {
                        message: format!(
                            "Exists quantifier with {} variables not supported (only single variable)",
                            vars.len()
                        ),
                        span: None,
                        help: Some("Consider restructuring to use a single bound variable".to_string()),
                    });
                }

                let var = &vars[0];
                let var_name = var.name_string();

                // Try to extract container and predicate from body
                if let Some((container, predicate)) = self.extract_exists_container_and_pred(body, &var_name) {
                    // Transform: exists |x| container.contains(x) && pred(x)
                    // To: container.iter().any(|x| pred(x))
                    let container_expr = self.transform_expr(&container, ctx)?;
                    let pred_expr = self.transform_expr(&predicate, ctx)?;

                    Ok(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::MethodCall {
                            receiver: Box::new(container_expr),
                            method: "iter".to_string(),
                            args: vec![],
                        }),
                        method: "any".to_string(),
                        args: vec![ExecExpr::Closure {
                            params: vec![var_name],
                            body: Box::new(pred_expr),
                        }],
                    })
                } else {
                    // Fallback: try to handle simple exists without container extraction
                    // Pattern: exists |x| pred(x) where pred doesn't have container.contains(x)
                    Err(TranspileError::UnsupportedPattern {
                        message: format!(
                            "Exists quantifier pattern not recognized. Expected: exists |{}| container.contains({}) && pred({})",
                            var_name, var_name, var_name
                        ),
                        span: None,
                        help: Some("Restructure to: exists |x| container.contains(x) && predicate(x)".to_string()),
                    })
                }
            }

            Expr::Cast(inner_expr, target_type) => {
                let inner = self.transform_expr(inner_expr, ctx)?;
                let exec_type = self.translate_type(target_type);
                Ok(ExecExpr::Cast(Box::new(inner), exec_type.to_rust_string()))
            }
        }
    }

    /// Transform an equality expression
    fn transform_equality(
        &self,
        lhs: &Expr,
        rhs: &Expr,
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        // Check if this is a simple output assignment: s_ == expr
        if let Expr::Ident(name) = lhs {
            if ctx.is_output(name) {
                // Check if rhs is also an identifier (copy case)
                if let Expr::Ident(rhs_name) = rhs {
                    if ctx.input_params.contains(rhs_name) {
                        return Ok(ExecExpr::Clone(Box::new(ExecExpr::Var(rhs_name.clone()))));
                    }
                }
                return self.transform_expr(rhs, ctx);
            }
        }

        // Check if this is a field assignment: s_.field == expr
        if let Expr::Field(base, _field) = lhs {
            if let Expr::Ident(name) = base.as_ref() {
                if ctx.is_output(name) {
                    // This is a field assignment - will be collected by try_extract_struct_construction
                    return self.transform_expr(rhs, ctx);
                }
            }
        }

        // Regular equality comparison
        let lhs_expr = self.transform_expr(lhs, ctx)?;
        let rhs_expr = self.transform_expr(rhs, ctx)?;
        Ok(ExecExpr::Binary {
            lhs: Box::new(lhs_expr),
            op: "==".to_string(),
            rhs: Box::new(rhs_expr),
        })
    }

    /// Categorize expressions in a conjunction into output assignments and other expressions
    /// Returns: (Vec of output expressions with their param name, Vec of other expressions)
    fn categorize_output_assignments(
        &self,
        exprs: &[Expr],
        ctx: &TransformContext,
    ) -> TranspileResult<(Vec<(String, ExecExpr)>, Vec<ExecExpr>)> {
        let mut output_exprs: Vec<(String, ExecExpr)> = Vec::new();
        let mut other_exprs: Vec<ExecExpr> = Vec::new();

        for expr in exprs {
            if let Expr::Eq(lhs, rhs) = expr {
                // Check if LHS is an output parameter: s_ == expr or sent_packets == expr
                if let Expr::Ident(name) = lhs.as_ref() {
                    if ctx.is_output(name) {
                        let transformed = self.transform_expr(rhs, ctx)?;
                        output_exprs.push((name.clone(), transformed));
                        continue;
                    }
                }
            }
            // Not an output assignment, add to other expressions
            let transformed = self.transform_expr(expr, ctx)?;
            other_exprs.push(transformed);
        }

        Ok((output_exprs, other_exprs))
    }

    /// Sort output expressions by their parameter order in the context
    fn sort_outputs_by_param_order(
        &self,
        outputs: &[(String, ExecExpr)],
        ctx: &TransformContext,
    ) -> Vec<ExecExpr> {
        let mut sorted: Vec<_> = outputs.to_vec();
        sorted.sort_by(|a, b| {
            let a_idx = ctx.output_params.iter().position(|p| p == &a.0).unwrap_or(usize::MAX);
            let b_idx = ctx.output_params.iter().position(|p| p == &b.0).unwrap_or(usize::MAX);
            a_idx.cmp(&b_idx)
        });
        sorted.into_iter().map(|(_, e)| e).collect()
    }

    /// Try to extract struct construction from a conjunction of field assignments
    fn try_extract_struct_construction(
        &self,
        exprs: &[Expr],
        ctx: &TransformContext,
    ) -> TranspileResult<Option<ExecExpr>> {
        // Track direct field assignments: output_var -> [(field_name, expr)]
        let mut field_assignments: HashMap<String, Vec<(String, Expr)>> = HashMap::new();
        // Track nested field assignments: output_var -> { outer_field -> [(inner_field, expr)] }
        let mut nested_assignments: HashMap<String, HashMap<String, Vec<(String, Expr)>>> =
            HashMap::new();
        // Track pre-translated nested structs: output_var -> [(field_name, ExecExpr)]
        let mut pre_translated: HashMap<String, Vec<(String, ExecExpr)>> = HashMap::new();
        let mut other_exprs = Vec::new();

        for expr in exprs {
            if let Expr::Eq(lhs, rhs) = expr {
                // Check for nested field: s_.outer.inner == expr
                if let Expr::Field(mid, inner_field) = lhs.as_ref() {
                    if let Expr::Field(base, outer_field) = mid.as_ref() {
                        if let Expr::Ident(name) = base.as_ref() {
                            if ctx.is_output(name) {
                                nested_assignments
                                    .entry(name.clone())
                                    .or_default()
                                    .entry(outer_field.clone())
                                    .or_default()
                                    .push((inner_field.clone(), *rhs.clone()));
                                continue;
                            }
                        }
                    }
                }
                // Check for direct field: s_.field == expr
                if let Expr::Field(base, field) = lhs.as_ref() {
                    if let Expr::Ident(name) = base.as_ref() {
                        if ctx.is_output(name) {
                            field_assignments
                                .entry(name.clone())
                                .or_default()
                                .push((field.clone(), *rhs.clone()));
                            continue;
                        }
                    }
                }
                // Check for s_ == s (full copy)
                if let Expr::Ident(name) = lhs.as_ref() {
                    if ctx.is_output(name) {
                        other_exprs.push(expr.clone());
                        continue;
                    }
                }
            }
            // Pattern 2: !s_.field (equivalent to s_.field == false)
            else if let Expr::Not(inner) = expr {
                if let Expr::Field(base, field) = inner.as_ref() {
                    if let Expr::Ident(name) = base.as_ref() {
                        if ctx.is_output(name) {
                            field_assignments.entry(name.clone()).or_default().push((
                                field.clone(),
                                Expr::Literal(crate::ast::Literal::Bool(false)),
                            ));
                            continue;
                        }
                    }
                }
            }
            // Pattern 3: s_.field (equivalent to s_.field == true)
            else if let Expr::Field(base, field) = expr {
                if let Expr::Ident(name) = base.as_ref() {
                    if ctx.is_output(name) {
                        field_assignments.entry(name.clone()).or_default().push((
                            field.clone(),
                            Expr::Literal(crate::ast::Literal::Bool(true)),
                        ));
                        continue;
                    }
                }
            }
            other_exprs.push(expr.clone());
        }

        // Convert nested assignments to pre-translated struct constructions
        for (output_name, nested_map) in nested_assignments {
            for (outer_field, inner_fields) in nested_map {
                // Build a nested struct construction for this outer field
                let struct_name = self.derive_nested_struct_name(&outer_field);
                let translated_inner: TranspileResult<Vec<_>> = inner_fields
                    .into_iter()
                    .map(|(fname, fexpr)| {
                        let expr = self.transform_expr(&fexpr, ctx)?;
                        Ok((fname, expr))
                    })
                    .collect();
                let inner_struct = ExecExpr::Struct {
                    name: struct_name,
                    fields: translated_inner?,
                };
                // Store pre-translated nested struct
                pre_translated
                    .entry(output_name.clone())
                    .or_default()
                    .push((outer_field, inner_struct));
            }
        }

        // If we have field assignments or pre-translated fields, construct the struct
        if !field_assignments.is_empty() || !pre_translated.is_empty() {
            let mut results = Vec::new();

            // Collect all output variable names
            let mut all_outputs: std::collections::HashSet<String> =
                field_assignments.keys().cloned().collect();
            all_outputs.extend(pre_translated.keys().cloned());

            for output_name in all_outputs {
                // Get the struct name from the output parameter's type
                let struct_name = ctx
                    .get_output_struct_name(&output_name)
                    .map(|n| self.translate_name(&n))
                    .unwrap_or_else(|| {
                        // Fallback: derive from variable name
                        self.translate_name(output_name.trim_end_matches('_'))
                    });

                // Find the input variable this is based on (usually same name without _)
                let base_name = output_name.trim_end_matches('_');
                let base_input = if ctx.input_params.contains(&base_name.to_string()) {
                    Some(base_name.to_string())
                } else {
                    None
                };

                // Translate direct field expressions
                let direct_fields = field_assignments.remove(&output_name).unwrap_or_default();
                let mut translated_fields: Vec<_> = direct_fields
                    .into_iter()
                    .map(|(fname, fexpr)| {
                        let expr = self.transform_expr(&fexpr, ctx)?;
                        Ok((fname, expr))
                    })
                    .collect::<TranspileResult<Vec<_>>>()?;

                // Add pre-translated nested struct fields
                if let Some(nested_fields) = pre_translated.remove(&output_name) {
                    translated_fields.extend(nested_fields);
                }

                if let Some(base) = base_input {
                    // Struct update syntax: S { field: value, ..base.clone() }
                    results.push(ExecExpr::StructUpdate {
                        name: struct_name,
                        base: Box::new(ExecExpr::Clone(Box::new(ExecExpr::Var(base)))),
                        fields: translated_fields,
                    });
                } else {
                    // Generate a struct literal
                    results.push(ExecExpr::Struct {
                        name: struct_name,
                        fields: translated_fields,
                    });
                }
            }

            // Add any other expressions
            for expr in other_exprs {
                results.push(self.transform_expr(&expr, ctx)?);
            }

            if results.len() == 1 {
                return Ok(Some(results.into_iter().next().unwrap()));
            } else {
                return Ok(Some(ExecExpr::Tuple(results)));
            }
        }

        Ok(None)
    }

    /// Transform a binary operation
    fn transform_binary_op(
        &self,
        lhs: &Expr,
        rhs: &Expr,
        op: &str,
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        let lhs_expr = self.transform_expr(lhs, ctx)?;
        let rhs_expr = self.transform_expr(rhs, ctx)?;
        Ok(ExecExpr::Binary {
            lhs: Box::new(lhs_expr),
            op: op.to_string(),
            rhs: Box::new(rhs_expr),
        })
    }

    /// Format a literal value
    fn format_literal(&self, lit: &crate::ast::Literal) -> String {
        match lit {
            crate::ast::Literal::Bool(b) => b.to_string(),
            crate::ast::Literal::Int(i) => i.to_string(),
            crate::ast::Literal::String(s) => format!("\"{}\"", s),
        }
    }

    /// Format a binding pattern for let expressions
    fn format_binding_pattern(&self, pattern: &crate::ast::Pattern) -> String {
        self.format_pattern(pattern)
    }

    /// Format a pattern for match arms
    fn format_pattern(&self, pattern: &crate::ast::Pattern) -> String {
        match pattern {
            crate::ast::Pattern::Wildcard => "_".to_string(),
            crate::ast::Pattern::Ident(name) => name.clone(),
            crate::ast::Pattern::Tuple(patterns) => {
                let parts: Vec<_> = patterns.iter().map(|p| self.format_pattern(p)).collect();
                format!("({})", parts.join(", "))
            }
            crate::ast::Pattern::Struct { name, fields } => {
                let field_strs: Vec<_> = fields
                    .iter()
                    .map(|(fname, fpat)| format!("{}: {}", fname, self.format_pattern(fpat)))
                    .collect();
                format!(
                    "{} {{ {} }}",
                    self.translate_name(name.last().unwrap_or("Unknown")),
                    field_strs.join(", ")
                )
            }
            crate::ast::Pattern::Variant { name, fields } => {
                let variant_name = self.translate_name(name.last().unwrap_or("Unknown"));
                if fields.is_empty() {
                    variant_name
                } else {
                    let field_strs: Vec<_> =
                        fields.iter().map(|p| self.format_pattern(p)).collect();
                    format!("{}({})", variant_name, field_strs.join(", "))
                }
            }
            crate::ast::Pattern::Literal(lit) => self.format_literal(lit),
        }
    }

    /// Extract source map and filter predicate from a domain predicate
    /// Returns (source_map_name, filter_predicate) if the pattern is recognized
    ///
    /// Handles patterns like:
    /// - `source.contains_key(k) && filter_pred`
    /// - `filter_pred && source.contains_key(k)`
    /// - `source.dom().contains(k) && filter_pred`
    fn extract_source_and_filter(
        &self,
        pred: &Expr,
        key_var: &str,
    ) -> Option<(String, Expr)> {
        use crate::ast::Expr;

        // Check for conjunction (&&)
        if let Expr::Conjunction(parts) = pred {
            // Look for source.contains_key(k) in the parts
            for (i, part) in parts.iter().enumerate() {
                if let Some(source_map) = self.extract_contains_key_source(part, key_var) {
                    // Collect all other parts as the filter predicate
                    let other_parts: Vec<Expr> =
                        parts.iter().enumerate().filter(|(j, _)| *j != i).map(|(_, p)| p.clone()).collect();

                    let filter = if other_parts.len() == 1 {
                        other_parts.into_iter().next().unwrap()
                    } else {
                        Expr::Conjunction(other_parts)
                    };

                    return Some((source_map, filter));
                }
            }
        }

        // Check for binary && (Binary with && op)
        if let Expr::Binary(lhs, crate::ast::BinOp::And, rhs) = pred {
            if let Some(source_map) = self.extract_contains_key_source(lhs, key_var) {
                return Some((source_map, (**rhs).clone()));
            }
            if let Some(source_map) = self.extract_contains_key_source(rhs, key_var) {
                return Some((source_map, (**lhs).clone()));
            }
        }

        // Pattern: just source.contains_key(k) without filter (returns true as filter)
        if let Some(source_map) = self.extract_contains_key_source(pred, key_var) {
            return Some((source_map, Expr::Literal(crate::ast::Literal::Bool(true))));
        }

        None
    }

    /// Extract container and predicate from exists body
    /// Handles: container.contains(x) && pred(x)
    /// Returns (container, predicate_without_contains)
    fn extract_exists_container_and_pred(
        &self,
        body: &Expr,
        var_name: &str,
    ) -> Option<(Expr, Expr)> {
        use crate::ast::Expr;

        // Check for conjunction: container.contains(x) && pred(x)
        if let Expr::Conjunction(parts) = body {
            for (i, part) in parts.iter().enumerate() {
                if let Some(container) = self.extract_contains_receiver(part, var_name) {
                    // Found container.contains(x), rest is predicate
                    let other_parts: Vec<Expr> = parts
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, p)| p.clone())
                        .collect();

                    let predicate = if other_parts.len() == 1 {
                        other_parts.into_iter().next().unwrap()
                    } else if other_parts.is_empty() {
                        Expr::Literal(crate::ast::Literal::Bool(true))
                    } else {
                        Expr::Conjunction(other_parts)
                    };

                    return Some((container, predicate));
                }
            }
        }

        // Check for binary &&: container.contains(x) && pred(x)
        if let Expr::Binary(lhs, crate::ast::BinOp::And, rhs) = body {
            if let Some(container) = self.extract_contains_receiver(lhs, var_name) {
                return Some((container, (**rhs).clone()));
            }
            if let Some(container) = self.extract_contains_receiver(rhs, var_name) {
                return Some((container, (**lhs).clone()));
            }
        }

        // Check for just container.contains(x) without additional predicate
        if let Some(container) = self.extract_contains_receiver(body, var_name) {
            return Some((
                container,
                Expr::Literal(crate::ast::Literal::Bool(true)),
            ));
        }

        None
    }

    /// Extract the receiver expression from a contains call
    /// Returns the full expression (e.g., s.acceptor.last_checkpointed_operation)
    fn extract_contains_receiver(&self, expr: &Expr, element_var: &str) -> Option<Expr> {
        use crate::ast::Expr;

        if let Expr::MethodCall {
            receiver,
            method,
            args,
        } = expr
        {
            if method == "contains" && args.len() == 1 {
                if let Expr::Ident(arg_name) = &args[0] {
                    if arg_name == element_var {
                        return Some((**receiver).clone());
                    }
                }
            }
        }
        None
    }

    /// Extract source set and filter predicate from a domain predicate (for sets)
    /// Handles: source.contains(x) && filter_pred
    fn extract_source_set_and_filter(
        &self,
        pred: &Expr,
        element_var: &str,
    ) -> Option<(String, Expr)> {
        use crate::ast::Expr;

        // Check for conjunction
        if let Expr::Conjunction(parts) = pred {
            for (i, part) in parts.iter().enumerate() {
                if let Some(source) = self.extract_set_contains_source(part, element_var) {
                    let other_parts: Vec<Expr> =
                        parts.iter().enumerate().filter(|(j, _)| *j != i).map(|(_, p)| p.clone()).collect();

                    let filter = if other_parts.len() == 1 {
                        other_parts.into_iter().next().unwrap()
                    } else {
                        Expr::Conjunction(other_parts)
                    };

                    return Some((source, filter));
                }
            }
        }

        // Check for binary &&
        if let Expr::Binary(lhs, crate::ast::BinOp::And, rhs) = pred {
            if let Some(source) = self.extract_set_contains_source(lhs, element_var) {
                return Some((source, (**rhs).clone()));
            }
            if let Some(source) = self.extract_set_contains_source(rhs, element_var) {
                return Some((source, (**lhs).clone()));
            }
        }

        // Just contains without filter
        if let Some(source) = self.extract_set_contains_source(pred, element_var) {
            return Some((source, Expr::Literal(crate::ast::Literal::Bool(true))));
        }

        None
    }

    /// Extract source set name from a contains expression
    fn extract_set_contains_source(&self, expr: &Expr, element_var: &str) -> Option<String> {
        use crate::ast::Expr;

        if let Expr::MethodCall {
            receiver,
            method,
            args,
        } = expr
        {
            if method == "contains" && args.len() == 1 {
                if let Expr::Ident(arg_name) = &args[0] {
                    if arg_name == element_var {
                        // Use expr_to_name to handle arbitrary nesting depth
                        return Some(Self::expr_to_name_static(receiver));
                    }
                }
            }
        }
        None
    }

    /// Convert an expression to a string name (for collection names)
    /// Handles identifiers and nested field access chains
    fn expr_to_name_static(expr: &Expr) -> String {
        use crate::ast::Expr;

        match expr {
            Expr::Ident(name) => name.clone(),
            Expr::Field(base, field) => {
                format!("{}.{}", Self::expr_to_name_static(base), field)
            }
            // For other expression types, use a placeholder
            _ => "_expr_".to_string(),
        }
    }

    /// Extract source map from a conditional value expression
    /// Handles: if cond { v1 } else { source[k] }
    fn extract_source_from_conditional_value(&self, expr: &Expr, key_var: &str) -> Option<String> {
        use crate::ast::Expr;

        match expr {
            // if cond { v1 } else { source[k] }
            Expr::If {
                else_branch: Some(else_branch),
                ..
            } => {
                // Check if else branch is source[k]
                if let Expr::Index(source, idx) = else_branch.as_ref() {
                    if let Expr::Ident(idx_name) = idx.as_ref() {
                        if idx_name == key_var {
                            if let Expr::Ident(source_name) = source.as_ref() {
                                return Some(source_name.clone());
                            }
                            if let Expr::Field(base, field) = source.as_ref() {
                                if let Expr::Ident(base_name) = base.as_ref() {
                                    return Some(format!("{}.{}", base_name, field));
                                }
                            }
                        }
                    }
                }
                // Recursively check then branch
                if let Expr::If { then_branch, .. } = expr {
                    if let Some(source) =
                        self.extract_source_from_conditional_value(then_branch, key_var)
                    {
                        return Some(source);
                    }
                }
            }
            // source[k] directly
            Expr::Index(source, idx) => {
                if let Expr::Ident(idx_name) = idx.as_ref() {
                    if idx_name == key_var {
                        if let Expr::Ident(source_name) = source.as_ref() {
                            return Some(source_name.clone());
                        }
                    }
                }
            }
            _ => {}
        }
        None
    }

    /// Extract the source map name from a contains_key expression
    /// Handles: source.contains_key(k), source.dom().contains(k)
    fn extract_contains_key_source(&self, expr: &Expr, key_var: &str) -> Option<String> {
        use crate::ast::Expr;

        match expr {
            // source.contains_key(k)
            Expr::MethodCall {
                receiver,
                method,
                args,
            } if method == "contains_key" && args.len() == 1 => {
                if let Expr::Ident(arg_name) = &args[0] {
                    if arg_name == key_var {
                        if let Expr::Ident(source) = receiver.as_ref() {
                            return Some(source.clone());
                        }
                        // Also handle field access like s.votes.contains_key(k)
                        if let Expr::Field(base, field) = receiver.as_ref() {
                            if let Expr::Ident(base_name) = base.as_ref() {
                                return Some(format!("{}.{}", base_name, field));
                            }
                        }
                    }
                }
            }
            // source.dom().contains(k)
            Expr::MethodCall {
                receiver,
                method,
                args,
            } if method == "contains" && args.len() == 1 => {
                if let Expr::Ident(arg_name) = &args[0] {
                    if arg_name == key_var {
                        // Check if receiver is source.dom()
                        if let Expr::MethodCall {
                            receiver: inner_recv,
                            method: inner_method,
                            args: inner_args,
                        } = receiver.as_ref()
                        {
                            if inner_method == "dom" && inner_args.is_empty() {
                                if let Expr::Ident(source) = inner_recv.as_ref() {
                                    return Some(source.clone());
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        None
    }

    /// Translate a matched quantifier template to executable code
    fn translate_quantifier_template(
        &self,
        template: &crate::checker::QuantifierTemplate,
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        use crate::checker::QuantifierTemplate;

        match template {
            QuantifierTemplate::SeqComprehension {
                length_expr,
                element_expr,
                index_var,
            } => {
                // Generate: (0..length).map(|i| element).collect::<Vec<_>>()
                let length = self.transform_expr(length_expr, ctx)?;
                let element = self.transform_expr(element_expr, ctx)?;

                Ok(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::Range {
                            start: Box::new(ExecExpr::Literal("0".to_string())),
                            end: Box::new(length),
                        }),
                        method: "map".to_string(),
                        args: vec![ExecExpr::Closure {
                            params: vec![index_var.clone()],
                            body: Box::new(element),
                        }],
                    }),
                    method: "collect".to_string(),
                    args: vec![],
                })
            }

            QuantifierTemplate::MapDomainBiconditional {
                output_map: _,
                key_var,
                domain_predicate,
            } => {
                // Try to extract source map and filter predicate from domain predicate
                // Common pattern: source.contains_key(k) && filter_pred
                // or: filter_pred && source.contains_key(k)
                if let Some((source_map, filter_pred)) =
                    self.extract_source_and_filter(domain_predicate, key_var)
                {
                    // Generate: source.iter().filter(|(k, _)| filter_pred).cloned().collect()
                    let filter_expr = self.transform_expr(&filter_pred, ctx)?;

                    Ok(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::MethodCall {
                                receiver: Box::new(ExecExpr::MethodCall {
                                    receiver: Box::new(ExecExpr::Var(source_map)),
                                    method: "iter".to_string(),
                                    args: vec![],
                                }),
                                method: "filter".to_string(),
                                args: vec![ExecExpr::Closure {
                                    params: vec![format!("({}, _)", key_var)],
                                    body: Box::new(filter_expr),
                                }],
                            }),
                            method: "cloned".to_string(),
                            args: vec![],
                        }),
                        method: "collect".to_string(),
                        args: vec![],
                    })
                } else {
                    // Fallback: generate a comment if we can't extract the pattern
                    let pred = self.transform_expr(domain_predicate, ctx)?;
                    Ok(ExecExpr::Comment(format!(
                        "TODO: Map domain constraint - {} in output <==> {:?}",
                        key_var, pred
                    )))
                }
            }

            QuantifierTemplate::MapPreservation {
                source_map,
                output_map: _,
                key_var: _,
            } => {
                // Generate: source.clone() - this preserves all values
                // Filtering is done by combining with domain constraint
                Ok(ExecExpr::Clone(Box::new(ExecExpr::Var(source_map.clone()))))
            }

            QuantifierTemplate::MapConditionalValue {
                output_map: _,
                key_var,
                value_expr,
            } => {
                // This pattern indicates how values should be computed
                // For patterns like: output[k] == if cond { v1 } else { source[k] }
                // We need a source map to iterate over
                //
                // Try to extract source map from the value expression
                if let Some(source_map) = self.extract_source_from_conditional_value(value_expr, key_var) {
                    // Generate: source.iter().map(|(k, v)| (k.clone(), value_expr)).collect()
                    let value = self.transform_expr(value_expr, ctx)?;

                    Ok(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::MethodCall {
                                receiver: Box::new(ExecExpr::Var(source_map)),
                                method: "iter".to_string(),
                                args: vec![],
                            }),
                            method: "map".to_string(),
                            args: vec![ExecExpr::Closure {
                                params: vec![format!("({}, v)", key_var)],
                                body: Box::new(ExecExpr::Tuple(vec![
                                    ExecExpr::MethodCall {
                                        receiver: Box::new(ExecExpr::Var(key_var.clone())),
                                        method: "clone".to_string(),
                                        args: vec![],
                                    },
                                    value,
                                ])),
                            }],
                        }),
                        method: "collect".to_string(),
                        args: vec![],
                    })
                } else {
                    // Fallback: generate a comment if we can't extract the source
                    let value = self.transform_expr(value_expr, ctx)?;
                    Ok(ExecExpr::Comment(format!(
                        "TODO: Value mapping - output[{}] = {:?}",
                        key_var, value
                    )))
                }
            }

            QuantifierTemplate::MapFilter {
                source_map,
                output_map: _,
                key_var,
                filter_predicate,
            } => {
                // Generate: source.iter().filter(|(k, _)| predicate).collect()
                let pred = self.transform_expr(filter_predicate, ctx)?;

                Ok(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::Var(source_map.clone())),
                            method: "iter".to_string(),
                            args: vec![],
                        }),
                        method: "filter".to_string(),
                        args: vec![ExecExpr::Closure {
                            params: vec![format!("({}, _)", key_var)],
                            body: Box::new(pred),
                        }],
                    }),
                    method: "collect".to_string(),
                    args: vec![],
                })
            }

            QuantifierTemplate::SetComprehension {
                domain_predicate,
                element_var,
            } => {
                // Try to extract source set from domain predicate
                // Pattern: source.contains(x) && filter_pred
                if let Some((source_set, filter_pred)) =
                    self.extract_source_set_and_filter(domain_predicate, element_var)
                {
                    let filter_expr = self.transform_expr(&filter_pred, ctx)?;

                    // Generate: source.iter().filter(|x| filter_pred).cloned().collect()
                    Ok(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::MethodCall {
                                receiver: Box::new(ExecExpr::MethodCall {
                                    receiver: Box::new(ExecExpr::Var(source_set)),
                                    method: "iter".to_string(),
                                    args: vec![],
                                }),
                                method: "filter".to_string(),
                                args: vec![ExecExpr::Closure {
                                    params: vec![element_var.clone()],
                                    body: Box::new(filter_expr),
                                }],
                            }),
                            method: "cloned".to_string(),
                            args: vec![],
                        }),
                        method: "collect".to_string(),
                        args: vec![],
                    })
                } else {
                    // Fallback
                    let pred = self.transform_expr(domain_predicate, ctx)?;
                    Ok(ExecExpr::Comment(format!(
                        "TODO: Set comprehension - {} in output <==> {:?}",
                        element_var, pred
                    )))
                }
            }

            QuantifierTemplate::MapComprehension {
                domain_predicate,
                value_expr,
                key_var,
            } => {
                // Try to extract source from domain predicate
                if let Some((source_map, filter_pred)) =
                    self.extract_source_and_filter(domain_predicate, key_var)
                {
                    let filter_expr = self.transform_expr(&filter_pred, ctx)?;
                    let value = self.transform_expr(value_expr, ctx)?;

                    // Generate: source.iter().filter(|(k, _)| filter_pred).map(|(k, v)| (k.clone(), value)).collect()
                    Ok(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::MethodCall {
                            receiver: Box::new(ExecExpr::MethodCall {
                                receiver: Box::new(ExecExpr::MethodCall {
                                    receiver: Box::new(ExecExpr::Var(source_map)),
                                    method: "iter".to_string(),
                                    args: vec![],
                                }),
                                method: "filter".to_string(),
                                args: vec![ExecExpr::Closure {
                                    params: vec![format!("({}, _)", key_var)],
                                    body: Box::new(filter_expr),
                                }],
                            }),
                            method: "map".to_string(),
                            args: vec![ExecExpr::Closure {
                                params: vec![format!("({}, v)", key_var)],
                                body: Box::new(ExecExpr::Tuple(vec![
                                    ExecExpr::MethodCall {
                                        receiver: Box::new(ExecExpr::Var(key_var.clone())),
                                        method: "clone".to_string(),
                                        args: vec![],
                                    },
                                    value,
                                ])),
                            }],
                        }),
                        method: "collect".to_string(),
                        args: vec![],
                    })
                } else {
                    // Fallback
                    let pred = self.transform_expr(domain_predicate, ctx)?;
                    let value = self.transform_expr(value_expr, ctx)?;
                    Ok(ExecExpr::Comment(format!(
                        "TODO: Map comprehension - {} where {:?} -> {:?}",
                        key_var, pred, value
                    )))
                }
            }

            QuantifierTemplate::MapExclusion {
                output_map: _,
                key_var,
                exclusion_predicate,
            } => {
                // This is a constraint pattern - keys matching predicate are NOT in output
                // In the context of map construction, this combines with other constraints
                let pred = self.transform_expr(exclusion_predicate, ctx)?;
                Ok(ExecExpr::Comment(format!(
                    "Exclusion constraint: when {:?}, {} is NOT in output",
                    pred, key_var
                )))
            }

            QuantifierTemplate::MapInclusion {
                output_map: _,
                source_map,
                key_var,
                inclusion_predicate,
            } => {
                // This is a constraint pattern - keys matching predicate (and in source) ARE in output
                let pred = self.transform_expr(inclusion_predicate, ctx)?;
                Ok(ExecExpr::Comment(format!(
                    "Inclusion constraint: when {:?}{}, {} is in output",
                    pred,
                    source_map
                        .as_ref()
                        .map(|s| format!(" and in {}", s))
                        .unwrap_or_default(),
                    key_var
                )))
            }

            QuantifierTemplate::CollectionCheck {
                container,
                element_var,
                predicate,
            } => {
                // Generate: container.iter().all(|x| predicate)
                // Pattern: forall |x| container.contains(x) ==> pred(x)
                let container_expr = self.transform_expr(container, ctx)?;
                let pred_expr = self.transform_expr(predicate, ctx)?;

                Ok(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::MethodCall {
                        receiver: Box::new(container_expr),
                        method: "iter".to_string(),
                        args: vec![],
                    }),
                    method: "all".to_string(),
                    args: vec![ExecExpr::Closure {
                        params: vec![element_var.clone()],
                        body: Box::new(pred_expr),
                    }],
                })
            }
        }
    }
}

impl Default for Translator {
    fn default() -> Self {
        Self::new(TranslatorConfig::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Literal, Path};

    #[test]
    fn test_translate_name() {
        let translator = Translator::default();
        assert_eq!(translator.translate_name("LAcceptor"), "CAcceptor");
        assert_eq!(translator.translate_name("Ballot"), "CBallot");
    }

    #[test]
    fn test_translate_type() {
        let translator = Translator::default();

        let named = Type::Named(Path::single("LAcceptor".to_string()));
        let result = translator.translate_type(&named);
        assert!(matches!(result, ExecType::Named(n) if n == "CAcceptor"));

        let seq = Type::Seq(Box::new(Type::Named(Path::single("LPacket".to_string()))));
        let result = translator.translate_type(&seq);
        assert!(matches!(result, ExecType::Vec(_)));
    }

    #[test]
    fn test_exec_type_to_string() {
        let ty = ExecType::Vec(Box::new(ExecType::Named("CPacket".to_string())));
        assert_eq!(ty.to_rust_string(), "Vec<CPacket>");

        let tuple = ExecType::Tuple(vec![
            ExecType::Named("CAcceptor".to_string()),
            ExecType::Vec(Box::new(ExecType::Named("CPacket".to_string()))),
        ]);
        assert_eq!(tuple.to_rust_string(), "(CAcceptor, Vec<CPacket>)");
    }

    fn make_ctx() -> TransformContext<'static> {
        static CONFIG: std::sync::OnceLock<TranslatorConfig> = std::sync::OnceLock::new();
        let mut output_types = HashMap::new();
        output_types.insert(
            "s_".to_string(),
            Type::Named(Path::single("LState".to_string())),
        );
        TransformContext {
            config: CONFIG.get_or_init(TranslatorConfig::default),
            output_params: vec!["s_".to_string()],
            input_params: vec!["s".to_string(), "inp".to_string()],
            output_types,
        }
    }

    #[test]
    fn test_transform_literal() {
        let translator = Translator::default();
        let ctx = make_ctx();

        let expr = Expr::Literal(Literal::Int(42));
        let result = translator.transform_expr(&expr, &ctx).unwrap();
        assert!(matches!(result, ExecExpr::Literal(s) if s == "42"));
    }

    #[test]
    fn test_transform_field_access() {
        let translator = Translator::default();
        let ctx = make_ctx();

        let expr = Expr::Field(
            Box::new(Expr::Ident("s".to_string())),
            "max_bal".to_string(),
        );
        let result = translator.transform_expr(&expr, &ctx).unwrap();
        match result {
            ExecExpr::Field(base, field) => {
                assert_eq!(field, "max_bal");
                assert!(matches!(*base, ExecExpr::Var(name) if name == "s"));
            }
            _ => panic!("Expected Field, got {:?}", result),
        }
    }

    #[test]
    fn test_transform_if_else() {
        let translator = Translator::default();
        let ctx = make_ctx();

        let expr = Expr::If {
            cond: Box::new(Expr::Literal(Literal::Bool(true))),
            then_branch: Box::new(Expr::Literal(Literal::Int(1))),
            else_branch: Some(Box::new(Expr::Literal(Literal::Int(2)))),
        };
        let result = translator.transform_expr(&expr, &ctx).unwrap();
        assert!(matches!(result, ExecExpr::If { .. }));
    }

    #[test]
    fn test_transform_binary_comparison() {
        let translator = Translator::default();
        let ctx = make_ctx();

        let expr = Expr::Lt(
            Box::new(Expr::Ident("a".to_string())),
            Box::new(Expr::Ident("b".to_string())),
        );
        let result = translator.transform_expr(&expr, &ctx).unwrap();
        match result {
            ExecExpr::Binary { op, .. } => {
                assert_eq!(op, "<");
            }
            _ => panic!("Expected Binary, got {:?}", result),
        }
    }

    #[test]
    fn test_transform_clone_output() {
        let translator = Translator::default();
        let ctx = make_ctx();

        // s_ == s should produce clone
        let expr = Expr::Eq(
            Box::new(Expr::Ident("s_".to_string())),
            Box::new(Expr::Ident("s".to_string())),
        );
        let result = translator.transform_expr(&expr, &ctx).unwrap();
        assert!(matches!(result, ExecExpr::Clone(_)));
    }

    #[test]
    fn test_transform_seq_empty() {
        let translator = Translator::default();
        let ctx = make_ctx();

        let expr = Expr::SeqEmpty;
        let result = translator.transform_expr(&expr, &ctx).unwrap();
        assert!(matches!(result, ExecExpr::VecLit(v) if v.is_empty()));
    }

    #[test]
    fn test_extract_source_and_filter() {
        let translator = Translator::default();

        // Test: source.contains_key(k) && k >= threshold
        let contains_key = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("source".to_string())),
            method: "contains_key".to_string(),
            args: vec![Expr::Ident("k".to_string())],
        };
        let filter = Expr::Ge(
            Box::new(Expr::Ident("k".to_string())),
            Box::new(Expr::Ident("threshold".to_string())),
        );
        let pred = Expr::Conjunction(vec![contains_key, filter.clone()]);

        let result = translator.extract_source_and_filter(&pred, "k");
        assert!(result.is_some());
        let (source, extracted_filter) = result.unwrap();
        assert_eq!(source, "source");
        // Filter should be the Ge expression
        assert!(matches!(extracted_filter, Expr::Ge(..)));
    }

    #[test]
    fn test_extract_source_dom_contains() {
        let translator = Translator::default();

        // Test: source.dom().contains(k)
        let dom = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("source".to_string())),
            method: "dom".to_string(),
            args: vec![],
        };
        let contains = Expr::MethodCall {
            receiver: Box::new(dom),
            method: "contains".to_string(),
            args: vec![Expr::Ident("k".to_string())],
        };

        let result = translator.extract_contains_key_source(&contains, "k");
        assert!(result.is_some());
        assert_eq!(result.unwrap(), "source");
    }

    #[test]
    fn test_extract_source_from_conditional_value() {
        let translator = Translator::default();

        // Test: if cond { new_value } else { source[k] }
        let source_index = Expr::Index(
            Box::new(Expr::Ident("source".to_string())),
            Box::new(Expr::Ident("k".to_string())),
        );
        let conditional = Expr::If {
            cond: Box::new(Expr::Literal(Literal::Bool(true))),
            then_branch: Box::new(Expr::Ident("new_value".to_string())),
            else_branch: Some(Box::new(source_index)),
        };

        let result = translator.extract_source_from_conditional_value(&conditional, "k");
        assert!(result.is_some());
        assert_eq!(result.unwrap(), "source");
    }

    #[test]
    fn test_exists_with_container_contains() {
        let translator = Translator::default();
        let ctx = make_ctx();

        // Test: exists |p| S.contains(p) && pred(p)
        // Build S.contains(p)
        let contains = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("S".to_string())),
            method: "contains".to_string(),
            args: vec![Expr::Ident("p".to_string())],
        };
        // Build pred(p) as p.valid
        let pred = Expr::Field(
            Box::new(Expr::Ident("p".to_string())),
            "valid".to_string(),
        );
        // Build conjunction
        let body = Expr::Conjunction(vec![contains, pred]);

        // Build exists expression
        let exists = Expr::Exists {
            vars: vec![crate::ast::Binding {
                pattern: crate::ast::Pattern::Ident("p".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            }],
            body: Box::new(body),
        };

        let result = translator.transform_expr(&exists, &ctx);
        assert!(result.is_ok(), "exists should transform successfully: {:?}", result);

        // Check the result is a method call to .any()
        let exec_expr = result.unwrap();
        match &exec_expr {
            ExecExpr::MethodCall { method, .. } => {
                assert_eq!(method, "any", "Should generate .any() call");
            }
            _ => panic!("Expected MethodCall, got {:?}", exec_expr),
        }
    }

    #[test]
    fn test_extract_exists_container_and_pred() {
        let translator = Translator::default();

        // Test: S.contains(p) && pred_call(p)
        let contains = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("S".to_string())),
            method: "contains".to_string(),
            args: vec![Expr::Ident("p".to_string())],
        };
        let pred = Expr::Call {
            func: crate::ast::Path::single("some_pred".to_string()),
            args: vec![Expr::Ident("p".to_string())],
        };
        let body = Expr::Conjunction(vec![contains, pred.clone()]);

        let result = translator.extract_exists_container_and_pred(&body, "p");
        assert!(result.is_some());
        let (container, predicate) = result.unwrap();

        // Container should be S
        if let Expr::Ident(name) = container {
            assert_eq!(name, "S");
        } else {
            panic!("Container should be identifier");
        }

        // Predicate should be the call expression
        assert!(matches!(predicate, Expr::Call { .. }));
    }

    #[test]
    fn test_collection_check_template() {
        let translator = Translator::default();
        let ctx = make_ctx();

        // Test: forall |p| packets.contains(p) ==> p.src != other.src
        // Build packets.contains(p)
        let contains = Expr::MethodCall {
            receiver: Box::new(Expr::Ident("packets".to_string())),
            method: "contains".to_string(),
            args: vec![Expr::Ident("p".to_string())],
        };
        // Build p.src != other.src
        let pred = Expr::Ne(
            Box::new(Expr::Field(
                Box::new(Expr::Ident("p".to_string())),
                "src".to_string(),
            )),
            Box::new(Expr::Field(
                Box::new(Expr::Ident("other".to_string())),
                "src".to_string(),
            )),
        );
        // Build implication
        let body = Expr::Implies(Box::new(contains), Box::new(pred));

        // Build forall expression
        let forall = Expr::Forall {
            vars: vec![crate::ast::Binding {
                pattern: crate::ast::Pattern::Ident("p".to_string()),
                ty: None,
                variable_mode: crate::ast::VariableMode::Exec,
            }],
            triggers: vec![],
            body: Box::new(body),
        };

        let result = translator.transform_expr(&forall, &ctx);
        assert!(result.is_ok(), "forall collection check should transform: {:?}", result);

        // Check the result is a method call to .all()
        let exec_expr = result.unwrap();
        match &exec_expr {
            ExecExpr::MethodCall { method, .. } => {
                assert_eq!(method, "all", "Should generate .all() call");
            }
            _ => panic!("Expected MethodCall with .all(), got {:?}", exec_expr),
        }
    }

    #[test]
    fn test_tuple_return_generation() {
        let translator = Translator::default();

        // Create context with two output params: s_ and sent_packets
        let config = TranslatorConfig::default();
        let ctx = TransformContext {
            config: &config,
            output_params: vec!["s_".to_string(), "sent_packets".to_string()],
            input_params: vec!["s".to_string()],
            output_types: HashMap::new(),
        };

        // Build: s_ == s &&& sent_packets == Seq::empty()
        let s_assign = Expr::Eq(
            Box::new(Expr::Ident("s_".to_string())),
            Box::new(Expr::Ident("s".to_string())),
        );
        let packets_assign = Expr::Eq(
            Box::new(Expr::Ident("sent_packets".to_string())),
            Box::new(Expr::SeqEmpty),
        );
        let conjunction = Expr::Conjunction(vec![s_assign, packets_assign]);

        let result = translator.transform_expr(&conjunction, &ctx);
        assert!(result.is_ok(), "Conjunction should transform: {:?}", result);

        // Check that result is a Tuple with two elements
        let exec_expr = result.unwrap();
        match &exec_expr {
            ExecExpr::Tuple(elems) => {
                assert_eq!(elems.len(), 2, "Should have 2 tuple elements");
                // First should be clone of s (or Var if not recognized as clone)
                assert!(
                    matches!(&elems[0], ExecExpr::Clone(_)) || matches!(&elems[0], ExecExpr::Var(_)),
                    "First element should be Clone or Var, got {:?}", elems[0]
                );
                // Second should be empty vec
                assert!(matches!(&elems[1], ExecExpr::VecLit(v) if v.is_empty()));
            }
            _ => panic!("Expected Tuple, got {:?}", exec_expr),
        }
    }
}
