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
        name: String,
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
    Call {
        func: String,
        args: Vec<ExecExpr>,
    },
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
}

/// Context for expression transformation
pub struct TransformContext<'a> {
    pub config: &'a TranslatorConfig,
    pub output_params: Vec<String>,
    pub input_params: Vec<String>,
}

impl<'a> TransformContext<'a> {
    pub fn is_output(&self, name: &str) -> bool {
        self.output_params.contains(&name.to_string())
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
                        ty: ExecType::Reference(
                            Box::new(self.translate_type(&param.ty)),
                            false,
                        ),
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

    /// Transform a spec expression to an exec expression
    fn transform_expr(&self, expr: &Expr, ctx: &TransformContext) -> TranspileResult<ExecExpr> {
        match expr {
            Expr::Literal(lit) => Ok(ExecExpr::Literal(format!("{:?}", lit))),

            Expr::Ident(name) => Ok(ExecExpr::Var(name.clone())),

            Expr::Field(base, field) => {
                let base_expr = self.transform_expr(base, ctx)?;
                Ok(ExecExpr::Field(Box::new(base_expr), field.clone()))
            }

            Expr::If { cond, then_branch, else_branch } => {
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
                // Transform conjunction into a block of statements
                let stmts: TranspileResult<Vec<_>> = exprs
                    .iter()
                    .map(|e| self.transform_expr(e, ctx))
                    .collect();
                Ok(ExecExpr::Block(stmts?))
            }

            Expr::Eq(lhs, rhs) => {
                // Check if this is an assignment (output = expression)
                if let Expr::Ident(name) = lhs.as_ref() {
                    if ctx.is_output(name) {
                        let value = self.transform_expr(rhs, ctx)?;
                        return Ok(value); // The output is just the computed value
                    }
                }
                // Otherwise it's a comparison
                let lhs_expr = self.transform_expr(lhs, ctx)?;
                let rhs_expr = self.transform_expr(rhs, ctx)?;
                Ok(ExecExpr::Call {
                    func: "eq".to_string(),
                    args: vec![lhs_expr, rhs_expr],
                })
            }

            Expr::Call { func, args } => {
                let translated_args: TranspileResult<Vec<_>> = args
                    .iter()
                    .map(|a| self.transform_expr(a, ctx))
                    .collect();
                let func_name = func.last().unwrap_or("unknown");
                Ok(ExecExpr::Call {
                    func: self.translate_name(func_name),
                    args: translated_args?,
                })
            }

            Expr::SeqEmpty => Ok(ExecExpr::VecLit(vec![])),

            Expr::SeqLit(elems) => {
                let translated: TranspileResult<Vec<_>> = elems
                    .iter()
                    .map(|e| self.transform_expr(e, ctx))
                    .collect();
                Ok(ExecExpr::VecLit(translated?))
            }

            // TODO: Handle more expression types
            _ => Err(TranspileError::UnsupportedPattern {
                message: format!("Unsupported expression type: {:?}", std::mem::discriminant(expr)),
                span: None,
                help: Some("This pattern may need manual implementation".to_string()),
            }),
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
    use crate::ast::Path;

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
}
