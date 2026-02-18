//! Code generation from quantifier templates.
//!
//! This module transforms recognized quantifier templates into executable code.
//! It connects the template matching system with code generation.

use crate::ast::Expr;
use crate::error::{TranspileError, TranspileResult};
use crate::templates::QuantifierTemplate;
use crate::translator::{ExecExpr, TransformContext, TranslatorConfig};

/// Code generator for quantifier templates
pub struct TemplateCodeGenerator {
    config: TranslatorConfig,
}

impl TemplateCodeGenerator {
    /// Create a new template code generator
    pub fn new(config: TranslatorConfig) -> Self {
        Self { config }
    }

    /// Generate executable code from a quantifier template
    pub fn generate(
        &self,
        template: &QuantifierTemplate,
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        match template {
            QuantifierTemplate::SeqComprehension {
                index_var,
                length_expr,
                element_expr,
                seq_var: _,
            } => self.generate_seq_comprehension(index_var, length_expr, element_expr, ctx),

            QuantifierTemplate::SetComprehension {
                elem_var,
                domain_predicate,
                set_var: _,
            } => self.generate_set_comprehension(elem_var, domain_predicate, ctx),

            QuantifierTemplate::MapDomain {
                key_var,
                domain_predicate,
                map_var: _,
            } => self.generate_map_domain(key_var, domain_predicate, ctx),

            QuantifierTemplate::MapValue {
                key_var,
                value_expr,
                map_var,
            } => self.generate_map_value(key_var, value_expr, map_var, ctx),

            QuantifierTemplate::MapComprehension {
                key_var,
                domain_predicate,
                value_expr,
                map_var,
            } => {
                self.generate_map_comprehension(key_var, domain_predicate, value_expr, map_var, ctx)
            }

            QuantifierTemplate::SimpleAssignment {
                output_var: _,
                value_expr,
            } => self.transform_expr(value_expr, ctx),

            QuantifierTemplate::Copy {
                output_var: _,
                input_var,
            } => Ok(ExecExpr::Clone(Box::new(ExecExpr::Var(input_var.clone())))),

            QuantifierTemplate::StructConstruction { output_var, fields } => {
                self.generate_struct_construction(output_var, fields, ctx)
            }

            QuantifierTemplate::Unrecognized { reason, hint, .. } => {
                Err(TranspileError::UnsupportedPattern {
                    message: reason.clone(),
                    span: None,
                    help: hint.clone(),
                })
            }
        }
    }

    /// Generate Vec::from_fn style sequence comprehension
    /// Spec: forall |i| 0 <= i < len ==> seq[i] == f(i)
    /// Exec: (0..len).map(|i| f(i)).collect()
    fn generate_seq_comprehension(
        &self,
        index_var: &str,
        length_expr: &Expr,
        element_expr: &Expr,
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        let len_expr = self.transform_expr(length_expr, ctx)?;
        let elem_expr = self.transform_expr(element_expr, ctx)?;

        // Generate: (0..len).map(|i| elem_expr).collect()
        Ok(ExecExpr::MethodCall {
            receiver: Box::new(ExecExpr::MethodCall {
                receiver: Box::new(ExecExpr::Range {
                    start: Box::new(ExecExpr::Literal("0".to_string())),
                    end: Box::new(len_expr),
                }),
                method: "map".to_string(),
                args: vec![ExecExpr::Closure {
                    params: vec![index_var.to_string()],
                    body: Box::new(elem_expr),
                }],
            }),
            method: "collect".to_string(),
            args: vec![],
        })
    }

    /// Generate set comprehension (filter operation)
    fn generate_set_comprehension(
        &self,
        _elem_var: &str,
        _domain_predicate: &Expr,
        _ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        // Set comprehension requires knowing the domain to iterate over
        // This is a more complex case that typically needs additional context
        Err(TranspileError::UnsupportedPattern {
            message: "Set comprehension requires explicit domain specification".to_string(),
            span: None,
            help: Some("Consider specifying the source set to iterate over".to_string()),
        })
    }

    /// Generate map domain (keys only)
    fn generate_map_domain(
        &self,
        _key_var: &str,
        _domain_predicate: &Expr,
        _ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        // Map domain alone needs to be combined with value pattern
        Err(TranspileError::UnsupportedPattern {
            message: "Map domain pattern needs to be combined with value pattern".to_string(),
            span: None,
            help: Some("Use full MapComprehension pattern instead".to_string()),
        })
    }

    /// Generate map value iteration
    /// Spec: forall |k| k in map ==> map[k] == f(source[k])
    /// Exec: source.iter().map(|(k, v)| (k.clone(), f(v))).collect()
    fn generate_map_value(
        &self,
        key_var: &str,
        value_expr: &Expr,
        map_var: &str,
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        let val_expr = self.transform_expr(value_expr, ctx)?;

        // Generate: source.iter().map(|(k, v)| (k.clone(), val_expr)).collect()
        Ok(ExecExpr::MethodCall {
            receiver: Box::new(ExecExpr::MethodCall {
                receiver: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::Var(map_var.to_string())),
                    method: "iter".to_string(),
                    args: vec![],
                }),
                method: "map".to_string(),
                args: vec![ExecExpr::Closure {
                    params: vec![format!("({}, _v)", key_var)],
                    body: Box::new(ExecExpr::Tuple(vec![
                        ExecExpr::Clone(Box::new(ExecExpr::Var(key_var.to_string()))),
                        val_expr,
                    ])),
                }],
            }),
            method: "collect".to_string(),
            args: vec![],
        })
    }

    /// Generate full map comprehension with domain filter and value transformation
    /// Spec: forall |k| k in result <==> pred(k) && forall |k| k in result ==> result[k] == f(k)
    /// Exec: source.iter().filter(|(k,_)| pred(k)).map(|(k,v)| (k.clone(), f(v))).collect()
    fn generate_map_comprehension(
        &self,
        key_var: &str,
        domain_predicate: &Expr,
        value_expr: &Expr,
        map_var: &str,
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        let pred_expr = self.transform_expr(domain_predicate, ctx)?;
        let val_expr = self.transform_expr(value_expr, ctx)?;

        // Generate: source.iter()
        //              .filter(|(k,_)| pred(k))
        //              .map(|(k, v)| (k.clone(), f(v)))
        //              .collect()
        Ok(ExecExpr::MethodCall {
            receiver: Box::new(ExecExpr::MethodCall {
                receiver: Box::new(ExecExpr::MethodCall {
                    receiver: Box::new(ExecExpr::MethodCall {
                        receiver: Box::new(ExecExpr::Var(map_var.to_string())),
                        method: "iter".to_string(),
                        args: vec![],
                    }),
                    method: "filter".to_string(),
                    args: vec![ExecExpr::Closure {
                        params: vec![format!("({}, _)", key_var)],
                        body: Box::new(pred_expr),
                    }],
                }),
                method: "map".to_string(),
                args: vec![ExecExpr::Closure {
                    params: vec![format!("({}, _v)", key_var)],
                    body: Box::new(ExecExpr::Tuple(vec![
                        ExecExpr::Clone(Box::new(ExecExpr::Var(key_var.to_string()))),
                        val_expr,
                    ])),
                }],
            }),
            method: "collect".to_string(),
            args: vec![],
        })
    }

    /// Generate struct construction from field assignments
    fn generate_struct_construction(
        &self,
        output_var: &str,
        fields: &[(String, Expr)],
        ctx: &TransformContext,
    ) -> TranspileResult<ExecExpr> {
        let translated_fields: TranspileResult<Vec<_>> = fields
            .iter()
            .map(|(fname, fexpr)| {
                let expr = self.transform_expr(fexpr, ctx)?;
                Ok((fname.clone(), expr))
            })
            .collect();

        // Determine base variable name (remove trailing _)
        let base_name = output_var.trim_end_matches('_');

        // Get struct name from output parameter's type
        let struct_name = ctx
            .get_output_struct_name(output_var)
            .map(|n| self.translate_name(&n))
            .unwrap_or_else(|| self.translate_name(base_name));

        if ctx.input_params.contains(&base_name.to_string()) {
            // Struct update syntax
            Ok(ExecExpr::StructUpdate {
                name: struct_name,
                base: Box::new(ExecExpr::Clone(Box::new(ExecExpr::Var(
                    base_name.to_string(),
                )))),
                fields: translated_fields?,
            })
        } else {
            // Full struct construction (need struct name from type info)
            Ok(ExecExpr::Struct {
                name: struct_name,
                fields: translated_fields?,
            })
        }
    }

    /// Transform a spec expression to exec expression (simplified version)
    fn transform_expr(&self, expr: &Expr, ctx: &TransformContext) -> TranspileResult<ExecExpr> {
        // Delegate to the main translator's transform_expr
        // This is a simplified version for template code generation
        use crate::translator::Translator;
        let translator = Translator::new(self.config.clone());
        translator.transform_expr_public(expr, ctx)
    }

    /// Translate L* to C* naming
    fn translate_name(&self, name: &str) -> String {
        if name.starts_with(&self.config.spec_prefix) {
            format!(
                "{}{}",
                self.config.exec_prefix,
                &name[self.config.spec_prefix.len()..]
            )
        } else {
            format!("{}{}", self.config.exec_prefix, name)
        }
    }
}

impl Default for TemplateCodeGenerator {
    fn default() -> Self {
        Self::new(TranslatorConfig::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Literal;

    fn make_ctx() -> TransformContext<'static> {
        use std::collections::HashMap;
        static CONFIG: std::sync::OnceLock<TranslatorConfig> = std::sync::OnceLock::new();
        let mut output_types = HashMap::new();
        output_types.insert(
            "result".to_string(),
            crate::ast::Type::Named(crate::ast::Path::single("LResult".to_string())),
        );
        TransformContext {
            config: CONFIG.get_or_init(TranslatorConfig::default),
            output_params: vec!["result".to_string()],
            input_params: vec!["src".to_string()],
            output_types,
            input_types: std::collections::HashMap::new(),
            field_substitutions: std::collections::HashMap::new(),
            temp_var_counter: std::cell::RefCell::new(0),
            requires: vec![],
        }
    }

    #[test]
    fn test_generate_copy() {
        let generator = TemplateCodeGenerator::default();
        let ctx = make_ctx();

        let template = QuantifierTemplate::Copy {
            output_var: "result".to_string(),
            input_var: "src".to_string(),
        };

        let result = generator.generate(&template, &ctx).unwrap();
        assert!(matches!(result, ExecExpr::Clone(_)));
    }

    #[test]
    fn test_generate_simple_assignment() {
        let generator = TemplateCodeGenerator::default();
        let ctx = make_ctx();

        let template = QuantifierTemplate::SimpleAssignment {
            output_var: "result".to_string(),
            value_expr: Box::new(Expr::Literal(Literal::Int(42))),
        };

        let result = generator.generate(&template, &ctx).unwrap();
        assert!(matches!(result, ExecExpr::Literal(_)));
    }

    // --- Helper for struct construction with update syntax ---
    // When the base name (output_var trimmed of trailing '_') is in input_params,
    // generate_struct_construction produces StructUpdate instead of Struct.
    fn make_ctx_with_result_as_input() -> TransformContext<'static> {
        use std::collections::HashMap;
        static CONFIG: std::sync::OnceLock<TranslatorConfig> = std::sync::OnceLock::new();
        let mut output_types = HashMap::new();
        output_types.insert(
            "result_".to_string(),
            crate::ast::Type::Named(crate::ast::Path::single("LResult".to_string())),
        );
        TransformContext {
            config: CONFIG.get_or_init(TranslatorConfig::default),
            output_params: vec!["result_".to_string()],
            input_params: vec!["result".to_string()],
            output_types,
            input_types: std::collections::HashMap::new(),
            field_substitutions: std::collections::HashMap::new(),
            temp_var_counter: std::cell::RefCell::new(0),
            requires: vec![],
        }
    }

    #[test]
    fn test_generate_unrecognized_returns_error() {
        let generator = TemplateCodeGenerator::default();
        let ctx = make_ctx();

        let template = QuantifierTemplate::Unrecognized {
            expr: Box::new(Expr::Literal(Literal::Bool(true))),
            reason: "cannot match".to_string(),
            hint: Some("try something else".to_string()),
        };

        let result = generator.generate(&template, &ctx);
        assert!(result.is_err());
        match result.unwrap_err() {
            crate::error::TranspileError::UnsupportedPattern { message, help, .. } => {
                assert_eq!(message, "cannot match");
                assert_eq!(help, Some("try something else".to_string()));
            }
            other => panic!("Expected UnsupportedPattern, got {:?}", other),
        }
    }

    #[test]
    fn test_generate_seq_comprehension() {
        let generator = TemplateCodeGenerator::default();
        let ctx = make_ctx();

        let template = QuantifierTemplate::SeqComprehension {
            index_var: "i".to_string(),
            length_expr: Box::new(Expr::Literal(Literal::Int(10))),
            element_expr: Box::new(Expr::Ident("i".to_string())),
            seq_var: "result".to_string(),
        };

        let result = generator.generate(&template, &ctx).unwrap();
        // Should produce: (0..10).map(|i| i).collect()
        // Top-level is MethodCall { method: "collect", receiver: MethodCall { method: "map", ... } }
        match &result {
            ExecExpr::MethodCall {
                method,
                receiver,
                args,
            } => {
                assert_eq!(method, "collect");
                assert!(args.is_empty());
                // Inner should be a "map" call
                match receiver.as_ref() {
                    ExecExpr::MethodCall {
                        method: inner_method,
                        receiver: inner_receiver,
                        args: inner_args,
                    } => {
                        assert_eq!(inner_method, "map");
                        assert_eq!(inner_args.len(), 1);
                        // The closure param should be "i"
                        match &inner_args[0] {
                            ExecExpr::Closure { params, .. } => {
                                assert_eq!(params, &["i".to_string()]);
                            }
                            other => panic!("Expected Closure in map args, got {:?}", other),
                        }
                        // Innermost should be a Range
                        assert!(matches!(inner_receiver.as_ref(), ExecExpr::Range { .. }));
                    }
                    other => panic!("Expected MethodCall(map) inside collect, got {:?}", other),
                }
            }
            other => panic!("Expected MethodCall(collect), got {:?}", other),
        }
    }

    #[test]
    fn test_generate_set_comprehension_returns_error() {
        let generator = TemplateCodeGenerator::default();
        let ctx = make_ctx();

        let template = QuantifierTemplate::SetComprehension {
            elem_var: "x".to_string(),
            domain_predicate: Box::new(Expr::Literal(Literal::Bool(true))),
            set_var: "result".to_string(),
        };

        let result = generator.generate(&template, &ctx);
        assert!(result.is_err());
        match result.unwrap_err() {
            crate::error::TranspileError::UnsupportedPattern { message, .. } => {
                assert!(message.contains("Set comprehension"));
            }
            other => panic!("Expected UnsupportedPattern, got {:?}", other),
        }
    }

    #[test]
    fn test_generate_map_domain_returns_error() {
        let generator = TemplateCodeGenerator::default();
        let ctx = make_ctx();

        let template = QuantifierTemplate::MapDomain {
            key_var: "k".to_string(),
            domain_predicate: Box::new(Expr::Literal(Literal::Bool(true))),
            map_var: "result".to_string(),
        };

        let result = generator.generate(&template, &ctx);
        assert!(result.is_err());
        match result.unwrap_err() {
            crate::error::TranspileError::UnsupportedPattern { message, .. } => {
                assert!(message.contains("Map domain"));
            }
            other => panic!("Expected UnsupportedPattern, got {:?}", other),
        }
    }

    #[test]
    fn test_generate_map_value() {
        let generator = TemplateCodeGenerator::default();
        let ctx = make_ctx();

        let template = QuantifierTemplate::MapValue {
            key_var: "k".to_string(),
            value_expr: Box::new(Expr::Literal(Literal::Int(99))),
            map_var: "src".to_string(),
        };

        let result = generator.generate(&template, &ctx).unwrap();
        // Should produce: src.iter().map(|(k, _v)| (k.clone(), 99)).collect()
        match &result {
            ExecExpr::MethodCall {
                method,
                receiver,
                args,
            } => {
                assert_eq!(method, "collect");
                assert!(args.is_empty());
                // Inner chain: .map(...)
                match receiver.as_ref() {
                    ExecExpr::MethodCall {
                        method: map_method,
                        receiver: iter_call,
                        args: map_args,
                    } => {
                        assert_eq!(map_method, "map");
                        assert_eq!(map_args.len(), 1);
                        // Closure param should contain the key_var pattern
                        match &map_args[0] {
                            ExecExpr::Closure { params, body } => {
                                assert_eq!(params[0], "(k, _v)");
                                // Body should be a Tuple with (Clone(k), literal)
                                match body.as_ref() {
                                    ExecExpr::Tuple(elems) => {
                                        assert_eq!(elems.len(), 2);
                                        assert!(matches!(&elems[0], ExecExpr::Clone(_)));
                                    }
                                    other => panic!("Expected Tuple body, got {:?}", other),
                                }
                            }
                            other => panic!("Expected Closure, got {:?}", other),
                        }
                        // Inner should be .iter()
                        match iter_call.as_ref() {
                            ExecExpr::MethodCall {
                                method: iter_method,
                                receiver: source,
                                ..
                            } => {
                                assert_eq!(iter_method, "iter");
                                assert!(matches!(source.as_ref(), ExecExpr::Var(v) if v == "src"));
                            }
                            other => panic!("Expected MethodCall(iter), got {:?}", other),
                        }
                    }
                    other => panic!("Expected MethodCall(map), got {:?}", other),
                }
            }
            other => panic!("Expected MethodCall(collect), got {:?}", other),
        }
    }

    #[test]
    fn test_generate_map_comprehension() {
        let generator = TemplateCodeGenerator::default();
        let ctx = make_ctx();

        let template = QuantifierTemplate::MapComprehension {
            key_var: "k".to_string(),
            domain_predicate: Box::new(Expr::Literal(Literal::Bool(true))),
            value_expr: Box::new(Expr::Literal(Literal::Int(0))),
            map_var: "src".to_string(),
        };

        let result = generator.generate(&template, &ctx).unwrap();
        // Should produce: src.iter().filter(...).map(...).collect()
        match &result {
            ExecExpr::MethodCall {
                method,
                receiver,
                args,
            } => {
                assert_eq!(method, "collect");
                assert!(args.is_empty());
                // Next level: .map(...)
                match receiver.as_ref() {
                    ExecExpr::MethodCall {
                        method: map_method,
                        receiver: filter_call,
                        ..
                    } => {
                        assert_eq!(map_method, "map");
                        // Next level: .filter(...)
                        match filter_call.as_ref() {
                            ExecExpr::MethodCall {
                                method: filter_method,
                                receiver: iter_call,
                                args: filter_args,
                            } => {
                                assert_eq!(filter_method, "filter");
                                assert_eq!(filter_args.len(), 1);
                                // filter closure param should contain key_var
                                match &filter_args[0] {
                                    ExecExpr::Closure { params, .. } => {
                                        assert_eq!(params[0], "(k, _)");
                                    }
                                    other => {
                                        panic!("Expected Closure in filter, got {:?}", other)
                                    }
                                }
                                // Innermost: .iter()
                                match iter_call.as_ref() {
                                    ExecExpr::MethodCall {
                                        method: iter_method,
                                        ..
                                    } => {
                                        assert_eq!(iter_method, "iter");
                                    }
                                    other => {
                                        panic!("Expected MethodCall(iter), got {:?}", other)
                                    }
                                }
                            }
                            other => panic!("Expected MethodCall(filter), got {:?}", other),
                        }
                    }
                    other => panic!("Expected MethodCall(map), got {:?}", other),
                }
            }
            other => panic!("Expected MethodCall(collect), got {:?}", other),
        }
    }

    #[test]
    fn test_generate_struct_construction_update() {
        let generator = TemplateCodeGenerator::default();
        let ctx = make_ctx_with_result_as_input();

        // output_var = "result_", base_name = "result" which IS in input_params
        // So this should produce StructUpdate syntax
        let template = QuantifierTemplate::StructConstruction {
            output_var: "result_".to_string(),
            fields: vec![
                (
                    "field_a".to_string(),
                    Expr::Literal(Literal::Int(1)),
                ),
                (
                    "field_b".to_string(),
                    Expr::Literal(Literal::Int(2)),
                ),
            ],
        };

        let result = generator.generate(&template, &ctx).unwrap();
        match &result {
            ExecExpr::StructUpdate {
                name,
                base,
                fields,
            } => {
                // Type is LResult -> translate_name -> CResult
                assert_eq!(name, "CResult");
                // Base should be Clone(Var("result"))
                match base.as_ref() {
                    ExecExpr::Clone(inner) => {
                        assert!(matches!(inner.as_ref(), ExecExpr::Var(v) if v == "result"));
                    }
                    other => panic!("Expected Clone(Var(result)), got {:?}", other),
                }
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0, "field_a");
                assert_eq!(fields[1].0, "field_b");
            }
            other => panic!("Expected StructUpdate, got {:?}", other),
        }
    }

    #[test]
    fn test_generate_struct_construction_new() {
        let generator = TemplateCodeGenerator::default();
        let ctx = make_ctx();

        // output_var = "result", base_name = "result" which is NOT in input_params (only "src" is)
        // So this should produce full Struct construction
        let template = QuantifierTemplate::StructConstruction {
            output_var: "result".to_string(),
            fields: vec![(
                "value".to_string(),
                Expr::Literal(Literal::Int(42)),
            )],
        };

        let result = generator.generate(&template, &ctx).unwrap();
        match &result {
            ExecExpr::Struct { name, fields } => {
                // output_types has "result" -> LResult, translate_name("LResult") -> "CResult"
                assert_eq!(name, "CResult");
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].0, "value");
            }
            other => panic!("Expected Struct, got {:?}", other),
        }
    }

    #[test]
    fn test_translate_name_l_to_c() {
        let generator = TemplateCodeGenerator::default();
        // Default config: spec_prefix = "L", exec_prefix = "C"
        assert_eq!(generator.translate_name("LAcceptor"), "CAcceptor");
    }

    #[test]
    fn test_translate_name_no_prefix() {
        let generator = TemplateCodeGenerator::default();
        // "Ballot" does not start with "L", so exec_prefix is prepended: "CBallot"
        assert_eq!(generator.translate_name("Ballot"), "CBallot");
    }

    #[test]
    fn test_default_impl() {
        let generator = TemplateCodeGenerator::default();
        // Verify it works and has the expected default config
        assert_eq!(generator.config.spec_prefix, "L");
        assert_eq!(generator.config.exec_prefix, "C");
    }

    #[test]
    fn test_generate_copy_var_name() {
        let generator = TemplateCodeGenerator::default();
        let ctx = make_ctx();

        let template = QuantifierTemplate::Copy {
            output_var: "result".to_string(),
            input_var: "my_input".to_string(),
        };

        let result = generator.generate(&template, &ctx).unwrap();
        // Should produce Clone(Var("my_input"))
        match &result {
            ExecExpr::Clone(inner) => match inner.as_ref() {
                ExecExpr::Var(name) => assert_eq!(name, "my_input"),
                other => panic!("Expected Var(my_input), got {:?}", other),
            },
            other => panic!("Expected Clone, got {:?}", other),
        }
    }
}
