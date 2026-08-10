//! Mode annotation handling.
//!
//! This module handles parsing and processing of `.automan` annotation files
//! that specify input/output modes for spec function parameters.
//!
//! Format example:
//! ```text
//! module RSL::Acceptor {
//!     LAcceptorInit(-, +);           // Predicate: first param is output
//!     LAcceptorProcess1a(+, -, +, -); // Predicate: in, out, in, out
//!     helper ComputeSuccessorView(+, +) -> Ballot; // Helper function
//! }
//! ```

use crate::ast::{FunctionKind, ParameterMode};
use crate::error::{TranspileError, TranspileResult};
use std::collections::HashMap;

/// Parsed mode annotations for a module
#[derive(Debug, Clone, Default)]
pub struct ModuleAnnotations {
    /// Module path (e.g., "RSL::Acceptor")
    pub module_path: String,
    /// Function annotations indexed by function name
    pub functions: HashMap<String, FunctionAnnotation>,
}

/// Mode annotations for a single function
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionAnnotation {
    /// Function name
    pub name: String,
    /// Function kind (predicate or helper)
    pub kind: FunctionKind,
    /// Parameter modes in order
    pub param_modes: Vec<ParameterMode>,
    /// Return type for helper functions (e.g., "Ballot", "Seq<Request>")
    pub return_type: Option<String>,
}

/// Parser for .automan annotation files
pub struct AnnotationParser {
    /// Source content
    source: String,
    /// File path for error reporting
    file_path: Option<String>,
}

impl AnnotationParser {
    /// Create a new annotation parser
    pub fn new(source: String) -> Self {
        Self {
            source,
            file_path: None,
        }
    }

    /// Set the file path for error reporting
    pub fn with_file_path(mut self, path: String) -> Self {
        self.file_path = Some(path);
        self
    }

    /// Parse all module annotations from the source
    pub fn parse(&self) -> TranspileResult<Vec<ModuleAnnotations>> {
        let mut modules = Vec::new();
        let mut current_module: Option<ModuleAnnotations> = None;
        let mut brace_depth = 0;

        for line in self.source.lines() {
            let line = line.trim();

            // Skip empty lines and comments
            if line.is_empty() || line.starts_with("//") {
                continue;
            }

            // Handle module declaration
            if line.starts_with("module ") {
                // Save previous module if any
                if let Some(module) = current_module.take() {
                    modules.push(module);
                }

                // Parse module path
                let rest = line.strip_prefix("module ").unwrap().trim();
                let module_path = if let Some(brace_pos) = rest.find('{') {
                    rest[..brace_pos].trim().to_string()
                } else {
                    rest.trim_end_matches('{').trim().to_string()
                };

                current_module = Some(ModuleAnnotations {
                    module_path,
                    functions: HashMap::new(),
                });

                if line.contains('{') {
                    brace_depth += 1;
                }
                continue;
            }

            // Handle opening brace (standalone)
            if line == "{" {
                brace_depth += 1;
                continue;
            }

            // Handle closing brace
            if line == "}" || line.ends_with('}') {
                brace_depth -= 1;
                if brace_depth == 0 {
                    // Module ended
                    if let Some(module) = current_module.take() {
                        modules.push(module);
                    }
                }
                continue;
            }

            // Parse function annotation if we're inside a module
            if let Some(ref mut module) = current_module {
                // Try to parse as function annotation
                if let Ok(func) = self.parse_function_line(line) {
                    module.functions.insert(func.name.clone(), func);
                }
                // Silently skip lines that don't parse (could be other syntax)
            }
        }

        // Handle unclosed module (shouldn't happen in valid files)
        if let Some(module) = current_module {
            modules.push(module);
        }

        Ok(modules)
    }

    /// Parse a single function annotation line
    ///
    /// Formats supported:
    /// - Predicate: `FunctionName(+, -, +);`
    /// - Helper: `helper FunctionName(+, +) -> ReturnType;`
    pub fn parse_function_line(&self, line: &str) -> TranspileResult<FunctionAnnotation> {
        let line = line.trim();
        if line.is_empty() || line.starts_with("//") {
            return Err(TranspileError::Annotation {
                message: "Empty or comment line".to_string(),
                span: None,
            });
        }

        // Check for helper function prefix
        let (kind, line) = if line.starts_with("helper ") {
            (
                FunctionKind::Helper,
                line.strip_prefix("helper ").unwrap().trim(),
            )
        } else {
            (FunctionKind::Predicate, line)
        };

        // Find function name and modes
        let paren_start = line.find('(').ok_or_else(|| TranspileError::Annotation {
            message: "Missing opening parenthesis".to_string(),
            span: None,
        })?;

        let paren_end = line.find(')').ok_or_else(|| TranspileError::Annotation {
            message: "Missing closing parenthesis".to_string(),
            span: None,
        })?;

        let name = line[..paren_start].trim().to_string();
        let modes_str = &line[paren_start + 1..paren_end];

        // Parse parameter modes
        let mut param_modes = Vec::new();
        for mode_char in modes_str.split(',') {
            let mode_char = mode_char.trim();
            if mode_char.is_empty() {
                continue; // Skip empty entries (e.g., trailing comma)
            }
            match mode_char {
                "+" => param_modes.push(ParameterMode::Input),
                "-" => param_modes.push(ParameterMode::Output),
                _ => {
                    return Err(TranspileError::Annotation {
                        message: format!("Invalid mode character: {}", mode_char),
                        span: None,
                    });
                }
            }
        }

        // Parse return type for helper functions (optional — falls back to spec fn return type)
        let return_type = if kind == FunctionKind::Helper {
            let after_paren = &line[paren_end + 1..];
            if let Some(arrow_pos) = after_paren.find("->") {
                let type_str = after_paren[arrow_pos + 2..]
                    .trim()
                    .trim_end_matches(';')
                    .trim();
                if type_str.is_empty() {
                    return Err(TranspileError::Annotation {
                        message: "Helper function missing return type after ->".to_string(),
                        span: None,
                    });
                }
                Some(type_str.to_string())
            } else {
                // No explicit return type — will fall back to spec function's return type
                None
            }
        } else {
            None
        };

        Ok(FunctionAnnotation {
            name,
            kind,
            param_modes,
            return_type,
        })
    }
}

/// Parse annotations from a file
pub fn parse_annotation_file(path: &std::path::Path) -> TranspileResult<Vec<ModuleAnnotations>> {
    let source = std::fs::read_to_string(path)?;
    let parser = AnnotationParser::new(source).with_file_path(path.display().to_string());
    parser.parse()
}

/// Parse the body of an inline `// @automan ...` directive (Phase 55.1).
///
/// `directive` is the text after the `@automan` marker; multi-line directives
/// arrive here already joined into one line. `param_names` is the parameter
/// list of the `spec fn` the directive precedes, in declaration order —
/// named bindings are resolved against it, which is what makes a parameter
/// rename or a same-typed reorder an error instead of a silent meaning change.
///
/// Grammar:
/// ```text
/// directive  := ("predicate" | "helper") "(" bindings? ")" ["->" Type] [";"]
/// bindings   := named | positional
/// named      := name ":" ("in" | "out" | "+" | "-") ("," ...)* [","]
/// positional := ("+" | "-") ("," ("+" | "-"))* [","]        // migration form
/// ```
///
/// The named form is canonical. The positional form exists so a mechanical
/// sidecar migration can land in one step; it deliberately accepts only the
/// sidecar's `+`/`-` spellings — writing `in`/`out` positionally is rejected
/// because those spellings are reserved for the checked, named form.
pub fn parse_inline_directive(
    directive: &str,
    fn_name: &str,
    param_names: &[String],
    location: &str,
) -> TranspileResult<FunctionAnnotation> {
    let err = |message: String| TranspileError::Annotation {
        message,
        span: None,
    };

    let text = directive.trim().trim_end_matches(';').trim_end();

    let (kind, rest) = if let Some(r) = text.strip_prefix("predicate") {
        (FunctionKind::Predicate, r)
    } else if let Some(r) = text.strip_prefix("helper") {
        (FunctionKind::Helper, r)
    } else {
        return Err(err(format!(
            "{location}: @automan directive on `{fn_name}` must start with \
             `predicate` or `helper`, got `{text}`"
        )));
    };

    let rest = rest.trim_start();
    let Some(open) = rest.strip_prefix('(') else {
        return Err(err(format!(
            "{location}: @automan directive on `{fn_name}` expects `(` after the kind"
        )));
    };

    // Matching close paren. Binding lists never nest, but scanning by depth
    // costs nothing and keeps a stray `(` from silently truncating the list.
    let mut depth = 1usize;
    let mut close = None;
    for (i, c) in open.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    close = Some(i);
                    break;
                }
            }
            _ => {}
        }
    }
    let Some(close) = close else {
        return Err(err(format!(
            "{location}: @automan directive on `{fn_name}` has unbalanced parentheses"
        )));
    };
    let bindings = &open[..close];
    let after = open[close + 1..].trim();

    let return_type = if let Some(r) = after.strip_prefix("->") {
        let ty = r.trim();
        if ty.is_empty() {
            return Err(err(format!(
                "{location}: @automan directive on `{fn_name}` is missing a return type after `->`"
            )));
        }
        if kind == FunctionKind::Predicate {
            return Err(err(format!(
                "{location}: predicate directive on `{fn_name}` cannot carry a `-> Type` \
                 override; that is a helper-only feature"
            )));
        }
        Some(ty.to_string())
    } else if after.is_empty() {
        None
    } else {
        return Err(err(format!(
            "{location}: unexpected trailing text `{after}` in @automan directive on `{fn_name}`"
        )));
    };

    let entries: Vec<&str> = bindings
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect();

    let named_count = entries.iter().filter(|e| e.contains(':')).count();
    if named_count > 0 && named_count < entries.len() {
        return Err(err(format!(
            "{location}: @automan directive on `{fn_name}` mixes named and positional \
             bindings; use one form for the whole list"
        )));
    }

    let param_modes = if named_count > 0 {
        let mut by_name: HashMap<&str, ParameterMode> = HashMap::new();
        for entry in &entries {
            let (name, mode_word) = entry.split_once(':').expect("checked above");
            let name = name.trim();
            let mode = match mode_word.trim() {
                "in" | "+" => ParameterMode::Input,
                "out" | "-" => ParameterMode::Output,
                other => {
                    return Err(err(format!(
                        "{location}: invalid mode `{other}` for `{name}` in @automan \
                         directive on `{fn_name}`; expected `in`, `out`, `+`, or `-`"
                    )));
                }
            };
            if by_name.insert(name, mode).is_some() {
                return Err(err(format!(
                    "{location}: parameter `{name}` appears twice in @automan directive \
                     on `{fn_name}`"
                )));
            }
        }

        let unknown: Vec<&str> = by_name
            .keys()
            .filter(|n| !param_names.iter().any(|p| p == *n))
            .copied()
            .collect();
        if !unknown.is_empty() {
            let mut unknown = unknown;
            unknown.sort_unstable();
            return Err(err(format!(
                "{location}: @automan directive on `{fn_name}` names unknown parameter(s) \
                 {unknown:?}; the function declares {param_names:?}"
            )));
        }

        let missing: Vec<&String> = param_names
            .iter()
            .filter(|p| !by_name.contains_key(p.as_str()))
            .collect();
        if !missing.is_empty() {
            return Err(err(format!(
                "{location}: @automan directive on `{fn_name}` is missing mode(s) for \
                 {missing:?}; every parameter must be bound"
            )));
        }

        param_names
            .iter()
            .map(|p| by_name[p.as_str()])
            .collect::<Vec<_>>()
    } else {
        let mut modes = Vec::with_capacity(entries.len());
        for entry in &entries {
            match *entry {
                "+" => modes.push(ParameterMode::Input),
                "-" => modes.push(ParameterMode::Output),
                "in" | "out" => {
                    return Err(err(format!(
                        "{location}: positional @automan bindings accept only `+`/`-`; \
                         spell `{entry}` as `name: {entry}` instead (directive on `{fn_name}`)"
                    )));
                }
                other => {
                    return Err(err(format!(
                        "{location}: invalid positional mode `{other}` in @automan \
                         directive on `{fn_name}`; expected `+` or `-`"
                    )));
                }
            }
        }
        if modes.len() != param_names.len() {
            return Err(err(format!(
                "{location}: @automan directive on `{fn_name}` has {} mode(s) but the \
                 function declares {} parameter(s) {param_names:?}",
                modes.len(),
                param_names.len()
            )));
        }
        modes
    };

    match kind {
        FunctionKind::Predicate => {
            if !param_modes.contains(&ParameterMode::Output) {
                return Err(err(format!(
                    "{location}: predicate `{fn_name}` needs at least one `out` parameter"
                )));
            }
        }
        FunctionKind::Helper => {
            if let Some(pos) = param_modes.iter().position(|m| *m == ParameterMode::Output) {
                return Err(err(format!(
                    "{location}: helper parameters are always inputs, but `{}` is marked \
                     `out` in the directive on `{fn_name}`",
                    param_names
                        .get(pos)
                        .map(String::as_str)
                        .unwrap_or("<unknown>")
                )));
            }
        }
    }

    Ok(FunctionAnnotation {
        name: fn_name.to_string(),
        kind,
        param_modes,
        return_type,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_function_line() {
        let parser = AnnotationParser::new(String::new());
        let result = parser.parse_function_line("LAcceptorProcess1a(+, -, +, -);");
        assert!(result.is_ok());

        let annotation = result.unwrap();
        assert_eq!(annotation.name, "LAcceptorProcess1a");
        assert_eq!(annotation.kind, FunctionKind::Predicate);
        assert_eq!(annotation.param_modes.len(), 4);
        assert_eq!(annotation.param_modes[0], ParameterMode::Input);
        assert_eq!(annotation.param_modes[1], ParameterMode::Output);
        assert_eq!(annotation.param_modes[2], ParameterMode::Input);
        assert_eq!(annotation.param_modes[3], ParameterMode::Output);
        assert!(annotation.return_type.is_none());
    }

    #[test]
    fn test_parse_simple_annotation() {
        let parser = AnnotationParser::new(String::new());
        let result = parser.parse_function_line("NodeInit(-, +);");
        assert!(result.is_ok());

        let annotation = result.unwrap();
        assert_eq!(annotation.name, "NodeInit");
        assert_eq!(annotation.kind, FunctionKind::Predicate);
        assert_eq!(annotation.param_modes.len(), 2);
        assert!(annotation.return_type.is_none());
    }

    #[test]
    fn test_parse_helper_function() {
        let parser = AnnotationParser::new(String::new());
        let result = parser.parse_function_line("helper ComputeSuccessorView(+, +) -> Ballot;");
        assert!(result.is_ok());

        let annotation = result.unwrap();
        assert_eq!(annotation.name, "ComputeSuccessorView");
        assert_eq!(annotation.kind, FunctionKind::Helper);
        assert_eq!(annotation.param_modes.len(), 2);
        assert_eq!(annotation.param_modes[0], ParameterMode::Input);
        assert_eq!(annotation.param_modes[1], ParameterMode::Input);
        assert_eq!(annotation.return_type, Some("Ballot".to_string()));
    }

    #[test]
    fn test_parse_helper_with_generic_return() {
        let parser = AnnotationParser::new(String::new());
        let result =
            parser.parse_function_line("helper BoundRequestSequence(+, +) -> Seq<Request>;");
        assert!(result.is_ok());

        let annotation = result.unwrap();
        assert_eq!(annotation.name, "BoundRequestSequence");
        assert_eq!(annotation.kind, FunctionKind::Helper);
        assert_eq!(annotation.return_type, Some("Seq<Request>".to_string()));
    }

    #[test]
    fn test_parse_helper_bool_return() {
        let parser = AnnotationParser::new(String::new());
        let result = parser.parse_function_line("helper RequestsMatch(+, +) -> bool;");
        assert!(result.is_ok());

        let annotation = result.unwrap();
        assert_eq!(annotation.name, "RequestsMatch");
        assert_eq!(annotation.kind, FunctionKind::Helper);
        assert_eq!(annotation.return_type, Some("bool".to_string()));
    }

    #[test]
    fn test_parse_helper_missing_return_type() {
        // Return type is optional — falls back to spec function's return type
        let parser = AnnotationParser::new(String::new());
        let result = parser.parse_function_line("helper MissingReturn(+, +);");
        assert!(result.is_ok());
        let annotation = result.unwrap();
        assert_eq!(annotation.name, "MissingReturn");
        assert_eq!(annotation.kind, FunctionKind::Helper);
        assert_eq!(annotation.return_type, None);
    }

    #[test]
    fn test_parse_helper_empty_return_type() {
        let parser = AnnotationParser::new(String::new());
        let result = parser.parse_function_line("helper EmptyReturn(+, +) -> ;");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_module() {
        let source = r#"
            module RSL::Acceptor {
                LAcceptorInit(-, +);
                LAcceptorProcess1a(+, -, +, -);
            }
        "#;

        let parser = AnnotationParser::new(source.to_string());
        let result = parser.parse();
        assert!(result.is_ok());

        let modules = result.unwrap();
        assert_eq!(modules.len(), 1);

        let module = &modules[0];
        assert_eq!(module.module_path, "RSL::Acceptor");
        assert_eq!(module.functions.len(), 2);
        assert!(module.functions.contains_key("LAcceptorInit"));
        assert!(module.functions.contains_key("LAcceptorProcess1a"));

        let init = module.functions.get("LAcceptorInit").unwrap();
        assert_eq!(init.param_modes.len(), 2);
        assert_eq!(init.param_modes[0], ParameterMode::Output);
        assert_eq!(init.param_modes[1], ParameterMode::Input);
    }

    #[test]
    fn test_parse_multiple_modules() {
        let source = r#"
            // Acceptor module annotations
            module RSL::Acceptor {
                LAcceptorInit(-, +);
            }

            // Proposer module annotations
            module RSL::Proposer {
                LProposerInit(-, +);
                LProposerProcess1b(+, -, +, +, -);
            }
        "#;

        let parser = AnnotationParser::new(source.to_string());
        let modules = parser.parse().unwrap();
        assert_eq!(modules.len(), 2);

        assert_eq!(modules[0].module_path, "RSL::Acceptor");
        assert_eq!(modules[1].module_path, "RSL::Proposer");

        let proposer = &modules[1];
        assert!(proposer.functions.contains_key("LProposerProcess1b"));
        let process1b = proposer.functions.get("LProposerProcess1b").unwrap();
        assert_eq!(process1b.param_modes.len(), 5);
    }

    #[test]
    fn test_parse_with_comments() {
        let source = r#"
            // This is a comment at the top
            module RSL::Acceptor {
                // Init function
                LAcceptorInit(-, +);
                // Process 1a - handles 1a messages
                LAcceptorProcess1a(+, -, +, -);
            }
        "#;

        let parser = AnnotationParser::new(source.to_string());
        let modules = parser.parse().unwrap();
        assert_eq!(modules.len(), 1);
        assert_eq!(modules[0].functions.len(), 2);
    }

    #[test]
    fn test_parse_empty_module() {
        let source = r#"
            module Empty::Module {
            }
        "#;

        let parser = AnnotationParser::new(source.to_string());
        let modules = parser.parse().unwrap();
        assert_eq!(modules.len(), 1);
        assert_eq!(modules[0].module_path, "Empty::Module");
        assert!(modules[0].functions.is_empty());
    }

    #[test]
    fn test_parse_mixed_predicates_and_helpers() {
        let source = r#"
            module RSL::Election {
                // Predicates
                ElectionStateInit(-, +);
                ElectionStateProcessHeartbeat(+, -, +, +);

                // Helper functions
                helper ComputeSuccessorView(+, +) -> Ballot;
                helper BoundRequestSequence(+, +) -> Seq<Request>;
                helper RequestsMatch(+, +) -> bool;
            }
        "#;

        let parser = AnnotationParser::new(source.to_string());
        let modules = parser.parse().unwrap();
        assert_eq!(modules.len(), 1);

        let module = &modules[0];
        assert_eq!(module.module_path, "RSL::Election");
        assert_eq!(module.functions.len(), 5);

        // Check predicates
        let init = module.functions.get("ElectionStateInit").unwrap();
        assert_eq!(init.kind, FunctionKind::Predicate);
        assert!(init.return_type.is_none());

        let heartbeat = module
            .functions
            .get("ElectionStateProcessHeartbeat")
            .unwrap();
        assert_eq!(heartbeat.kind, FunctionKind::Predicate);
        assert_eq!(heartbeat.param_modes.len(), 4);

        // Check helpers
        let compute = module.functions.get("ComputeSuccessorView").unwrap();
        assert_eq!(compute.kind, FunctionKind::Helper);
        assert_eq!(compute.return_type, Some("Ballot".to_string()));

        let bound = module.functions.get("BoundRequestSequence").unwrap();
        assert_eq!(bound.kind, FunctionKind::Helper);
        assert_eq!(bound.return_type, Some("Seq<Request>".to_string()));

        let matches = module.functions.get("RequestsMatch").unwrap();
        assert_eq!(matches.kind, FunctionKind::Helper);
        assert_eq!(matches.return_type, Some("bool".to_string()));
    }

    // ---- Phase 55.1: inline directive grammar ----

    fn names(list: &[&str]) -> Vec<String> {
        list.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn inline_named_predicate() {
        let ann = parse_inline_directive(
            " predicate(s: out, c: in)",
            "LInit",
            &names(&["s", "c"]),
            "line 1",
        )
        .unwrap();
        assert_eq!(ann.name, "LInit");
        assert_eq!(ann.kind, FunctionKind::Predicate);
        assert_eq!(
            ann.param_modes,
            vec![ParameterMode::Output, ParameterMode::Input]
        );
        assert_eq!(ann.return_type, None);
    }

    #[test]
    fn inline_named_order_follows_declaration_not_directive() {
        // Directive lists c before s; modes must still come out in (s, c) order.
        let ann = parse_inline_directive(
            " predicate(c: in, s: out)",
            "LInit",
            &names(&["s", "c"]),
            "line 1",
        )
        .unwrap();
        assert_eq!(
            ann.param_modes,
            vec![ParameterMode::Output, ParameterMode::Input]
        );
    }

    #[test]
    fn inline_helper_with_return_type() {
        let ann = parse_inline_directive(
            " helper(s: in, requests: in, limit: in) -> Seq<CPacket>",
            "packets_for_requests",
            &names(&["s", "requests", "limit"]),
            "line 1",
        )
        .unwrap();
        assert_eq!(ann.kind, FunctionKind::Helper);
        assert_eq!(ann.return_type, Some("Seq<CPacket>".to_string()));
        assert!(ann.param_modes.iter().all(|m| *m == ParameterMode::Input));
    }

    #[test]
    fn inline_helper_return_type_optional() {
        let ann = parse_inline_directive(" helper(x: in)", "f", &names(&["x"]), "line 1").unwrap();
        assert_eq!(ann.return_type, None);
    }

    #[test]
    fn inline_positional_migration_form() {
        let ann =
            parse_inline_directive(" predicate(-, +)", "LInit", &names(&["s", "c"]), "line 1")
                .unwrap();
        assert_eq!(
            ann.param_modes,
            vec![ParameterMode::Output, ParameterMode::Input]
        );
    }

    #[test]
    fn inline_named_accepts_plus_minus_spellings() {
        let ann = parse_inline_directive(
            " predicate(s: -, c: +)",
            "LInit",
            &names(&["s", "c"]),
            "line 1",
        )
        .unwrap();
        assert_eq!(
            ann.param_modes,
            vec![ParameterMode::Output, ParameterMode::Input]
        );
    }

    #[test]
    fn inline_trailing_semicolon_tolerated() {
        assert!(
            parse_inline_directive(" predicate(s: out);", "F", &names(&["s"]), "line 1").is_ok()
        );
    }

    #[test]
    fn inline_matches_sidecar_output() {
        // The named inline form and the sidecar line must produce identical
        // FunctionAnnotation values — this is the 55.1 equivalence contract.
        let sidecar = AnnotationParser::new(String::new())
            .parse_function_line("LInit(-, +);")
            .unwrap();
        let inline = parse_inline_directive(
            " predicate(s: out, c: in)",
            "LInit",
            &names(&["s", "c"]),
            "line 1",
        )
        .unwrap();
        assert_eq!(sidecar, inline);

        let sidecar_helper = AnnotationParser::new(String::new())
            .parse_function_line("helper BuildLBroadcast(+, +, +) -> Seq<CPacket>;")
            .unwrap();
        let inline_helper = parse_inline_directive(
            " helper(a: in, b: in, c: in) -> Seq<CPacket>",
            "BuildLBroadcast",
            &names(&["a", "b", "c"]),
            "line 1",
        )
        .unwrap();
        assert_eq!(sidecar_helper, inline_helper);
    }

    fn expect_err(directive: &str, params: &[&str], needle: &str) {
        let result = parse_inline_directive(directive, "F", &names(params), "line 7");
        let msg = match result {
            Err(TranspileError::Annotation { message, .. }) => message,
            other => panic!("expected Annotation error containing {needle:?}, got {other:?}"),
        };
        assert!(
            msg.contains(needle) && msg.contains("line 7"),
            "message {msg:?} should contain {needle:?} and the location"
        );
    }

    #[test]
    fn inline_rejects_unknown_name() {
        expect_err(
            " predicate(s: out, cfg: in)",
            &["s", "c"],
            "unknown parameter",
        );
    }

    #[test]
    fn inline_rejects_missing_name() {
        expect_err(" predicate(s: out)", &["s", "c"], "missing mode");
    }

    #[test]
    fn inline_rejects_duplicate_name() {
        expect_err(" predicate(s: out, s: in)", &["s", "c"], "appears twice");
    }

    #[test]
    fn inline_rejects_positional_arity_mismatch() {
        expect_err(" predicate(-, +, +)", &["s", "c"], "2 parameter(s)");
    }

    #[test]
    fn inline_rejects_predicate_without_output() {
        expect_err(
            " predicate(s: in, c: in)",
            &["s", "c"],
            "at least one `out`",
        );
    }

    #[test]
    fn inline_rejects_helper_with_output() {
        expect_err(" helper(s: out)", &["s"], "always inputs");
    }

    #[test]
    fn inline_rejects_positional_in_out_words() {
        expect_err(" predicate(out, in)", &["s", "c"], "only `+`/`-`");
    }

    #[test]
    fn inline_rejects_mixed_forms() {
        expect_err(
            " predicate(s: out, +)",
            &["s", "c"],
            "mixes named and positional",
        );
    }

    #[test]
    fn inline_rejects_bad_kind() {
        expect_err(" function(s: out)", &["s"], "must start with");
    }

    #[test]
    fn inline_rejects_predicate_return_type() {
        expect_err(" predicate(s: out) -> bool", &["s"], "helper-only");
    }

    #[test]
    fn inline_rejects_trailing_junk() {
        expect_err(" predicate(s: out) whatever", &["s"], "unexpected trailing");
    }

    #[test]
    fn inline_rejects_bad_mode_word() {
        expect_err(" predicate(s: inout)", &["s"], "invalid mode");
    }

    #[test]
    fn inline_rejects_unbalanced_parens() {
        expect_err(" predicate(s: out", &["s"], "unbalanced");
    }
}
