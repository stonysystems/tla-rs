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
#[derive(Debug, Clone)]
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

        // Parse return type for helper functions
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
                return Err(TranspileError::Annotation {
                    message: "Helper function requires return type (-> Type)".to_string(),
                    span: None,
                });
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
        let parser = AnnotationParser::new(String::new());
        let result = parser.parse_function_line("helper MissingReturn(+, +);");
        assert!(result.is_err());
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
}
