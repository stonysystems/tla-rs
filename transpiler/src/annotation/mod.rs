//! Mode annotation handling.
//!
//! This module handles parsing and processing of `.automan` annotation files
//! that specify input/output modes for spec function parameters.
//!
//! Format example:
//! ```text
//! module RSL::Acceptor {
//!     LAcceptorInit(-, +);           // (out, in) - a is output, c is input
//!     LAcceptorProcess1a(+, -, +, -); // (in, out, in, out)
//! }
//! ```

use crate::ast::ParameterMode;
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
    /// Parameter modes in order
    pub param_modes: Vec<ParameterMode>,
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
        // TODO: Implement full parsing
        let _ = &self.source; // Use the field to avoid warning
        Ok(Vec::new())
    }

    /// Parse a single function annotation line
    pub fn parse_function_line(&self, line: &str) -> TranspileResult<FunctionAnnotation> {
        // Simple parser for format: FunctionName(+, -, +);
        let line = line.trim();
        if line.is_empty() || line.starts_with("//") {
            return Err(TranspileError::Annotation {
                message: "Empty or comment line".to_string(),
                span: None,
            });
        }

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

        let mut param_modes = Vec::new();
        for mode_char in modes_str.split(',') {
            let mode_char = mode_char.trim();
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

        Ok(FunctionAnnotation { name, param_modes })
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
        assert_eq!(annotation.param_modes.len(), 4);
        assert_eq!(annotation.param_modes[0], ParameterMode::Input);
        assert_eq!(annotation.param_modes[1], ParameterMode::Output);
        assert_eq!(annotation.param_modes[2], ParameterMode::Input);
        assert_eq!(annotation.param_modes[3], ParameterMode::Output);
    }

    #[test]
    fn test_parse_simple_annotation() {
        let parser = AnnotationParser::new(String::new());
        let result = parser.parse_function_line("NodeInit(-, +);");
        assert!(result.is_ok());

        let annotation = result.unwrap();
        assert_eq!(annotation.name, "NodeInit");
        assert_eq!(annotation.param_modes.len(), 2);
    }
}
