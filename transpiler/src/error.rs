//! Error types for the Verus transpiler.
//!
//! This module provides span-aware error handling with support for:
//! - Multiple error accumulation (don't stop at first error)
//! - Warning vs error distinction
//! - Source location tracking

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

/// The main error type for transpiler operations.
#[derive(Error, Diagnostic, Debug)]
pub enum TranspileError {
    /// Error during parsing phase
    #[error("Parse error: {message}")]
    #[diagnostic(code(verus_transpiler::parse_error))]
    Parse {
        message: String,
        #[label("here")]
        span: Option<SourceSpan>,
    },

    /// Error during annotation processing
    #[error("Annotation error: {message}")]
    #[diagnostic(code(verus_transpiler::annotation_error))]
    Annotation {
        message: String,
        #[label("here")]
        span: Option<SourceSpan>,
    },

    /// Error during mode analysis
    #[error("Mode analysis error: {message}")]
    #[diagnostic(code(verus_transpiler::mode_error))]
    Mode {
        message: String,
        #[label("here")]
        span: Option<SourceSpan>,
    },

    /// Saturation check failure - output members not fully assigned
    #[error("Saturation error: {message}")]
    #[diagnostic(code(verus_transpiler::saturation_error))]
    Saturation {
        message: String,
        #[label("output parameter")]
        span: Option<SourceSpan>,
        #[help]
        help: Option<String>,
    },

    /// Harmony check failure - double assignment detected
    #[error("Harmony error: {message}")]
    #[diagnostic(code(verus_transpiler::harmony_error))]
    Harmony {
        message: String,
        #[label("first assignment")]
        first_span: Option<SourceSpan>,
        #[label("second assignment")]
        second_span: Option<SourceSpan>,
    },

    /// Obligation check failure - output used before assignment
    #[error("Obligation error: {message}")]
    #[diagnostic(code(verus_transpiler::obligation_error))]
    Obligation {
        message: String,
        #[label("here")]
        span: Option<SourceSpan>,
    },

    /// Error during code generation
    #[error("Code generation error: {message}")]
    #[diagnostic(code(verus_transpiler::codegen_error))]
    CodeGen {
        message: String,
        #[label("here")]
        span: Option<SourceSpan>,
    },

    /// Configuration error
    #[error("Configuration error: {message}")]
    #[diagnostic(code(verus_transpiler::config_error))]
    Config { message: String },

    /// I/O error
    #[error("I/O error: {0}")]
    #[diagnostic(code(verus_transpiler::io_error))]
    Io(#[from] std::io::Error),

    /// Unsupported pattern that cannot be functionalized
    #[error("Unsupported pattern: {message}")]
    #[diagnostic(code(verus_transpiler::unsupported_pattern))]
    UnsupportedPattern {
        message: String,
        #[label("here")]
        span: Option<SourceSpan>,
        #[help]
        help: Option<String>,
    },
}

/// Warning type for non-fatal issues
#[derive(Debug, Clone)]
pub struct TranspileWarning {
    pub message: String,
    pub span: Option<SourceSpan>,
    pub suggestion: Option<String>,
}

impl std::fmt::Display for TranspileWarning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Warning: {}", self.message)?;
        if let Some(suggestion) = &self.suggestion {
            write!(f, " (suggestion: {})", suggestion)?;
        }
        Ok(())
    }
}

/// Result type alias for transpiler operations
pub type TranspileResult<T> = Result<T, TranspileError>;

/// Accumulator for collecting multiple errors and warnings
#[derive(Debug, Default)]
pub struct DiagnosticAccumulator {
    pub errors: Vec<TranspileError>,
    pub warnings: Vec<TranspileWarning>,
}

impl DiagnosticAccumulator {
    /// Create a new empty accumulator
    pub fn new() -> Self {
        Self::default()
    }

    /// Add an error to the accumulator
    pub fn add_error(&mut self, error: TranspileError) {
        self.errors.push(error);
    }

    /// Add a warning to the accumulator
    pub fn add_warning(&mut self, warning: TranspileWarning) {
        self.warnings.push(warning);
    }

    /// Check if any errors have been accumulated
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Check if any warnings have been accumulated
    pub fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }

    /// Get the total number of diagnostics
    pub fn total_count(&self) -> usize {
        self.errors.len() + self.warnings.len()
    }

    /// Consume the accumulator and return errors if any exist
    pub fn into_result<T>(self, value: T) -> TranspileResult<T> {
        if self.has_errors() {
            // Return the first error for now
            // TODO: Consider returning a multi-error type
            Err(self.errors.into_iter().next().unwrap())
        } else {
            Ok(value)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_diagnostic_accumulator() {
        let mut acc = DiagnosticAccumulator::new();
        assert!(!acc.has_errors());
        assert!(!acc.has_warnings());

        acc.add_warning(TranspileWarning {
            message: "test warning".to_string(),
            span: None,
            suggestion: None,
        });
        assert!(!acc.has_errors());
        assert!(acc.has_warnings());

        acc.add_error(TranspileError::Config {
            message: "test error".to_string(),
        });
        assert!(acc.has_errors());
        assert_eq!(acc.total_count(), 2);
    }

    #[test]
    fn test_into_result_with_errors() {
        let mut acc = DiagnosticAccumulator::new();
        acc.add_error(TranspileError::Config {
            message: "test".to_string(),
        });
        let result: TranspileResult<()> = acc.into_result(());
        assert!(result.is_err());
    }

    #[test]
    fn test_into_result_without_errors() {
        let acc = DiagnosticAccumulator::new();
        let result: TranspileResult<i32> = acc.into_result(42);
        assert_eq!(result.unwrap(), 42);
    }
}
