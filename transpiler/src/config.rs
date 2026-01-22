//! Configuration for the Verus transpiler.
//!
//! This module handles loading and parsing configuration files that control
//! transpiler behavior, naming conventions, and type mappings.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::Path;

use crate::error::{TranspileError, TranspileResult};

/// Root configuration structure for the transpiler.
///
/// Example TOML configuration:
/// ```toml
/// [naming]
/// spec_prefix = "L"
/// exec_prefix = "C"
///
/// [remapping]
/// "LAcceptor" = "CAcceptor"
/// "Ballot" = "CBallot"
///
/// [output]
/// generate_abstraction_fns = true
/// generate_validity_predicates = true
/// ```
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct TranspilerConfig {
    /// Naming convention configuration
    #[serde(default)]
    pub naming: NamingConfig,

    /// Type remapping configuration
    #[serde(default)]
    pub remapping: HashMap<String, String>,

    /// Output generation configuration
    #[serde(default)]
    pub output: OutputConfig,

    /// Module-specific configuration
    #[serde(default)]
    pub modules: HashMap<String, ModuleConfig>,
}

impl TranspilerConfig {
    /// Load configuration from a TOML file
    pub fn from_file(path: &Path) -> TranspileResult<Self> {
        let content = std::fs::read_to_string(path)?;
        Self::from_toml(&content)
    }

    /// Parse configuration from a TOML string
    pub fn from_toml(content: &str) -> TranspileResult<Self> {
        toml::from_str(content).map_err(|e| TranspileError::Config {
            message: format!("Failed to parse configuration: {}", e),
        })
    }

    /// Save configuration to a TOML file
    pub fn to_file(&self, path: &Path) -> TranspileResult<()> {
        let content = self.to_toml()?;
        std::fs::write(path, content)?;
        Ok(())
    }

    /// Serialize configuration to TOML string
    pub fn to_toml(&self) -> TranspileResult<String> {
        toml::to_string_pretty(self).map_err(|e| TranspileError::Config {
            message: format!("Failed to serialize configuration: {}", e),
        })
    }

    /// Get the exec type name for a given spec type
    pub fn get_exec_type(&self, spec_type: &str) -> String {
        // First check explicit remapping
        if let Some(exec_type) = self.remapping.get(spec_type) {
            return exec_type.clone();
        }

        // Then try prefix replacement
        if spec_type.starts_with(&self.naming.spec_prefix) {
            let base = &spec_type[self.naming.spec_prefix.len()..];
            return format!("{}{}", self.naming.exec_prefix, base);
        }

        // Default: prepend exec prefix
        format!("{}{}", self.naming.exec_prefix, spec_type)
    }

    /// Get the spec type name for a given exec type
    pub fn get_spec_type(&self, exec_type: &str) -> String {
        // First check reverse remapping
        for (spec, exec) in &self.remapping {
            if exec == exec_type {
                return spec.clone();
            }
        }

        // Then try prefix replacement
        if exec_type.starts_with(&self.naming.exec_prefix) {
            let base = &exec_type[self.naming.exec_prefix.len()..];
            return format!("{}{}", self.naming.spec_prefix, base);
        }

        // Default: prepend spec prefix
        format!("{}{}", self.naming.spec_prefix, exec_type)
    }
}

/// Configuration for naming conventions
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NamingConfig {
    /// Prefix for spec types (e.g., "L" for LAcceptor)
    #[serde(default = "default_spec_prefix")]
    pub spec_prefix: String,

    /// Prefix for exec types (e.g., "C" for CAcceptor)
    #[serde(default = "default_exec_prefix")]
    pub exec_prefix: String,

    /// Suffix for spec functions (optional)
    #[serde(default)]
    pub spec_fn_suffix: String,

    /// Suffix for exec functions (optional)
    #[serde(default)]
    pub exec_fn_suffix: String,
}

fn default_spec_prefix() -> String {
    "L".to_string()
}

fn default_exec_prefix() -> String {
    "C".to_string()
}

impl Default for NamingConfig {
    fn default() -> Self {
        Self {
            spec_prefix: default_spec_prefix(),
            exec_prefix: default_exec_prefix(),
            spec_fn_suffix: String::new(),
            exec_fn_suffix: String::new(),
        }
    }
}

/// Configuration for output generation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OutputConfig {
    /// Whether to generate abstraction functions (View trait impls)
    #[serde(default = "default_true")]
    pub generate_abstraction_fns: bool,

    /// Whether to generate validity predicates (well_formed)
    #[serde(default = "default_true")]
    pub generate_validity_predicates: bool,

    /// Whether to generate Clone implementations
    #[serde(default = "default_true")]
    pub generate_clone: bool,

    /// Whether to include debug comments in generated code
    #[serde(default)]
    pub include_debug_comments: bool,

    /// Output directory for generated files
    #[serde(default)]
    pub output_dir: Option<String>,
}

fn default_true() -> bool {
    true
}

impl Default for OutputConfig {
    fn default() -> Self {
        Self {
            generate_abstraction_fns: true,
            generate_validity_predicates: true,
            generate_clone: true,
            include_debug_comments: false,
            output_dir: None,
        }
    }
}

/// Configuration for a specific module
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ModuleConfig {
    /// Additional type remappings for this module
    #[serde(default)]
    pub remapping: HashMap<String, String>,

    /// Functions to skip during transpilation
    #[serde(default)]
    pub skip_functions: Vec<String>,

    /// Custom includes for the generated module
    #[serde(default)]
    pub custom_includes: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = TranspilerConfig::default();
        assert_eq!(config.naming.spec_prefix, "L");
        assert_eq!(config.naming.exec_prefix, "C");
        assert!(config.output.generate_abstraction_fns);
    }

    #[test]
    fn test_parse_toml() {
        let toml = r#"
            [naming]
            spec_prefix = "L"
            exec_prefix = "C"

            [remapping]
            "LAcceptor" = "CAcceptor"
            "Ballot" = "CBallot"

            [output]
            generate_abstraction_fns = true
            generate_validity_predicates = true
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.naming.spec_prefix, "L");
        assert_eq!(
            config.remapping.get("LAcceptor"),
            Some(&"CAcceptor".to_string())
        );
        assert_eq!(config.remapping.get("Ballot"), Some(&"CBallot".to_string()));
    }

    #[test]
    fn test_get_exec_type_with_remapping() {
        let mut config = TranspilerConfig::default();
        config
            .remapping
            .insert("LAcceptor".to_string(), "CAcceptor".to_string());
        config
            .remapping
            .insert("Ballot".to_string(), "CBallot".to_string());

        assert_eq!(config.get_exec_type("LAcceptor"), "CAcceptor");
        assert_eq!(config.get_exec_type("Ballot"), "CBallot");
    }

    #[test]
    fn test_get_exec_type_with_prefix() {
        let config = TranspilerConfig::default();
        assert_eq!(config.get_exec_type("LProposer"), "CProposer");
        assert_eq!(config.get_exec_type("LLearner"), "CLearner");
    }

    #[test]
    fn test_get_exec_type_without_prefix() {
        let config = TranspilerConfig::default();
        // Types without the spec prefix get the exec prefix prepended
        assert_eq!(config.get_exec_type("EndPoint"), "CEndPoint");
    }

    #[test]
    fn test_roundtrip_toml() {
        let mut config = TranspilerConfig::default();
        config
            .remapping
            .insert("LAcceptor".to_string(), "CAcceptor".to_string());
        config.output.include_debug_comments = true;

        let toml = config.to_toml().unwrap();
        let parsed = TranspilerConfig::from_toml(&toml).unwrap();

        assert_eq!(
            parsed.remapping.get("LAcceptor"),
            Some(&"CAcceptor".to_string())
        );
        assert!(parsed.output.include_debug_comments);
    }

    #[test]
    fn test_module_config() {
        let toml = r#"
            [naming]
            spec_prefix = "L"

            [modules.RSL_Acceptor]
            skip_functions = ["LAcceptorOldFunction"]
            custom_includes = ["use crate::common::*;"]
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        let module = config.modules.get("RSL_Acceptor").unwrap();
        assert_eq!(module.skip_functions, vec!["LAcceptorOldFunction"]);
        assert_eq!(module.custom_includes, vec!["use crate::common::*;"]);
    }
}
