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

    /// Function path mapping for cross-module calls
    /// Maps spec function names to their qualified exec paths
    /// e.g., "BroadcastToEveryone" -> "crate::generated::RSL::broadcast_gen::CBroadcastToEveryone"
    #[serde(default)]
    pub function_paths: HashMap<String, String>,

    /// Spec-only functions that should NOT have C-prefix added
    /// These are functions that only exist in the spec layer and have no exec implementation
    /// The transpiler will use their names as-is without adding C-prefix
    /// e.g., ["WellFormedLConfiguration", "LtUpperBound", "LeqUpperBound"]
    #[serde(default)]
    pub spec_only_functions: Vec<String>,

    /// Method call mappings for spec functions that should become method calls in exec code.
    /// Maps spec function name to method call configuration.
    /// The value is a struct with method_name and receiver_arg_index (0-based).
    /// Example: "LMinQuorumSize" -> { method_name = "CMinQuorumSize", receiver_arg_index = 0 }
    /// This transforms `LMinQuorumSize(config)` to `config.CMinQuorumSize()`
    #[serde(default)]
    pub method_calls: HashMap<String, MethodCallConfig>,

    /// Primitive types that should NOT have valid() predicates generated.
    /// These are types that don't have a valid() method (e.g., type aliases to u64, HashMap).
    /// Both the spec type name and the remapped exec type name can be listed.
    /// e.g., ["COperationNumber", "CVotes", "ClearnerState"]
    #[serde(default)]
    pub primitive_types: Vec<String>,

    /// Functions to skip during transpilation (require manual implementation).
    /// These are functions that have patterns too complex for automatic transpilation,
    /// such as dispatch functions that match on I/O sequence enum variants.
    /// e.g., ["LReplicaNextProcessPacket", "LReplicaNextReadClockAndProcessPacket"]
    #[serde(default)]
    pub skip_functions: Vec<String>,

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

    /// Check if a type should be treated as primitive (no valid() predicate).
    /// This checks both spec type names and remapped exec type names.
    pub fn is_primitive_type(&self, type_name: &str) -> bool {
        // Check if directly in primitive_types list
        if self.primitive_types.contains(&type_name.to_string()) {
            return true;
        }

        // Check if the remapped exec type is in primitive_types
        let exec_type = self.get_exec_type(type_name);
        if self.primitive_types.contains(&exec_type) {
            return true;
        }

        false
    }

    /// Check if a function should be skipped during transpilation.
    /// This is used for functions that require manual implementation due to
    /// complex patterns that cannot be automatically transpiled.
    pub fn should_skip_function(&self, func_name: &str) -> bool {
        self.skip_functions.contains(&func_name.to_string())
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

    /// Name of the validity predicate (default: "well_formed", RSL uses "valid")
    #[serde(default = "default_validity_predicate_name")]
    pub validity_predicate_name: String,

    /// Whether to generate Clone implementations
    #[serde(default = "default_true")]
    pub generate_clone: bool,

    /// Whether to include debug comments in generated code
    #[serde(default)]
    pub include_debug_comments: bool,

    /// Output directory for generated files
    #[serde(default)]
    pub output_dir: Option<String>,

    /// Custom imports to include before verus! block
    #[serde(default)]
    pub custom_imports: Vec<String>,

    /// Whether to generate explicit for loops instead of iterator chains.
    /// When true, generates Verus-verifiable loop code with placeholders for invariants.
    /// When false (default), generates iterator-based code (.iter().filter().collect()).
    #[serde(default)]
    pub generate_loops_for_verification: bool,

    /// Whether to generate type definitions inline from the spec file.
    /// When true, parses struct/enum definitions from the spec file and generates
    /// corresponding exec types with View trait implementations.
    /// This makes the output self-contained without depending on manual implementation code.
    #[serde(default)]
    pub generate_inline_types: bool,

    /// Whether to generate wrapper methods in an impl block for &mut self pattern.
    /// When true, generates wrapper methods that call the functional-style generated
    /// functions and update `*self` with the result.
    #[serde(default)]
    pub generate_wrapper_methods: bool,

    /// The type name for the impl block when generating wrapper methods.
    /// Required when `generate_wrapper_methods` is true.
    /// Example: "CElectionState"
    #[serde(default)]
    pub wrapper_impl_type: Option<String>,
}

fn default_validity_predicate_name() -> String {
    "well_formed".to_string()
}

fn default_true() -> bool {
    true
}

impl Default for OutputConfig {
    fn default() -> Self {
        Self {
            generate_abstraction_fns: true,
            generate_validity_predicates: true,
            validity_predicate_name: "well_formed".to_string(),
            generate_clone: true,
            include_debug_comments: false,
            output_dir: None,
            custom_imports: Vec::new(),
            generate_loops_for_verification: false,
            generate_inline_types: false,
            generate_wrapper_methods: false,
            wrapper_impl_type: None,
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

/// Configuration for transforming a spec function call into a method call.
/// Used when a spec function like `LMinQuorumSize(config)` should become
/// a method call like `config.CMinQuorumSize()` in exec code.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MethodCallConfig {
    /// The exec method name to call (e.g., "CMinQuorumSize")
    pub method_name: String,
    /// The 0-based index of the argument that becomes the receiver (e.g., 0 for first arg)
    #[serde(default)]
    pub receiver_arg_index: usize,
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

    #[test]
    fn test_custom_imports_in_output() {
        let toml = r#"
            [output]
            validity_predicate_name = "valid"
            custom_imports = [
                "use vstd::prelude::*;",
                "use std::collections::HashMap;",
            ]
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.output.validity_predicate_name, "valid");
        assert_eq!(config.output.custom_imports.len(), 2);
        assert_eq!(config.output.custom_imports[0], "use vstd::prelude::*;");
        assert_eq!(
            config.output.custom_imports[1],
            "use std::collections::HashMap;"
        );
    }

    #[test]
    fn test_method_calls_config() {
        let toml = r#"
            [method_calls]
            "LMinQuorumSize" = { method_name = "CMinQuorumSize", receiver_arg_index = 0 }
            "GetReplicaIndex" = { method_name = "CGetReplicaIndex", receiver_arg_index = 1 }
            "LReplicaConstantsValid" = { method_name = "CReplicaConstantsValid", receiver_arg_index = 0 }
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.method_calls.len(), 3);

        let min_quorum = config.method_calls.get("LMinQuorumSize").unwrap();
        assert_eq!(min_quorum.method_name, "CMinQuorumSize");
        assert_eq!(min_quorum.receiver_arg_index, 0);

        let get_replica = config.method_calls.get("GetReplicaIndex").unwrap();
        assert_eq!(get_replica.method_name, "CGetReplicaIndex");
        assert_eq!(get_replica.receiver_arg_index, 1);

        let valid = config.method_calls.get("LReplicaConstantsValid").unwrap();
        assert_eq!(valid.method_name, "CReplicaConstantsValid");
        assert_eq!(valid.receiver_arg_index, 0);
    }
}
