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

    /// Primitive types that should NOT have valid() predicates generated
    /// AND should use `*param as int` in ensures spec arguments.
    /// These are types that map to integer primitives (e.g., type aliases to u64).
    /// e.g., ["OperationNumber"]
    #[serde(default)]
    pub primitive_types: Vec<String>,

    /// Types that should skip valid() predicates but use `param@` in ensures
    /// (not `*param as int`). Used for collection type aliases like Votes (= Map<int, Vote>)
    /// that don't have valid() but DO have a View trait.
    /// e.g., ["Votes", "CVotes"]
    #[serde(default)]
    pub skip_valid_types: Vec<String>,

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

    /// Per-field custom View expressions for type generation.
    /// Key format: "TypeName.field_name" (spec type name, e.g., "LAcceptor.votes")
    /// Value: custom view expression (e.g., "abstractify_cvotes(&self.votes)")
    /// Used when a field needs deep conversion instead of simple `@` or `as int`.
    #[serde(default)]
    pub view_overrides: HashMap<String, String>,

    /// Extra fields to add to generated exec types that don't exist in the spec.
    /// These are optimization/bookkeeping fields with default values.
    /// Key format: "TypeName.field_name" (exec type name, e.g., "CAcceptor.min_vote_opn")
    /// Value: "type = default_value" (e.g., "u64 = 0")
    #[serde(default)]
    pub extra_fields: HashMap<String, String>,

    /// Clone strategy per exec type.
    /// Determines how #[derive(Clone)] or manual Clone impl is generated.
    /// Values: "derive" (default), "external_body" (for types containing HashSet)
    /// Key: exec type name (e.g., "CElectionState")
    #[serde(default)]
    pub clone_strategy: HashMap<String, String>,

    /// Types to skip during generation (already manually implemented).
    /// These spec type names will be parsed but NOT generated as exec types.
    /// e.g., ["Ballot", "Request", "Reply", "Vote", "LearnerTuple"]
    #[serde(default)]
    pub skip_types: Vec<String>,

    /// Re-export statements to include at the top of the generated file.
    /// Each entry is a full `use` path (without the `use` keyword or semicolon).
    /// e.g., ["crate::implementation::RSL::types_i::*"]
    #[serde(default)]
    pub re_exports: Vec<String>,

    /// Custom derives per exec type.
    /// These are ADDITIONAL derives beyond what clone_strategy provides.
    /// Key: exec type name (e.g., "CBallot")
    /// Value: list of derive names (e.g., ["Copy", "Eq", "PartialEq", "Hash"])
    #[serde(default)]
    pub custom_derives: HashMap<String, Vec<String>>,

    /// Fields to skip during generation for specific exec types.
    /// These fields exist in the spec type but should NOT be generated in the exec type.
    /// Key: exec type name (e.g., "CConfiguration")
    /// Value: list of field names to skip (e.g., ["clientIds"])
    #[serde(default)]
    pub skip_fields: HashMap<String, Vec<String>>,

    /// Enum variant remapping for struct field initialization.
    /// Maps bare spec variant names to their fully-qualified exec enum paths.
    /// Used when spec has `s_.field is Variant` and exec needs `EnumType::Variant`.
    /// e.g., "Init" -> "CTMState::Init", "Committed" -> "CTMState::Committed"
    #[serde(default)]
    pub variant_remapping: HashMap<String, String>,

    /// Fields that are collection types (Set, Map) requiring `clone_hashset()`.
    /// Non-listed fields are assumed to be Copy types (u64, bool) and use direct access.
    /// Used by `clone_input_field_access()` to avoid wrapping primitives with `clone_hashset()`.
    /// e.g., ["electing", "alive", "max_bal", "max_v_bal", "max_val", "pending_sent"]
    #[serde(default)]
    pub collection_fields: Vec<String>,

    /// Fields that are Vec/HashMap types requiring `.clone()` instead of `clone_hashset()`.
    /// These fields still need `@` in view context (like collection_fields) but use standard
    /// `.clone()` for copying since `clone_hashset()` only works on HashSet.
    /// e.g., ["log", "history", "match_index"]
    #[serde(default)]
    pub vec_fields: Vec<String>,

    /// Fields that are non-Copy types requiring `.clone()` but NOT needing `@` in view context.
    /// Used for enum fields or other types that need cloning but have identity View.
    /// e.g., ["role"] for CNodeRole enum fields
    #[serde(default)]
    pub clone_fields: Vec<String>,

    /// Maps clone_fields field names to their exec enum type names.
    /// Used to generate `clone_<lowercase_type>()` helper functions with view/validity ensures.
    /// The variants for each type are derived from `variant_remapping`.
    /// e.g., {"role" = "CNodeRole"} generates `fn clone_cnoderol(r: &CNodeRole) -> CNodeRole`
    #[serde(default)]
    pub clone_field_types: HashMap<String, String>,

    /// Maps Vec field names to their [exec_element_type, spec_element_type] pairs.
    /// Used for Vec fields containing struct elements that have a View trait (e.g., CLogEntry → LLogEntry).
    /// Generates:
    /// - `clone_<field>()`: external_body clone wrapper with mapped-view ensures
    /// - `lemma_empty_<field>_map()`: empty Seq proof helper
    /// - `lemma_<field>_push_map_commute()`: push commutativity proof helper
    /// e.g., {"log" = ["CLogEntry", "LLogEntry"]}
    #[serde(default)]
    pub struct_vec_fields: HashMap<String, Vec<String>>,

    /// Maps HashMap field names to their [exec_map_type, abstractify_prefix, exec_value_type] triples.
    /// Used for HashMap<u64, V> fields with deep abstraction (key and value type conversion).
    /// The abstractify function is `abstractify_{prefix}()` and validity is `{prefix}_is_valid()`.
    /// Generates:
    /// - `clone_{prefix}()`: external_body clone wrapper
    /// - `filter_{prefix}()`: external_body filter-by-key-threshold helper
    /// - `lemma_abstractify_empty_{prefix}()`: empty map proof
    /// - `lemma_abstractify_{prefix}_insert()`: insert commutativity proof
    /// - `lemma_abstractify_{prefix}_remove()`: remove commutativity proof
    /// - `lemma_abstractify_singleton_{prefix}()`: singleton map proof
    /// e.g., {"unexecuted_learner_state" = ["CLearnerState", "clearnerstate", "CLearnerTuple"]}
    #[serde(default)]
    pub map_fields: HashMap<String, Vec<String>>,

    /// Extra requires clauses per exec function name.
    /// These are manually specified preconditions that the transpiler can't derive
    /// automatically (e.g., covering conditions for implication groups).
    /// e.g., {"CInit" = ["c.node_id < c.chain_len"]}
    #[serde(default)]
    pub extra_requires: HashMap<String, Vec<String>>,
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
    /// This checks both spec type names and remapped exec type names,
    /// in both primitive_types and skip_valid_types lists.
    pub fn is_primitive_type(&self, type_name: &str) -> bool {
        // Check if directly in primitive_types list
        if self.primitive_types.contains(&type_name.to_string()) {
            return true;
        }

        // Check if directly in skip_valid_types list
        if self.skip_valid_types.contains(&type_name.to_string()) {
            return true;
        }

        // Check if the remapped exec type is in primitive_types or skip_valid_types
        let exec_type = self.get_exec_type(type_name);
        if self.primitive_types.contains(&exec_type) || self.skip_valid_types.contains(&exec_type) {
            return true;
        }

        false
    }

    /// Check if a type is strictly primitive (maps to `*param as int` in ensures).
    /// Unlike `is_primitive_type`, this does NOT include `skip_valid_types`.
    pub fn is_strict_primitive(&self, type_name: &str) -> bool {
        if self.primitive_types.contains(&type_name.to_string()) {
            return true;
        }

        let exec_type = self.get_exec_type(type_name);
        self.primitive_types.contains(&exec_type)
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

    /// Rust type to use for spec `int` type (default: "i64")
    /// Use "u64" for codebases that use unsigned integers
    #[serde(default = "default_int_type")]
    pub int_type: String,

    /// Rust type to use for spec `nat` type (default: "u64")
    #[serde(default = "default_nat_type")]
    pub nat_type: String,
}

fn default_spec_prefix() -> String {
    "L".to_string()
}

fn default_exec_prefix() -> String {
    "C".to_string()
}

fn default_int_type() -> String {
    "i64".to_string()
}

fn default_nat_type() -> String {
    "u64".to_string()
}

impl Default for NamingConfig {
    fn default() -> Self {
        Self {
            spec_prefix: default_spec_prefix(),
            exec_prefix: default_exec_prefix(),
            spec_fn_suffix: String::new(),
            exec_fn_suffix: String::new(),
            int_type: default_int_type(),
            nat_type: default_nat_type(),
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

    /// Whether to generate proof blocks instead of assume() calls.
    /// When true, the transpiler emits `proof { ... }` blocks with assertions
    /// and lemma calls that Verus can verify. When false (default), emits
    /// `assume(...)` calls as trusted placeholders.
    #[serde(default)]
    pub generate_proofs: bool,

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

    /// Clone method to use in generated loops.
    /// When set (e.g., "clone_up_to_view"), uses `x.clone_up_to_view()` instead of `x.clone()`.
    /// Needed for types where `.clone()` doesn't have `ensures res@ == self@` spec.
    #[serde(default)]
    pub clone_method: Option<String>,

    /// Path to a file containing manual Verus code to inject into the generated output.
    /// The file contents are inserted inside the `verus! {}` block after all auto-generated
    /// items (functions for transpile mode, types/functions for generate-types mode).
    /// Use this for logic too complex for auto-generation (e.g., protocol-specific helpers).
    /// The path is relative to the config file.
    #[serde(default)]
    pub manual_code: Option<String>,
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
            generate_proofs: false,
            generate_wrapper_methods: false,
            wrapper_impl_type: None,
            clone_method: None,
            manual_code: None,
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

    #[test]
    fn test_view_overrides_config() {
        let toml = r#"
            [view_overrides]
            "LAcceptor.votes" = "abstractify_cvotes(&self.votes)"
            "LExecutor.reply_cache" = "abstractify_creplycache(&self.reply_cache)"
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.view_overrides.len(), 2);
        assert_eq!(
            config.view_overrides.get("LAcceptor.votes"),
            Some(&"abstractify_cvotes(&self.votes)".to_string())
        );
    }

    #[test]
    fn test_extra_fields_config() {
        let toml = r#"
            [extra_fields]
            "CAcceptor.min_vote_opn" = "u64 = 0"
            "CProposer.max_opn_with_proposal" = "u64 = 0"
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.extra_fields.len(), 2);
        assert_eq!(
            config.extra_fields.get("CAcceptor.min_vote_opn"),
            Some(&"u64 = 0".to_string())
        );
    }

    #[test]
    fn test_clone_strategy_config() {
        let toml = r#"
            [clone_strategy]
            "CElectionState" = "external_body"
            "CProposer" = "external_body"
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.clone_strategy.len(), 2);
        assert_eq!(
            config.clone_strategy.get("CElectionState"),
            Some(&"external_body".to_string())
        );
    }

    #[test]
    fn test_skip_types_config() {
        let toml = r#"
            skip_types = ["Ballot", "Request", "Reply"]
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.skip_types.len(), 3);
        assert!(config.skip_types.contains(&"Ballot".to_string()));
        assert!(config.skip_types.contains(&"Request".to_string()));
    }

    #[test]
    fn test_re_exports_config() {
        let toml = r#"
            re_exports = [
                "crate::implementation::RSL::types_i::*",
                "crate::implementation::RSL::cmessage::CPacket",
            ]
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.re_exports.len(), 2);
        assert!(config
            .re_exports
            .contains(&"crate::implementation::RSL::types_i::*".to_string()));
    }

    #[test]
    fn test_generate_proofs_default_false() {
        let config = TranspilerConfig::default();
        assert!(!config.output.generate_proofs);
    }

    #[test]
    fn test_generate_proofs_from_toml() {
        let toml = r#"
            [output]
            generate_proofs = true
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert!(config.output.generate_proofs);
    }

    #[test]
    fn test_generate_proofs_false_from_toml() {
        let toml = r#"
            [output]
            generate_proofs = false
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert!(!config.output.generate_proofs);
    }

    #[test]
    fn test_generate_proofs_omitted_defaults_false() {
        let toml = r#"
            [output]
            generate_loops_for_verification = true
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert!(!config.output.generate_proofs);
        assert!(config.output.generate_loops_for_verification);
    }

    #[test]
    fn test_variant_remapping_config() {
        let toml = r#"
            [variant_remapping]
            "Init" = "CTMState::Init"
            "Committed" = "CTMState::Committed"
            "Aborted" = "CTMState::Aborted"
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.variant_remapping.len(), 3);
        assert_eq!(
            config.variant_remapping.get("Init"),
            Some(&"CTMState::Init".to_string())
        );
        assert_eq!(
            config.variant_remapping.get("Committed"),
            Some(&"CTMState::Committed".to_string())
        );
        assert_eq!(
            config.variant_remapping.get("Aborted"),
            Some(&"CTMState::Aborted".to_string())
        );
    }

    #[test]
    fn test_variant_remapping_default_empty() {
        let config = TranspilerConfig::default();
        assert!(config.variant_remapping.is_empty());
    }

    #[test]
    fn test_collection_fields_config() {
        let toml = r#"
            collection_fields = ["electing", "alive", "pending_sent"]
        "#;
        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.collection_fields.len(), 3);
        assert!(config.collection_fields.contains(&"electing".to_string()));
        assert!(config.collection_fields.contains(&"alive".to_string()));
        assert!(config.collection_fields.contains(&"pending_sent".to_string()));
    }

    #[test]
    fn test_collection_fields_default_empty() {
        let config = TranspilerConfig::default();
        assert!(config.collection_fields.is_empty());
    }

    #[test]
    fn test_vec_fields_config() {
        let toml = r#"
            collection_fields = ["pending_sent"]
            vec_fields = ["history", "log"]
        "#;
        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.collection_fields.len(), 1);
        assert!(config.collection_fields.contains(&"pending_sent".to_string()));
        assert_eq!(config.vec_fields.len(), 2);
        assert!(config.vec_fields.contains(&"history".to_string()));
        assert!(config.vec_fields.contains(&"log".to_string()));
    }

    #[test]
    fn test_vec_fields_default_empty() {
        let config = TranspilerConfig::default();
        assert!(config.vec_fields.is_empty());
    }

    #[test]
    fn test_clone_field_types_config() {
        let toml = r#"
            clone_fields = ["role"]

            [clone_field_types]
            "role" = "CNodeRole"
        "#;
        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.clone_fields.len(), 1);
        assert!(config.clone_fields.contains(&"role".to_string()));
        assert_eq!(config.clone_field_types.len(), 1);
        assert_eq!(
            config.clone_field_types.get("role"),
            Some(&"CNodeRole".to_string())
        );
    }

    #[test]
    fn test_clone_field_types_default_empty() {
        let config = TranspilerConfig::default();
        assert!(config.clone_field_types.is_empty());
    }

    #[test]
    fn test_extra_requires_config() {
        let toml = r#"
            [extra_requires]
            "CInit" = ["c.node_id < c.chain_len"]
            "CStartElection" = ["c.valid()", "s.alive.len() > 0"]
        "#;
        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.extra_requires.len(), 2);
        assert_eq!(
            config.extra_requires.get("CInit"),
            Some(&vec!["c.node_id < c.chain_len".to_string()])
        );
        assert_eq!(
            config.extra_requires.get("CStartElection").unwrap().len(),
            2
        );
    }

    #[test]
    fn test_extra_requires_default_empty() {
        let config = TranspilerConfig::default();
        assert!(config.extra_requires.is_empty());
    }

    #[test]
    fn test_map_fields_config() {
        let toml = r#"
            [map_fields]
            "unexecuted_learner_state" = ["CLearnerState", "clearnerstate", "CLearnerTuple"]
            "votes" = ["CVotes", "cvotes", "CVote"]
        "#;
        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.map_fields.len(), 2);
        let learner = config.map_fields.get("unexecuted_learner_state").unwrap();
        assert_eq!(learner[0], "CLearnerState");
        assert_eq!(learner[1], "clearnerstate");
        assert_eq!(learner[2], "CLearnerTuple");
        let votes = config.map_fields.get("votes").unwrap();
        assert_eq!(votes[0], "CVotes");
    }

    #[test]
    fn test_map_fields_default_empty() {
        let config = TranspilerConfig::default();
        assert!(config.map_fields.is_empty());
    }
}
