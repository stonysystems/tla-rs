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

    /// Functions to skip WITHOUT generating stubs (even in proof-fallback mode).
    /// Use for functions that already exist in implementation files and would
    /// cause duplicate definitions if stubs were generated.
    /// e.g., ["IsLogTruncationPointValid"]
    #[serde(default)]
    pub no_stub_functions: Vec<String>,

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

    /// Custom view expressions for types used in ensures clauses of helper/action functions.
    /// When a type appears as a parameter or return type, use this expression instead of `param@`.
    /// Key: spec type name (e.g., "Votes")
    /// Value: view expression template with `{param}` placeholder (e.g., "abstractify_cvotes({param})")
    /// The `{param}` is replaced with the actual parameter name at generation time.
    #[serde(default)]
    pub type_view_exprs: HashMap<String, String>,

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

    /// Types that should use `.clone_up_to_view()` instead of `.clone()`.
    /// When cloning a value whose type is in this list, the transpiler emits
    /// `.clone_up_to_view()` which provides `ensures res@ == self@`.
    /// e.g., ["CRequest", "CReply", "CVote", "CLearnerTuple", "EndPoint"]
    #[serde(default)]
    pub clone_up_to_view_types: Vec<String>,

    /// Types to skip during generation (already manually implemented).
    /// These spec type names will be parsed but NOT generated as exec types.
    /// e.g., ["Ballot", "Request", "Reply", "Vote", "LearnerTuple"]
    #[serde(default)]
    pub skip_types: Vec<String>,

    /// Exec type names whose validity predicates are provided manually.
    /// These types are still generated, but no `validity_predicate_name()` method is emitted.
    /// e.g., ["CParameters"]
    #[serde(default)]
    pub skip_validity_types: Vec<String>,

    /// Exec type names whose `View` trait implementations are provided manually.
    /// These types are still generated, but no `impl View for ...` block is emitted.
    /// e.g., ["CParameters"]
    #[serde(default)]
    pub skip_view_types: Vec<String>,

    /// Re-export statements to include at the top of the generated file.
    /// Each entry is a full `use` path (without the `use` keyword or semicolon).
    /// e.g., ["crate::implementation::RSL::types_i::*"]
    #[serde(default)]
    pub re_exports: Vec<String>,

    /// Extra type aliases to emit in generated type files.
    /// Key: alias name (e.g., "CRslIo")
    /// Value: target type expression (e.g., "LIoOp<EndPoint, CMessage>")
    #[serde(default)]
    pub extra_type_aliases: HashMap<String, String>,

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
    ///   e.g., {"log" = ["CLogEntry", "LLogEntry"]}
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
    ///   e.g., {"unexecuted_learner_state" = ["CLearnerState", "clearnerstate", "CLearnerTuple"]}
    #[serde(default)]
    pub map_fields: HashMap<String, Vec<String>>,

    /// Verified clone functions for map_fields.
    /// Maps abstractify_prefix to a verified clone function name.
    /// When set, the generated `clone_{prefix}()` delegates to this function
    /// instead of using `#[verifier(external_body)]` + `m.clone()`.
    /// e.g., {"clearnerstate" = "clone_clearnerstate_up_to_view"}
    #[serde(default)]
    pub verified_clone_fns: HashMap<String, String>,

    /// Message type for sent_packets Vec proof helpers in composite handlers.
    /// Generates `lemma_empty_msg_map()` for proving `Seq::<ExecType>::empty().map(f) =~= Seq::<SpecType>::empty()`.
    /// Format: ["CRaftMessage", "LRaftMessage"]
    #[serde(default)]
    pub msg_vec_type: Option<Vec<String>>,

    /// Fields that are HashMap-typed and need `&key` indexing, but should NOT trigger
    /// helper code generation (unlike `map_fields` which generates abstractify/clone/filter).
    /// Used purely for `is_map_index_base()` detection in Index expressions.
    /// e.g., ["reply_cache", "highest_seqno_requested_by_client_this_view"]
    #[serde(default)]
    pub hashmap_index_fields: Vec<String>,

    /// Extra requires clauses per exec function name.
    /// These are manually specified preconditions that the transpiler can't derive
    /// automatically (e.g., covering conditions for implication groups).
    /// e.g., {"CInit" = ["c.node_id < c.chain_len"]}
    #[serde(default)]
    pub extra_requires: HashMap<String, Vec<String>>,

    /// Inline expansion configuration for spec function calls.
    /// Maps spec function name to expansion config controlling both
    /// spec-context expansion (binary op) and exec-context call shaping.
    /// e.g., {"LeqUpperBound" = {spec_binary_op = "<=", strategy = "conditional_binary", ...}}
    #[serde(default)]
    pub inline_expansions: HashMap<String, InlineExpansionConfig>,

    /// Maps field names to equality comparison functions.
    /// When a `==` comparison involves a field in this map, the transpiler generates
    /// a function call instead of using `==` (which may use external PartialEq).
    /// e.g., {"bal_heartbeat" = "CBalEq", "current_view" = "CBalEq", "max_bal" = "CBalEq"}
    #[serde(default)]
    pub eq_function_fields: HashMap<String, String>,

    /// Maps enum variant field names to their containing variant path.
    /// Used to convert spec-only `->` arrow accesses into exec-level `match` destructuring.
    /// e.g., {"bal_1a" = "CMessage::CMessage1a", "bal_2a" = "CMessage::CMessage2a"}
    #[serde(default)]
    pub arrow_variants: HashMap<String, String>,

    /// Per-element ensures predicates for Vec/Seq output parameters.
    /// When an output parameter has type `Seq<T>` (mapped to `Vec<ExecT>`), the transpiler
    /// normally skips `valid()` because Vec itself doesn't have a `valid()` method.
    /// This field specifies predicates that should be asserted for each element.
    /// Generates: `forall |i:int| 0 <= i < result.X@.len() ==> result.X@[i].pred()`
    /// e.g., ["valid", "abstractable"]
    #[serde(default)]
    pub vec_element_ensures: Vec<String>,

    /// Field names whose exec type is HashSet<T> and spec type is Set<T>.
    /// Used by cardinality bridge proof injection (`inject_cardinality_bridge_proofs`)
    /// and to distinguish HashSet.contains() from Vec.contains().
    /// Auto-populated when `generate_inline_types = true`; specify manually otherwise.
    /// e.g., ["votes_granted", "servers"]
    #[serde(default)]
    pub set_fields: Vec<String>,

    /// Optional message generation configuration.
    /// When present, `generate-messages` subcommand can generate ProtocolMessage impl.
    #[serde(default)]
    pub messages: Option<MessageConfig>,

    /// Optional Marshalable generation configuration.
    /// When present, `generate-marshalable` subcommand can generate `impl Marshalable` for structs.
    #[serde(default)]
    pub marshalable: Option<MarshalableConfig>,

    /// Optional scheduler configuration for host code generation.
    /// When present, `generate-host` subcommand can generate a host.rs scaffold.
    #[serde(default)]
    pub scheduler: Option<SchedulerTomlConfig>,
}

/// Configuration for generating ProtocolMessage implementations.
///
/// Describes the message enum and its variants for a protocol.
/// Each variant has named fields with `u64` or `bool` types.
///
/// Example TOML:
/// ```toml
/// [messages]
/// enum_name = "PaxosMessage"
/// import_path = "crate::common::framework::protocol_trait::ProtocolMessage"
///
/// [[messages.variants]]
/// name = "Prepare"
/// fields = [["ballot", "u64"]]
///
/// [[messages.variants]]
/// name = "Promise"
/// fields = [["ballot", "u64"], ["accepted_bal", "u64"], ["accepted_val", "u64"]]
/// ```
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct MessageConfig {
    /// The name of the generated enum (e.g., "PaxosMessage")
    #[serde(default)]
    pub enum_name: String,

    /// Import path for the ProtocolMessage trait
    #[serde(default = "MessageConfig::default_import_path")]
    pub import_path: String,

    /// Module doc comment (optional)
    #[serde(default)]
    pub doc_comment: String,

    /// Variant definitions
    #[serde(default)]
    pub variants: Vec<MessageVariant>,
}

impl MessageConfig {
    fn default_import_path() -> String {
        "crate::common::framework::protocol_trait::ProtocolMessage".to_string()
    }
}

/// A single message variant with named fields.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct MessageVariant {
    /// Variant name (e.g., "Prepare")
    pub name: String,

    /// Named fields as [name, type] pairs. Types: "u64", "bool"
    #[serde(default)]
    pub fields: Vec<Vec<String>>,

    /// Optional doc comment for the variant
    #[serde(default)]
    pub doc: String,
}

/// Configuration for generating `impl Marshalable` for struct types.
///
/// Generates field-by-field serialize/deserialize with Verus proof annotations,
/// matching the output of the `derive_marshalable_for_struct!` macro.
///
/// Example TOML:
/// ```toml
/// [[marshalable.types]]
/// name = "CBallot"
/// fields = [["seqno", "u64"], ["proposer_id", "u64"]]
///
/// [[marshalable.types]]
/// name = "CRequest"
/// fields = [["client", "EndPoint"], ["seqno", "u64"], ["request", "CAppMessage"]]
/// ```
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct MarshalableConfig {
    /// Struct types to generate Marshalable impls for
    #[serde(default)]
    pub types: Vec<MarshalableType>,

    /// Enum types to generate Marshalable impls for
    #[serde(default)]
    pub enums: Vec<MarshalableEnum>,
}

/// A single struct type to generate `impl Marshalable` for.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct MarshalableType {
    /// Struct name (e.g., "CBallot")
    pub name: String,

    /// Fields as [name, type] pairs.
    /// Supported types: "u64", "bool", "Vec<u8>", or any named type implementing Marshalable.
    #[serde(default)]
    pub fields: Vec<Vec<String>>,
}

/// A single enum type to generate `impl Marshalable` for.
///
/// Each variant has a u8 tag and optional named fields.
/// Example TOML:
/// ```toml
/// [[marshalable.enums]]
/// name = "CAppMessage"
/// [[marshalable.enums.variants]]
/// name = "CAppIncrement"
/// tag = 0
/// [[marshalable.enums.variants]]
/// name = "CAppReply"
/// tag = 1
/// fields = [["response", "u64"]]
/// ```
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct MarshalableEnum {
    /// Enum name (e.g., "CMessage")
    pub name: String,

    /// Variant definitions with tags and fields
    #[serde(default)]
    pub variants: Vec<MarshalableEnumVariant>,
}

/// A single variant in a Marshalable enum.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct MarshalableEnumVariant {
    /// Variant name (e.g., "CMessageRequest")
    pub name: String,

    /// Tag byte (u8) for serialization dispatch
    pub tag: u8,

    /// Fields as [name, type] pairs (empty for unit variants)
    #[serde(default)]
    pub fields: Vec<Vec<String>>,
}

/// Configuration for scheduler/host code generation.
///
/// Describes the protocol actions extracted from LNext, their classification
/// (message_driven vs timer_driven), and optional message variant mapping.
///
/// Example TOML:
/// ```toml
/// [scheduler]
/// next_fn = "LNext"
/// params = ["s", "s_", "c"]
/// action_count = 7
///
/// [[scheduler.actions]]
/// spec_name = "LSend1a"
/// exec_name = "CSend1a"
/// kind = "timer_driven"
///
/// [[scheduler.actions]]
/// spec_name = "LSend1b"
/// exec_name = "CSend1b"
/// kind = "message_driven"
/// message_variant = "Prepare"
/// ```
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct SchedulerTomlConfig {
    /// The LNext function name (usually "LNext")
    #[serde(default = "SchedulerTomlConfig::default_next_fn")]
    pub next_fn: String,

    /// Parameter names of LNext (e.g., ["s", "s_", "c"])
    #[serde(default)]
    pub params: Vec<String>,

    /// Number of actions (informational, derived from actions.len())
    #[serde(default)]
    pub action_count: usize,

    /// The protocol actions
    #[serde(default)]
    pub actions: Vec<SchedulerActionConfig>,

    /// Optional role-based dispatch configuration.
    /// When present, the generated host scaffold dispatches to per-role step methods.
    #[serde(default)]
    pub role_dispatch: Option<RoleDispatchConfig>,

    /// Protocol-specific action name patterns classified as message-driven responses.
    /// These are actions that respond to incoming messages but don't contain standard
    /// message keywords (receive/rcv/handle). TOML overrides take priority over defaults.
    /// e.g., ["Send1b", "Send2b"] for Paxos, ["GrantVote"] for Raft
    #[serde(default)]
    pub message_response_overrides: Vec<String>,

    /// Protocol-specific role prefixes to strip from action names for variant matching.
    /// e.g., ["TM", "RM"] for TwoPhase, ["Primary", "Backup"] for PrimaryBackup
    #[serde(default)]
    pub role_prefixes: Vec<String>,

    /// Protocol-specific action name patterns that should be timer-driven even when
    /// they contain message keywords (like "Handle"). Checked before keyword matching.
    /// e.g., ["HandleAppendReject"] for Raft
    #[serde(default)]
    pub timer_overrides: Vec<String>,
}

impl SchedulerTomlConfig {
    fn default_next_fn() -> String {
        "LNext".to_string()
    }
}

/// A single action entry in the scheduler TOML config.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct SchedulerActionConfig {
    /// Spec function name (e.g., "LSend1a")
    pub spec_name: String,

    /// Exec function name (e.g., "CSend1a")
    pub exec_name: String,

    /// "message_driven" or "timer_driven"
    #[serde(default = "SchedulerActionConfig::default_kind")]
    pub kind: String,

    /// For message_driven actions, the triggering message variant name
    #[serde(default)]
    pub message_variant: Option<String>,

    /// Existential parameters as [name, type] pairs
    #[serde(default)]
    pub existential_params: Vec<Vec<String>>,

    /// Flag injections: list of [state_field, value] pairs to emit before calling C* function.
    /// Protocols that model messages as shared-state boolean fields (e.g., `msgs_election: bool`)
    /// need the host to inject received packet fields into `self.state.msgs_*` before the
    /// generated function can check guards.
    ///
    /// `value` is either "true"/"false" (literal) or a message parameter name (passed through).
    /// Default: empty (backwards compatible — no injections generated).
    ///
    /// Example TOML:
    /// ```toml
    /// flag_injections = [["msgs_election", "true"], ["msgs_election_sender", "sender"]]
    /// ```
    #[serde(default)]
    pub flag_injections: Vec<Vec<String>>,

    /// Guard checks: list of Rust boolean conditions to emit as early-return guards.
    /// Each string is a condition that must be true for the action to proceed.
    /// The scaffold generator emits `if !({condition}) { return StepResult::noop() }`.
    ///
    /// Conditions should use `self.state.*` for state fields and `config.constants.*`
    /// for constants. Use `matches!(...)` for enum variant checks.
    ///
    /// Default: empty (backwards compatible — only TODO comment emitted).
    ///
    /// Example TOML:
    /// ```toml
    /// guard_checks = [
    ///     "matches!(self.state.phase, CPhase::Phase1)",
    ///     "ballot >= self.state.promised_bal",
    /// ]
    /// ```
    #[serde(default)]
    pub guard_checks: Vec<String>,
}

impl SchedulerActionConfig {
    fn default_kind() -> String {
        "timer_driven".to_string()
    }

    pub fn is_message_driven(&self) -> bool {
        self.kind == "message_driven"
    }

    /// Returns true if this action has any flag injections configured.
    pub fn has_flag_injections(&self) -> bool {
        !self.flag_injections.is_empty()
    }

    /// Returns true if this action has any guard checks configured.
    pub fn has_guard_checks(&self) -> bool {
        !self.guard_checks.is_empty()
    }
}

/// Configuration for role-based dispatch in the host scaffold.
///
/// When present, the generated `next()` method dispatches to per-role step
/// methods instead of a flat message/timer dispatch.
///
/// Two dispatch styles are supported:
/// - `"config_index"`: Role determined by `config.my_index` (static, e.g., TwoPhase TM vs RM)
/// - `"state_field"`: Role determined by matching on a state enum field (e.g., ChainReplication Head/Middle/Tail)
///
/// Example TOML:
/// ```toml
/// [scheduler.role_dispatch]
/// dispatch_style = "config_index"
/// dispatch_field = "config.my_index"
///
/// [[scheduler.role_dispatch.roles]]
/// name = "tm"
/// condition = "config.my_index == 0"
/// actions = ["CTMSendPrepare", "CTMSendCommit", "CTMSendAbort", "CTMReceivePrepared"]
///
/// [[scheduler.role_dispatch.roles]]
/// name = "rm"
/// condition = ""
/// actions = ["CRMReceivePrepare", "CRMReceiveCommit", "CRMReceiveAbort"]
/// ```
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct RoleDispatchConfig {
    /// Dispatch style: "config_index" or "state_field"
    pub dispatch_style: String,

    /// For state_field: the field path to match on (e.g., "self.state.role").
    /// For config_index: informational (e.g., "config.my_index").
    #[serde(default)]
    pub dispatch_field: String,

    /// The roles with their conditions and assigned actions.
    pub roles: Vec<RoleConfig>,
}

/// A single role in a role-based dispatch configuration.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct RoleConfig {
    /// Role name in snake_case (e.g., "tm", "head", "primary").
    /// Used to generate `{name}_step()` method names.
    pub name: String,

    /// Dispatch condition:
    /// - For config_index: e.g., "config.my_index == 0" (last role can be "" for else)
    /// - For state_field: enum variant e.g., "CNodeRole::Head"
    #[serde(default)]
    pub condition: String,

    /// Exec function names that belong to this role (e.g., ["CTMSendPrepare", "CTMSendCommit"]).
    /// These must match `exec_name` values in `[[scheduler.actions]]`.
    #[serde(default)]
    pub actions: Vec<String>,
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

    /// When true, prepend `assume(false)` at the start of each generated function body.
    /// This makes all postconditions vacuously true (trusted), equivalent to
    /// manually writing `assume(result.valid()); assume(SpecFn(...));`.
    /// Use when proof generation is not yet mature enough for a module.
    #[serde(default)]
    pub assume_postconditions: bool,

    /// Spec function names for which `assume(false)` should NOT be emitted,
    /// even when `assume_postconditions = true`. Use to selectively un-trust
    /// functions whose proofs have been verified to work without assume(false).
    /// Uses the L-prefix spec name (e.g., "LExecutorInit").
    #[serde(default)]
    pub proven_functions: Vec<String>,

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

    /// Whether to generate `clone_up_to_view()` for primitive-only generated structs.
    /// This is a migration aid for moving simple helper methods out of manual type code.
    #[serde(default)]
    pub generate_clone_up_to_view_simple: bool,

    /// Whether to generate a shared `unreachable_value<T>()` helper in generated type files.
    /// Useful when generated/manual RSL modules rely on this trusted helper and we want
    /// to migrate it out of manual helper code.
    #[serde(default)]
    pub generate_unreachable_value_helper: bool,

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
            generate_clone_up_to_view_simple: false,
            generate_unreachable_value_helper: false,
            manual_code: None,
            assume_postconditions: false,
            proven_functions: Vec::new(),
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

/// Exec-level call strategy for inline-expanded functions.
///
/// Determines how function arguments are shaped and whether the call
/// is lowered to a binary operator in exec context.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "strategy")]
pub enum ExecCallStrategy {
    /// All args forced to owned via `clone_if_input_ref`, kept as function call.
    /// e.g., `UpperBoundedAddition(x, y, z)` → all args owned
    #[serde(rename = "owned_call")]
    OwnedCall,

    /// Args are owned; if arg at `condition_arg` has a type matching `condition_types`,
    /// keep as function call; otherwise lower to binary op.
    /// e.g., `LtUpperBound(x, y)` → if y is UpperBound-typed → call, else → `x < y`
    #[serde(rename = "conditional_binary")]
    ConditionalBinary {
        op: String,
        condition_arg: usize,
        condition_types: Vec<String>,
    },

    /// Specific args wrapped in `&` via `ensure_borrowed_expr`; rest are owned.
    /// e.g., `BoundRequestSequence(seq, n)` → `&seq, owned n`
    #[serde(rename = "mixed_borrow")]
    MixedBorrowCall { borrowed_args: Vec<usize> },
}

/// Configuration for inline expansion of a spec function call.
///
/// Controls how a function is expanded in both spec/ensures context
/// (via `spec_binary_op`) and exec body context (via `exec` strategy).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InlineExpansionConfig {
    /// If set, `F(a, b)` → `(a op b)` in spec/ensures context (expr_to_simple_string).
    #[serde(default)]
    pub spec_binary_op: Option<String>,
    /// Exec call strategy.
    #[serde(flatten)]
    pub exec: ExecCallStrategy,
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
    /// If the exec method returns a tuple but the spec returns a single value,
    /// this is the 0-based index of the tuple element to extract.
    /// e.g., CGetReplicaIndex returns (bool, usize) but spec GetReplicaIndex returns int,
    /// so destructure_index = 1 extracts the usize element.
    #[serde(default)]
    pub destructure_index: Option<usize>,
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
    fn test_skip_validity_and_view_types_config() {
        let toml = r#"
            skip_validity_types = ["CParameters", "CConfiguration"]
            skip_view_types = ["CParameters"]
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.skip_validity_types.len(), 2);
        assert!(config
            .skip_validity_types
            .contains(&"CParameters".to_string()));
        assert!(config
            .skip_validity_types
            .contains(&"CConfiguration".to_string()));
        assert_eq!(config.skip_view_types, vec!["CParameters".to_string()]);
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
    fn test_extra_type_aliases_config() {
        let toml = r#"
            [extra_type_aliases]
            "CRslIo" = "LIoOp<EndPoint, CMessage>"
            "CReplyMap" = "HashMap<EndPoint, CReply>"
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(
            config.extra_type_aliases.get("CRslIo"),
            Some(&"LIoOp<EndPoint, CMessage>".to_string())
        );
        assert_eq!(
            config.extra_type_aliases.get("CReplyMap"),
            Some(&"HashMap<EndPoint, CReply>".to_string())
        );
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
    fn test_generate_unreachable_value_helper_default_false() {
        let config = TranspilerConfig::default();
        assert!(!config.output.generate_unreachable_value_helper);
    }

    #[test]
    fn test_generate_clone_up_to_view_simple_default_false() {
        let config = TranspilerConfig::default();
        assert!(!config.output.generate_clone_up_to_view_simple);
    }

    #[test]
    fn test_generate_clone_up_to_view_simple_from_toml() {
        let toml = r#"
            [output]
            generate_clone_up_to_view_simple = true
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert!(config.output.generate_clone_up_to_view_simple);
    }

    #[test]
    fn test_generate_unreachable_value_helper_from_toml() {
        let toml = r#"
            [output]
            generate_unreachable_value_helper = true
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert!(config.output.generate_unreachable_value_helper);
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
        assert!(config
            .collection_fields
            .contains(&"pending_sent".to_string()));
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
        assert!(config
            .collection_fields
            .contains(&"pending_sent".to_string()));
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

    #[test]
    fn test_messages_config() {
        let toml = r#"
            [messages]
            enum_name = "PaxosMessage"
            doc_comment = "Paxos messages."

            [[messages.variants]]
            name = "Prepare"
            fields = [["ballot", "u64"]]
            doc = "Phase 1a"

            [[messages.variants]]
            name = "Promise"
            fields = [["ballot", "u64"], ["accepted_bal", "u64"], ["accepted_val", "u64"]]
        "#;
        let config = TranspilerConfig::from_toml(toml).unwrap();
        let msg = config.messages.unwrap();
        assert_eq!(msg.enum_name, "PaxosMessage");
        assert_eq!(msg.doc_comment, "Paxos messages.");
        assert_eq!(msg.variants.len(), 2);
        assert_eq!(msg.variants[0].name, "Prepare");
        assert_eq!(msg.variants[0].doc, "Phase 1a");
        assert_eq!(msg.variants[0].fields.len(), 1);
        assert_eq!(msg.variants[0].fields[0], vec!["ballot", "u64"]);
        assert_eq!(msg.variants[1].name, "Promise");
        assert_eq!(msg.variants[1].fields.len(), 3);
    }

    #[test]
    fn test_messages_config_default_none() {
        let config = TranspilerConfig::default();
        assert!(config.messages.is_none());
    }

    #[test]
    fn test_messages_config_with_bool_fields() {
        let toml = r#"
            [messages]
            enum_name = "RaftMessage"

            [[messages.variants]]
            name = "VoteResponse"
            fields = [["term", "u64"], ["granted", "bool"], ["voter", "u64"]]
        "#;
        let config = TranspilerConfig::from_toml(toml).unwrap();
        let msg = config.messages.unwrap();
        assert_eq!(msg.variants[0].fields[1], vec!["granted", "bool"]);
    }

    #[test]
    fn test_parse_clone_up_to_view_types() {
        let toml = r#"
            clone_up_to_view_types = ["CRequest", "CReply", "CVote", "CLearnerTuple", "EndPoint"]

            [naming]
            spec_prefix = "L"
            exec_prefix = "C"
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert_eq!(config.clone_up_to_view_types.len(), 5);
        assert!(config.clone_up_to_view_types.contains(&"CRequest".to_string()));
        assert!(config.clone_up_to_view_types.contains(&"CReply".to_string()));
        assert!(config.clone_up_to_view_types.contains(&"CVote".to_string()));
        assert!(config.clone_up_to_view_types.contains(&"CLearnerTuple".to_string()));
        assert!(config.clone_up_to_view_types.contains(&"EndPoint".to_string()));
    }

    #[test]
    fn test_clone_up_to_view_types_defaults_empty() {
        let toml = r#"
            [naming]
            spec_prefix = "L"
            exec_prefix = "C"
        "#;

        let config = TranspilerConfig::from_toml(toml).unwrap();
        assert!(config.clone_up_to_view_types.is_empty());
    }
}
