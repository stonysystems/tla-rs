use crate::error::{TranspileError, TranspileResult};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::path::Path;

/// Parsed `model.toml` configuration for source-first model checking.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct ModelConfig {
    #[serde(default)]
    pub constants: ConstantConfig,
    #[serde(default)]
    pub quantifiers: QuantifierConfig,
    #[serde(default)]
    pub collections: CollectionBounds,
    #[serde(default)]
    pub search: SearchLimits,
    #[serde(default)]
    pub properties: PropertyConfig,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct ConstantConfig {
    /// Concrete assignments for `LConstants` fields.
    #[serde(default)]
    pub assignments: HashMap<String, ModelValue>,
    /// Finite domains for fields not explicitly assigned.
    #[serde(default)]
    pub domains: HashMap<String, DomainSpec>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct QuantifierConfig {
    /// Fallback finite domain for `int`.
    pub int: Option<IntDomain>,
    /// Fallback finite domain for `nat`.
    pub nat: Option<NatDomain>,
    /// Type-specific finite domains (e.g. `NodeId`, `Role`, `Phase`).
    #[serde(default)]
    pub types: HashMap<String, DomainSpec>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CollectionBounds {
    #[serde(default = "default_seq_bound")]
    pub max_seq_len: usize,
    #[serde(default = "default_set_bound")]
    pub max_set_len: usize,
    #[serde(default = "default_map_bound")]
    pub max_map_len: usize,
}

impl Default for CollectionBounds {
    fn default() -> Self {
        Self {
            max_seq_len: default_seq_bound(),
            max_set_len: default_set_bound(),
            max_map_len: default_map_bound(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SearchLimits {
    #[serde(default = "default_max_depth")]
    pub max_depth: usize,
    #[serde(default = "default_max_states")]
    pub max_states: usize,
    #[serde(default = "default_timeout_ms")]
    pub timeout_ms: u64,
    /// State deduplication strategy used by exploration.
    #[serde(default)]
    pub state_dedup: StateDedupMode,
    /// Optional top-level `LState` field names to symmetry-normalize before dedup.
    ///
    /// This intentionally merges states that differ only in selected field identities.
    /// Keep this empty for exact exploration.
    #[serde(default)]
    pub symmetry_fields: Vec<String>,
    /// Partial-order-reduction heuristic mode.
    #[serde(default)]
    pub por_heuristic: PorHeuristic,
}

impl Default for SearchLimits {
    fn default() -> Self {
        Self {
            max_depth: default_max_depth(),
            max_states: default_max_states(),
            timeout_ms: default_timeout_ms(),
            state_dedup: StateDedupMode::Canonical,
            symmetry_fields: Vec::new(),
            por_heuristic: PorHeuristic::None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum StateDedupMode {
    /// Exact state deduplication using canonical runtime-value keys.
    #[default]
    Canonical,
    /// Lossy deduplication using a 64-bit hash fingerprint of canonical keys.
    ///
    /// This can reduce memory pressure but may merge distinct states on hash collisions.
    /// Use for bug-finding/exploration acceleration, not for sound proof obligations.
    HashCompaction64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum PorHeuristic {
    /// Disable POR-style branch pruning.
    #[default]
    None,
    /// Prune branches that write only fields proven syntactically invisible
    /// to all other branches and selected invariants.
    InvisibleBranch,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct PropertyConfig {
    /// Invariant spec function names (e.g. `LTypeOK`, `LSafety`).
    #[serde(default)]
    pub invariants: Vec<String>,
    /// Whether to report deadlock states (no successors).
    #[serde(default)]
    pub check_deadlock: bool,
    /// Transition semantics when no branch successors exist.
    #[serde(default)]
    pub successor_semantics: SuccessorSemantics,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "snake_case")]
pub enum SuccessorSemantics {
    /// No implicit transition when `LNext` has no enabled branch.
    #[default]
    Deadlock,
    /// Add a stutter successor (`s_ == s`) when no branch is enabled.
    Stuttering,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntDomain {
    pub min: i64,
    pub max: i64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NatDomain {
    pub max: u64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum DomainSpec {
    /// Explicit finite values for primitive-like domains.
    Values { values: Vec<ModelValue> },
    /// Finite signed integer range.
    IntRange { min: i64, max: i64 },
    /// Finite natural-number range [0, max].
    NatRange { max: u64 },
    /// Subset of enum variants by name.
    EnumSubset { variants: Vec<String> },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum ModelValue {
    Bool(bool),
    Int(i64),
    String(String),
}

/// CLI-provided override values for key model-check limits/domains.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ModelConfigOverrides {
    pub max_depth: Option<usize>,
    pub max_states: Option<usize>,
    pub timeout_ms: Option<u64>,
    pub max_seq_len: Option<usize>,
    pub max_set_len: Option<usize>,
    pub max_map_len: Option<usize>,
    pub int_range: Option<IntDomain>,
    pub nat_max: Option<u64>,
}

/// Parse an `int` range override from `MIN..MAX` or `MIN:MAX` syntax.
pub fn parse_int_range_override(raw: &str) -> TranspileResult<IntDomain> {
    let (min_raw, max_raw) = raw
        .split_once("..")
        .or_else(|| raw.split_once(':'))
        .ok_or_else(|| TranspileError::Config {
            message: format!(
                "Invalid int range override `{}`: expected `MIN..MAX` (or `MIN:MAX`).",
                raw
            ),
        })?;

    let min = min_raw
        .trim()
        .parse::<i64>()
        .map_err(|e| TranspileError::Config {
            message: format!(
                "Invalid int range override `{}`: failed to parse min value `{}`: {}.",
                raw,
                min_raw.trim(),
                e
            ),
        })?;
    let max = max_raw
        .trim()
        .parse::<i64>()
        .map_err(|e| TranspileError::Config {
            message: format!(
                "Invalid int range override `{}`: failed to parse max value `{}`: {}.",
                raw,
                max_raw.trim(),
                e
            ),
        })?;

    if min > max {
        return Err(TranspileError::Config {
            message: format!(
                "Invalid int range override `{}`: min ({}) must be <= max ({}).",
                raw, min, max
            ),
        });
    }

    Ok(IntDomain { min, max })
}

/// Apply CLI overrides to a parsed `model.toml` and revalidate the resulting config.
pub fn apply_model_config_overrides(
    config: &mut ModelConfig,
    overrides: &ModelConfigOverrides,
) -> TranspileResult<()> {
    if let Some(max_depth) = overrides.max_depth {
        config.search.max_depth = max_depth;
    }
    if let Some(max_states) = overrides.max_states {
        config.search.max_states = max_states;
    }
    if let Some(timeout_ms) = overrides.timeout_ms {
        config.search.timeout_ms = timeout_ms;
    }

    if let Some(max_seq_len) = overrides.max_seq_len {
        config.collections.max_seq_len = max_seq_len;
    }
    if let Some(max_set_len) = overrides.max_set_len {
        config.collections.max_set_len = max_set_len;
    }
    if let Some(max_map_len) = overrides.max_map_len {
        config.collections.max_map_len = max_map_len;
    }

    if let Some(int_range) = &overrides.int_range {
        config.quantifiers.int = Some(int_range.clone());
    }
    if let Some(nat_max) = overrides.nat_max {
        config.quantifiers.nat = Some(NatDomain { max: nat_max });
    }

    validate_model_config(config)
}

/// Parse and validate `model.toml` from a string.
pub fn parse_model_config_str(source: &str) -> TranspileResult<ModelConfig> {
    let config: ModelConfig = toml::from_str(source).map_err(|e| TranspileError::Config {
        message: format!("Failed to parse model.toml: {}", e),
    })?;
    validate_model_config(&config)?;
    Ok(config)
}

/// Parse and validate `model.toml` from disk.
pub fn parse_model_config_file<P: AsRef<Path>>(path: P) -> TranspileResult<ModelConfig> {
    let path = path.as_ref();
    let source = std::fs::read_to_string(path).map_err(|e| TranspileError::Config {
        message: format!("Failed to read model.toml `{}`: {}", path.display(), e),
    })?;
    parse_model_config_str(&source).map_err(|e| match e {
        TranspileError::Config { message } => TranspileError::Config {
            message: format!("In `{}`: {}", path.display(), message),
        },
        other => other,
    })
}

/// Validate a parsed `model.toml`.
pub fn validate_model_config(config: &ModelConfig) -> TranspileResult<()> {
    for key in config.constants.assignments.keys() {
        validate_non_empty_key(key, "constants.assignments")?;
    }
    for key in config.constants.domains.keys() {
        validate_non_empty_key(key, "constants.domains")?;
    }
    for key in config.quantifiers.types.keys() {
        validate_non_empty_key(key, "quantifiers.types")?;
    }

    for key in config.constants.assignments.keys() {
        if config.constants.domains.contains_key(key) {
            return Err(TranspileError::Config {
                message: format!(
                    "Invalid model.toml: constants field `{}` appears in both \
                     `[constants.assignments]` and `[constants.domains]`.",
                    key
                ),
            });
        }
    }

    if let Some(int_domain) = &config.quantifiers.int {
        if int_domain.min > int_domain.max {
            return Err(TranspileError::Config {
                message: format!(
                    "Invalid model.toml: `quantifiers.int.min` ({}) must be <= \
                     `quantifiers.int.max` ({}).",
                    int_domain.min, int_domain.max
                ),
            });
        }
    }

    validate_domain_map(&config.constants.domains, "constants.domains")?;
    validate_domain_map(&config.quantifiers.types, "quantifiers.types")?;

    if config.collections.max_seq_len == 0
        || config.collections.max_set_len == 0
        || config.collections.max_map_len == 0
    {
        return Err(TranspileError::Config {
            message: format!(
                "Invalid model.toml: collection bounds must be > 0 (got seq={}, set={}, map={}).",
                config.collections.max_seq_len,
                config.collections.max_set_len,
                config.collections.max_map_len
            ),
        });
    }

    if config.search.max_depth == 0
        || config.search.max_states == 0
        || config.search.timeout_ms == 0
    {
        return Err(TranspileError::Config {
            message: format!(
                "Invalid model.toml: search limits must be > 0 (got max_depth={}, max_states={}, timeout_ms={}).",
                config.search.max_depth, config.search.max_states, config.search.timeout_ms
            ),
        });
    }

    let mut seen_symmetry_fields = HashSet::new();
    for field in &config.search.symmetry_fields {
        let trimmed = field.trim();
        if trimmed.is_empty() {
            return Err(TranspileError::Config {
                message:
                    "Invalid model.toml: `search.symmetry_fields` cannot contain empty field names."
                        .to_string(),
            });
        }
        if !seen_symmetry_fields.insert(trimmed.to_string()) {
            return Err(TranspileError::Config {
                message: format!(
                    "Invalid model.toml: duplicate symmetry field `{}` in `search.symmetry_fields`.",
                    trimmed
                ),
            });
        }
    }

    let mut seen = HashSet::new();
    for name in &config.properties.invariants {
        let trimmed = name.trim();
        if trimmed.is_empty() {
            return Err(TranspileError::Config {
                message: "Invalid model.toml: `properties.invariants` cannot contain empty names."
                    .to_string(),
            });
        }
        if !seen.insert(trimmed.to_string()) {
            return Err(TranspileError::Config {
                message: format!(
                    "Invalid model.toml: duplicate invariant `{}` in `properties.invariants`.",
                    trimmed
                ),
            });
        }
    }

    if config.properties.check_deadlock
        && matches!(
            config.properties.successor_semantics,
            SuccessorSemantics::Stuttering
        )
    {
        return Err(TranspileError::Config {
            message: "Invalid model.toml: `properties.check_deadlock = true` conflicts with \
                      `properties.successor_semantics = \"stuttering\"` (stuttering removes deadlocks)."
                .to_string(),
        });
    }

    if config.properties.check_deadlock
        && !matches!(config.search.por_heuristic, PorHeuristic::None)
    {
        return Err(TranspileError::Config {
            message:
                "Invalid model.toml: POR heuristic requires `properties.check_deadlock = false` \
                      (branch pruning can hide deadlock-only transitions)."
                    .to_string(),
        });
    }

    Ok(())
}

fn validate_domain_map(
    domains: &HashMap<String, DomainSpec>,
    section: &str,
) -> TranspileResult<()> {
    for (key, domain) in domains {
        match domain {
            DomainSpec::Values { values } => {
                if values.is_empty() {
                    return Err(TranspileError::Config {
                        message: format!(
                            "Invalid model.toml: `{}` for key `{}` must have at least one value.",
                            section, key
                        ),
                    });
                }
            }
            DomainSpec::IntRange { min, max } => {
                if min > max {
                    return Err(TranspileError::Config {
                        message: format!(
                            "Invalid model.toml: `{}` key `{}` has invalid int_range (min={} > max={}).",
                            section, key, min, max
                        ),
                    });
                }
            }
            DomainSpec::NatRange { .. } => {}
            DomainSpec::EnumSubset { variants } => {
                if variants.is_empty() {
                    return Err(TranspileError::Config {
                        message: format!(
                            "Invalid model.toml: `{}` key `{}` must have at least one enum variant.",
                            section, key
                        ),
                    });
                }
                for variant in variants {
                    if variant.trim().is_empty() {
                        return Err(TranspileError::Config {
                            message: format!(
                                "Invalid model.toml: `{}` key `{}` contains an empty enum variant name.",
                                section, key
                            ),
                        });
                    }
                }
            }
        }
    }
    Ok(())
}

fn validate_non_empty_key(key: &str, section: &str) -> TranspileResult<()> {
    if key.trim().is_empty() {
        return Err(TranspileError::Config {
            message: format!(
                "Invalid model.toml: `{}` contains an empty field/type key.",
                section
            ),
        });
    }
    Ok(())
}

const fn default_seq_bound() -> usize {
    4
}
const fn default_set_bound() -> usize {
    4
}
const fn default_map_bound() -> usize {
    4
}
const fn default_max_depth() -> usize {
    30
}
const fn default_max_states() -> usize {
    100_000
}
const fn default_timeout_ms() -> u64 {
    30_000
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_model_config_full_valid() {
        let source = r#"
[constants.assignments]
quorum = 2
leader = "n1"

[constants.domains.node_id]
kind = "values"
values = ["n1", "n2", "n3"]

[constants.domains.role]
kind = "enum_subset"
variants = ["Follower", "Leader"]

[quantifiers.int]
min = -1
max = 3

[quantifiers.nat]
max = 5

[quantifiers.types.node_id]
kind = "values"
values = ["n1", "n2", "n3"]

[collections]
max_seq_len = 3
max_set_len = 2
max_map_len = 4

[search]
max_depth = 12
max_states = 5000
timeout_ms = 1000
state_dedup = "canonical"

[properties]
invariants = ["LTypeOK", "LSafety"]
check_deadlock = true
successor_semantics = "deadlock"
"#;
        let config = parse_model_config_str(source).unwrap();
        assert_eq!(config.constants.assignments.len(), 2);
        assert_eq!(config.constants.domains.len(), 2);
        assert_eq!(config.quantifiers.types.len(), 1);
        assert_eq!(config.properties.invariants.len(), 2);
        assert!(config.properties.check_deadlock);
        assert_eq!(
            config.properties.successor_semantics,
            SuccessorSemantics::Deadlock
        );
        assert_eq!(config.search.state_dedup, StateDedupMode::Canonical);
    }

    #[test]
    fn test_parse_model_config_defaults() {
        let source = r#"
[properties]
invariants = ["LTypeOK"]
"#;
        let config = parse_model_config_str(source).unwrap();
        assert_eq!(config.collections.max_seq_len, 4);
        assert_eq!(config.search.max_depth, 30);
        assert_eq!(config.search.max_states, 100_000);
        assert_eq!(config.search.timeout_ms, 30_000);
        assert_eq!(config.search.state_dedup, StateDedupMode::Canonical);
        assert!(config.search.symmetry_fields.is_empty());
        assert_eq!(config.search.por_heuristic, PorHeuristic::None);
        assert_eq!(config.properties.invariants, vec!["LTypeOK".to_string()]);
        assert_eq!(
            config.properties.successor_semantics,
            SuccessorSemantics::Deadlock
        );
    }

    #[test]
    fn test_parse_model_config_rejects_assignment_domain_overlap() {
        let source = r#"
[constants.assignments]
node_count = 3

[constants.domains.node_count]
kind = "int_range"
min = 1
max = 5
"#;
        let err = parse_model_config_str(source).unwrap_err();
        assert!(err
            .to_string()
            .contains("appears in both `[constants.assignments]` and `[constants.domains]`"));
    }

    #[test]
    fn test_parse_model_config_rejects_bad_int_range() {
        let source = r#"
[quantifiers.int]
min = 4
max = 3
"#;
        let err = parse_model_config_str(source).unwrap_err();
        assert!(err.to_string().contains("must be <= `quantifiers.int.max`"));
    }

    #[test]
    fn test_parse_model_config_rejects_empty_values_domain() {
        let source = r#"
[constants.domains.node_id]
kind = "values"
values = []
"#;
        let err = parse_model_config_str(source).unwrap_err();
        assert!(err.to_string().contains("must have at least one value"));
    }

    #[test]
    fn test_parse_model_config_rejects_empty_enum_subset() {
        let source = r#"
[quantifiers.types.role]
kind = "enum_subset"
variants = []
"#;
        let err = parse_model_config_str(source).unwrap_err();
        assert!(err
            .to_string()
            .contains("must have at least one enum variant"));
    }

    #[test]
    fn test_parse_model_config_rejects_invalid_search_limits() {
        let source = r#"
[search]
max_depth = 0
max_states = 10
timeout_ms = 100
"#;
        let err = parse_model_config_str(source).unwrap_err();
        assert!(err.to_string().contains("search limits must be > 0"));
    }

    #[test]
    fn test_parse_model_config_rejects_duplicate_invariants() {
        let source = r#"
[properties]
invariants = ["LSafety", "LSafety"]
"#;
        let err = parse_model_config_str(source).unwrap_err();
        assert!(err.to_string().contains("duplicate invariant `LSafety`"));
    }

    #[test]
    fn test_parse_model_config_accepts_stuttering_semantics() {
        let source = r#"
[properties]
invariants = ["LTypeOK"]
check_deadlock = false
successor_semantics = "stuttering"
"#;
        let config = parse_model_config_str(source).unwrap();
        assert_eq!(
            config.properties.successor_semantics,
            SuccessorSemantics::Stuttering
        );
    }

    #[test]
    fn test_parse_model_config_accepts_hash_compaction_dedup_mode() {
        let source = r#"
[search]
state_dedup = "hash_compaction64"
"#;
        let config = parse_model_config_str(source).unwrap();
        assert_eq!(config.search.state_dedup, StateDedupMode::HashCompaction64);
    }

    #[test]
    fn test_parse_model_config_rejects_unknown_dedup_mode() {
        let source = r#"
[search]
state_dedup = "unknown_mode"
"#;
        let err = parse_model_config_str(source).unwrap_err();
        assert!(err.to_string().contains("state_dedup"));
    }

    #[test]
    fn test_parse_model_config_accepts_invisible_branch_por_heuristic() {
        let source = r#"
[search]
por_heuristic = "invisible_branch"
"#;
        let config = parse_model_config_str(source).unwrap();
        assert_eq!(config.search.por_heuristic, PorHeuristic::InvisibleBranch);
    }

    #[test]
    fn test_parse_model_config_accepts_symmetry_fields() {
        let source = r#"
[search]
symmetry_fields = ["members", "leader"]
"#;
        let config = parse_model_config_str(source).unwrap();
        assert_eq!(
            config.search.symmetry_fields,
            vec!["members".to_string(), "leader".to_string()]
        );
    }

    #[test]
    fn test_parse_model_config_rejects_empty_symmetry_field_name() {
        let source = r#"
[search]
symmetry_fields = ["members", "  "]
"#;
        let err = parse_model_config_str(source).unwrap_err();
        assert!(err.to_string().contains("search.symmetry_fields"));
    }

    #[test]
    fn test_parse_model_config_rejects_duplicate_symmetry_field_names() {
        let source = r#"
[search]
symmetry_fields = ["members", "members"]
"#;
        let err = parse_model_config_str(source).unwrap_err();
        assert!(err.to_string().contains("duplicate symmetry field"));
    }

    #[test]
    fn test_parse_model_config_rejects_deadlock_check_with_stuttering_semantics() {
        let source = r#"
[properties]
invariants = ["LTypeOK"]
check_deadlock = true
successor_semantics = "stuttering"
"#;
        let err = parse_model_config_str(source).unwrap_err();
        assert!(err.to_string().contains("conflicts with"));
    }

    #[test]
    fn test_parse_model_config_rejects_por_with_deadlock_check() {
        let source = r#"
[search]
por_heuristic = "invisible_branch"

[properties]
check_deadlock = true
"#;
        let err = parse_model_config_str(source).unwrap_err();
        assert!(err.to_string().contains("POR heuristic requires"));
    }

    #[test]
    fn test_parse_int_range_override_accepts_dotdot() {
        let parsed = parse_int_range_override("-2..5").unwrap();
        assert_eq!(parsed, IntDomain { min: -2, max: 5 });
    }

    #[test]
    fn test_parse_int_range_override_accepts_colon() {
        let parsed = parse_int_range_override("0:3").unwrap();
        assert_eq!(parsed, IntDomain { min: 0, max: 3 });
    }

    #[test]
    fn test_parse_int_range_override_rejects_invalid_format() {
        let err = parse_int_range_override("0,3").unwrap_err();
        assert!(err.to_string().contains("expected `MIN..MAX`"));
    }

    #[test]
    fn test_apply_model_config_overrides_updates_limits_and_domains() {
        let mut config = parse_model_config_str(
            r#"
[search]
max_depth = 10
max_states = 100
timeout_ms = 1000

[collections]
max_seq_len = 2
max_set_len = 2
max_map_len = 2
"#,
        )
        .unwrap();

        let overrides = ModelConfigOverrides {
            max_depth: Some(22),
            max_states: Some(1500),
            timeout_ms: Some(5000),
            max_seq_len: Some(4),
            max_set_len: Some(5),
            max_map_len: Some(6),
            int_range: Some(IntDomain { min: -1, max: 7 }),
            nat_max: Some(9),
        };

        apply_model_config_overrides(&mut config, &overrides).unwrap();

        assert_eq!(config.search.max_depth, 22);
        assert_eq!(config.search.max_states, 1500);
        assert_eq!(config.search.timeout_ms, 5000);
        assert_eq!(config.collections.max_seq_len, 4);
        assert_eq!(config.collections.max_set_len, 5);
        assert_eq!(config.collections.max_map_len, 6);
        assert_eq!(config.quantifiers.int, Some(IntDomain { min: -1, max: 7 }));
        assert_eq!(config.quantifiers.nat, Some(NatDomain { max: 9 }));
    }

    #[test]
    fn test_apply_model_config_overrides_revalidates_result() {
        let mut config = parse_model_config_str("[properties]\ninvariants = []\n").unwrap();
        let overrides = ModelConfigOverrides {
            max_depth: Some(0),
            ..Default::default()
        };
        let err = apply_model_config_overrides(&mut config, &overrides).unwrap_err();
        assert!(err.to_string().contains("search limits must be > 0"));
    }
}
