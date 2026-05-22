use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::config::{CollectionBounds, ModelValue};
use crate::modelcheck::symbol::Symbol;
use serde_json::Value as JsonValue;
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};

/// Concrete runtime value used by source-first model checking.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum RuntimeValue {
    Unit,
    Bool(bool),
    Int(i128),
    Nat(u64),
    String(String),
    Enum {
        ty: String,
        variant: String,
        fields: BTreeMap<Symbol, RuntimeValue>,
    },
    Tuple(Vec<RuntimeValue>),
    Struct {
        ty: String,
        fields: BTreeMap<Symbol, RuntimeValue>,
    },
    Seq(Vec<RuntimeValue>),
    Set(BTreeSet<RuntimeValue>),
    Map(BTreeMap<RuntimeValue, RuntimeValue>),
}

/// Length limits for model-check collections.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RuntimeCollectionBounds {
    pub max_seq_len: usize,
    pub max_set_len: usize,
    pub max_map_len: usize,
}

impl From<&CollectionBounds> for RuntimeCollectionBounds {
    fn from(value: &CollectionBounds) -> Self {
        Self {
            max_seq_len: value.max_seq_len,
            max_set_len: value.max_set_len,
            max_map_len: value.max_map_len,
        }
    }
}

impl RuntimeValue {
    pub fn enum_value<I>(
        ty: impl Into<String>,
        variant: impl Into<String>,
        fields: I,
    ) -> TranspileResult<Self>
    where
        I: IntoIterator<Item = (String, RuntimeValue)>,
    {
        Ok(Self::Enum {
            ty: ty.into(),
            variant: variant.into(),
            fields: collect_named_fields(fields)?,
        })
    }

    pub fn struct_value<I>(ty: impl Into<String>, fields: I) -> TranspileResult<Self>
    where
        I: IntoIterator<Item = (String, RuntimeValue)>,
    {
        Ok(Self::Struct {
            ty: ty.into(),
            fields: collect_named_fields(fields)?,
        })
    }

    /// Construct an enum value with pre-interned Symbol keys.
    pub fn enum_value_sym<I>(
        ty: impl Into<String>,
        variant: impl Into<String>,
        fields: I,
    ) -> Self
    where
        I: IntoIterator<Item = (Symbol, RuntimeValue)>,
    {
        Self::Enum {
            ty: ty.into(),
            variant: variant.into(),
            fields: fields.into_iter().collect(),
        }
    }

    /// Construct a struct value with pre-interned Symbol keys.
    pub fn struct_value_sym<I>(ty: impl Into<String>, fields: I) -> Self
    where
        I: IntoIterator<Item = (Symbol, RuntimeValue)>,
    {
        Self::Struct {
            ty: ty.into(),
            fields: fields.into_iter().collect(),
        }
    }

    pub fn seq_bounded(
        values: Vec<RuntimeValue>,
        bounds: &RuntimeCollectionBounds,
    ) -> TranspileResult<Self> {
        if values.len() > bounds.max_seq_len {
            return Err(TranspileError::Config {
                message: format!(
                    "Model-check Seq value length {} exceeds configured max_seq_len {}.",
                    values.len(),
                    bounds.max_seq_len
                ),
            });
        }
        Ok(Self::Seq(values))
    }

    pub fn set_bounded<I>(values: I, bounds: &RuntimeCollectionBounds) -> TranspileResult<Self>
    where
        I: IntoIterator<Item = RuntimeValue>,
    {
        let mut set = BTreeSet::new();
        for value in values {
            set.insert(value);
            if set.len() > bounds.max_set_len {
                return Err(TranspileError::Config {
                    message: format!(
                        "Model-check Set value size {} exceeds configured max_set_len {}.",
                        set.len(),
                        bounds.max_set_len
                    ),
                });
            }
        }
        Ok(Self::Set(set))
    }

    pub fn map_bounded<I>(entries: I, bounds: &RuntimeCollectionBounds) -> TranspileResult<Self>
    where
        I: IntoIterator<Item = (RuntimeValue, RuntimeValue)>,
    {
        let mut map = BTreeMap::new();
        for (key, value) in entries {
            if map.insert(key.clone(), value).is_some() {
                return Err(TranspileError::Config {
                    message: format!(
                        "Model-check Map value has duplicate key `{}`.",
                        key.canonical_key()
                    ),
                });
            }
            if map.len() > bounds.max_map_len {
                return Err(TranspileError::Config {
                    message: format!(
                        "Model-check Map value size {} exceeds configured max_map_len {}.",
                        map.len(),
                        bounds.max_map_len
                    ),
                });
            }
        }
        Ok(Self::Map(map))
    }

    /// Access a field by string name (interns on each call — use `field_sym` in hot paths).
    pub fn field(&self, name: &str) -> Option<&RuntimeValue> {
        let sym = Symbol::intern(name);
        self.field_sym(sym)
    }

    /// Access a field by pre-interned Symbol (no allocation).
    pub fn field_sym(&self, sym: Symbol) -> Option<&RuntimeValue> {
        match self {
            RuntimeValue::Struct { fields, .. } | RuntimeValue::Enum { fields, .. } => {
                fields.get(&sym)
            }
            _ => None,
        }
    }

    pub fn element_at(&self, index: usize) -> Option<&RuntimeValue> {
        match self {
            RuntimeValue::Tuple(items) | RuntimeValue::Seq(items) => items.get(index),
            _ => None,
        }
    }

    /// Compute a 64-bit fingerprint by streaming the value structure directly
    /// into a hasher, without building an intermediate String. Produces the
    /// same hash as hashing `canonical_key()` would logically imply (same
    /// structural ordering guarantees), but avoids all String allocations.
    ///
    /// For struct/enum fields: hashes fields sorted alphabetically by name
    /// (matching `canonical_key()`'s deterministic output).
    pub fn fingerprint(&self) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.hash_into(&mut hasher);
        hasher.finish()
    }

    /// Stream this value's canonical representation into the given hasher.
    /// Field order is alphabetical (by resolved symbol name) for determinism.
    fn hash_into(&self, h: &mut impl Hasher) {
        // Discriminant tag
        std::mem::discriminant(self).hash(h);
        match self {
            RuntimeValue::Unit => {}
            RuntimeValue::Bool(v) => v.hash(h),
            RuntimeValue::Int(v) => v.hash(h),
            RuntimeValue::Nat(v) => v.hash(h),
            RuntimeValue::String(v) => v.hash(h),
            RuntimeValue::Enum {
                ty,
                variant,
                fields,
            } => {
                ty.hash(h);
                variant.hash(h);
                // Sort fields by name for determinism
                let mut sorted: Vec<_> = fields.iter().collect();
                sorted.sort_by_key(|(k, _)| k.resolve());
                for (k, v) in sorted {
                    k.resolve().hash(h);
                    v.hash_into(h);
                }
            }
            RuntimeValue::Tuple(items) => {
                items.len().hash(h);
                for item in items {
                    item.hash_into(h);
                }
            }
            RuntimeValue::Struct { ty, fields } => {
                ty.hash(h);
                // Sort fields by name for determinism
                let mut sorted: Vec<_> = fields.iter().collect();
                sorted.sort_by_key(|(k, _)| k.resolve());
                for (k, v) in sorted {
                    k.resolve().hash(h);
                    v.hash_into(h);
                }
            }
            RuntimeValue::Seq(items) => {
                items.len().hash(h);
                for item in items {
                    item.hash_into(h);
                }
            }
            RuntimeValue::Set(items) => {
                items.len().hash(h);
                for item in items {
                    item.hash_into(h);
                }
            }
            RuntimeValue::Map(entries) => {
                entries.len().hash(h);
                for (k, v) in entries {
                    k.hash_into(h);
                    v.hash_into(h);
                }
            }
        }
    }

    /// Deterministic string key for future canonical-state hashing.
    pub fn canonical_key(&self) -> String {
        match self {
            RuntimeValue::Unit => "unit".to_string(),
            RuntimeValue::Bool(v) => format!("bool:{v}"),
            RuntimeValue::Int(v) => format!("int:{v}"),
            RuntimeValue::Nat(v) => format!("nat:{v}"),
            RuntimeValue::String(v) => format!("str:{v:?}"),
            RuntimeValue::Enum {
                ty,
                variant,
                fields,
            } => {
                // Sort by field name string for deterministic output
                let mut entries: Vec<_> = fields
                    .iter()
                    .map(|(k, v)| (k.resolve(), v.canonical_key()))
                    .collect();
                entries.sort_by(|a, b| a.0.cmp(&b.0));
                let rendered = entries
                    .iter()
                    .map(|(k, v)| format!("{k}:{v}"))
                    .collect::<Vec<_>>()
                    .join(",");
                format!("enum:{ty}::{variant}{{{rendered}}}")
            }
            RuntimeValue::Tuple(items) => {
                let rendered = items
                    .iter()
                    .map(RuntimeValue::canonical_key)
                    .collect::<Vec<_>>()
                    .join(",");
                format!("tuple:({rendered})")
            }
            RuntimeValue::Struct { ty, fields } => {
                // Sort by field name string for deterministic output
                let mut entries: Vec<_> = fields
                    .iter()
                    .map(|(k, v)| (k.resolve(), v.canonical_key()))
                    .collect();
                entries.sort_by(|a, b| a.0.cmp(&b.0));
                let rendered = entries
                    .iter()
                    .map(|(k, v)| format!("{k}:{v}"))
                    .collect::<Vec<_>>()
                    .join(",");
                format!("struct:{ty}{{{rendered}}}")
            }
            RuntimeValue::Seq(items) => {
                let rendered = items
                    .iter()
                    .map(RuntimeValue::canonical_key)
                    .collect::<Vec<_>>()
                    .join(",");
                format!("seq:[{rendered}]")
            }
            RuntimeValue::Set(items) => {
                let rendered = items
                    .iter()
                    .map(RuntimeValue::canonical_key)
                    .collect::<Vec<_>>()
                    .join(",");
                format!("set:{{{rendered}}}")
            }
            RuntimeValue::Map(entries) => {
                let rendered = entries
                    .iter()
                    .map(|(k, v)| format!("{}=>{}", k.canonical_key(), v.canonical_key()))
                    .collect::<Vec<_>>()
                    .join(",");
                format!("map:{{{rendered}}}")
            }
        }
    }

    /// Convert to the canonical JSON representation defined in
    /// `docs/cross-engine-state-normalization.md`.
    ///
    /// Records/structs become JSON objects with alphabetically sorted fields
    /// (type name is dropped). Enums become objects with a `_variant` key.
    /// Sets become sorted arrays. Maps become sorted `[key, value]` pair arrays.
    pub fn to_canonical_json(&self) -> JsonValue {
        match self {
            RuntimeValue::Unit => JsonValue::Null,
            RuntimeValue::Bool(v) => JsonValue::Bool(*v),
            RuntimeValue::Int(v) => serde_json::json!(*v),
            RuntimeValue::Nat(v) => serde_json::json!(*v),
            RuntimeValue::String(v) => JsonValue::String(v.clone()),
            RuntimeValue::Enum {
                variant, fields, ..
            } => {
                let mut obj = serde_json::Map::new();
                obj.insert("_variant".to_string(), JsonValue::String(variant.clone()));
                for (k, v) in fields {
                    obj.insert(k.resolve(), v.to_canonical_json());
                }
                JsonValue::Object(obj)
            }
            RuntimeValue::Tuple(items) => {
                JsonValue::Array(items.iter().map(|v| v.to_canonical_json()).collect())
            }
            RuntimeValue::Struct { fields, .. } => {
                // Symbols are ordered by intern-id; re-sort by name for stable JSON
                let mut obj: serde_json::Map<String, JsonValue> = fields
                    .iter()
                    .map(|(k, v)| (k.resolve(), v.to_canonical_json()))
                    .collect();
                obj.sort_keys();
                JsonValue::Object(obj)
            }
            RuntimeValue::Seq(items) => {
                JsonValue::Array(items.iter().map(|v| v.to_canonical_json()).collect())
            }
            RuntimeValue::Set(items) => {
                // BTreeSet is already canonically sorted
                JsonValue::Array(items.iter().map(|v| v.to_canonical_json()).collect())
            }
            RuntimeValue::Map(entries) => {
                // BTreeMap is already sorted by key
                JsonValue::Array(
                    entries
                        .iter()
                        .map(|(k, v)| {
                            JsonValue::Array(vec![k.to_canonical_json(), v.to_canonical_json()])
                        })
                        .collect(),
                )
            }
        }
    }
}

impl From<ModelValue> for RuntimeValue {
    fn from(value: ModelValue) -> Self {
        match value {
            ModelValue::Bool(v) => RuntimeValue::Bool(v),
            ModelValue::Int(v) => RuntimeValue::Int(v.into()),
            ModelValue::String(v) => RuntimeValue::String(v),
        }
    }
}

impl From<&ModelValue> for RuntimeValue {
    fn from(value: &ModelValue) -> Self {
        match value {
            ModelValue::Bool(v) => RuntimeValue::Bool(*v),
            ModelValue::Int(v) => RuntimeValue::Int((*v).into()),
            ModelValue::String(v) => RuntimeValue::String(v.clone()),
        }
    }
}

fn collect_named_fields<I>(fields: I) -> TranspileResult<BTreeMap<Symbol, RuntimeValue>>
where
    I: IntoIterator<Item = (String, RuntimeValue)>,
{
    let mut out = BTreeMap::new();
    for (name, value) in fields {
        let sym = Symbol::intern(&name);
        if out.insert(sym, value).is_some() {
            return Err(TranspileError::Config {
                message: format!(
                    "Model-check value contains duplicate field `{}` in named fields.",
                    name
                ),
            });
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bounds() -> RuntimeCollectionBounds {
        RuntimeCollectionBounds {
            max_seq_len: 2,
            max_set_len: 2,
            max_map_len: 2,
        }
    }

    #[test]
    fn test_model_value_conversion() {
        assert_eq!(
            RuntimeValue::from(ModelValue::Bool(true)),
            RuntimeValue::Bool(true)
        );
        assert_eq!(
            RuntimeValue::from(ModelValue::Int(-3)),
            RuntimeValue::Int(-3)
        );
        assert_eq!(
            RuntimeValue::from(ModelValue::String("x".to_string())),
            RuntimeValue::String("x".to_string())
        );
    }

    #[test]
    fn test_seq_bounded_respects_limit() {
        let ok =
            RuntimeValue::seq_bounded(vec![RuntimeValue::Int(1), RuntimeValue::Int(2)], &bounds())
                .unwrap();
        assert!(matches!(ok, RuntimeValue::Seq(values) if values.len() == 2));

        let err = RuntimeValue::seq_bounded(
            vec![
                RuntimeValue::Int(1),
                RuntimeValue::Int(2),
                RuntimeValue::Int(3),
            ],
            &bounds(),
        )
        .unwrap_err();
        assert!(err.to_string().contains("max_seq_len"));
    }

    #[test]
    fn test_set_bounded_respects_limit_after_dedup() {
        let set = RuntimeValue::set_bounded(
            vec![
                RuntimeValue::Int(1),
                RuntimeValue::Int(1),
                RuntimeValue::Int(2),
            ],
            &bounds(),
        )
        .unwrap();
        assert!(matches!(set, RuntimeValue::Set(values) if values.len() == 2));

        let err = RuntimeValue::set_bounded(
            vec![
                RuntimeValue::Int(1),
                RuntimeValue::Int(2),
                RuntimeValue::Int(3),
            ],
            &bounds(),
        )
        .unwrap_err();
        assert!(err.to_string().contains("max_set_len"));
    }

    #[test]
    fn test_map_bounded_rejects_duplicate_keys() {
        let err = RuntimeValue::map_bounded(
            vec![
                (RuntimeValue::Int(1), RuntimeValue::Bool(true)),
                (RuntimeValue::Int(1), RuntimeValue::Bool(false)),
            ],
            &bounds(),
        )
        .unwrap_err();
        assert!(err.to_string().contains("duplicate key"));
    }

    #[test]
    fn test_map_bounded_rejects_oversized_maps() {
        let err = RuntimeValue::map_bounded(
            vec![
                (RuntimeValue::Int(1), RuntimeValue::Bool(true)),
                (RuntimeValue::Int(2), RuntimeValue::Bool(false)),
                (RuntimeValue::Int(3), RuntimeValue::Bool(true)),
            ],
            &bounds(),
        )
        .unwrap_err();
        assert!(err.to_string().contains("max_map_len"));
    }

    #[test]
    fn test_named_field_constructors_reject_duplicates() {
        let struct_err = RuntimeValue::struct_value(
            "State",
            vec![
                ("x".to_string(), RuntimeValue::Int(1)),
                ("x".to_string(), RuntimeValue::Int(2)),
            ],
        )
        .unwrap_err();
        assert!(struct_err.to_string().contains("duplicate field"));

        let enum_err = RuntimeValue::enum_value(
            "Msg",
            "Prepare",
            vec![
                ("term".to_string(), RuntimeValue::Nat(1)),
                ("term".to_string(), RuntimeValue::Nat(2)),
            ],
        )
        .unwrap_err();
        assert!(enum_err.to_string().contains("duplicate field"));
    }

    #[test]
    fn test_field_and_index_accessors() {
        let value =
            RuntimeValue::struct_value("State", vec![("count".to_string(), RuntimeValue::Int(7))])
                .unwrap();
        assert_eq!(value.field("count"), Some(&RuntimeValue::Int(7)));
        assert_eq!(value.field("missing"), None);

        let seq = RuntimeValue::seq_bounded(
            vec![RuntimeValue::Bool(false), RuntimeValue::Bool(true)],
            &bounds(),
        )
        .unwrap();
        assert_eq!(seq.element_at(1), Some(&RuntimeValue::Bool(true)));
        assert_eq!(seq.element_at(2), None);
    }

    #[test]
    fn test_to_canonical_json_struct_drops_type_name() {
        let state = RuntimeValue::struct_value(
            "LState",
            vec![
                ("b".to_string(), RuntimeValue::Int(2)),
                ("a".to_string(), RuntimeValue::Int(1)),
            ],
        )
        .unwrap();
        let json = state.to_canonical_json();
        // Fields sorted alphabetically, type name dropped
        assert_eq!(json, serde_json::json!({"a": 1, "b": 2}));
    }

    #[test]
    fn test_to_canonical_json_enum_has_variant_tag() {
        use std::collections::BTreeMap;
        let val = RuntimeValue::Enum {
            ty: "TMState".to_string(),
            variant: "Committed".to_string(),
            fields: BTreeMap::new(),
        };
        assert_eq!(
            val.to_canonical_json(),
            serde_json::json!({"_variant": "Committed"})
        );
    }

    #[test]
    fn test_to_canonical_json_nested() {
        use std::collections::BTreeMap;
        let inner_enum = RuntimeValue::Enum {
            ty: "TMState".to_string(),
            variant: "Init".to_string(),
            fields: BTreeMap::new(),
        };
        let set = RuntimeValue::Set(
            vec![RuntimeValue::Int(1), RuntimeValue::Int(0)]
                .into_iter()
                .collect(),
        );
        let state = RuntimeValue::struct_value(
            "LState",
            vec![
                ("tm_state".to_string(), inner_enum),
                ("prepared".to_string(), set),
            ],
        )
        .unwrap();
        let json = state.to_canonical_json();
        assert_eq!(
            json,
            serde_json::json!({
                "prepared": [0, 1],
                "tm_state": {"_variant": "Init"},
            })
        );
    }

    #[test]
    fn test_canonical_key_is_stable_for_set_and_map() {
        let left_set =
            RuntimeValue::set_bounded(vec![RuntimeValue::Int(2), RuntimeValue::Int(1)], &bounds())
                .unwrap();
        let right_set =
            RuntimeValue::set_bounded(vec![RuntimeValue::Int(1), RuntimeValue::Int(2)], &bounds())
                .unwrap();
        assert_eq!(left_set.canonical_key(), right_set.canonical_key());

        let left_map = RuntimeValue::map_bounded(
            vec![
                (RuntimeValue::Int(2), RuntimeValue::Bool(false)),
                (RuntimeValue::Int(1), RuntimeValue::Bool(true)),
            ],
            &bounds(),
        )
        .unwrap();
        let right_map = RuntimeValue::map_bounded(
            vec![
                (RuntimeValue::Int(1), RuntimeValue::Bool(true)),
                (RuntimeValue::Int(2), RuntimeValue::Bool(false)),
            ],
            &bounds(),
        )
        .unwrap();
        assert_eq!(left_map.canonical_key(), right_map.canonical_key());
    }

    #[test]
    fn test_fingerprint_deterministic_for_same_value() {
        let a = RuntimeValue::struct_value(
            "State",
            vec![
                ("x".to_string(), RuntimeValue::Int(42)),
                ("y".to_string(), RuntimeValue::Bool(true)),
            ],
        )
        .unwrap();
        let b = RuntimeValue::struct_value(
            "State",
            vec![
                ("x".to_string(), RuntimeValue::Int(42)),
                ("y".to_string(), RuntimeValue::Bool(true)),
            ],
        )
        .unwrap();
        assert_eq!(a.fingerprint(), b.fingerprint());
    }

    #[test]
    fn test_fingerprint_differs_for_different_values() {
        let a = RuntimeValue::struct_value(
            "State",
            vec![("x".to_string(), RuntimeValue::Int(1))],
        )
        .unwrap();
        let b = RuntimeValue::struct_value(
            "State",
            vec![("x".to_string(), RuntimeValue::Int(2))],
        )
        .unwrap();
        assert_ne!(a.fingerprint(), b.fingerprint());
    }

    #[test]
    fn test_fingerprint_field_order_independent() {
        // Fields inserted in different order should produce the same fingerprint
        // (since fingerprint sorts by field name)
        let a = RuntimeValue::struct_value(
            "State",
            vec![
                ("alpha".to_string(), RuntimeValue::Int(1)),
                ("beta".to_string(), RuntimeValue::Int(2)),
            ],
        )
        .unwrap();
        let b = RuntimeValue::struct_value(
            "State",
            vec![
                ("beta".to_string(), RuntimeValue::Int(2)),
                ("alpha".to_string(), RuntimeValue::Int(1)),
            ],
        )
        .unwrap();
        assert_eq!(a.fingerprint(), b.fingerprint());
    }

    #[test]
    fn test_fingerprint_set_order_independent() {
        let a =
            RuntimeValue::set_bounded(vec![RuntimeValue::Int(2), RuntimeValue::Int(1)], &bounds())
                .unwrap();
        let b =
            RuntimeValue::set_bounded(vec![RuntimeValue::Int(1), RuntimeValue::Int(2)], &bounds())
                .unwrap();
        assert_eq!(a.fingerprint(), b.fingerprint());
    }

    #[test]
    fn test_fingerprint_type_discriminant_matters() {
        // Int(1) vs Nat(1) should differ
        let a = RuntimeValue::Int(1);
        let b = RuntimeValue::Nat(1);
        assert_ne!(a.fingerprint(), b.fingerprint());
    }
}
