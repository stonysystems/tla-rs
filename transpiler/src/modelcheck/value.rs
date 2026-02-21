use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::config::{CollectionBounds, ModelValue};
use std::collections::{BTreeMap, BTreeSet};

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
        fields: BTreeMap<String, RuntimeValue>,
    },
    Tuple(Vec<RuntimeValue>),
    Struct {
        ty: String,
        fields: BTreeMap<String, RuntimeValue>,
    },
    Seq(Vec<RuntimeValue>),
    Set(BTreeSet<RuntimeValue>),
    Map(BTreeMap<RuntimeValue, RuntimeValue>),
}

/// Length limits for model-check collections.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

    pub fn field(&self, name: &str) -> Option<&RuntimeValue> {
        match self {
            RuntimeValue::Struct { fields, .. } | RuntimeValue::Enum { fields, .. } => {
                fields.get(name)
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
                let rendered = fields
                    .iter()
                    .map(|(k, v)| format!("{k}:{}", v.canonical_key()))
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
                let rendered = fields
                    .iter()
                    .map(|(k, v)| format!("{k}:{}", v.canonical_key()))
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

fn collect_named_fields<I>(fields: I) -> TranspileResult<BTreeMap<String, RuntimeValue>>
where
    I: IntoIterator<Item = (String, RuntimeValue)>,
{
    let mut out = BTreeMap::new();
    for (name, value) in fields {
        if out.insert(name.clone(), value).is_some() {
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
}
