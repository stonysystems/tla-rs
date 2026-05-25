//! Re-export from `transpiler-runtime` plus bridge impls.
//!
//! The canonical value types live in `transpiler_runtime::value`.
//! This module re-exports them and adds `From` impls that bridge
//! transpiler-specific types (`CollectionBounds`, `ModelValue`)
//! to the runtime types.

pub use transpiler_runtime::value::*;

use crate::error::TranspileError;
use crate::modelcheck::config::{CollectionBounds, ModelValue};

// ── Bridge: RuntimeError → TranspileError ────────────────────────────

impl From<RuntimeError> for TranspileError {
    fn from(e: RuntimeError) -> Self {
        TranspileError::Config { message: e.message }
    }
}

// ── Bridge: CollectionBounds → RuntimeCollectionBounds ────────────────

impl From<&CollectionBounds> for RuntimeCollectionBounds {
    fn from(value: &CollectionBounds) -> Self {
        Self {
            max_seq_len: value.max_seq_len,
            max_set_len: value.max_set_len,
            max_map_len: value.max_map_len,
        }
    }
}

// ── Bridge: ModelValue → RuntimeValue ────────────────────────────────

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

#[cfg(test)]
mod tests {
    use super::*;

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
    fn test_collection_bounds_bridge() {
        let cb = CollectionBounds {
            max_seq_len: 10,
            max_set_len: 20,
            max_map_len: 30,
        };
        let rcb = RuntimeCollectionBounds::from(&cb);
        assert_eq!(rcb.max_seq_len, 10);
        assert_eq!(rcb.max_set_len, 20);
        assert_eq!(rcb.max_map_len, 30);
    }

    #[test]
    fn test_runtime_error_to_transpile_error() {
        let re = RuntimeError {
            message: "test".to_string(),
        };
        let te: TranspileError = re.into();
        assert!(matches!(te, TranspileError::Config { message } if message == "test"));
    }
}
