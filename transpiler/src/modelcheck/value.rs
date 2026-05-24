use crate::error::{TranspileError, TranspileResult};
use crate::modelcheck::config::{CollectionBounds, ModelValue};
use crate::modelcheck::symbol::Symbol;
use serde_json::Value as JsonValue;
use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// Sorted vector of named fields, replacement for `BTreeMap<Symbol, RuntimeValue>`.
///
/// Fields are kept sorted by `Symbol` (intern-id order) so that
/// `PartialEq`/`Ord`/`Hash` are deterministic and consistent with the
/// former `BTreeMap` representation. Typical struct sizes (3-10 fields)
/// make linear-scan lookups and insertion-sort cheaper than B-tree node
/// allocation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NamedFields(Vec<(Symbol, RuntimeValue)>);

impl NamedFields {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self(Vec::with_capacity(cap))
    }

    pub fn get(&self, key: &Symbol) -> Option<&RuntimeValue> {
        let i = self.0.partition_point(|(k, _)| k < key);
        self.0.get(i).filter(|(k, _)| k == key).map(|(_, v)| v)
    }

    pub fn get_mut(&mut self, key: &Symbol) -> Option<&mut RuntimeValue> {
        let i = self.0.partition_point(|(k, _)| k < key);
        self.0.get_mut(i).filter(|(k, _)| k == key).map(|(_, v)| v)
    }

    /// Insert a field. Returns the previous value if the key already existed.
    /// Maintains sorted order by Symbol.
    pub fn insert(&mut self, key: Symbol, value: RuntimeValue) -> Option<RuntimeValue> {
        let pos = self.0.partition_point(|(k, _)| *k < key);
        if let Some(entry) = self.0.get_mut(pos).filter(|(k, _)| *k == key) {
            Some(std::mem::replace(&mut entry.1, value))
        } else {
            self.0.insert(pos, (key, value));
            None
        }
    }

    pub fn contains_key(&self, key: &Symbol) -> bool {
        let i = self.0.partition_point(|(k, _)| k < key);
        self.0.get(i).is_some_and(|(k, _)| k == key)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Symbol, &RuntimeValue)> + '_ {
        self.0.iter().map(|(k, v)| (k, v))
    }

    pub fn keys(&self) -> impl Iterator<Item = &Symbol> + '_ {
        self.0.iter().map(|(k, _)| k)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl std::iter::FromIterator<(Symbol, RuntimeValue)> for NamedFields {
    fn from_iter<I: IntoIterator<Item = (Symbol, RuntimeValue)>>(iter: I) -> Self {
        let mut v: Vec<(Symbol, RuntimeValue)> = iter.into_iter().collect();
        v.sort_by_key(|(k, _)| *k);
        Self(v)
    }
}

impl IntoIterator for NamedFields {
    type Item = (Symbol, RuntimeValue);
    type IntoIter = std::vec::IntoIter<(Symbol, RuntimeValue)>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a NamedFields {
    type Item = (&'a Symbol, &'a RuntimeValue);
    type IntoIter = std::iter::Map<
        std::slice::Iter<'a, (Symbol, RuntimeValue)>,
        fn(&'a (Symbol, RuntimeValue)) -> (&'a Symbol, &'a RuntimeValue),
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().map(|(k, v)| (k, v))
    }
}

/// Memoization cell for `fingerprint()`.  Transparent to `Eq`/`Ord`/`Clone`:
/// two `FingerprintCache` values are always equal, and cloning preserves the
/// cached hash so that a clone of an already-fingerprinted value skips
/// recomputation.
#[derive(Debug, Clone)]
pub(crate) struct FingerprintCache(Cell<u64>);

/// Sentinel: 0 means "not yet computed".  If a real hash happens to be 0 we
/// recompute each time — negligible cost in practice.
const FINGERPRINT_NOT_COMPUTED: u64 = 0;

impl FingerprintCache {
    fn new() -> Self {
        Self(Cell::new(FINGERPRINT_NOT_COMPUTED))
    }
    fn get(&self) -> Option<u64> {
        let v = self.0.get();
        if v != FINGERPRINT_NOT_COMPUTED {
            Some(v)
        } else {
            None
        }
    }
    fn set(&self, hash: u64) {
        // If the real hash is 0, don't store it — we'll recompute next time.
        if hash != FINGERPRINT_NOT_COMPUTED {
            self.0.set(hash);
        }
    }
    /// Invalidate the cached hash (e.g. after mutation).
    fn invalidate(&self) {
        self.0.set(FINGERPRINT_NOT_COMPUTED);
    }
}

// FingerprintCache is semantically invisible — always equal, always Eq::Equal.
impl PartialEq for FingerprintCache {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}
impl Eq for FingerprintCache {}
impl PartialOrd for FingerprintCache {
    fn partial_cmp(&self, _other: &Self) -> Option<Ordering> {
        Some(Ordering::Equal)
    }
}
impl Ord for FingerprintCache {
    fn cmp(&self, _other: &Self) -> Ordering {
        Ordering::Equal
    }
}

/// Concrete runtime value used by source-first model checking.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[allow(private_interfaces)]
pub enum RuntimeValue {
    Unit,
    Bool(bool),
    Int(i128),
    Nat(u64),
    String(String),
    Enum {
        ty: String,
        variant: String,
        fields: NamedFields,
        #[doc(hidden)]
        _cache: FingerprintCache,
    },
    Tuple(Vec<RuntimeValue>),
    Struct {
        ty: String,
        fields: NamedFields,
        #[doc(hidden)]
        _cache: FingerprintCache,
    },
    Seq(Arc<Vec<RuntimeValue>>),
    Set(Arc<SetRepr>),
    Map(Arc<BTreeMap<RuntimeValue, RuntimeValue>>),
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
            _cache: FingerprintCache::new(),
        })
    }

    pub fn struct_value<I>(ty: impl Into<String>, fields: I) -> TranspileResult<Self>
    where
        I: IntoIterator<Item = (String, RuntimeValue)>,
    {
        Ok(Self::Struct {
            ty: ty.into(),
            fields: collect_named_fields(fields)?,
            _cache: FingerprintCache::new(),
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
            _cache: FingerprintCache::new(),
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
            _cache: FingerprintCache::new(),
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
        Ok(Self::Seq(Arc::new(values)))
    }

    pub fn set_bounded<I>(values: I, bounds: &RuntimeCollectionBounds) -> TranspileResult<Self>
    where
        I: IntoIterator<Item = RuntimeValue>,
    {
        let mut repr = SetRepr::new();
        for value in values {
            repr.insert(value);
            if repr.len() > bounds.max_set_len {
                return Err(TranspileError::Config {
                    message: format!(
                        "Model-check Set value size {} exceeds configured max_set_len {}.",
                        repr.len(),
                        bounds.max_set_len
                    ),
                });
            }
        }
        Ok(Self::Set(Arc::new(repr)))
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
        Ok(Self::Map(Arc::new(map)))
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
            RuntimeValue::Tuple(items) => items.get(index),
            RuntimeValue::Seq(items) => items.get(index),
            _ => None,
        }
    }

    /// Compute a 64-bit fingerprint for within-run state deduplication.
    ///
    /// Hashes the value structure directly into a hasher without building an
    /// intermediate String. Struct/Enum fields are hashed in intern-id order
    /// (deterministic within a run, zero allocations). For cross-run
    /// deterministic output, use `canonical_key()` instead.
    ///
    /// For `Struct` and `Enum` variants the result is memoized: the first call
    /// computes the hash and subsequent calls return the cached value in O(1).
    /// The cache is preserved through `Clone`.
    pub fn fingerprint(&self) -> u64 {
        // Check cache for Struct/Enum variants
        match self {
            RuntimeValue::Struct { _cache, .. } | RuntimeValue::Enum { _cache, .. } => {
                if let Some(cached) = _cache.get() {
                    return cached;
                }
            }
            _ => {}
        }

        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.hash_into(&mut hasher);
        let hash = hasher.finish();

        // Store in cache for Struct/Enum variants
        match self {
            RuntimeValue::Struct { _cache, .. } | RuntimeValue::Enum { _cache, .. } => {
                _cache.set(hash);
            }
            _ => {}
        }

        hash
    }

    /// Invalidate the memoized fingerprint hash (call after in-place mutation).
    pub fn invalidate_fingerprint_cache(&self) {
        match self {
            RuntimeValue::Struct { _cache, .. } | RuntimeValue::Enum { _cache, .. } => {
                _cache.invalidate();
            }
            _ => {}
        }
    }

    /// Stream this value into the given hasher for within-run deduplication.
    ///
    /// Struct/Enum fields are hashed in intern-id order (the order stored in
    /// `NamedFields`). This is deterministic within a single model-check run
    /// and avoids the Vec allocation + sort that name-based ordering required.
    /// For cross-run deterministic output, use `canonical_key()` instead.
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
                ..
            } => {
                ty.hash(h);
                variant.hash(h);
                for (k, v) in fields.iter() {
                    k.hash(h);
                    v.hash_into(h);
                }
            }
            RuntimeValue::Tuple(items) => {
                items.len().hash(h);
                for item in items {
                    item.hash_into(h);
                }
            }
            RuntimeValue::Struct { ty, fields, .. } => {
                ty.hash(h);
                for (k, v) in fields.iter() {
                    k.hash(h);
                    v.hash_into(h);
                }
            }
            RuntimeValue::Seq(items) => {
                items.len().hash(h);
                for item in items.iter() {
                    item.hash_into(h);
                }
            }
            RuntimeValue::Set(repr) => {
                repr.len().hash(h);
                for item in repr.iter() {
                    item.hash_into(h);
                }
            }
            RuntimeValue::Map(entries) => {
                entries.len().hash(h);
                for (k, v) in entries.iter() {
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
                ..
            } => {
                // Sort by field name for deterministic output
                let mut sorted: Vec<_> = fields.iter().collect();
                sorted.sort_by(|(a, _), (b, _)| a.cmp_by_name(b));
                let rendered = sorted
                    .iter()
                    .map(|(k, v)| format!("{}:{}", k.as_str(), v.canonical_key()))
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
            RuntimeValue::Struct { ty, fields, .. } => {
                // Sort by field name for deterministic output
                let mut sorted: Vec<_> = fields.iter().collect();
                sorted.sort_by(|(a, _), (b, _)| a.cmp_by_name(b));
                let rendered = sorted
                    .iter()
                    .map(|(k, v)| format!("{}:{}", k.as_str(), v.canonical_key()))
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
            RuntimeValue::Set(repr) => {
                let rendered = repr
                    .iter()
                    .map(|v| v.canonical_key())
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
            RuntimeValue::Set(repr) => {
                // SetRepr iter yields elements in ascending order
                JsonValue::Array(repr.iter().map(|v| v.to_canonical_json()).collect())
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

fn collect_named_fields<I>(fields: I) -> TranspileResult<NamedFields>
where
    I: IntoIterator<Item = (String, RuntimeValue)>,
{
    let mut out = NamedFields::new();
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

// ── SetRepr: dual-representation set ─────────────────────────────────

use crate::modelcheck::small_int_set::SmallIntSet;

/// Dual-representation set: either a general `BTreeSet<RuntimeValue>` or
/// a bitmap-packed `SmallIntSet` when all elements are small integers.
///
/// This is a drop-in replacement for `BTreeSet<RuntimeValue>` in
/// `RuntimeValue::Set`.  All operations dispatch to the appropriate
/// representation transparently.
#[derive(Debug, Clone)]
pub enum SetRepr {
    /// General representation: arbitrary `RuntimeValue` elements.
    General(BTreeSet<RuntimeValue>),
    /// Packed representation: all elements are `RuntimeValue::Int(n)` and
    /// fit in a 64-wide bitmap.
    SmallInt(SmallIntSet),
}

impl SetRepr {
    /// Create an empty general set.
    pub fn new() -> Self {
        SetRepr::General(BTreeSet::new())
    }

    /// Try to create a `SmallInt` set from an iterator of `RuntimeValue`.
    /// Returns `General` if any element is not `Int` or the range exceeds 64.
    pub fn from_values(values: impl IntoIterator<Item = RuntimeValue>) -> Self {
        let values: Vec<RuntimeValue> = values.into_iter().collect();
        // Try SmallInt path: all must be Int and fit in 64-wide range.
        let ints: Option<Vec<i128>> = values
            .iter()
            .map(|v| match v {
                RuntimeValue::Int(n) => Some(*n),
                _ => None,
            })
            .collect();
        if let Some(ints) = ints {
            if let Some(small) = SmallIntSet::try_from_iter(ints) {
                return SetRepr::SmallInt(small);
            }
        }
        SetRepr::General(values.into_iter().collect())
    }

    /// Number of elements.
    pub fn len(&self) -> usize {
        match self {
            SetRepr::General(s) => s.len(),
            SetRepr::SmallInt(s) => s.len(),
        }
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        match self {
            SetRepr::General(s) => s.is_empty(),
            SetRepr::SmallInt(s) => s.is_empty(),
        }
    }

    /// Check membership.
    pub fn contains(&self, value: &RuntimeValue) -> bool {
        match (self, value) {
            (SetRepr::SmallInt(s), RuntimeValue::Int(n)) => s.contains(*n),
            (SetRepr::SmallInt(_), _) => false,
            (SetRepr::General(s), _) => s.contains(value),
        }
    }

    /// Insert an element. Returns `true` if the element was newly added.
    ///
    /// If the current representation is `SmallInt` and the new element
    /// doesn't fit, the set is promoted to `General`.
    pub fn insert(&mut self, value: RuntimeValue) -> bool {
        match self {
            SetRepr::SmallInt(s) => {
                if let RuntimeValue::Int(n) = &value {
                    match s.insert(*n) {
                        Ok(was_new) => return was_new,
                        Err(_) => {
                            // Out of range — promote to General
                            let mut general: BTreeSet<RuntimeValue> =
                                s.iter().map(RuntimeValue::Int).collect();
                            let was_new = general.insert(value);
                            *self = SetRepr::General(general);
                            return was_new;
                        }
                    }
                }
                // Non-int element — promote to General
                let mut general: BTreeSet<RuntimeValue> =
                    s.iter().map(RuntimeValue::Int).collect();
                let was_new = general.insert(value);
                *self = SetRepr::General(general);
                was_new
            }
            SetRepr::General(s) => s.insert(value),
        }
    }

    /// Remove an element. Returns `true` if the element was present.
    pub fn remove(&mut self, value: &RuntimeValue) -> bool {
        match (self as &mut SetRepr, value) {
            (SetRepr::SmallInt(s), RuntimeValue::Int(n)) => s.remove(*n),
            (SetRepr::SmallInt(_), _) => false,
            (SetRepr::General(s), _) => s.remove(value),
        }
    }

    /// Set union. Returns a new set.
    pub fn union(&self, other: &SetRepr) -> SetRepr {
        match (self, other) {
            (SetRepr::SmallInt(a), SetRepr::SmallInt(b)) => {
                // Try to merge into a single SmallIntSet
                if let Some(merged) = SmallIntSet::try_from_iter(a.iter().chain(b.iter())) {
                    return SetRepr::SmallInt(merged);
                }
                let combined: BTreeSet<RuntimeValue> =
                    self.iter().chain(other.iter()).collect();
                SetRepr::General(combined)
            }
            _ => {
                let combined: BTreeSet<RuntimeValue> =
                    self.iter().chain(other.iter()).collect();
                SetRepr::General(combined)
            }
        }
    }

    /// Set difference (self \ other). Returns a new set.
    pub fn difference(&self, other: &SetRepr) -> SetRepr {
        match (self, other) {
            (SetRepr::SmallInt(a), SetRepr::SmallInt(b)) => {
                // Difference can only shrink, so result fits in a's range.
                // Rebuild with shared offset from a.
                let result_ints: Vec<i128> = a.iter().filter(|n| !b.contains(*n)).collect();
                SetRepr::SmallInt(
                    SmallIntSet::try_from_iter(result_ints).unwrap_or_else(|| SmallIntSet::empty()),
                )
            }
            _ => {
                let result: BTreeSet<RuntimeValue> = self
                    .iter()
                    .filter(|v| !other.contains(v))
                    .collect();
                SetRepr::General(result)
            }
        }
    }

    /// Set intersection. Returns a new set.
    pub fn intersection(&self, other: &SetRepr) -> SetRepr {
        match (self, other) {
            (SetRepr::SmallInt(a), SetRepr::SmallInt(b)) => {
                // Intersection can only shrink, fits in either's range.
                let result_ints: Vec<i128> = a.iter().filter(|n| b.contains(*n)).collect();
                SetRepr::SmallInt(
                    SmallIntSet::try_from_iter(result_ints).unwrap_or_else(|| SmallIntSet::empty()),
                )
            }
            _ => {
                let result: BTreeSet<RuntimeValue> = self
                    .iter()
                    .filter(|v| other.contains(v))
                    .collect();
                SetRepr::General(result)
            }
        }
    }

    /// Iterate over elements in ascending order.
    ///
    /// For `SmallInt`, elements are yielded as `RuntimeValue::Int(n)`.
    pub fn iter(&self) -> SetReprIter<'_> {
        match self {
            SetRepr::General(s) => SetReprIter::General(s.iter()),
            SetRepr::SmallInt(s) => SetReprIter::SmallInt(s.iter()),
        }
    }

    /// Convert to a `BTreeSet<RuntimeValue>` (materializes SmallInt elements).
    pub fn to_btree_set(&self) -> BTreeSet<RuntimeValue> {
        match self {
            SetRepr::General(s) => s.clone(),
            SetRepr::SmallInt(s) => s.iter().map(RuntimeValue::Int).collect(),
        }
    }

    /// Check if a value is representable in the current SmallInt form.
    /// Always true for General.
    pub fn is_small_int(&self) -> bool {
        matches!(self, SetRepr::SmallInt(_))
    }
}

impl Default for SetRepr {
    fn default() -> Self {
        SetRepr::new()
    }
}

impl PartialEq for SetRepr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (SetRepr::SmallInt(a), SetRepr::SmallInt(b)) => a == b,
            _ => {
                // Cross-representation or both General: compare element-by-element.
                self.len() == other.len() && self.iter().eq(other.iter())
            }
        }
    }
}

impl Eq for SetRepr {}

impl PartialOrd for SetRepr {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SetRepr {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (SetRepr::SmallInt(a), SetRepr::SmallInt(b)) => a.cmp(b),
            _ => {
                // Compare by length first, then element-by-element.
                self.len().cmp(&other.len())
                    .then_with(|| self.iter().cmp(other.iter()))
            }
        }
    }
}

/// Iterator over `SetRepr` elements, yielding `RuntimeValue` in ascending order.
pub enum SetReprIter<'a> {
    General(std::collections::btree_set::Iter<'a, RuntimeValue>),
    SmallInt(crate::modelcheck::small_int_set::SmallIntSetIter),
}

impl<'a> Iterator for SetReprIter<'a> {
    type Item = RuntimeValue;

    fn next(&mut self) -> Option<RuntimeValue> {
        match self {
            SetReprIter::General(it) => it.next().cloned(),
            SetReprIter::SmallInt(it) => it.next().map(RuntimeValue::Int),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            SetReprIter::General(it) => it.size_hint(),
            SetReprIter::SmallInt(it) => it.size_hint(),
        }
    }
}

impl<'a> ExactSizeIterator for SetReprIter<'a> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modelcheck::symbol::Symbol;

    fn sym(s: &str) -> Symbol {
        Symbol::intern(s)
    }

    fn nf(pairs: impl IntoIterator<Item = (Symbol, RuntimeValue)>) -> NamedFields {
        NamedFields::from_iter(pairs)
    }

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
        let val = RuntimeValue::Enum {
            ty: "TMState".to_string(),
            variant: "Committed".to_string(),
            fields: NamedFields::new(),
            _cache: FingerprintCache::new(),
        };
        assert_eq!(
            val.to_canonical_json(),
            serde_json::json!({"_variant": "Committed"})
        );
    }

    #[test]
    fn test_to_canonical_json_nested() {
        let inner_enum = RuntimeValue::Enum {
            ty: "TMState".to_string(),
            variant: "Init".to_string(),
            fields: NamedFields::new(),
            _cache: FingerprintCache::new(),
        };
        let set = RuntimeValue::Set(Arc::new(SetRepr::from_values(
            vec![RuntimeValue::Int(1), RuntimeValue::Int(0)],
        )));
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
        // (NamedFields sorts by intern-id, so same fields → same order)
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

    #[test]
    fn test_fingerprint_cache_returns_same_value() {
        let s = RuntimeValue::struct_value_sym("T", nf([(sym("x"), RuntimeValue::Int(42))]));
        let first = s.fingerprint();
        let second = s.fingerprint();
        assert_eq!(first, second, "cached fingerprint must match first computation");
    }

    #[test]
    fn test_fingerprint_cache_preserved_through_clone() {
        let s = RuntimeValue::struct_value_sym("T", nf([(sym("x"), RuntimeValue::Int(1))]));
        let _ = s.fingerprint(); // populate cache
        let cloned = s.clone();
        // Clone should carry the cached value — same result without recomputation
        assert_eq!(s.fingerprint(), cloned.fingerprint());
    }

    #[test]
    fn test_fingerprint_cache_invalidation() {
        let s = RuntimeValue::struct_value_sym("T", nf([(sym("x"), RuntimeValue::Int(1))]));
        let before = s.fingerprint();
        s.invalidate_fingerprint_cache();
        let after = s.fingerprint(); // recomputes from scratch
        assert_eq!(before, after, "same content should produce same hash after invalidation");
    }

    #[test]
    fn test_fingerprint_cache_enum_variant() {
        let e = RuntimeValue::enum_value_sym("Color", "Red", std::iter::empty::<(Symbol, RuntimeValue)>());
        let first = e.fingerprint();
        let second = e.fingerprint();
        assert_eq!(first, second, "enum cached fingerprint must be consistent");
    }

    #[test]
    fn test_fingerprint_cache_no_effect_on_equality() {
        let a = RuntimeValue::struct_value_sym("T", nf([(sym("x"), RuntimeValue::Int(1))]));
        let b = RuntimeValue::struct_value_sym("T", nf([(sym("x"), RuntimeValue::Int(1))]));
        // a has cache populated, b does not
        let _ = a.fingerprint();
        assert_eq!(a, b, "cache state must not affect equality");
    }

    #[test]
    fn test_fingerprint_cache_no_effect_on_ord() {
        let a = RuntimeValue::struct_value_sym("T", nf([(sym("x"), RuntimeValue::Int(1))]));
        let b = RuntimeValue::struct_value_sym("T", nf([(sym("x"), RuntimeValue::Int(1))]));
        let _ = a.fingerprint();
        assert_eq!(a.cmp(&b), std::cmp::Ordering::Equal, "cache state must not affect ordering");
    }

    // ── SetRepr tests ────────────────────────────────────────────────

    #[test]
    fn test_set_repr_from_values_small_int() {
        let repr = SetRepr::from_values(vec![
            RuntimeValue::Int(1),
            RuntimeValue::Int(3),
            RuntimeValue::Int(5),
        ]);
        assert!(repr.is_small_int());
        assert_eq!(repr.len(), 3);
        assert!(repr.contains(&RuntimeValue::Int(3)));
        assert!(!repr.contains(&RuntimeValue::Int(2)));
    }

    #[test]
    fn test_set_repr_from_values_general_mixed() {
        let repr = SetRepr::from_values(vec![
            RuntimeValue::Int(1),
            RuntimeValue::Bool(true),
        ]);
        assert!(!repr.is_small_int());
        assert_eq!(repr.len(), 2);
        assert!(repr.contains(&RuntimeValue::Int(1)));
        assert!(repr.contains(&RuntimeValue::Bool(true)));
    }

    #[test]
    fn test_set_repr_from_values_general_wide_range() {
        let repr = SetRepr::from_values(vec![
            RuntimeValue::Int(0),
            RuntimeValue::Int(100),
        ]);
        assert!(!repr.is_small_int());
        assert_eq!(repr.len(), 2);
    }

    #[test]
    fn test_set_repr_from_values_empty() {
        let repr = SetRepr::from_values(Vec::<RuntimeValue>::new());
        // Empty all-int → SmallInt
        assert!(repr.is_small_int());
        assert!(repr.is_empty());
    }

    #[test]
    fn test_set_repr_insert_small_int() {
        let mut repr = SetRepr::from_values(vec![RuntimeValue::Int(1)]);
        assert!(repr.is_small_int());
        assert!(repr.insert(RuntimeValue::Int(2)));
        assert!(!repr.insert(RuntimeValue::Int(2))); // duplicate
        assert_eq!(repr.len(), 2);
        assert!(repr.is_small_int());
    }

    #[test]
    fn test_set_repr_insert_promotes_on_non_int() {
        let mut repr = SetRepr::from_values(vec![RuntimeValue::Int(1)]);
        assert!(repr.is_small_int());
        repr.insert(RuntimeValue::Bool(true));
        assert!(!repr.is_small_int());
        assert_eq!(repr.len(), 2);
        assert!(repr.contains(&RuntimeValue::Int(1)));
        assert!(repr.contains(&RuntimeValue::Bool(true)));
    }

    #[test]
    fn test_set_repr_insert_promotes_on_out_of_range() {
        let mut repr = SetRepr::from_values(vec![RuntimeValue::Int(0)]);
        assert!(repr.is_small_int());
        repr.insert(RuntimeValue::Int(100)); // out of 64-wide range
        assert!(!repr.is_small_int());
        assert_eq!(repr.len(), 2);
    }

    #[test]
    fn test_set_repr_remove() {
        let mut repr = SetRepr::from_values(vec![
            RuntimeValue::Int(1),
            RuntimeValue::Int(2),
            RuntimeValue::Int(3),
        ]);
        assert!(repr.remove(&RuntimeValue::Int(2)));
        assert!(!repr.remove(&RuntimeValue::Int(2)));
        assert_eq!(repr.len(), 2);
        assert!(!repr.contains(&RuntimeValue::Int(2)));
    }

    #[test]
    fn test_set_repr_union_small_int() {
        let a = SetRepr::from_values(vec![RuntimeValue::Int(1), RuntimeValue::Int(2)]);
        let b = SetRepr::from_values(vec![RuntimeValue::Int(2), RuntimeValue::Int(3)]);
        let c = a.union(&b);
        assert!(c.is_small_int());
        let elems: Vec<RuntimeValue> = c.iter().collect();
        assert_eq!(elems, vec![RuntimeValue::Int(1), RuntimeValue::Int(2), RuntimeValue::Int(3)]);
    }

    #[test]
    fn test_set_repr_difference_small_int() {
        let a = SetRepr::from_values(vec![RuntimeValue::Int(1), RuntimeValue::Int(2), RuntimeValue::Int(3)]);
        let b = SetRepr::from_values(vec![RuntimeValue::Int(2)]);
        let c = a.difference(&b);
        assert!(c.is_small_int());
        let elems: Vec<RuntimeValue> = c.iter().collect();
        assert_eq!(elems, vec![RuntimeValue::Int(1), RuntimeValue::Int(3)]);
    }

    #[test]
    fn test_set_repr_intersection_small_int() {
        let a = SetRepr::from_values(vec![RuntimeValue::Int(1), RuntimeValue::Int(2), RuntimeValue::Int(3)]);
        let b = SetRepr::from_values(vec![RuntimeValue::Int(2), RuntimeValue::Int(4)]);
        let c = a.intersection(&b);
        assert!(c.is_small_int());
        let elems: Vec<RuntimeValue> = c.iter().collect();
        assert_eq!(elems, vec![RuntimeValue::Int(2)]);
    }

    #[test]
    fn test_set_repr_union_cross_repr() {
        let a = SetRepr::from_values(vec![RuntimeValue::Int(1)]);
        let b = SetRepr::from_values(vec![RuntimeValue::Bool(true)]);
        let c = a.union(&b);
        assert!(!c.is_small_int());
        assert_eq!(c.len(), 2);
    }

    #[test]
    fn test_set_repr_iter_ascending() {
        let repr = SetRepr::from_values(vec![
            RuntimeValue::Int(5),
            RuntimeValue::Int(1),
            RuntimeValue::Int(3),
        ]);
        let elems: Vec<RuntimeValue> = repr.iter().collect();
        assert_eq!(elems, vec![RuntimeValue::Int(1), RuntimeValue::Int(3), RuntimeValue::Int(5)]);
    }

    #[test]
    fn test_set_repr_eq_same_repr() {
        let a = SetRepr::from_values(vec![RuntimeValue::Int(1), RuntimeValue::Int(2)]);
        let b = SetRepr::from_values(vec![RuntimeValue::Int(2), RuntimeValue::Int(1)]);
        assert_eq!(a, b);
    }

    #[test]
    fn test_set_repr_eq_cross_repr() {
        let small = SetRepr::from_values(vec![RuntimeValue::Int(1), RuntimeValue::Int(2)]);
        let general = SetRepr::General(
            vec![RuntimeValue::Int(1), RuntimeValue::Int(2)].into_iter().collect(),
        );
        assert!(small.is_small_int());
        assert!(!general.is_small_int());
        assert_eq!(small, general);
    }

    #[test]
    fn test_set_repr_ord_cross_repr() {
        let small = SetRepr::from_values(vec![RuntimeValue::Int(1), RuntimeValue::Int(2)]);
        let general = SetRepr::General(
            vec![RuntimeValue::Int(1), RuntimeValue::Int(2)].into_iter().collect(),
        );
        assert_eq!(small.cmp(&general), std::cmp::Ordering::Equal);
    }

    #[test]
    fn test_set_repr_to_btree_set() {
        let repr = SetRepr::from_values(vec![
            RuntimeValue::Int(3),
            RuntimeValue::Int(1),
        ]);
        let btree = repr.to_btree_set();
        assert_eq!(btree.len(), 2);
        assert!(btree.contains(&RuntimeValue::Int(1)));
        assert!(btree.contains(&RuntimeValue::Int(3)));
    }

    #[test]
    fn test_set_repr_dedup() {
        let repr = SetRepr::from_values(vec![
            RuntimeValue::Int(1),
            RuntimeValue::Int(1),
            RuntimeValue::Int(2),
        ]);
        assert_eq!(repr.len(), 2);
    }
}
