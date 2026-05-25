//! Interned field-name symbols for efficient struct/enum field maps.
//!
//! `Symbol` is a `u32` handle into a global string interner. Using `Symbol`
//! instead of `String` as the key in `BTreeMap<_, RuntimeValue>` eliminates
//! per-field String allocations on every state clone and makes BTreeMap
//! comparisons integer-only (not pointer-chasing + memcmp).

use std::collections::HashMap;
use std::hash::Hash;
use std::sync::{LazyLock, RwLock};

/// An interned field-name handle. Cheap to copy, compare, and hash.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(u32);

impl Symbol {
    /// Intern a string, returning a stable Symbol handle.
    /// If the string was already interned, returns the existing handle.
    pub fn intern(s: &str) -> Self {
        // Fast path: read lock
        {
            let interner = INTERNER.read().unwrap();
            if let Some(&id) = interner.str_to_id.get(s) {
                return Symbol(id);
            }
        }
        // Slow path: write lock
        let mut interner = INTERNER.write().unwrap();
        // Double-check after acquiring write lock
        if let Some(&id) = interner.str_to_id.get(s) {
            return Symbol(id);
        }
        let id = interner.strings.len() as u32;
        let owned = s.to_string();
        interner.str_to_id.insert(owned.clone(), id);
        interner.strings.push(owned);
        Symbol(id)
    }

    /// Resolve this symbol back to its string representation.
    #[inline]
    pub fn as_str(&self) -> SymbolStr {
        SymbolStr(self.0)
    }

    /// Get the string value. Requires acquiring the read lock briefly.
    pub fn resolve(&self) -> String {
        let interner = INTERNER.read().unwrap();
        interner.strings[self.0 as usize].clone()
    }

    /// Compare two symbols by their resolved name (alphabetical order).
    /// Avoids allocating Strings — acquires the read lock once.
    pub fn cmp_by_name(&self, other: &Symbol) -> std::cmp::Ordering {
        if self.0 == other.0 {
            return std::cmp::Ordering::Equal;
        }
        let interner = INTERNER.read().unwrap();
        interner.strings[self.0 as usize].cmp(&interner.strings[other.0 as usize])
    }

    /// Hash this symbol's resolved name into the given hasher.
    /// Avoids allocating a String — acquires the read lock once.
    pub fn hash_name(&self, h: &mut impl std::hash::Hasher) {
        let interner = INTERNER.read().unwrap();
        interner.strings[self.0 as usize].hash(h);
    }
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let interner = INTERNER.read().unwrap();
        write!(f, "Symbol({:?})", &interner.strings[self.0 as usize])
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let interner = INTERNER.read().unwrap();
        f.write_str(&interner.strings[self.0 as usize])
    }
}

/// Helper for displaying a symbol's string without cloning.
/// Used in format strings via Display.
pub struct SymbolStr(u32);

impl std::fmt::Display for SymbolStr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let interner = INTERNER.read().unwrap();
        f.write_str(&interner.strings[self.0 as usize])
    }
}

struct Interner {
    str_to_id: HashMap<String, u32>,
    strings: Vec<String>,
}

static INTERNER: LazyLock<RwLock<Interner>> = LazyLock::new(|| {
    RwLock::new(Interner {
        str_to_id: HashMap::new(),
        strings: Vec::new(),
    })
});

/// Convenience: create a Symbol from a String (consumes the String).
impl From<String> for Symbol {
    fn from(s: String) -> Self {
        Symbol::intern(&s)
    }
}

impl From<&str> for Symbol {
    fn from(s: &str) -> Self {
        Symbol::intern(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_intern_returns_same_id() {
        let a = Symbol::intern("hello");
        let b = Symbol::intern("hello");
        assert_eq!(a, b);
    }

    #[test]
    fn test_different_strings_different_ids() {
        let a = Symbol::intern("foo");
        let b = Symbol::intern("bar");
        assert_ne!(a, b);
    }

    #[test]
    fn test_resolve_roundtrip() {
        let s = Symbol::intern("test_field");
        assert_eq!(s.resolve(), "test_field");
    }

    #[test]
    fn test_display() {
        let s = Symbol::intern("my_field");
        assert_eq!(format!("{}", s), "my_field");
    }

    #[test]
    fn test_ordering_is_by_id() {
        // Symbols are ordered by insertion order (u32), not alphabetically
        let first = Symbol::intern("zzz_first_interned");
        let second = Symbol::intern("aaa_second_interned");
        assert!(first < second);
    }
}
