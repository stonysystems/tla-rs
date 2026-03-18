# Cross-Engine State Normalization Schema (Phase 36.1.2)

This document defines the canonical normalization schema used to compare
reachable state sets between the source-first model checker and TLC.
Both engines must project their internal state representation to this
schema before any parity comparison.

## 1. Projection: Protocol State Only

Both engines model protocols with a `(state, constants)` pair and
optional bookkeeping (e.g., message channels). For parity diffing,
**only the protocol state is compared**:

| Engine | Raw state variables | Projected for parity |
|--------|---------------------|---------------------|
| Source-first | `RuntimeValue::Struct { ty: "LState", fields }` | All fields of `LState` |
| TLC | `state`, `constants`, optionally `msgs` | `state` variable only |

- **`constants`** is excluded because it is fixed for a given model
  configuration and identical across all states.
- **`msgs`** (message channel) is excluded because source-first uses a
  relational `sent_packets` output parameter and does not accumulate
  messages as part of the protocol state. The TLC benchmark wrappers
  (e.g., `TwoPhase_Benchmark_MC.tla`) add `msgs` as a wrapper-level
  variable; this is bookkeeping, not protocol state. (The auto-generated
  relational wrappers from `generate-mc-wrapper` do not include `msgs`
  unless `--packet-mode` is explicitly set.)

**Consequence**: TLC's `Distinct states` count may be higher than
source-first's even on identical semantics, because TLC deduplicates on
`(state, constants, msgs)` tuples while source-first deduplicates on
`LState` only. After projecting TLC states to the `state` variable
only, the distinct counts should match.

## 2. Canonical Value Representation

After projection, each state is a nested record/struct. The canonical
representation normalizes all values to a uniform JSON-compatible form.

### 2.1 Scalar Types

| Type | Canonical JSON form | Example |
|------|-------------------|---------|
| Boolean | `true` / `false` | `true` |
| Integer | JSON number (signed, arbitrary precision as string if needed) | `42` |
| String | JSON string | `"hello"` |

Source-first `RuntimeValue::Int(i128)` and `RuntimeValue::Nat(u64)` both
normalize to a single integer representation. TLC integers normalize the
same way.

### 2.2 Enum / Variant Types

Enums (tagged unions) normalize to a JSON object with a `"_variant"` key
and field keys for any associated data:

```json
{ "_variant": "Init" }
{ "_variant": "PreparedVote", "rm": 1 }
```

Source-first `RuntimeValue::Enum { ty, variant, fields }` drops the `ty`
and uses `variant` as `_variant`. TLC model values representing enum
tags (e.g., `[tag |-> Init_tag]` or string-encoded variants) are mapped
to the same form using the protocol's type definitions.

### 2.3 Records / Structs

Records normalize to a JSON object with fields sorted alphabetically by
field name. The struct type name is dropped (it is implicit from the
protocol schema).

```json
{
  "rm_aborted": [],
  "rm_committed": [],
  "rm_prepared": [0, 1],
  "tm_prepared": [0],
  "tm_state": { "_variant": "Init" }
}
```

Source-first `RuntimeValue::Struct { ty, fields }` uses `fields`
(already a `BTreeMap`, so alphabetically sorted). TLC TLA+ records
`[f1 |-> v1, f2 |-> v2]` are normalized with the same field ordering.

### 2.4 Sets

Sets normalize to a JSON array of canonically sorted elements:

```json
[0, 1, 2]
```

The sort order is the canonical value order defined recursively:
1. Booleans: `false` < `true`
2. Integers: numeric order
3. Strings: lexicographic order
4. Enums: sort by `(_variant, fields...)` lexicographically
5. Records/structs: sort by fields in alphabetical key order, then values
6. Sequences: lexicographic on elements
7. Sets: lexicographic on sorted element lists
8. Maps: lexicographic on sorted `(key, value)` pair lists

Source-first `RuntimeValue::Set(BTreeSet)` is already sorted by the
`Ord` impl on `RuntimeValue`. TLC set values `{v1, v2, v3}` must be
sorted by the same canonical order.

### 2.5 Sequences

Sequences normalize to a JSON array preserving element order:

```json
[10, 20, 30]
```

TLA+ sequences are 1-indexed; the normalized form uses 0-indexed
position (implicit in the JSON array). Source-first
`RuntimeValue::Seq(Vec)` is already 0-indexed.

### 2.6 Maps (Functions)

Maps normalize to a JSON array of `[key, value]` pairs, sorted by
canonical key order:

```json
[[0, true], [1, false], [2, true]]
```

Source-first `RuntimeValue::Map(BTreeMap)` is already sorted by key.
TLC function values `(d :> r1 @@ d2 :> r2)` are normalized with the
same key ordering.

## 3. State Identity

Two states are **parity-equal** if and only if their canonical JSON
representations (after projection and normalization) are identical as
strings.

The **canonical state ID** is the SHA-256 hex digest of the canonical
JSON string (minified, no trailing newline). This provides a stable,
diffable identifier for each distinct state.

## 4. Export Format

Each engine exports its reachable state set as a JSON Lines (`.jsonl`)
file, one state per line, sorted by canonical state ID:

```jsonl
{"id":"a1b2c3...","state":{...},"initial":true,"depth":0}
{"id":"d4e5f6...","state":{...},"initial":false,"depth":1}
```

Fields:
- `id`: SHA-256 hex digest of the minified canonical JSON of `state`
- `state`: the canonical JSON value (protocol state only)
- `initial`: boolean, whether this is an initial state
- `depth`: BFS depth at which this state was first discovered

The file is sorted by `id` for stable diffing.

## 5. Edge Export (Optional)

For deeper parity debugging, each engine may also export an edge file:

```jsonl
{"src":"a1b2c3...","dst":"d4e5f6...","action":"TMSendPrepare"}
```

Fields:
- `src`: canonical state ID of the source state
- `dst`: canonical state ID of the successor state
- `action`: action/branch label

Sorted by `(src, dst, action)` for stable diffing.

## 6. Protocol-Specific Notes

### TwoPhase

- **Source-first state**: `LState { tm_state, tm_prepared, rm_prepared, rm_committed, rm_aborted }`
- **TLC state**: `state` record with same fields; `msgs` excluded from projection
- **Enum mapping**: `LTMState::Init` -> `{"_variant":"Init"}`, etc.
- **Expected parity**: After projecting TLC to `state` only, distinct
  counts should match. TLC's 64 distinct states likely collapse to
  fewer once `msgs` is excluded.

### PrimaryBackup

- **Source-first state**: `LState` with view/backup/pending fields
- **TLC state**: `state` record; `msgs` excluded
- **Expected parity**: Source-first 60 vs TLC 54 suggests a potential
  semantic difference (source-first has MORE states, not fewer).

### LeaderElection

- **Source-first state**: `LState` with epoch/leaders/acceptors
- **TLC state**: `state` record; `msgs` excluded
- **Note**: Source-first times out at 280 states; parity can only be
  checked if source-first can exhaust the small model.

### Paxos

- **Source-first state**: `LState` with ballot/vote/decision fields
- **TLC state**: `state` record; `msgs` excluded
- **Note**: Source-first times out at 75 states; parity requires
  source-first to exhaust a smaller model first.

## 7. Diff Procedure

Given two export files (`source_first.jsonl` and `tlc.jsonl`):

1. Compare the sets of `id` values.
2. Report:
   - **Source-first-only states**: IDs present in source-first but not TLC.
   - **TLC-only states**: IDs present in TLC but not source-first.
   - **Shared states**: IDs present in both.
3. For the first witness state in each direction, print the full
   canonical JSON for manual inspection.
4. If initial-state sets differ, report that separately (initial-state
   construction bug vs successor-generation bug).
5. If edge files are available, compare transition graphs for shared
   states to isolate missing/extra successors.

## 8. Implementation Checklist

- [ ] Source-first export: add `--export-states <path>` flag to
  `verus-transpile model-check` that writes `.jsonl` in the format above.
- [ ] TLC export: add a post-processing script or TLC `-dump` parser
  that extracts the `state` variable, normalizes, and writes `.jsonl`.
- [ ] Diff tool: `scripts/diff_parity_states.sh` or Rust test helper.
- [ ] Regression test: assert zero diff on shared small models.
