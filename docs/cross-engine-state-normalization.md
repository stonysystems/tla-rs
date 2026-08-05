# Cross-Engine State Normalization Schema

> **Status:** Maintained parity contract. The original Phase 36 proposal used SHA-256
> identifiers and proposed a two-file ordinary export. The implementation now uses canonical
> source-first state keys, compares canonical `state` values across engines, and writes only
> `states.jsonl` on the ordinary CLI path. The schema below describes that current behavior.

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

The source-first `id` field is `RuntimeValue::canonical_key()`. It is a stable key for one
source-first export, but it is not a SHA-256 digest and must not be assumed to match an ID
chosen by TLC tooling. Cross-engine comparison therefore keys entries by minified canonical
JSON in the `state` field. `scripts/diff_parity_states.py` implements this rule.

## 4. Export Format

`verus-transpile model-check --export-parity DIR` currently writes
`DIR/states.jsonl`, one state per line, sorted by the source-first canonical key:

```jsonl
{"id":"<canonical-key>","state":{...},"initial":true,"depth":0}
{"id":"<canonical-key>","state":{...},"initial":false,"depth":1}
```

Fields:
- `id`: source-first canonical state-key string
- `state`: the canonical JSON value (protocol state only)
- `initial`: boolean, whether this is an initial state
- `depth`: BFS depth at which this state was first discovered

Although the CLI help still says “states + edges,” the ordinary command does not currently
write `edges.jsonl`. Absence of that file is an implementation gap, not evidence that the
explored graph has no edges.

## 5. Debug and Edge Export

`--export-parity-debug DIR` streams three files during ordinary BFS/DFS exploration:

| File | Per-line fields |
|---|---|
| `generated_states.jsonl` | `state_id`, `state`, `depth`, `initial`, nullable `branch_label`, nullable `predecessor_state_id`, and `classification` |
| `distinct_states.jsonl` | The same provenance fields except `classification`; one line per first-seen state |
| `edges.jsonl` | `src`, `dst`, `branch_label`, and successor `depth` |

`classification` is `accepted_distinct` or `duplicate`. Debug edges include transitions to
duplicate states, which is useful when locating the first divergence. The identifiers in these
files are still engine-local canonical keys. DPOR does not currently populate the ordinary
stream needed for an equivalent useful debug export.

The lower-level graph exporter can serialize an edge as:

```jsonl
{"src":"<source-key>","dst":"<destination-key>","action":"TMSendPrepare"}
```

Fields:
- `src`: canonical state ID of the source state
- `dst`: canonical state ID of the successor state
- `action`: action/branch label

When that lower-level path is used, edges are sorted by `(src, dst, action)`.

## 6. Protocol-Specific Notes

TwoPhase, PrimaryBackup, LeaderElection, and Paxos parity fixtures all apply the projection
rules above: compare the protocol `LState`/TLC `state`, exclude wrapper message bookkeeping,
and map enum variants through `_variant`. Do not copy state counts into this schema. Current,
dated outcomes belong in `docs/model_checker_status.md`, checked-in parity artifacts, and the
Phase 36 analyses.

## 7. Diff Procedure

Given two export files (`source_first.jsonl` and `tlc.jsonl`):

1. Canonicalize each entry's `state` value and compare those strings; do not compare `id`
   fields across engines.
2. Report:
   - **Source-first-only states**: canonical states present in source-first but not TLC.
   - **TLC-only states**: canonical states present in TLC but not source-first.
   - **Shared states**: canonical states present in both.
3. For the first witness state in each direction, print the full
   canonical JSON for manual inspection.
4. If initial-state sets differ, report that separately (initial-state
   construction bug vs successor-generation bug).
5. If edge files are available, compare transition graphs for shared
   states to isolate missing/extra successors.

## 8. Implementation Checklist

- [x] Source-first ordinary export: `model-check --export-parity DIR` writes
  `states.jsonl` in the format above.
- [x] Source-first streaming debug export: `--export-parity-debug DIR` writes generated,
  distinct, and edge JSONL files for ordinary exploration.
- [x] TLC post-processing: `scripts/tlc_dump_to_parity_jsonl.py` projects and normalizes TLC
  dumps.
- [x] Diff tool: `scripts/diff_parity_states.py` compares canonical `state` values.
- [x] Checked-in small-model parity artifacts and regression coverage exist for shared
  fixtures; consult `docs/model_checker_status.md` for current outcomes and limitations.
