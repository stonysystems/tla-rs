# Phase 22 `model.toml` Format (MVP)

This document defines the finite-domain configuration format for source-first
model checking over protocol specs (`LInit`/`LNext`).

## Goals

- Assign concrete values or finite domains to `LConstants` fields.
- Bound quantifier expansion.
- Bound collection sizes used by runtime value generation.
- Bound state-space exploration (`max_depth`, `max_states`, `timeout`).
- Select invariants and optional deadlock checking.

## Top-Level Sections

- `[constants.assignments]`: concrete values for constant fields.
- `[constants.domains.<field>]`: finite domain for constant fields not fixed by assignment.
- `[quantifiers.int]` / `[quantifiers.nat]`: fallback ranges.
- `[quantifiers.types.<TypeName>]`: finite domain per type.
- `[collections]`: bounds for `Seq`/`Set`/`Map`.
- `[search]`: exploration limits.
- `[properties]`: invariants and deadlock toggle.

## Domain Kinds

`kind = "values"`
- explicit finite list (bool/int/string values)

`kind = "int_range"`
- finite signed range (`min`, `max`)

`kind = "nat_range"`
- finite natural range (`max`, interpreted as `[0, max]`)

`kind = "enum_subset"`
- allowed variant names for enum-typed domains

## Example

```toml
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

[quantifiers.types.NodeId]
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

[properties]
invariants = ["LTypeOK", "LSafety"]
check_deadlock = true
```

## Validation Rules (Current)

- A constant field cannot appear in both assignments and domains.
- Ranges must be valid (`min <= max`).
- Domain lists/subsets must be non-empty.
- Collection bounds and search limits must be positive.
- Invariant names must be non-empty and unique.

## CLI Overrides (Current)

Use:

```bash
verus-transpile model-config --model path/to/model.toml [overrides...]
```

Supported override flags:

- `--max-depth <N>`
- `--max-states <N>`
- `--timeout-ms <N>`
- `--max-seq-len <N>`
- `--max-set-len <N>`
- `--max-map-len <N>`
- `--int-range <MIN..MAX>` (also accepts `MIN:MAX`)
- `--nat-max <N>`

The command applies overrides on top of `model.toml`, revalidates the final
configuration, and prints the resolved TOML to stdout.
