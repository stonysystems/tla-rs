# Trigger-note inventories (Phase 54)

Artifacts in this directory are produced by
`scripts/collect_trigger_inventory.sh` and consumed by
`scripts/trigger_inventory.py diff`. They record which quantifier triggers
Verus chose *for us* on a given release, so that Phase 54 can (a) measure
progress as explicit `#[trigger]` annotations replace those choices and
(b) detect the dangerous case where a Verus upgrade silently picks different
triggers for an expression we never touched.

| file | what it is |
|---|---|
| `<version>-<mode>.json` | machine-readable trigger inventory; the artifact of record |
| `<version>-<mode>.md` | human-readable summary of the same run |
| `timing-*.json` / `.md` | per-module verification wall-clock (`scripts/verus_timing.py`), the other half of the baseline |
| `FORMAT_SAMPLE.md` | **not a baseline** — generated from the three-note test fixture in `scripts/fixtures/trigger_inventory/` purely to show the report format |

`<mode>` is the Verus `--triggers-mode`. `selective` (the Verus default)
prints only ambiguous choices; `all-modules` prints every automatically chosen
trigger. **Counts from different modes are not comparable**, which is why the
mode is part of the file name and the label.

The raw verification log is deleted after parsing unless
`--keep-log` is passed: logs are large and regenerable, the JSON is not.

## The Phase 54.2 baseline is not here yet

Recording it requires running the pinned verifier
(`release/0.2026.08.02.b677dd5`) over the whole crate, which the CI `verify`
job now does on every push: it publishes a `trigger-inventory-<version>`
artifact containing both inventories. Committing that artifact here is task
54.2.b. See `docs/phase54-trigger-workflow.md` for the capture design, the
20%-regression gate the timing half exists to support, and the toolchain
constraint that keeps this off a 2.35-glibc development box.
