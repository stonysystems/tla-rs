# The tla-rs Book

> **Status:** content outline and source-consolidation plan. This is not yet the
> canonical user or developer manual. Commands, feature claims, verification counts,
> and trust-boundary inventories must be checked against the current tree as chapters
> are expanded into final prose.

This book will be the single narrative guide to tla-rs. Part I is for people who want
to specify, check, generate, verify, and run a protocol. Part II is for contributors
who want to change the transpiler, proofs, model checker, runtime, or build system.
Reference material that would interrupt the narrative belongs in the appendices.

The outline below incorporates the durable parts of the existing documentation. It
also records which sources need reconciliation so that old phase notes do not become
new instructions by accident.

## Editorial contract

The finished book should follow these rules:

1. **Current behavior wins over historical prose.** Confirm commands and claims against
   source code, tests, CI, checked-in reports, and the pinned toolchain.
2. **Generated code has one source of truth.** Never instruct readers to hand-edit
   `src/generated/`. Fix the transpiler or its configuration, then regenerate.
3. **Verification claims name their boundary.** Distinguish Verus proofs, explicit
   assumptions, trusted or external bodies, bounded model-checking evidence, and the
   C#/FFI runtime.
4. **Examples are executable.** Every central example should be checked by CI or by a
   reproducible script. Illustrative snippets must be labeled as such.
5. **Status is dated or generated.** Avoid hard-coded test totals, proof counts, and
   performance numbers unless the book identifies their date and reproduction command.
6. **Stable guidance is separated from research history.** Phase reports may explain
   why a design exists, but they do not define the current interface.

## Source-of-truth order

When sources disagree, use this order:

1. Current source, tests, generated-output parity checks, `SConstruct`, and
   `.github/workflows/ci.yml`.
2. The generated-code policy and contribution constraints in [`AGENTS.md`](../AGENTS.md).
3. Current command output and real protocol configurations under `src/protocol/`.
4. The root [`README.md`](../README.md) and recently validated operational guides.
5. Durable design documents.
6. Dated status reports, phase plans, audits, `TODO.md`, `notes.md`, and `hacks.md`.

## Who should read what

| Reader | Suggested path |
|---|---|
| First-time user | Chapters 1–3, 5–8, then 11 |
| Existing TLA+ user | Chapters 1–3, 9, 8, 7, then 11 |
| User running an included protocol | Chapters 1–2, 7, and 10 |
| Verification-minded reader | Chapters 3–4, 7–8, then Chapters 14 and 20 |
| New contributor | Part I overview, then Chapters 13–20 and 24 |
| Transpiler contributor | Chapters 17–20, 23–27 |
| Model-checker contributor | Chapters 22–24 and 27 |

## Book outline at a glance

### Part I — User Guide

| Chapter | Title | Main question |
|---:|---|---|
| 1 | Welcome to tla-rs | What does the project do, and what does it guarantee? |
| 2 | Install tla-rs and Run the Counter Quickstart | Can I generate, verify, compile, and run a minimal example? |
| 3 | The tla-rs Mental Model | How do specs, proofs, generated code, and runtime code relate? |
| 4 | Write a TLA-Style Specification in Verus | How do I express state, actions, invariants, and refinement? |
| 5 | Design a Specification the Transpiler Can Execute | Which relational patterns can become executable functions? |
| 6 | Configure Code Generation | How do annotations and TOML control concrete output? |
| 7 | Generate, Inspect, and Verify Executable Code | How do I regenerate safely and understand the resulting contracts? |
| 8 | Model Check a Specification | How do I explore a finite model and interpret the evidence? |
| 9 | Import and Export TLA+ | How do I move between TLA+ and Verus responsibly? |
| 10 | Build and Run the Included Protocols | How do I run the integrated distributed services? |
| 11 | End-to-End Tutorial: Add a Small Protocol | How do all stages fit together for a new protocol? |
| 12 | Troubleshooting, Limitations, and Workflow Selection | What failed, and which supported path should I use? |

### Part II — Developer Guide

| Chapter | Title | Main question |
|---:|---|---|
| 13 | Contributor Orientation and Non-Negotiable Policies | What must every contributor preserve? |
| 14 | System Architecture and Trust Boundaries | Where are the verified and trusted boundaries? |
| 15 | Repository Tour and Conventions | Where does each kind of change belong? |
| 16 | Toolchain, Build System, and Local Development Loop | How do I reproduce the project gates locally? |
| 17 | Transpiler Architecture | How does a spec become printed executable Verus? |
| 18 | Annotation and Configuration Internals | How are modes and code-generation options resolved? |
| 19 | Generated Artifact Lifecycle | How do I fix and regenerate derived code safely? |
| 20 | Verus Proof Engineering and Proof Generation | How do I solve proof gaps generically? |
| 21 | Protocol, Scheduler, Runtime, and FFI Integration | How does a transition become a distributed service action? |
| 22 | Source-First Model Checker Internals | How are states, successors, reductions, and evidence produced? |
| 23 | TLA+ Translation and Round-Trip Internals | How are constructs mapped and preservation tested? |
| 24 | Testing, CI, and Evidence Integrity | Which regression layer and artifact guard applies? |
| 25 | Performance and Solver Diagnostics | How do I optimize without hiding semantic or proof costs? |
| 26 | Verus Compatibility, Toolchain Upgrades, and Releases | How do I advance the verifier safely? |
| 27 | Contributor Playbooks | What is the end-to-end recipe for common changes? |
| 28 | Roadmap, Research Context, and Documentation Maintenance | What is current, experimental, historical, or proposed? |

The appendices hold the CLI, annotation grammar, full configuration schema,
TLA+/Verus support matrix, model/evidence schema, protocol/trust matrix, proof-pattern
catalog, glossary, and bibliography.

## Extracted foundation for the eventual prose

The following material is stable enough to seed the book, while still requiring a
final source review.

### Project in one paragraph

tla-rs lets users express TLA-style distributed-state-machine relations in Rust and
Verus, then derive executable Rust functions and the proof obligations connecting the
implementation to the specification. The project primarily reimplements the ideas of
IronFleet and AutoMan in Verus, and extends them with additional protocols, TLA+/Verus
translation, source-first model checking, dynamic partial-order reduction (DPOR), code
generation, and a deployable C# networking runtime.

Primary source: the opening of [`README.md`](../README.md). The final chapter must keep
the distinction between the IronFleet/AutoMan lineage and tla-rs-specific extensions.

### End-to-end artifact flow

```text
TLA+ source (optional)
        │ translate-tla, or tla-lint + clean-tla for clean-subset projection
        ▼
Verus TLA-style spec ───────► bounded model checking
        │                         │ counterexample or bounded evidence
        │ .automan modes          │
        │ _transpile.toml         │
        ▼                         │
spec-to-exec transpiler ◄─────────┘
        │
        ├── generated concrete types and exec functions
        └── requires/ensures and proof obligations
                    │
                    ▼
             Verus verification
                    │
                    ▼
       Rust library + C# I/O/runtime integration
                    │
                    ▼
          runnable distributed service
```

Sources: [`README.md`](../README.md),
[`project-overview.md`](project-overview.md), and
[`REPRODUCE_WORKFLOW.md`](REPRODUCE_WORKFLOW.md). The diagram intentionally separates
bounded model checking from deductive verification; neither substitutes for the other.

### Core artifact vocabulary

| Artifact | Role | Ownership rule |
|---|---|---|
| `src/protocol/<P>/*.rs` | Logical types, TLA-style actions, invariants, and refinement proofs | Hand-written source |
| `*.automan` | Declares input/output modes and helper signatures | Hand-written source |
| `*_transpile.toml` | Selects mappings, proof/codegen options, and calling convention | Hand-written source |
| `src/generated/<P>/*_gen.rs` | Concrete types and executable transitions | Generated only; never hand-edit |
| `src/implementation/<P>/` | Runtime integration and protocol-specific executable support | Hand-written unless explicitly generated |
| `src/services/<P>/` | Service entry points | Hand-written integration |
| `model.toml` | Finite domains, search limits, and checked properties | Hand-written model-check configuration |
| `reports/` | Reproducible evidence and performance/diagnostic artifacts | Generated and drift-guarded where documented |

Sources: [`REPRODUCE_WORKFLOW.md`](REPRODUCE_WORKFLOW.md),
[`README.md`](../README.md), and [`AGENTS.md`](../AGENTS.md).

### Core notation

| Notation | Meaning |
|---|---|
| `L*` | Logical/specification type or operation |
| `C*` | Concrete/executable type or operation |
| `s`, `s_` | Pre-state and post-state in a relational action |
| `spec fn` | Mathematical, ghost-only function used in specifications |
| `proof fn` | Ghost-only lemma or proof procedure |
| `exec fn` | Function retained in executable Rust |
| `value@` | A concrete value's logical view through `View` |
| `+` / `-` | Supplied input / synthesized output in an AutoMan annotation |

Sources: [`tla-rs-guide.md`](tla-rs-guide.md),
[`AGENTS.md`](../AGENTS.md), and
[`ANNOTATION_FORMAT.md`](../transpiler/docs/ANNOTATION_FORMAT.md). Definitions of
`open`, `recommends`, and transparency must be rewritten from current Verus semantics;
some older explanations are too absolute.

### Verification and trust vocabulary

The book must use the following terms consistently:

| Term | What it establishes | What it does not establish by itself |
|---|---|---|
| Verus-verified function | Its checked body satisfies its Verus contract under its preconditions and trusted dependencies | That dependencies, environment, or specification are correct |
| Refinement link | Concrete behavior is related to a stated logical predicate | End-to-end correctness beyond the relation's scope |
| `assume` | A proposition accepted without proof at that site | A proved fact |
| `external_body` / external specification | A trusted implementation boundary with a checked interface or specification | Verification of the hidden body |
| Bounded model-check result | No violation was found within the resolved finite model and search limits | An unbounded proof |
| C#/FFI runtime | Networking, I/O, and service machinery used by the executable system | Verus verification unless explicitly modeled and linked |

Sources: [`README.md`](../README.md),
[`io-trust-boundary-analysis.md`](dev/io-trust-boundary-analysis.md), and current
source/report audits. Exact trust-site counts must be generated afresh rather than copied
from phase documents.

# Part I — User Guide

Part I should take a reader from the project's purpose to a small protocol that they can
model check, generate, verify, compile, and run. It should teach the common path first and
move alternatives and exhaustive option lists to later chapters or appendices.

## Chapter 1 — Welcome to tla-rs

**Reader outcome:** understand what tla-rs does, where it came from, and which guarantees
belong to which layer.

### Planned sections

1. The one-sentence project promise.
2. IronFleet: refinement methodology, verified distributed systems, and RSL lineage.
3. AutoMan: mode-directed specification-to-implementation generation.
4. What tla-rs changes by using Rust and Verus.
5. Extensions beyond the two papers: additional protocols, bidirectional translation,
   model checking, DPOR, and runtime/codegen tooling.
6. Protocol gallery, with a generated current-status matrix rather than prose counts.
7. What is in scope: safety, refinement, bounded exploration, generation, and deployment.
8. Non-goals and research-frontier features.
9. Verification and trust boundaries, using the vocabulary above.
10. Choosing a reading path through the book.

### Material to consolidate

- Project identity, attribution, protocol list, and architecture from
  [`README.md`](../README.md).
- Only the vision and high-level pipeline from
  [`project-overview.md`](project-overview.md); its status tables and milestones are stale.
- TLA+ and Verus motivation from [`tla-rs-guide.md`](tla-rs-guide.md), corrected to
  distinguish deductive safety/refinement reasoning from bounded liveness checks.
- Primary-paper references from the README and the bibliography appendix.

### Editorial checks

- Do not present the legacy Lock example as a currently mounted protocol.
- Do not describe every included protocol as Byzantine fault tolerant.
- Avoid undated verification totals or assumption counts.

## Chapter 2 — Install tla-rs and Run the Counter Quickstart

**Reader outcome:** verify the installation and see a complete spec become a verified,
runnable program.

### Planned sections

1. Supported platform and pinned Verus/Rust relationship.
2. Additional dependencies: stable Rust for the transpiler, Python/SCons, and .NET.
3. Clone the repository and inspect tool versions.
4. Set `VERUS_PATH` and other environment variables without assuming a fixed install path.
5. Read the counter's `LInit` and `LIncrement` relations.
6. Read `LInit(-)` and `LIncrement(+, -)` in the annotation file.
7. Generate `counter_gen.rs` with the checked-in configuration.
8. Read its `requires` and `ensures` clauses.
9. Verify, compile, and run the binary.
10. Interpret `2 verified, 0 errors` and `Counter: 0 -> 1` without overclaiming.
11. Use the CI-backed checker to detect stale generated output or proof shortcuts.
12. First-install troubleshooting: toolchain mismatch, glibc, executable path, and linker
    issues.

### Material to consolidate

- The CI-backed example in [`README.md`](../README.md) and `examples/quickstart/`.
- Current prerequisites from [`README.md`](../README.md), CI, and
  [`REPRODUCE_WORKFLOW.md`](REPRODUCE_WORKFLOW.md).
- Old-host verifier guidance from
  [`phase54-trigger-workflow.md`](phase54-trigger-workflow.md), kept as troubleshooting
  rather than the main installation path.

## Chapter 3 — The tla-rs Mental Model

**Reader outcome:** understand the layers and vocabulary used throughout the book.

### Planned sections

1. State machines: state, constants, initial states, and transitions.
2. `Init`, action predicates, and `Next` as relations rather than imperative functions.
3. Safety properties, invariants, refinement, and bounded liveness.
4. `spec`, `proof`, and `exec` modes.
5. Logical `L*` types and concrete `C*` types.
6. Views (`@`), validity predicates, and abstraction functions.
7. Generated executable functions and their refinement contracts.
8. Spec/proof/generated/runtime layers in one worked counter transition.
9. Why executable integers and collections need finite representations even when logical
   `int`, `Set`, and `Map` need not be finite.
10. The difference between model-check evidence and proof.

### Material to consolidate

- Core concepts and function modes from [`tla-rs-guide.md`](tla-rs-guide.md).
- View and Verus patterns from [`AGENTS.md`](../AGENTS.md).
- Artifact flow from [`REPRODUCE_WORKFLOW.md`](REPRODUCE_WORKFLOW.md).
- Evidence distinctions from
  [`model-checking-source-first.md`](model-checking-source-first.md).

## Chapter 4 — Write a TLA-Style Specification in Verus

**Reader outcome:** write readable relational specifications before considering code
generation.

### Planned sections

1. Define logical state and constants.
2. Write an initialization predicate.
3. Express pre-state/post-state actions with `s` and `s_`.
4. Compose actions into `LNext` with stuttering made explicit.
5. Translate conjunction, disjunction, implication, and conditionals.
6. Use finite-domain quantifiers responsibly and choose triggers deliberately.
7. Express `UNCHANGED`, record/struct updates, sequences, sets, and maps.
8. Define invariants and supporting lemmas.
9. Model messages, packets, I/O operations, and environment steps.
10. Compose proposer, acceptor, learner, executor, and election components.
11. Introduce abstraction functions and refinement relations.
12. Specification style: explicit frames, guard/transition/stutter, small helpers, and
    meaningful names.

### Material to consolidate

- Chapters 2–7 and Best Practices from [`tla-rs-guide.md`](tla-rs-guide.md), using
  examples rebuilt from current protocol source.
- Feature mapping tables from [`tla_features.md`](tla_features.md) and
  [`verus_features.md`](verus_features.md), after reconciling them with tests.
- Durable translation rules from [`translation-rules.md`](dev/translation-rules.md).

### Editorial checks

- Correct old snippets that use assignment where a spec relation needs equality.
- Explain that `open` concerns logical transparency/unfolding, not Rust visibility.
- Do not claim that all quantifier, recursion, or temporal constructs are executable.

## Chapter 5 — Design a Specification the Transpiler Can Execute

**Reader outcome:** shape relations so output values can be synthesized without weakening
the specification.

### Planned sections

1. Relational specification versus functionalizable relation.
2. Inputs, outputs, and deterministic construction.
3. The `.automan` module format.
4. `+` input and `-` output modes.
5. Predicate annotations and value-returning helper annotations.
6. Saturation: every output is constructed.
7. Harmony: no output receives incompatible constructions.
8. Obligation: no value is consumed before it is available.
9. Supported assignment, struct, conditional, collection, map/filter/fold, and helper
   patterns.
10. Spec-only functions, skipped functions, and explicit unsupported-pattern handling.
11. Diagnostic-only fallback modes and why trusted stubs are not a production proof.
12. Refactoring a relation to make data flow explicit without changing its meaning.

### Material to consolidate

- [`ANNOTATION_FORMAT.md`](../transpiler/docs/ANNOTATION_FORMAT.md), extended with current
  helper syntax and examples.
- Basic, current portions of [`PATTERNS.md`](../transpiler/docs/PATTERNS.md).
- Mode-analysis concepts from the transpiler checker and selected material in
  `docs/dev/`.
- General limitation categories from
  [`LIMITATIONS.md`](../transpiler/docs/LIMITATIONS.md), checked against current tests.

## Chapter 6 — Configure Code Generation

**Reader outcome:** create a minimal correct `_transpile.toml` and understand when advanced
options are necessary.

### Planned sections

1. Minimal configuration for a scalar example.
2. Naming prefixes and logical-to-concrete type mapping.
3. Integer and natural-number representations and overflow preconditions.
4. Type, function, variant, method-call, and view remapping.
5. Imports and generated-module placement.
6. Validity predicates, proof generation, and extra `requires` clauses.
7. Collection-aware cloning and abstraction helpers.
8. Functional return style versus in-place `&mut self` style.
9. When Arc-backed fields remain appropriate for functional code.
10. Debugging the resolved configuration.
11. Advanced options moved to Appendix C.

### Material to consolidate

- [`transpiler-config-reference.md`](transpiler-config-reference.md), treated as a draft
  and reconciled field-by-field with `transpiler/src/config.rs`.
- Real `_transpile.toml` files under `src/protocol/`.
- Only the final `&mut self` and ownership decision sections of
  [`EFFICIENT_EMIT.md`](../transpiler/docs/EFFICIENT_EMIT.md).

### Editorial checks

- Fix obsolete `method_calls`, `view_overrides`, and `custom_imports` examples.
- Ensure the full TOML example obeys TOML table scoping.
- Do not recommend `manual_code` as a way around the generated-code policy.

## Chapter 7 — Generate, Inspect, and Verify Executable Code

**Reader outcome:** run the supported generation path, understand its contracts, and verify
the result without editing generated artifacts.

### Planned sections

1. Input and output file map.
2. Build the transpiler.
3. Generate concrete types.
4. Generate executable action/helper functions.
5. Use protocol regeneration scripts where they are policy-compliant.
6. Inspect generated signatures, `requires`, `ensures`, proof blocks, and views.
7. Understand the functional and `&mut self` calling conventions.
8. Run focused Verus verification.
9. Run the whole-crate proof gate.
10. Check deterministic regeneration and generated-output drift.
11. Respond to unsupported output by fixing source/config/transpiler, never the generated
    file.
12. Audit assumptions and trusted boundaries.

### Material to consolidate

- The operational sequence in
  [`REPRODUCE_WORKFLOW.md`](REPRODUCE_WORKFLOW.md), corrected against current scripts and
  `SConstruct`.
- The README transformation example.
- The generated-code rule in [`AGENTS.md`](../AGENTS.md).
- Verification checklists from
  [`MIGRATION_GUIDE.md`](../transpiler/docs/MIGRATION_GUIDE.md), after removing manual
  patch advice.

## Chapter 8 — Model Check a Specification

**Reader outcome:** configure a finite model, explore it, and interpret results at the right
confidence level.

### Planned sections

1. Why model check before or alongside deductive proof.
2. Source-first inputs: protocol source, types, and `model.toml`.
3. Finite domains for constants, quantifiers, enums, collections, and states.
4. Search limits, timeouts, BFS, DFS, and DPOR.
5. Invariants, deadlock semantics, counterexample traces, and stop reasons.
6. Bounded liveness plus weak/strong fairness.
7. Canonical exact deduplication versus explicitly lossy modes.
8. Symmetry, partial-order reduction, bytecode/native execution, and parallel workers.
9. Read human output and JSON reports.
10. Reproduce checked-in evidence and understand drift guards.
11. Generate TLC wrappers when cross-engine checking is appropriate.
12. Compare state sets using canonical normalization.
13. State-explosion, unsupported-expression, and incomplete-search troubleshooting.

### Material to consolidate

- [`model-checking-source-first.md`](model-checking-source-first.md) as the main practical
  source.
- The beginner sequence under
  [`model-checker-architecture/`](model-checker-architecture/README.md), especially its
  glossary, walkthrough, and TLC/source-first comparison.
- [`model-checking-wrapper-workflow.md`](model-checking-wrapper-workflow.md),
  [`model-checking-migration.md`](model-checking-migration.md), and
  [`cross-engine-state-normalization.md`](cross-engine-state-normalization.md).
- Current code and CLI for integrated DPOR; the standalone prototype README is historical
  context, not the current user path.
- Artifact discipline from [`reports/model_check/README.md`](../reports/model_check/README.md).

## Chapter 9 — Import and Export TLA+

**Reader outcome:** choose a source of truth and move specifications between TLA+ and Verus
without assuming unsupported semantic equivalence.

### Planned sections

1. Three directions: TLA+ → Verus spec, Verus spec → executable Verus, and Verus spec →
   TLA+.
2. Choose TLA+ or Verus as the maintained source of truth.
3. The clean TLA+ subset and why mechanical projection needs a message-aware input
   contract.
4. The human/tool boundary: a human rewrites cross-node reads into explicit message
   behavior; the tool projects a clean global spec onto one node.
5. Run `tla-lint` and interpret C1–C5 diagnostics.
6. Run `clean-tla` to produce a single-process protocol-layer Verus spec.
7. Interpret the clean-subset evidence correctly: lint acceptance means projectable, the
   generated artifact is a spec rather than a proof, and corpus checks have explicit V1/V2/V3
   scopes.
8. Use the general `translate-tla` path with inferred or explicit types when appropriate.
9. Inspect generated Verus and `.automan` annotations.
10. Run the full TLA+ → spec → exec pipeline, noting that `pipeline --clean-subset`
    currently stops after the projected spec because projected mode annotations are separate
    work.
11. Export relational Verus specs to TLA+.
12. Generate TLC wrappers and validate with SANY/TLC where desired.
13. Indexing, records, maps/functions, non-determinism, recursion, and temporal-operator
    caveats.
14. Round-trip structural checks versus semantic equivalence.
15. Support matrix derived from tests, not old prose tables.

### Material to consolidate

- Architecture, syntax maps, type-annotation format, and examples from
  [`tla-to-verus-guide.md`](tla-to-verus-guide.md).
- Source-of-truth and round-trip advice from [`migration_guide.md`](migration_guide.md),
  with current command names (`translate-tla` and `verus2-tla`).
- The C1–C5 contract and diagnostics from
  [`clean_tla_subset.md`](clean_tla_subset.md), the human rewrite boundary from
  [`clean_tla_rewrite_playbook.md`](clean_tla_rewrite_playbook.md), and scoped translator
  results from [`clean_tla_translator_evidence.md`](clean_tla_translator_evidence.md).
- Current support evidence from [`conversion-testing-guide.md`](conversion-testing-guide.md),
  [`tla_features.md`](tla_features.md), [`verus_features.md`](verus_features.md), and tests.
- Known limitations from
  [`tla-transpiler-limitations.md`](tla-transpiler-limitations.md), only after reconciling
  contradictions.

## Chapter 10 — Build and Run the Included Protocols

**Reader outcome:** build the integrated system and run an existing distributed protocol.

### Planned sections

1. What SCons builds and verifies.
2. Build Verus/Rust only, C# only, or the complete stack.
3. Shared-library and `LD_LIBRARY_PATH` setup.
4. Generate service certificates.
5. Run an RSL cluster and client over UDP.
6. Understand the legacy TCP/SSL path.
7. Run the unified server/client for non-RSL protocols.
8. Protocol-specific node/quorum requirements.
9. Cluster integration tests and common networking failures.
10. Benchmark helpers, reproducibility metadata, and hardware-dependent results.
11. What the C# runtime contributes and why it is part of the trust boundary.

### Material to consolidate

- Building, Running, and Performance from [`README.md`](../README.md).
- End-to-end build/run recipe and troubleshooting from
  [`REPRODUCE_WORKFLOW.md`](REPRODUCE_WORKFLOW.md).
- Actual binaries and targets from `SConstruct`, `scripts/`, `src/services/`, and `csharp/`.

## Chapter 11 — End-to-End Tutorial: Add a Small Protocol

**Reader outcome:** apply the entire workflow to one maintained, comprehensible protocol.

### Planned tutorial

1. State the protocol and safety goal in plain language.
2. Choose a logical state, constants, messages, and environment boundary.
3. Write `LInit`, named actions, `LNext`, and invariants.
4. If starting from TLA+, lint and translate the clean input.
5. Create a small finite `model.toml` and find/fix one seeded bug.
6. Make action data flow functionalizable.
7. Write `.automan` modes and validate saturation/harmony/obligation.
8. Create a minimal transpiler configuration.
9. Generate types and exec functions.
10. Read and verify the refinement contracts.
11. Add host/scheduler/runtime integration.
12. Compile and run a local cluster or deterministic runner.
13. Add regeneration, model-check, verification, and runtime regression tests.
14. Document remaining trusted boundaries honestly.

### Source strategy

This chapter is the main missing piece in the existing documentation. Use the counter
quickstart for mechanics and a small currently maintained protocol (or a new dedicated
tutorial protocol) for the complete path. The old Lock example in
[`tla-rs-guide.md`](tla-rs-guide.md) may supply concepts, but should not be copied until it
is modernized and mounted in the current workflow.

## Chapter 12 — Troubleshooting, Limitations, and Workflow Selection

**Reader outcome:** identify which stage failed, choose a supported alternative, and know
when the tool cannot preserve the intended semantics automatically.

### Planned sections

1. A stage-by-stage diagnostic decision tree.
2. TLA+ parse, clean-subset, and type-inference failures.
3. Verus-spec parse and unsupported-expression failures.
4. Annotation mode errors: saturation, harmony, and obligation.
5. Configuration and import-resolution failures.
6. Generated Rust type, borrow, overflow, and collection-view failures.
7. Verus proof failure, trigger change, rlimit, and timeout diagnosis.
8. Model-check unsupported surface, state explosion, timeout, and incomplete evidence.
9. Linker, FFI, certificate, quorum, and cluster failures.
10. Choosing source-first model checking, TLC wrappers, direct proof, or manual protocol
    redesign.
11. Current limitations table generated from tests and issue/status sources.
12. How to produce a minimal reproducer and where to report it.

### Material to consolidate

- Troubleshooting from [`REPRODUCE_WORKFLOW.md`](REPRODUCE_WORKFLOW.md),
  [`model-checking-source-first.md`](model-checking-source-first.md), and
  [`conversion-testing-guide.md`](conversion-testing-guide.md).
- Carefully validated categories from
  [`LIMITATIONS.md`](../transpiler/docs/LIMITATIONS.md) and
  [`tla-transpiler-limitations.md`](tla-transpiler-limitations.md).
- Current known limitations from source, tests, CI, and status artifacts rather than old
  phase totals.

# Part II — Developer Guide

Part II explains how to evolve the implementation while preserving proof, generated-code,
and evidence integrity. The normal development loop is: change a source of truth, regenerate
derived artifacts, inspect the diff, run focused tests, and finish with the appropriate full
gate.

## Chapter 13 — Contributor Orientation and Non-Negotiable Policies

**Reader outcome:** make a safe first change without corrupting generated artifacts or
overstating verification.

### Planned sections

1. Contributor prerequisites and expected background.
2. The generated-code policy and why it exists.
3. Allowed sources of change: spec, annotation, config, transpiler, proof, runtime.
4. Prohibited generated-file workarounds, including manual patches and
   clone/delegate/extract patterns.
5. Source-of-truth hierarchy.
6. Verification/trust vocabulary for code review.
7. Working safely in a dirty tree.
8. A minimal local edit → format → test → verify loop.
9. Documentation expectations for commands, evidence, and historical claims.

### Material to consolidate

- [`AGENTS.md`](../AGENTS.md) is authoritative for policy.
- Contributor-oriented portions of the README.
- Do not merge obsolete manual-patch instructions from
  `transpiler/docs/REGEN_WORKFLOW.md`.

## Chapter 14 — System Architecture and Trust Boundaries

**Reader outcome:** trace one protocol action from logical relation to network execution and
identify every verified or trusted boundary.

### Planned sections

1. Logical protocol and refinement layer.
2. Generated concrete types and transitions.
3. Hand-written implementation/host layer.
4. Scheduler and service entry points.
5. Rust/C# FFI and network runtime.
6. Message serialization and certificate/configuration data.
7. Model-checking path alongside the proof path.
8. Trust inventory: `assume`, external specifications, `external_body`, FFI, and runtime.
9. How to update the trust inventory and avoid converting proof debt into invisible trust.
10. Implemented features versus research roadmap.

### Material to consolidate

- Architecture from [`README.md`](../README.md) and the conceptual pipeline in
  [`project-overview.md`](project-overview.md).
- Architectural lessons, but not stale counts, from
  [`io-trust-boundary-analysis.md`](dev/io-trust-boundary-analysis.md).
- Current code and machine-readable reports as the final authority.

## Chapter 15 — Repository Tour and Conventions

**Reader outcome:** know where each kind of change belongs.

### Planned sections

1. Root build, CI, scripts, reports, and documentation.
2. `src/protocol/`: logical types, actions, invariants, and refinement proofs.
3. `src/generated/`: derived concrete artifacts.
4. `src/implementation/`: runtime-facing implementation and host code.
5. `src/services/`: executable entry points.
6. `src/common/` and `src/verus_extra/`: shared verified/trusted infrastructure.
7. `csharp/`: network runtime and service tooling.
8. `transpiler/src/`: parser, analysis, translation, generation, model checking, and TLA
   conversion.
9. Tests, fixtures, model configurations, and evidence artifacts.
10. Naming: `L*`, `C*`, `s_`, `_s`, `_i`, and generated suffixes.
11. RSL component roles and non-RSL protocol organization.

### Material to consolidate

- Code Organization from [`README.md`](../README.md) and [`AGENTS.md`](../AGENTS.md),
  verified against the tree rather than preserving old line counts.
- Module-level documentation in `transpiler/src/lib.rs` and submodules.

## Chapter 16 — Toolchain, Build System, and Local Development Loop

**Reader outcome:** reproduce every CI class locally and understand which toolchain runs
which code.

### Planned sections

1. Pinned Verus and its Rust toolchain.
2. Stable Rust for transpiler development.
3. Python/SCons and .NET dependencies.
4. SCons target graph and key options.
5. Verus-only, .NET-only, no-verify, debug, and extra-flag workflows.
6. Cargo build, format, clippy, unit, integration, and focused-test commands.
7. Local verification helper and old-glibc execution path.
8. Cache and artifact locations.
9. Fast inner loop versus pre-push/full-gate loop.
10. Diagnosing a CI/local mismatch.

### Canonical sources

- `.github/workflows/ci.yml`, `SConstruct`, `scripts/verify_local.sh`, and current command
  output.
- README/AGENTS only for introductory prose; older toolchain references are historical.

## Chapter 17 — Transpiler Architecture

**Reader outcome:** follow a specification from text input to printed executable Verus.

### Planned sections

1. CLI entry points and default spec-to-exec mode.
2. Parsing Verus syntax into the internal AST.
3. Loading and resolving configuration.
4. Parsing annotations and classifying predicates/helpers.
5. Mode inference, saturation, harmony, and obligation checking.
6. Type registry, remapping, and executable type selection.
7. Pattern/template detection and functionalization.
8. Expression and function translation.
9. Proof-needs analysis and proof-block generation.
10. Printing executable functions and types.
11. Specialized generators: messages, marshalable code, scheduler, and host scaffolds.
12. Unsupported-pattern errors, auto-skip, and proof fallback.
13. Determinism and diagnostics.

### Material to consolidate

- Module documentation and current code under `transpiler/src/` as the primary source.
- The helper pipeline concept from
  [`h5-code-generation-pipeline.md`](dev/h5-code-generation-pipeline.md).
- Durable pattern names from [`PATTERNS.md`](../transpiler/docs/PATTERNS.md).
- Avoid proposed module layouts in old plans when they differ from current code.

## Chapter 18 — Annotation and Configuration Internals

**Reader outcome:** extend or debug input modes and configuration without adding
protocol-specific code to the translator.

### Planned sections

1. Annotation grammar and parser.
2. Predicate and helper function models.
3. Validation invariants and diagnostics.
4. Configuration deserialization and defaults.
5. Root options versus nested tables.
6. Name/type/function/view/variant remapping.
7. Collection, cloning, validity, and proof-helper configuration.
8. Calling-convention selection and interaction rules.
9. Extra requirements and inline expansions.
10. Adding a new option end to end: schema, resolved config, behavior, tests, and docs.
11. Dumping and comparing resolved configuration.
12. Keeping configuration generic rather than protocol-coded.

### Material to consolidate

- [`ANNOTATION_FORMAT.md`](../transpiler/docs/ANNOTATION_FORMAT.md).
- [`transpiler-config-reference.md`](transpiler-config-reference.md) as a checklist, with
  `transpiler/src/config.rs` and real configs as authoritative sources.

## Chapter 19 — Generated Artifact Lifecycle

**Reader outcome:** regenerate safely and fix generator defects at their source.

### Planned sections

1. Why generated files are checked in.
2. Inputs that determine each generated file.
3. Protocol and RSL regeneration entry points.
4. Generate into scratch space before replacement when diagnosing drift.
5. Inspect semantic and formatting diffs.
6. Regeneration parity tests.
7. Updating the transpiler, configuration, or spec to fix a generated problem.
8. Handling unsupported functions without manual generated bodies.
9. Auditing assumptions, external bodies, imports, and proof shortcuts.
10. Reviewing generated diffs for behavior, contract, proof, and performance changes.
11. Recovery when old documentation suggests a forbidden manual patch.

### Material to consolidate

- The policy in [`AGENTS.md`](../AGENTS.md).
- Current regeneration scripts and parity tests.
- The safe portions of [`MIGRATION_GUIDE.md`](../transpiler/docs/MIGRATION_GUIDE.md).
- `transpiler/docs/REGEN_WORKFLOW.md` is historical evidence only and must not supply
  current instructions.

## Chapter 20 — Verus Proof Engineering and Proof Generation

**Reader outcome:** diagnose proof failures and teach the transpiler reusable proof patterns
instead of inserting trust.

### Planned sections

1. Contracts, recommends, assertions, lemmas, and transparency.
2. Validity by construction.
3. Spec-refinement linkage and branch decomposition.
4. Input-only conjuncts as executable preconditions.
5. Views, abstraction functions, and clone preservation.
6. Empty collection mapping lemmas.
7. Set insert/remove and sequence push map-commutativity lemmas.
8. Hash-map abstraction and verified clone helpers.
9. Enum matching and unreachable branches.
10. Recursive specs, decreases, generated loops, and invariants.
11. Quantifier triggers and arithmetic/non-arithmetic trigger separation.
12. Reading Verus errors, rlimit failures, and trigger-choice changes.
13. Classifying a gap as proof work, executable precondition, or genuine trust boundary.
14. Guardrails for `assume`, `external_body`, and external specifications.
15. Turning one protocol proof into a generic generator capability plus regression test.

### Material to consolidate

- Patterns 1–14 from [`phase12-proof-patterns.md`](phase12-proof-patterns.md), stripped
  of old counts and forbidden generated-file workflows.
- Reusable P1–P9 and selected P11/P12 material from
  [`proof-pattern-catalog.md`](dev/proof-pattern-catalog.md).
- View/trigger guidance from [`AGENTS.md`](../AGENTS.md) and current source.
- Trigger inventory and timing discipline from
  [`phase54-trigger-workflow.md`](phase54-trigger-workflow.md).

## Chapter 21 — Protocol, Scheduler, Runtime, and FFI Integration

**Reader outcome:** connect generated state transitions to a runnable service without
blurring protocol proof and runtime trust.

### Planned sections

1. Standard files for a protocol.
2. Logical types, messages, state, actions, and refinement modules.
3. Generated types/functions and implementation imports.
4. Decomposing `LNext` into schedulable actions.
5. Message-driven, timer-driven, role-dispatched, and flag-injected actions.
6. Host generation and the hand-written integration shell.
7. Message and marshalable generation.
8. Service entry points and shared generic runtime.
9. Rust/C# FFI calls and ownership boundaries.
10. I/O logging, packet identity, certificates, and network lifecycle.
11. Adding a new protocol to build, service dispatch, tests, and docs.
12. Protocol-specific refinement and trust inventory.

### Material to consolidate

- Runtime architecture and service commands from [`README.md`](../README.md).
- Durable scheduler classification from
  [`scheduler-generation-analysis.md`](dev/scheduler-generation-analysis.md).
- Conceptual I/O-boundary analysis from
  [`io-trust-boundary-analysis.md`](dev/io-trust-boundary-analysis.md), with current
  sites/counts regenerated.
- Current `SConstruct`, service, implementation, and C# source.

## Chapter 22 — Source-First Model Checker Internals

**Reader outcome:** modify exploration or evaluation while preserving semantics and evidence.

### Planned sections

1. Source ingestion and entrypoint resolution.
2. `model.toml` schema resolution and finite-domain expansion.
3. Transition/branch intermediate representation.
4. Runtime values, evaluator, helper calls, and bytecode/native paths.
5. Direct solving versus bounded candidate enumeration.
6. BFS and DFS exploration.
7. Integrated DPOR, independence, sleep sets, and conflict profiling.
8. Sequential and parallel exploration.
9. Canonical state identity, symmetry, hash compaction, and POR.
10. Invariants, deadlocks, counterexamples, liveness, and fairness.
11. Telemetry, JSON schema, and checked-in evidence.
12. Cross-engine state/edge export and TLC parity.
13. Guardrails against unsound pruning and misleading incomplete results.
14. Adding an expression, reduction, search strategy, or report field.

### Material to consolidate

- Current `transpiler/src/modelcheck/` code and module docs.
- Practical semantics from [`model-checking-source-first.md`](model-checking-source-first.md).
- Beginner architecture and comparison material from
  [`model-checker-architecture/`](model-checker-architecture/README.md).
- Optimization lessons from
  [`model-checker-implementation-lessons.md`](model-checker-implementation-lessons.md).
- Normalization and evidence drift docs.
- DPOR prototype documents as dated design history; current user/developer behavior comes
  from the integrated module and CLI.

## Chapter 23 — TLA+ Translation and Round-Trip Internals

**Reader outcome:** extend translation while knowing which preservation claims the tests
actually justify.

### Planned sections

1. TLA+ lexer/parser and module AST.
2. Type inference, explicit type annotations, and unresolved types.
3. Clean-subset lint, mechanical projection, and the boundary where human message-aware
   rewriting is required.
4. TLA+ → relational Verus translation passes.
5. Mode-annotation generation.
6. Verus spec extraction and Verus → TLA+ conversion.
7. Naming and type mapping in both directions.
8. Canonicalization for structural round trips.
9. TLC wrapper generation.
10. Indexing, non-determinism, functions/maps, records, and temporal semantics.
11. Parser coverage, translation coverage, and semantic limitations.
12. Adding a construct with positive, negative, round-trip, and pipeline tests.

### Material to consolidate

- Current `transpiler/src/tla/`, `transpiler/src/verus2tla/`, and round-trip code.
- Mapping tables from [`tla-to-verus-guide.md`](tla-to-verus-guide.md),
  [`tla_features.md`](tla_features.md), and [`verus_features.md`](verus_features.md),
  regenerated against tests.
- Conceptual design only from [`verus2tla-design.md`](dev/verus2tla-design.md); proposed
  module names are not authoritative.
- Testing strategy from [`conversion-testing-guide.md`](conversion-testing-guide.md).

## Chapter 24 — Testing, CI, and Evidence Integrity

**Reader outcome:** choose the right regression layer and understand every required CI gate.

### Planned sections

1. Test pyramid: unit, parser/type, translator, integration, round-trip, regeneration,
   Verus, model-check, runtime cluster.
2. Focused test selection during development.
3. Full Cargo suite, formatting, and clippy.
4. Quickstart generation/verification/runtime guard.
5. Protocol generated-output parity tests.
6. Whole-crate Verus proof gate.
7. Model-check evidence regeneration and normalized drift guard.
8. DPOR corpus and parity/regression suites.
9. Trigger inventory, ceiling, diff, and verification timing artifacts.
10. Cluster integration and benchmark smoke tests.
11. Adding a new CI check without duplicating or weakening existing gates.
12. Diagnosing flaky timing versus structural drift.

### Canonical sources

- `.github/workflows/ci.yml`, current test files, and scripts.
- [`conversion-testing-guide.md`](conversion-testing-guide.md) for taxonomy, not old
  numeric totals.
- [`reports/model_check/README.md`](../reports/model_check/README.md) and
  [`phase54-trigger-workflow.md`](phase54-trigger-workflow.md) for artifact discipline.

## Chapter 25 — Performance and Solver Diagnostics

**Reader outcome:** optimize measured bottlenecks without breaking refinement or hiding proof
cost.

### Planned sections

1. Reproducible benchmark design and metadata.
2. Functional whole-state rebuild cost.
3. `&mut self` generation and when functional style is still required.
4. Arc-backed fields for functional hot paths.
5. Clone/View proof implications.
6. Runtime/network versus protocol/codegen bottlenecks.
7. Per-module Verus timing.
8. Trigger inventories and trigger-choice diffs.
9. Model-check evaluator, solver, exploration, DPOR, and parallelism profiles.
10. Performance claims: dated measurements, baselines, deltas, and hardware caveats.

### Material to consolidate

- Only the final Phase 47–49 and decision-matrix material from
  [`EFFICIENT_EMIT.md`](../transpiler/docs/EFFICIENT_EMIT.md).
- Reproduction methodology from [`REPRODUCE_WORKFLOW.md`](REPRODUCE_WORKFLOW.md).
- [`phase54-trigger-workflow.md`](phase54-trigger-workflow.md) and current trigger reports.
- Model-check performance reports as dated case studies, not timeless claims.

## Chapter 26 — Verus Compatibility, Toolchain Upgrades, and Releases

**Reader outcome:** advance the pinned verifier incrementally and keep code, CI, examples,
and documentation aligned.

### Planned sections

1. Where the Verus and Rust pins live.
2. Release versus rolling builds and platform/glibc constraints.
3. Establish the current full verification baseline.
4. Test the next compiler version and classify the first incompatibility.
5. Patch source/transpiler, regenerate, and rerun focused/full gates.
6. Repeat incrementally until the target release.
7. Detect syntax, vstd API, trigger, solver, and performance changes.
8. Update CI caches, local helpers, README/book, and evidence artifacts.
9. Release checklist for transpiler CLI, generated artifacts, runtime, and docs.
10. Rollback and bisect strategy.

### Material to consolidate

- Current CI, `scripts/verify_local.sh`, and toolchain pins.
- Durable migration lessons from dated Verus migration plans, clearly labeled historical.
- Trigger/timing comparison workflow from
  [`phase54-trigger-workflow.md`](phase54-trigger-workflow.md).

## Chapter 27 — Contributor Playbooks

**Reader outcome:** follow a reviewable, end-to-end recipe for common change types.

### Planned playbooks

1. Add a new protocol.
2. Add a TLA+ or Verus syntax construct.
3. Add a spec-to-exec transformation pattern.
4. Add an annotation feature.
5. Add a transpiler configuration option.
6. Add or modify a proof-generation pattern.
7. Diagnose a generated Verus failure.
8. Remove an `assume` or trusted body without moving the trust elsewhere.
9. Add a model-check evaluator/solver feature.
10. Add a search reduction and prove/test its guardrails.
11. Change the runtime or FFI boundary.
12. Upgrade Verus.
13. Review a generated diff.
14. Update status/evidence documentation after behavior changes.

Each playbook should name source files, focused tests, required regeneration, full gates,
and documentation/evidence updates. Phase plans may supply failure stories, but the final
steps must be reconstructed from current code and CI.

## Chapter 28 — Roadmap, Research Context, and Documentation Maintenance

**Reader outcome:** distinguish maintained functionality from experiments and preserve useful
history without letting it define current behavior.

### Planned sections

1. Implemented, experimental, and proposed feature labels.
2. IronFleet, AutoMan, verified IronKV, TLA+/TLC, Verus, and DPOR research context.
3. Current open technical directions, derived from active issues/TODO rather than old
   milestone tables.
4. How to use phase documents as dated case studies.
5. When to archive or retire a standalone guide after its content enters the book.
6. Keeping commands executable and feature matrices generated.
7. Dated verification/trust/status snapshots.
8. Book review checklist for every release.

### Material to consolidate

- Research vision from [`project-overview.md`](project-overview.md), separated from its
  stale current-status claims.
- Literature and tooling surveys under [`docs/survey/`](survey/README.md).
- Jetpack and DPOR documents as explicitly experimental case studies where still relevant.
- `TODO.md` only as a live planning source, never as polished user guidance.

# Appendices

## Appendix A — CLI Reference

- Generate from a Verus spec.
- `check`, `list-templates`, and resolved-config inspection.
- Type, message, marshalable, scheduler, and host generators.
- `translate-tla`, `verus2-tla`, and `pipeline`.
- `tla-lint` and `clean-tla`.
- `model-config` and `model-check`, including BFS/DFS/DPOR options.
- TLC wrapper generation.
- Assume reports and supported migration utilities.
- Exit codes and stdout/stderr/JSON conventions.

Generate or validate this appendix from the current CLI so it cannot drift.

## Appendix B — `.automan` Grammar and Validation Rules

- Module grammar.
- `+` and `-` modes.
- Predicate and helper forms.
- Comments and qualification.
- Saturation, harmony, and obligation.
- Complete current examples and checker diagnostics.

Starting source: [`ANNOTATION_FORMAT.md`](../transpiler/docs/ANNOTATION_FORMAT.md).

## Appendix C — Complete Transpiler Configuration Reference

- Every field from the current deserialization structs.
- Default, scope, accepted values, interactions, and examples.
- Root keys versus TOML tables.
- Minimal, common, and advanced configurations.
- A generated schema or config-dump-based drift test.

Starting source: [`transpiler-config-reference.md`](transpiler-config-reference.md), but the
current `config.rs` is authoritative.

## Appendix D — TLA+ ↔ Verus Syntax and Support Matrix

- Logical, arithmetic, set, sequence, map/function, record, tuple, quantifier, action, and
  temporal constructs.
- Parse, translate, round-trip, model-check, and exec-generation support as separate columns.
- Known semantic caveats and test anchors.

Starting sources: [`tla_features.md`](tla_features.md),
[`verus_features.md`](verus_features.md), and current tests. Existing tables conflict and
must not simply be concatenated.

## Appendix E — `model.toml`, Reports, and Evidence Schema

- Domain and constant configuration.
- Search, property, fairness, and reduction configuration.
- Resolved configuration.
- Human and JSON result fields.
- Counterexample and liveness traces.
- Parity exports and normalized evidence drift.

Starting sources: [`model-checking-source-first.md`](model-checking-source-first.md),
`docs/dev/phase22-model-toml-format.md`, current config structs, and report schemas.

## Appendix F — Protocol and Trust-Boundary Matrix

- Protocol purpose and fault model.
- Spec, generated implementation, runtime integration, model-check fixture, and service
  status.
- Refinement proof status.
- Active assumptions, external bodies/specifications, and runtime trust, generated from a
  dated audit.
- Reproduction commands for every row.

Do not seed this appendix with old counts from phase documents.

## Appendix G — Proof-Pattern Catalog

- Pattern name, applicability test, generated proof shape, required lemmas, counterexample,
  and current source/test anchor.
- Trigger patterns and performance checks.
- Trust-boundary decision tree.

Starting sources: [`phase12-proof-patterns.md`](phase12-proof-patterns.md) and
[`proof-pattern-catalog.md`](dev/proof-pattern-catalog.md), after removing historical counts
and forbidden generated-file techniques.

## Appendix H — Glossary, Error Index, and Further Reading

- TLA+, TLC, Verus, SMT, refinement, invariant, liveness, fairness, View, ghost code,
  functionalization, saturation, harmony, obligation, POR, and DPOR.
- Error-message-to-chapter index.
- IronFleet, AutoMan, Verus, TLA+, verified IronKV, TLC, and DPOR references.
- Project attribution and license.

Starting sources: [`model-checker-architecture/glossary.md`](model-checker-architecture/glossary.md),
[`tla-rs-guide.md`](tla-rs-guide.md), and the README attribution section.

# Existing Material Migration Map

The table records the intended disposition of current documentation. Nothing should be
deleted until its destination chapter is complete and reviewed.

| Existing source | Book destination | Treatment |
|---|---|---|
| [`README.md`](../README.md) | Chapters 1–2, 7, 10, 14–16 | Preserve as the short landing page; move depth into the book and link back |
| [`AGENTS.md`](../AGENTS.md) | Chapters 13–16, 19–20 | Keep as concise agent/contributor policy; book explains rationale and workflow |
| [`tla-rs-guide.md`](tla-rs-guide.md) | Chapters 3–4, 11–12, Appendix H | Extract conceptual teaching; rebuild examples; remove stale IronLock/current-status claims |
| [`REPRODUCE_WORKFLOW.md`](REPRODUCE_WORKFLOW.md) | Chapters 2, 7, 10, 16, 25 | Extract operational sequence; fix Verus-path and generated-patch conflicts |
| [`project-overview.md`](project-overview.md) | Chapters 1, 14, 28 | Keep vision and pipeline; rewrite status/milestones from current evidence |
| [`tla-to-verus-guide.md`](tla-to-verus-guide.md) | Chapters 9 and 23, Appendix D | Extract architecture and mappings; reconcile commands/features and repair links |
| [`migration_guide.md`](migration_guide.md) | Chapters 9, 19, 23 | Keep source-of-truth/round-trip guidance; replace obsolete CLI names |
| [`transpiler-config-reference.md`](transpiler-config-reference.md) | Chapters 6 and 18, Appendix C | Rebuild from current config structs; do not copy unsafe examples |
| [`clean_tla_subset.md`](clean_tla_subset.md), [`clean_tla_rewrite_playbook.md`](clean_tla_rewrite_playbook.md), and [`clean_tla_translator_evidence.md`](clean_tla_translator_evidence.md) | Chapters 9 and 23 | Preserve C1–C5, the human rewrite/tool projection boundary, current `tla-lint`/`clean-tla` workflow, and scoped V1/V2/V3 evidence claims |
| [`tla_features.md`](tla_features.md), [`verus_features.md`](verus_features.md) | Chapters 4, 9, 23, Appendix D | Merge into one tested multi-stage support matrix |
| [`tla-transpiler-limitations.md`](tla-transpiler-limitations.md) | Chapters 9 and 12, Appendix D | Use only after checking every claim against current tests/source |
| [`conversion-testing-guide.md`](conversion-testing-guide.md) | Chapters 9, 23–24 | Keep conversion taxonomy and debugging; remove historical test totals/status matrices |
| [`model-checking-source-first.md`](model-checking-source-first.md) | Chapters 8 and 22, Appendix E | Primary practical source; remove phase framing and update newer capabilities |
| [`model-checker-architecture/`](model-checker-architecture/README.md) | Chapters 8 and 22, Appendices D/H | Preserve beginner explanations, walkthrough, comparison, and glossary; compress process guardrails |
| [`model-checking-wrapper-workflow.md`](model-checking-wrapper-workflow.md) | Chapters 8–9 and 23 | Keep TLC selection and wrapper workflow |
| [`model-checking-migration.md`](model-checking-migration.md) | Chapters 8 and 22 | Keep old/new artifact mapping as historical migration help |
| [`cross-engine-state-normalization.md`](cross-engine-state-normalization.md) | Chapters 8 and 22, Appendix E | Preserve canonical parity schema and update current implementation anchors |
| [`model_checker_status.md`](model_checker_status.md) and `reports/model_check/` | Chapters 8, 22, 24, Appendix F | Use as dated/generated evidence, not timeless narrative |
| [`ANNOTATION_FORMAT.md`](../transpiler/docs/ANNOTATION_FORMAT.md) | Chapters 5 and 18, Appendix B | Consolidate and extend with helper/current calling-convention examples |
| [`PATTERNS.md`](../transpiler/docs/PATTERNS.md) | Chapters 5, 17, 20, Appendix G | Keep basic current patterns; separate obsolete Arc history and refresh limitations |
| [`LIMITATIONS.md`](../transpiler/docs/LIMITATIONS.md) | Chapters 5 and 12 | Keep validated categories/workarounds; discard stale feature/performance claims |
| [`EFFICIENT_EMIT.md`](../transpiler/docs/EFFICIENT_EMIT.md) | Chapters 6 and 25 | Keep final `&mut self`/functional/Arc decision; treat early alternatives as history |
| [`MIGRATION_GUIDE.md`](../transpiler/docs/MIGRATION_GUIDE.md) | Chapters 7, 19, 27 | Keep spec/exec pairing and verification checklist; remove manual generated-code advice |
| `transpiler/docs/REGEN_WORKFLOW.md` | Chapter 19 historical note | Do not reuse as instructions; it conflicts with current generated-code policy |
| [`phase12-proof-patterns.md`](phase12-proof-patterns.md) | Chapter 20, Appendix G | Extract reusable proof patterns; remove counts, phase ledger, and forbidden manual techniques |
| [`proof-pattern-catalog.md`](dev/proof-pattern-catalog.md) | Chapter 20, Appendix G | Merge general patterns with current source/test anchors and trust caveats |
| [`translation-rules.md`](dev/translation-rules.md) | Chapters 4, 17–18, 20 | Extract durable mappings and proof obligations; validate protocol-specific examples |
| [`scheduler-generation-analysis.md`](dev/scheduler-generation-analysis.md) | Chapters 17 and 21 | Extract action classification and runtime-source design; update implementation status |
| [`io-trust-boundary-analysis.md`](dev/io-trust-boundary-analysis.md) | Chapters 14, 20–21, Appendix F | Preserve trust-boundary reasoning; regenerate site inventory and counts |
| [`phase54-trigger-workflow.md`](phase54-trigger-workflow.md) and trigger reports | Chapters 20, 24–26 | Preserve inventory/diff/timing method; reconcile report README status with artifacts |
| Standalone DPOR prototype docs | Chapters 8, 22, 28 | Treat as dated incubation history; document current integrated DPOR from source/CLI |
| `docs/dev/F*`, `H*`, phase plans, and dated audits | Relevant developer chapters or Chapter 28 | Mine only durable lessons/case studies; otherwise retain as archive material |
| [`TODO.md`](../TODO.md), `notes.md`, `hacks.md` | Chapters 20 and 28 as inputs | Never copy directly; validate and rewrite durable guidance |
| [`docs/survey/`](survey/README.md) | Chapter 28 and bibliography | Condense research context and preserve evidence links |

# Known Reconciliation Work Before Full Prose

These conflicts were found while constructing the outline and should become explicit book
tasks:

1. Rebuild the TLA+/Verus feature matrix from current tests; existing support and limitation
   documents contradict one another.
2. Rebuild the transpiler configuration reference from `config.rs`; current examples omit or
   misplace options and use obsolete field shapes.
3. Replace all old manual-patching instructions for `src/generated/` with the current
   source/config/transpiler regeneration policy.
4. Generate one dated verification/trust inventory. Existing documents disagree about proof
   totals, assumptions, external bodies, and protocol status.
5. Validate every SCons/Verus command. In particular, `--verus-path` takes the verifier
   executable path, not merely its directory.
6. Update CLI names (`translate-tla`, `verus2-tla`, and current subcommands) and repair stale
   links.
7. Replace old Arc-first performance guidance with the current `&mut self` versus functional
   decision, retaining Arc only where current code/config justifies it.
8. Separate legacy Lock tutorial material, standalone DPOR incubation material, and proposed
   project milestones from maintained functionality.
9. Correct conceptual overstatements about `open`, `recommends`, collection finiteness,
   round-trip equivalence, and what `0 errors` proves.
10. Replace stale line counts, test totals, performance numbers, and milestone statuses with
    generated or dated evidence.
11. Keep three clean-subset claims distinct: `tla-lint` checks projectability,
    `clean-tla` mechanically emits a protocol-layer spec, and the human rewrite into the
    subset is neither automated nor proved behaviorally equivalent merely by lint or
    translation success.

# Definition of Done for the Book

The outline is fully expanded when:

- a new user can complete Chapters 2 and 11 from a clean checkout;
- every central command is exercised by CI or a documented reproducible check;
- the book contains one coherent user path and one coherent contributor path;
- every generated-code instruction follows `AGENTS.md`;
- the protocol/status/trust matrix is dated and reproducible;
- feature and configuration references are derived from current code/tests;
- examples compile or are labeled illustrative;
- historical phase material is clearly marked and cannot be mistaken for current policy;
- the root README links to the book and stays a concise landing page; and
- superseded standalone guides are archived or reduced to redirects only after their useful
  content has been reviewed and migrated.
