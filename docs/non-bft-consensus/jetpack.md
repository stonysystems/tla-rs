# Jetpack agreement, execution consistency and linearizability

Verus proves fast/base ordering agreement, execution consistency and client
linearizability for an abstract composition of Jetpack with a host protocol.
The proofs cover arbitrary finite executions, including recovery retries and
successive normal views. They extend the earlier recovery-set and admission
barrier proofs.

The result is conditional on explicit host contracts. The host supplies a
common durable executed prefix, preserves proposer order, and fences a view
change before recovering per-proposer prefixes. Fast result computation uses
the modeled executed prefix. These contracts have not been proved for Raft,
MongoDB, Mencius or the authors' implementation. This remains a partial
formalization of the paper.

## Proved properties

| Property | Verus theorem | Meaning |
|---|---|---|
| Recovery agreement | `recovery::execution_safety` | All chosen recovery sets in one recovery instance agree, including across ballots; each includes every certified fast command and excludes its conflicts |
| Fast/base ordering agreement | `execution::reachable_order_agreement` | Conflicting commands have the same relative order in the base execution and the constructed sequential history |
| Replica execution agreement | `execution::replica_execution_agreement` | Executors of any two prefixes of the common base log produce the same result for a command present in both; that result agrees with an existing client response |
| Execution consistency over time | `execution::execution_consistency_over_time` | A client response, including an early fast response, equals the result of later base-prefix execution of that command |
| State agreement after draining | `execution::drained_state_agreement` | When no fast commands await base execution, base execution and the sequential witness have identical application states and all returned values |
| Client linearizability | `execution::history_linearizable` | Every finite reachable client history has a legal sequential completion respecting response-before-invocation order |
| Recovery completion barrier | `ordering::finish_preserves` | Executing the chosen batch leaves no certified fast command pending before the next normal view opens |
| Earlier admission model | `view_change::admission_after_recovery` | Every prior-view fast certificate is durable before a new command is admitted, under that model's atomic durable-batch contract |

The client history records invocation and response events with logical times.
A legal sequential completion contains every returned operation exactly once,
contains only invoked operations, and may complete some pending invocations.
Executing that sequence produces every observed response. If one operation
returns before another is invoked, it precedes that operation in the sequence.
Command IDs identify logical operations; client transport retries are outside
this model.

Agreement permits different orders of independent commands. The application
contract requires independence to preserve both application state and returned
values. State commutation alone would be insufficient for linearizability.
The replica theorem quantifies over semantic execution of the host's common
prefixes; it does not independently prove host consensus or maintain a network
of concrete replica executors.

## Models and proof structure

[`recovery.rs`](../../src/protocol/Jetpack/recovery.rs) models per-replica fast
logs, freeze flags, promises, accepted values, prepare snapshots, proposals and
votes. Acknowledgment, freeze, prepare and accept are separate actions. Delayed
prepare replies and competing recovery ballots are allowed. For `2f+1` replicas,
recovery uses `f+1` replies, fast certification uses `f + ceil(f/2) + 1` replicas,
and fresh recovery selection requires `ceil(f/2) + 1` occurrences. The proofs
quantify over arbitrary finite command sets and symmetric, irreflexive conflict
relations.

[`ordering.rs`](../../src/protocol/Jetpack/ordering.rs) adds original-path
proposer queues, certificates containing all proposers, base execution and
successive recovery instances. An acknowledgment checks outstanding fast and
proposer conflicts. Appending proposals establishes their receipt order. The
host can execute an ordinary proposal only after its earlier conflicting
proposals have executed. A recovery can instead submit its chosen batch.

`commit_respects_fast` derives that an unexecuted fast command cannot be overtaken
by a distinct conflicting command. For an ordinary proposal, the proof uses
the acknowledgments from every proposer and the host's order rule. For a
recovery submission, it invokes the recovery completeness/conflict theorem.
`finish_preserves` derives that the pending set is empty when the chosen batch
has executed. Neither statement is an action guard.

Acknowledgment histories retain old entries, but ordinary conflict checks
ignore commands already executed by the base. Thus the new composition allows
sequential conflicting commands within a normal view. Beginning recovery
seeds the recovery core with the remaining outstanding commands and proves its
invariant. The recovery core retains that window's logs. This models the logical
effect of garbage collection; it does not verify garbage-collection messages or
memory reclamation.

[`execution.rs`](../../src/protocol/Jetpack/execution.rs) calls the actual
`ordering::next` relation and tracks invocations, computed results, responses,
the base execution sequence and pending fast commands. It also constructs a
ghost sequential witness. A fast command computes its result from the executed
base state and enters the witness immediately. When it later executes on the
base, its witness position stays fixed. Other base commands enter the witness
on execution.

The inductive invariant proves that executing `base + pending` and executing
the witness produce the same state and all outputs. Moving a command from the
pending sequence to the base can reorder it only across independent commands.
The invariant connects computed responses to the witness, while logical event
times prove real-time order. Result computation does not read the ghost witness,
and no transition assumes linearizability or execution consistency.

[`application.rs`](../../src/protocol/Jetpack/application.rs) proves these
reordering facts for a generic deterministic state machine.
[`registers.rs`](../../src/protocol/Jetpack/registers.rs) discharges the application
contract for reads and atomic exchanges on integer registers, with distinct
keys independent. An exchange returns the previous value. The formal
[`execution_witness.rs`](../../src/protocol/Jetpack/execution_witness.rs) proof
constructs a reachable fast response before any base execution, using that
application and three replicas. This is a Verus existence proof.

[`view_change.rs`](../../src/protocol/Jetpack/view_change.rs) remains a separate,
coarser admission model. It retains old instances for delayed messages and
models a durable recovery marker atomically. The new execution composition
uses `ordering.rs` directly; no refinement between these two view-change models
is claimed.

## Paper correspondence and host contracts

| Paper mechanism | New composition | Remaining implementation obligation |
|---|---|---|
| PR2, proposer receipt order | `propose` appends to a per-proposer queue | Host/shim receipt and proposal order must match |
| Fast conflict checks and all-proposer certificate | `acknowledge`, `certificate`, `fast` | Authenticate and associate acknowledgments with the correct view; implement local execution/conflict checks |
| PR1, order of conflicting proposals | `ready`, ordinary `commit` | Prove the host preserves this order across its actual log operations |
| Original recovery in B.3 | `begin_recovery` retains per-proposer prefixes after a fenced cut | Prove fencing and prefix preservation, including hole detection and truncation |
| Jetpack recovery in B.2 | `core_step` uses `recovery::next`; `choose_batch` requires a chosen set | Refine messages and durable state to the merged freeze/prepare organization |
| Recovery resubmission and stability marker | Recovery `commit`, then `finish` after the batch executes | Refine distributed marker discovery, persistence and admission gating |
| Fast execution and original execution | `execution::protocol_step` computes results from the modeled executed prefix | Prove local executors and snapshots supply the required state at response computation |

The host recovery contract deserves particular attention. An acknowledged
command may disappear from a recovered proposer queue only with the suffix
following it. `prefix_preserves_before` proves that retained conflicting
successors cannot lose that predecessor. **This prefix/fencing contract is an
explicit assumption about the host, not a consequence proved here from host
linearizability alone.** The model also abstracts the host's common committed
and executed prefix. These are the remaining links to an implementation-level
proof of B.3 Lemma 1.

Normal proposal admission is fenced during recovery. The merged freeze/prepare
core still allows separately scheduled replica freezes and delayed same-view
certification before the view finishes. Finishing changes the proposer set and
resets view-local queues and acknowledgments. Membership itself is fixed.
Old-view messages after finishing are abstracted away; proving that concrete
view tags reject them remains a refinement obligation.

The application must be deterministic and its conflict predicate must cover
all pairs that fail to commute in either state or output. This is a premise of
the generic theorem, proved separately for the register example. Crashes and
message loss may prevent progress indefinitely. Persistent protocol state is
assumed to survive restart; no fairness, termination or latency theorem is
claimed.

## Source and provenance

- [OSDI 2026 paper](https://www.usenix.org/system/files/osdi26-tang.pdf),
  sections 3.3, 4.3, B.2 and B.3.
- PDF SHA-256: `19b480f481b862543cb2270bde0f1d77f9e0c31b6f7f073eb50d0d525191559e`.
- [Authors' artifact at commit c03e318](https://github.com/stonysystems/jetpack/tree/c03e318ec355b11edd42aac56c68d0765f88d1d2/tla).
  The three files in `docs/jetpack_reference/` match this commit byte for byte.
  These Verus models were written from the paper and have no proved refinement
  to those reference files.

The historical `src/protocol/Jetpack/jetpack.rs` model is separate. Its two
previously verified obligations establish nonnegative ballots and
`accepted_ballot <= max_seen_ballot`; they do not establish these new results.

## Verification

The standalone package passes Verus `0.2026.08.02.b677dd5` with `--no-cheating`:
85 verified, 0 errors. The same seven modules pass through `src/lib.rs` with
85 verified, 0 errors. The latter is selected-module integration, not whole-crate
verification. These counts include supporting lemmas and are not counts of
independent protocol properties.

The proof package introduces no `assume`, `admit`, `external_body`,
`assume_specification` or trusted proof axioms. The usual Verus, SMT and vstd
trusted foundations remain. No generated files were edited.

```bash
VERUS_PATH=/path/to/verus \
  bash scripts/verify_consensus_jetpack.sh
```

See [standalone output](evidence/jetpack-verification.log),
[integration output](evidence/jetpack-integrated.log) and the
[verification ledger](verification.json). Only Verus-proved properties count.
The runner has no TLC dependency. Optional Verus mutation controls for the
older admission model remain separate from theorem evidence.

## Remaining obligations

- Refine the host ordering, fenced prefix recovery and executed-prefix contracts
  to each target host, including its log holes and marker discovery.
- Refine fast response computation, local replica execution, view tags,
  networking, persistence and physical garbage collection to implementation code.
- Relate the model to all unmerged recovery schedules and the authors' artifact.
- Prove membership changes, client retry/deduplication and liveness.

The new results discharge the requested safety properties for the stated
abstract composition. The full paper and host implementations remain open.
