# Mako safety proof

The target is Mako-v1 from OSDI 2025. MakoV2's scalar timestamps and one
Raft log per shard are outside this proof.

This model formalizes Mako's speculative transactions, watermark production,
and recovery rules from Sections 4 and 5 and Appendix A of the OSDI 2025 paper.
Verus checks inductive safety proofs over arbitrary finite executions, with
arbitrary positive numbers of shards, workers, and observers and no bound on
transactions, epochs, or clock values. It does not run a model checker.

The production model computes shard minima from worker reports and delivers
epoch-tagged gossip to independent observers. Its proof establishes that every
produced vector is safe and that finalized vectors denote exactly the final
cut. The global watermark bound is a proved invariant, not a production guard.

Consensus still supplies durable stream prefixes and immutable closed epochs.
OCC now has an explicit key-level model and an inductive serializability proof:
locks, clock replies, read validation, aborts, and speculative installation are
transitions, not a successful-OCC oracle. A second theorem proves that every
componentwise vector cut of its certified transactions remains serializable.

The OCC and producer models are separate. Their composition theorem requires
matching transaction identities, epochs, computed vectors, and write participants.
It proves serializable retained reads and durable retained fragments at that
interface. It does not prove that every split OCC/GetClock execution refines the
older producer model's atomic `Begin` action. This remaining correspondence
obligation, cross-epoch database reconstruction, and C++ refinement are not
claimed to be discharged. The OCC theorem itself has none of these premises.

## Source and artifacts

Reference: [Mako: Speculative Distributed Transactions with Geo-Replication](https://www.usenix.org/system/files/osdi25-shen-weihai.pdf),
OSDI 2025, pp. 129-152. Appendix A is on pp. 149-150. The downloaded PDF has
SHA-256 `1b10eac7a2a5b7dd2ab9270a887d0758a378e85500539ce777036f14414f659e`.

- [occ.rs](../src/protocol/Mako/occ.rs) models record reads, buffered writes,
  individual write-lock acquisitions, per-shard GetClock replies, individual
  read validations, certification, shard installs, and pre-certification aborts.
- [occ_proof.rs](../src/protocol/Mako/occ_proof.rs) proves its invariant and
  serializability over arbitrary finite histories.
- [occ_vectors.rs](../src/protocol/Mako/occ_vectors.rs) proves version uniqueness,
  the vector maximum computation, and dependency-clock ordering.
- [occ_serial.rs](../src/protocol/Mako/occ_serial.rs) supplies an explicit
  sequential execution and proves that its read values match the observed
  values, together with real-time ordering within an epoch.
- [occ_composition.rs](../src/protocol/Mako/occ_composition.rs) proves
  serializability of arbitrary vector cuts and the producer-interface theorem.
- [occ_scenarios.rs](../src/protocol/Mako/occ_scenarios.rs) constructs successful
  and conflicting executions, including a matching OCC/producer commit.
- [production.rs](../src/protocol/Mako/production.rs) is the checked producer,
  network, and transaction state machine, with `initial`, `next`, and `behavior`
  predicates in Verus.
- [watermark_math.rs](../src/protocol/Mako/watermark_math.rs) proves that the
  recursive reduction computes the greatest lower bound of all worker reports.
- [production_proof.rs](../src/protocol/Mako/production_proof.rs) proves the
  producer invariants and refines every production history to the transaction
  model. It includes local watermark soundness and final-cut agreement.
- [production_scenarios.rs](../src/protocol/Mako/production_scenarios.rs)
  constructs executions through the actual report and gossip handlers.
- [model.rs](../src/protocol/Mako/model.rs) is the abstract transaction model
  used as the refinement target. Its `Publish` action is unavailable to the
  production protocol.
- [invariants.rs](../src/protocol/Mako/invariants.rs) proves initialization
  and preservation for every action, then induction over arbitrary histories.
- [safety.rs](../src/protocol/Mako/safety.rs) contains the public theorems.
- [scenarios.rs](../src/protocol/Mako/scenarios.rs) constructs reachable
  executions of successful commit and partial-install recovery.
- [MakoProduction.tla](../src/tla+/Mako/MakoProduction.tla) and
  [Mako.tla](../src/tla+/Mako/Mako.tla), and
  [MakoOCC.tla](../src/tla+/Mako/MakoOCC.tla) are manually maintained TLA+ companions.
  SANY checks their syntax and semantics. There is no TLAPS proof of these files
  and no machine-checked equivalence between them and the Verus encodings.
  The formal proof claim applies to the Verus encodings.

## Model boundary

A transaction reserves one worker stream at each participant shard. Its clock
merges the versions it reads with fresh participant clocks. Each install is a
separate action, so a transaction can install on some shards and fail before
installing on another. A worker remains occupied until its install arrives.
The occupied worker cannot start another transaction in that epoch. This is
the missing-install barrier used in Appendix A, Lemma 6.

An install appends the fragment to the local stream and exposes it to readers.
Replication can independently make any logged prefix durable. The model keeps
installed and durable fragments as immutable historical evidence; rollback
records undo decisions rather than physically deleting this evidence.

A worker reports its current durable-prefix endpoint and whether its epoch is
closed. The collector merges reports by maximum and computes the minimum over
every worker on its shard. It sends that component, its epoch, and its final
status to observers. Each observer merges received components by maximum into
its own epoch-indexed vector. These actions never test the candidate against
the global durable-prefix state.

The proof establishes that each component is bounded by every worker stream on
its shard. When the collector has received closure reports from every worker,
its computed minimum equals the final shard watermark. An observer assembles a
final vector only after receiving every shard's finalized component.

A healthy stream reports infinity only after all its installs and replication
finish. A failed or timed-out stream closes with its current finite durable
prefix. Closed endpoints never change, even across further epoch advances;
this remains the Paxos recovery interface.

The current epoch can advance before old streams close. New transactions may
read same-epoch speculative versions, but can read earlier-epoch versions only
when that transaction's observer-local watermark covers them. This permits healthy new-epoch work
to proceed during recovery without inheriting an uncertain old dependency.
Rollback compares the transaction against the observer's assembled final
vector. The proof establishes its equivalence to the abstract final-cut test.

Worker reports and gossip can be delayed, duplicated, reordered, and dropped.
Messages retain their epoch and source component. A collector can restart,
clearing its reports, computed value, and final marker. An observer can restart,
clearing its vectors and final markers. Both can reconstruct their state from
fresh or delayed reports. The final-agreement theorem covers these executions.
Message forgery and Byzantine workers are outside the crash-failure model.

The original transaction/producer layer still abstracts these details:

- Its `Begin` action receives transaction dependencies and allocates clocks and
  participant reservations atomically. The separate OCC model now proves
  key-level validation and dependency-vector properties, but a general trace
  refinement from its split clock round to this atomic action is not provided.
- Paxos ballots, replicas, packets, leader election, and the configuration
  manager. Durable-prefix callbacks and closed-epoch immutability are their
  interfaces. A closed prefix includes all durability evidence already exposed.
- Physical epoch-switch barriers, batch encoding, vector compression, shard
  migration, log truncation, garbage collection, and Thomas-rule value replay.
  Replay here records a safe fragment decision, not a database value update.
- Read-only transactions, whose empty WriteSets do not enter the producer model.
  They are covered by the separate OCC serializability proof.
  There is no fairness or eventual-recovery assumption.

Production actions do not test the inductive invariant or a global safety
postcondition. The abstract `Publish` bound is discharged by the refinement
proof after a gossip delivery.
The proof derives watermark coverage from stream ordering and reservations.
In particular, `Acknowledge` does not require every fragment to be installed
or durable; the theorem establishes those facts from its watermark guard.

## Explicit OCC proof

The OCC model follows Section 4.2. Transactions optimistically read records and
buffer their writes. They freeze both sets, acquire exclusive locks on each
write key, and obtain an incremented clock from each write shard. Clock replies
and validation requests can interleave with other transactions. The computed
vector is the componentwise maximum of those replies and all read versions.
Validation compares the actual version vector and rejects a record locked by
another transaction. Each read is checked separately. Every read must pass before
any writes can be installed. Installation and lock release are atomic per shard;
different shards install independently. Aborts release locks before certification.

`Certified` in this model names the successful validation decision before the
install round, not completion of all install acknowledgments. Read and write
sets remain immutable from that point. The model retains historical metadata;
physical rollback is handled through the retained-set semantics below.

A proof-only counter assigns a distinct serial position after the last clock
reply and before the first validation. Protocol guards never inspect that
counter. The proof establishes:

- Authentic versions identify their writers and values. A written shard's vector
  component equals its uniquely allocated clock ticket; equality of full version
  vectors therefore cannot hide an overwrite, even when the value is unchanged.
- An installed writer must hold the key's write lock. A validated read excludes
  both installed and still-pending earlier writers that could contradict it.
- In increasing serial order, each certified transaction reads the last preceding
  writer's value, or the initial database value. `execute` constructs that
  sequential execution; its read values are proved equal to the observed values.
- Certification before another transaction is opened implies a smaller serial
  position. Final completion is later than certification, so this also preserves
  non-overlapping real-time order within the epoch.
- Each computed vector covers every actual read dependency's vector. Thus every
  vector cut is dependency-closed, and removing transactions above that cut
  preserves the retained transactions' sequential read semantics. This theorem
  does not assume that the cut was correctly produced or that OCC is correct.
  Durability additionally uses the watermark-production proof.

| Theorem | Checked statement |
|---|---|
| `theorem_occ_serializable` | All certified transactions in any OCC history admit the proved serial order. |
| `theorem_sequential_reads` | Sequentially executing retained predecessors returns the value actually read. |
| `theorem_real_time_order` | A transaction certified before another opens precedes it in the serial order. |
| `certified_dependency_clock` | An actual read dependency has an earlier serial position and a componentwise smaller-or-equal vector. |
| `theorem_vector_cut_serializable` | Any finite/infinite componentwise vector cut preserves serializable retained reads. |
| `theorem_occ_and_watermark_safety` | Matching OCC and producer records yield serializable retained reads, durable retained write fragments, and the existing producer safety properties. |

The scope is one speculation epoch with an arbitrary stable initial database,
unbounded point keys and integer values, finite read/write sets per transaction,
and no bound on transactions, schedules, or clock values. Read-only transactions
are included in the OCC theorem. Range queries and phantom detection, finite
clock wraparound, torn record reads, RPC implementation details, and the C++ code
are not modeled. Atomic record/version reads, lock operations, counter increments,
and shard-local installation are the primitive operations. This is a protocol
proof of OCC built from those operations, not a proof of their implementation.

The composition interface is intentionally explicit. It has no OCC-correctness
or dependency-closure premise, but it still requires the producer to contain the
same computed vectors and write participants for certified transaction IDs in the
selected epoch. A constructive two-shard execution satisfies this interface and
commits. Proving the interface for **every** concrete OCC/replication execution,
and proving that physical recovery supplies a consistent base to the next epoch,
remain separate obligations. In particular, the producer's atomic clock
allocation does not automatically cover all orders of the OCC model's separate
GetClock replies. The new proof must not be described as a complete removal of
all cross-layer assumptions from the existing multi-epoch model.

## Watermark production proof

`core.wm` in the production state is a ghost maximum of delivered components.
It exists to construct the abstract history. Transaction guards read the
specified observer's `views`, and the concrete action type rejects abstract
`Publish`, `Finalize`, and `Rollback` actions. Finalization and rollback instead
use the received final markers and observer-local vector.

| Theorem | Checked statement |
|---|---|
| `minimum_lower`, `minimum_greatest` | The reduction returns exactly the minimum of all worker reports, including finite and infinite endpoints. |
| `theorem_production_refines` | Every production behavior projects to a valid behavior of the abstract transaction protocol. |
| `theorem_production_safety` | The speculation, durability, and rollback safety properties hold for the producer and gossip state machine. |
| `theorem_observer_watermark_sound` | A transaction below an observer's received vector has every participant fragment durable and is not doomed. |
| `theorem_produced_final_cut` | A fully assembled final vector covers exactly the transactions covered by the abstract final cut. |
| `theorem_final_agreement` | Finalized components agree across observers and later states, including after restarts and reconstruction. |
| `receive_isolated`, `receive_monotone` | Delivery changes only the addressed observer, epoch, and shard component, and cannot regress its value. Explicit restarts may reset volatile values to zero. |

The proof starts from durable-prefix callbacks and closed-epoch reports, rather
than proving that a quorum of Paxos replicas generates those callbacks. It
formalizes the uncompressed scheme in Sections 4.4 and 5; it does not verify
Appendix D's compressed-vector pseudocode or the C++ callback implementation.

## Theorems

| Theorem | Checked statement |
|---|---|
| `theorem_mako_safety` | Every reachable state satisfies acknowledgment durability, absence of mixed replay/rollback outcomes, dependency rollback closure, and exclusion of incomplete installs from a finalized cut. |
| `theorem_final_atomicity` | A transaction retained by a finalized cut has all participant fragments durable and none rolled back. An excluded transaction has no acknowledgment or replay, and every installed fragment permits rollback. |
| `theorem_transitive_rollback` | Every transaction on an arbitrary read-dependency path from a doomed transaction is also doomed, in the same epoch. |
| `theorem_bounded_rollback` | Once an epoch has advanced, its finite set of transaction IDs is fixed throughout all later states. Rollback candidates cannot grow into new epochs. |
| `theorem_ack_irrevocable` | An acknowledged transaction remains durable and cannot be rolled back in any later state, across any number of recoveries. |
| `theorem_final_cut_stable` | The membership predicate for a finalized cut is identical in every later state. |

Atomicity concerns agreement and durability. Physical replay and undo happen
asynchronously, so the theorem does not require simultaneous changes on every
shard. Without fairness it also does not claim every eligible fragment is
eventually replayed or undone. Bounded rollback means a fixed finite set for
each closed epoch, not a workload-independent numeric bound.

The invariant records stream order, pending reservations, durable coverage,
watermark bounds, immutable transaction metadata, read-dependency order, and
past decisions. The proof connects `initial` to the invariant, every `next`
action to invariant preservation, and the invariant to safety. No safety
invariant appears as a hypothesis of the public history-based theorems.

## Reproduce

Run the standalone crate, so other protocols' trusted modules cannot hide
proof obligations:

```bash
VERUS_PATH=/path/to/verus scripts/verify_mako.sh
VERUS_PATH=/path/to/verus scripts/verify_mako_controls.py
(cd src/tla+/Mako && java -cp /path/to/tla2tools.jar tla2sany.SANY MakoProduction.tla)
(cd src/tla+/Mako && java -cp /path/to/tla2tools.jar tla2sany.SANY MakoOCC.tla)
```

Validation result: **123 verified, 0 errors**, with all eleven negative controls
rejected as intended. SANY reports no syntax or semantic errors for all three
TLA+ companion modules.

The verifier run uses `--no-cheating` and Verus
`0.2026.08.02.b677dd5`, with its bundled solver. The model uses `IMap` and
`ISet` explicitly for mathematical maps and sets that may have infinite domains.
The standalone proof contains no `assume`, `admit`, external proof bodies, or
trusted-module annotations. No files under `src/generated` are changed.

The standalone proof and all eleven controls also pass on rolling Verus
`0.2026.10.04.426d8b0`. Publication checks must cover both the pinned and rolling
toolchains, including CI's whole-crate verification (`scons --verus-path=/path/to/verus`),
not just the standalone harness. On the rolling toolchain, unfolding `read_max`
inside `step_streams` caused excessive quantifier instantiation; this lemma
keeps that predicate locally opaque because it needs only the allocated-clock
equation. The partial-failure scenario supplies explicit installed-transaction
and missing-shard witnesses. These proof hints do not change the model,
theorem statements, or solver resource limits.

The constructive scenario proofs establish that the model permits:

1. A two-shard transaction to install, replicate, acknowledge, and replay.
2. A transaction missing an install on one shard, a dependent transaction on
   the other shard, and rollback of both. Independent new-epoch work commits
   before the old epoch is finalized.
3. A two-shard commit through computed and delivered watermarks, while a second
   observer still has a stale vector.
4. A lagging second worker holding a shard watermark at zero, subsequent
   advancement after both workers report, and a commit. Finalized gossip then
   survives stale deliveries, an observer restart, a collector restart, and
   two epoch advances.
5. A partial transaction rolled back using the produced final vector
   `[Infinity, 0]`.
6. An OCC transaction reading a speculative writer and successfully certifying.
7. An equal-value overwrite failing validation because its version changed;
   an uninstalled writer's lock also blocking validation.
8. A read-only transaction certifying after a conflicting writer aborts.
9. A vector cut retaining a writer while removing its dependent transaction,
   and another cut removing both when the writer is excluded.
10. Matching OCC and producer histories reaching a durable two-shard commit.

The `collect` and `produce` witness helpers construct finite schedules for
arbitrary worker counts. They are existence proofs; they do not assume fair
scheduling or establish eventual delivery for every execution.

Negative controls run on temporary copies. Each must fail with an actual
proof error, rather than a compiler error or solver resource exhaustion:

- Allow infinity on a stream with a pending install.
- Permit a new-epoch read of an unstable old version.
- Acknowledge before the transaction is below the watermark.
- Compute a maximum instead of a minimum across worker reports.
- Relabel a received component with the receiver's current epoch.
- Replace a newer component with the value in a stale message.
- Validate an OCC read without comparing its version.
- Validate through another transaction's write lock.
- Enter OCC validation without requiring all write locks.
- Certify without checking every recorded read.
- Omit read vectors from the computed transaction vector.

These checks test the proof's sensitivity to the protocol rules. They do not
replace the unbounded inductive proof or establish source-code refinement.
