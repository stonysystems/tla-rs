# EPaxos distributed safety proof plan

The requested goal is a model-level distributed safety proof, including recovery,
comparable in scope to the Raft proof. The audit started from the actual predicates
in `src/protocol/EPaxos/epaxos.rs` and found checked counterexamples. The user then
selected the corrected EPaxos* baseline for the positive model proof.

## Proof goals

- Agreement on the command and ordering attributes chosen for each instance.
- Compatible execution order for commands that conflict. Independent commands
  may execute in different orders, so equal Raft-style log positions are not the
  right EPaxos property.
- Validity: only proposed commands execute, at most once per command identity.
- Stability: chosen commands and their dependencies survive later protocol
  actions and reboots that preserve durable state.
- Refinement to an abstract execution history respecting those properties.

The theorem must allow asynchronous message delay, duplication and reordering,
and arbitrary reboots under explicit persistence assumptions. Liveness and a
storage implementation are outside this task.

## Execution plan

1. Audit the existing model and host against the goals. Construct Verus-checked
   executions for suspected failures, using the existing action predicates.
   Separate failures of the desired safety property from failures of auxiliary
   proof obligations. Do not infer agreement failure from equal sequence numbers
   on different instances.
2. If the goals hold for the audited transitions, define the distributed state,
   routed network, command identities, conflict relation, execution history and
   behavior relation. If an execution refutes a goal, record it and the required
   model repair before claiming a positive theorem.
3. Establish the protocol invariants: authenticated and instance-bound responses,
   durable promises and accepted records, quorum intersection, uniqueness of
   chosen attributes, dependency coverage of conflicting commands, and safe
   execution of dependency graphs. Derive these from protocol actions, never
   require the desired safety theorem as a transition guard.
4. Add recovery and reboot transitions. Prove recovery selection preserves
   chosen attributes, retained state survives reboot, and delayed replies cannot
   be counted for a different instance or ballot.
5. Prove initialization and induction for every transition, then the distributed
   safety and refinement theorems for every finite valid behavior.
6. Verify every added lemma and affected module with pinned Verus. Record the
   command, result, assumptions, and remaining gaps. If executable generation
   changes, regenerate through the transpiler and verify its contracts. Never
   hand-edit `src/generated/`.

## Initial audit

The model has one reusable slot, a dependency count rather than dependency sets,
and no instance identity in messages. `PreAcceptOk` and `AcceptOk` omit ballots.
`LSendPreAcceptOk` and `LSendAcceptOk` leave recipient state unchanged.
`LExecute` tests only that the local slot is committed. `LRecover` restarts
pre-accept at a larger ballot without reading a quorum's accepted records.

The host's pre-accept handler always reports `conflict = false`, its commit
handler leaves the state unchanged, and it has no durable log of instances.
The [safety audit](epaxos-safety-audit.md) adds machine-checked witnesses for an
execution-refinement failure and reuse of an old reply for a new instance.

## Status

- Step 1: complete. The source audit and checked counterexamples are documented
  in `epaxos-safety-audit.md`.
- Step 2: complete. The separate EPaxos* model defines instance identities,
  routed packets, dependency sets, execution histories, and finite behaviors.
- Steps 3 through 5: complete. The proof covers agreement, conflict dependency
  coverage, compatible execution prefixes, validity, at-most-once execution,
  committed stability, reboot, and refinement to an abstract committed graph.
  All model actions participate in induction, including recovery validation and
  waiting resolution. No action requires agreement or execution safety as a guard.
- Step 6: complete. All EPaxos* model and proof modules pass together,
  **139 verified, 0 errors**, with Verus `0.2026.08.02.b677dd5`. The separate
  audit and existing EPaxos action modules also pass together,
  **27 verified, 0 errors**. No generated code changed.

The [EPaxos* proof report](epaxos-star-proof.md) records the exact theorem scope,
persistence assumptions, reference differences, and verification command.

## Required model repairs

The source audit identifies the following prerequisite changes. These change
the protocol model, not merely its proof annotations.

1. Replace the reusable scalar slot with a map from `InstanceId` to durable
   records. An identity must include its original coordinator and a persistent
   counter. Each record needs the command, dependency set, status, highest
   promised ballot and last accepted ballot. Keep the two ballots distinct.
   The selected EPaxos* baseline orders each strongly connected component by
   instance identity and does not use the simplified model's sequence number.
2. Carry the instance identity and ballot in requests and replies. Match both
   on receipt, verify sender membership, and collect each sender once for that
   particular round. Record accepted attributes before acknowledging them.
3. Define command conflicts and compute actual dependency sets. A fast-path
   certificate must concern identical ordering attributes for one instance;
   a boolean conflict flag and reply count do not establish that agreement.
   Parameterize and prove the relevant fast/slow quorum intersections.
4. Add commit reception and durable storage of learned instances. Execute only
   when the required dependency graph is committed, using deterministic ordering
   within strongly connected components and explicit execution bookkeeping.
5. Replace `LRecover`'s unconditional restart with a specified recovery protocol
   that collects durable records from a quorum and selects safe attributes.
   Define reboot by separating those durable records from transient reply maps
   and coordinator activity. Delayed pre-reboot packets remain deliverable.
6. Prove the repaired distributed model. Connecting generated actions and host
   message dispatch to it remains a separate implementation task. A proof of
   the corrected specification does not prove the existing implementation.

The pinned community specification in
`transpiler/tests/corpus/tier2/t2_02_epaxos/original.tla` can guide the instance
and message types. Its `clean.tla` derivative omits recovery and execution and
therefore cannot supply the requested proof by itself.

Recovery needs an explicitly selected reference algorithm. The
[EPaxos* paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.OPODIS.2025.22)
documents problems with original EPaxos recovery and gives a corrected variant.
Its baseline algorithm is the reference for the new proof model.

The user selected the recommended EPaxos* reference. The proof model lives in
`src/protocol/EPaxos/star/`; it is separate from the simplified runtime model
whose counterexamples remain in the audit. The target is model-level safety and
reboot recovery. Connecting a generated implementation to the repaired model
is a separate obligation and will not be implied by a model theorem.
