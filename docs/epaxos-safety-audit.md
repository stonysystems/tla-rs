# EPaxos safety audit

The current simplified EPaxos model does not satisfy the planned execution
refinement for an application whose commands all conflict. This is a verified
counterexample in the repository's model, not a claim about every EPaxos variant.
The positive distributed safety and crash-recovery goals remain unproved.

The [implementation plan](epaxos-proof-plan.md) records the required model
repairs. The audit is in
[`safety_audit.rs`](../src/protocol/EPaxos/safety_audit.rs).

## Execution counterexample

There are three replicas A, B and C. Both quorum sizes are two, matching the
current three-node runtime configuration. Start every replica with `LInit`.
Interpret commands 10 and 20 as distinct operations that conflict, for example
appending different tokens to the same sequence.

| Step | Action |
|---|---|
| 1 | A proposes command 10 and broadcasts PreAccept. |
| 2 | C receives A's request and replies with `conflict = false`. It retains no record of the request. |
| 3 | A receives C's reply, giving it the quorum {A, C}. |
| 4 | A fast-commits command 10. |
| 5 | A executes command 10. Its execution history is `[10]`. |
| 6 | B proposes command 20 and broadcasts PreAccept. |
| 7 | C receives B's request and again replies with `conflict = false`. |
| 8 | B receives C's reply, giving it the quorum {B, C}. |
| 9 | B fast-commits command 20. |
| 10 | B executes command 20. Its execution history is `[20]`. |

No sequential history can have both `[10]` and `[20]` as prefixes. For this
all-conflicting workload, the execution histories cannot refine one sequential
state machine. The witness uses distinct proposals, valid replica identities and
replies that were actually sent. It needs no crash or packet forgery.

This claim concerns actual execution prefixes. It does not mistake EPaxos
sequence numbers for Raft log indices, or require different instances to choose
the same command. It also does not assert that both nodes already executed both
commands in opposite orders. The refuted goal is the common-history refinement
required for this particular workload.

`lemma_conflicting_execution_prefixes` constructs the reachable execution.
`lemma_no_sequential_execution_refinement` states that it has no common
sequential execution history.

## Reply replay counterexample

After A executes command 10 in the first five steps above, it runs `LNewInstance`
and proposes command 20. Deliver the old reply from C to A again, without
delivering command 20's request to C. `LReceivePreAcceptOk` accepts it and
`LFastCommit` can commit command 20 using {A, C}.

`lemma_stale_reply_crosses_instances` checks this schedule. It refutes the
auxiliary obligation that replies counted toward a quorum belong to the current
instance. This is a separate finding from the execution-refinement failure.

## What the checker verifies

The audit defines a small distributed wrapper around existing source predicates:

- Every action calls its existing `LPropose`, `LSendPreAcceptOk`,
  `LReceivePreAcceptOk`, `LFastCommit`, `LExecute`, `LNewInstance` or `LRecover`
  predicate. None of these predicates was changed for the audit.
- The network contains only packets emitted by those actions. Delivery checks
  the destination, message variant and sender. Old packets remain available for
  delayed or duplicate delivery.
- Pre-accept replies use the current host's actual policy: `conflict = false`
  and `seq = committed_count`. This policy is visible in
  `src/implementation/EPaxos/host.rs::handle_preaccept`.
- Execution histories observe `LExecute` and impose no safety guard on steps.
- `lemma_step_projects_to_source` and `lemma_behavior_projects_to_source`
  connect the wrapper to the checked-in `LInit` and `LNext` predicates.
- `lemma_extend` proves reachability of the constructed traces from the initial
  state. The witnesses are not arbitrary unreachable states.

The wrapper includes only the actions needed by these witnesses. A legal subset
of transitions suffices to refute a universal safety goal. This audit does not
claim complete runtime refinement, a complete EPaxos specification, or a reboot
theorem. It adds no trusted proof bodies, `assume`, or `admit`.

## Reproduce

Use the repository's pinned Verus release, `0.2026.08.02.b677dd5`:

```bash
VERUS_PATH=/path/to/verus scripts/verify_epaxos_safety_audit.sh
```

The command checks the audit and the existing EPaxos source and generated action
modules together. A successful run verifies the counterexamples and local
action contracts. It does not mean the requested EPaxos safety theorem passed.

Recorded result: **27 verified, 0 errors** with Verus
`0.2026.08.02.b677dd5`. This includes eight audit proof functions and the existing
generated action contracts. The script exits successfully, `bash -n` passes,
and `git diff --check` reports no whitespace errors.

The source behavior under audit is from commit `8ce08b74`. Generated executable
files and runtime handlers are unchanged.
