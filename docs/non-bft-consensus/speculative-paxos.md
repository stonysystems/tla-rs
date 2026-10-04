# Speculative Paxos safety and linearizability

Verus proves fast/slow agreement, preservation across arbitrarily many modeled
views, execution consistency, and client-history linearizability for
deterministic state machines. The source is
[Designing Distributed Systems Using Approximate Synchrony in Data Center Networks, NSDI 2015](https://www.usenix.org/system/files/conference/nsdi15/nsdi15-paper-ports.pdf),
Sections 4.1 through 4.3.

[reconciliation.rs](../../src/protocol/SpecPaxos/reconciliation.rs) models the
final append-only normal-view log at each replica, reconciliation snapshots,
initial logs installed in each view, and fast/slow prefix certificates. There
are `2f+1` replicas. A fast certificate needs `f+ceil(f/2)+1` matching prefixes,
expressed as `f+(f+1)/2+1` in integer arithmetic. Reconciliation collects `f+1`
snapshots and considers those with the highest previous normal view. It selects
a longest prefix supported by a strict majority of that subset and installs
a log extending it.

| Source rule | Model and proof |
|---|---|
| Match speculative replies including summary hash | `fast`, exact common-prefix certificate |
| Freeze processing and report last normal view | `Recovery.previous`, fencing in `recovery_ok` |
| Use highest previous normal view | `highest` |
| Retain majority-agreed prefix | `majority_is_retained`, derived from support-set intersection and maximality |
| Install merged log and acknowledge reconciliation | `slow`, installed prefix with a majority of view installations |
| Append during normal processing | Each normal-view log extends its initial log |

`later_view_preserves` inducts over view numbers. If the highest previous
normal view is later than the certified view, induction preserves the prefix
in every selected snapshot. Otherwise, superquorum intersection leaves a
strict majority carrying the fast prefix. A slow prefix is already in the
initial log. `certificates_compatible` proves all certified prefixes are
comparable; `agreement` proves equal commands at shared slots.

[execution.rs](../../src/protocol/SpecPaxos/execution.rs) applies any
deterministic state machine to these prefixes. `execution_consistency` proves
equal results at shared certified positions. `history_linearizable` constructs
a sequential completion from the longest returned prefix, includes every
completed operation, preserves returned results and respects real-time order.
Operations in a response prefix must have been invoked before that response.
Unique logical request IDs prevent duplicate execution; invoked pending
operations may appear in the completion.

The model permits divergent speculative logs and needs no network-ordering
assumption for safety. `speculative_fast_then_reconciliation` in
[the execution witnesses](../../src/protocol/next_five_witnesses.rs) constructs
five replicas with a four-replica fast prefix and the opposite order at the
fifth. A three-replica recovery including the divergent replica preserves the
fast prefix and yields a slow certificate.

Snapshot fencing, one selected initial log per view, durable snapshots and
append-only normal logs are operational contracts, not derived here from
network handlers. Hashes are exact prefixes. Merge is a mathematical selection,
not verified merge code. COMMITTED markers and the optimization starting from
the largest committed prefix are omitted; the abstract merge must retain all
majority-supported prefixes. Appending every remaining request is a liveness
rule and is not required here. Concrete rollback, synchronization handlers,
checkpointing, lost-state recovery, dynamic membership and client retries
remain open. See [verification metadata](next-five-verification.json).
