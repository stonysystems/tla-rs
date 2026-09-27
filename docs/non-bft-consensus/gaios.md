# Gaios and SMARTER read safety

Verus proves chosen-slot agreement, read freshness across leader elections,
and linearizability of finite register histories under explicit host contracts.
The source is [Paxos Replicated State Machines as the Basis of a High-Performance Data Store, NSDI 2011](https://www.usenix.org/legacy/events/nsdi11/tech/full_papers/Bolosky.pdf),
especially the five read-protocol steps in Section 3.3.2.

[reads.rs](../../src/protocol/Gaios/reads.rs) has fixed membership, per-slot
Paxos execution traces, leader views, replica recognition events, individual
view-check replies and read execution cuts. Event times are proof ordering
indices, not synchronized clocks used by the protocol.

| Source step | Model |
|---|---|
| Stamp with the greater of committed and reproposed horizons | `Stamp.cut = max(known, recovered)` |
| Send view checks after stamping | Each reply follows `Stamp.at` |
| Collect replies still recognizing this leader | Responders cannot report the old view after recognizing a higher one; read quorums intersect election quorums |
| Dispatch read with the stamp | Read records the associated stamp |
| Wait for the stamped prefix, then execute | `Read.cut >= Stamp.cut`, with the result of the actual executed prefix |

`read_is_fresh` handles writes from older, equal and newer views. Older-view
writes are covered by the recovery horizon. Same-view writes are covered by
the leader's known prefix. A completed newer-view write would force a
read-quorum member to have recognized the newer view, contradicting its reply.

`committed_slot_agreement` uses an actual shared-kernel Paxos trace for the
slot, proving every learned value equals its committed value. Chosen-value
agreement is not assumed as a host contract.

`linearizable_reads_and_writes` derives freshness and invokes
[`register_history::history_linearizable`](../../src/protocol/ConsensusSafety/register_history.rs).
That theorem constructs a strict total order, places a read after its executed
write prefix, proves its returned value is the last preceding write's value,
and preserves real-time order for every operation pair. Executed pending writes
may be completed in the witness; unexecuted pending operations can be omitted.
This establishes register linearizability, beyond just read freshness.

The host contracts require durable, ordered prefix execution, accurate
same-view committed metadata, and a recovered horizon covering every
lower-view decision. The last condition is a substantive view-change
obligation, not proved by this read model. The shared kernel abstracts Phase 1
collection atomically. Dynamic membership and the configuration-change check
need a separate model. General Gaios storage operations, disk/checkpoint
refinement, retries and liveness remain open.

`gaios_nonempty_read` in [the execution witnesses](../../src/protocol/next_five_witnesses.rs)
constructs a Paxos write of `7` and a completed read returning `7`, establishing
that the premises admit nonempty behavior. See
[verification metadata](next-five-verification.json) for digests and commands.
