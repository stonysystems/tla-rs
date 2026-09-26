# Tiga model and proof plan

The target is the Tiga protocol in the SOSP 2025 paper, including normal
transaction processing and view-change recovery. The model will live under
`src/protocol/Tiga/`. It will not change generated code or the EPaxos work.

## Sources

- [SOSP paper](https://mpaxos.com/pub/tiga-sosp25.pdf), DOI
  [10.1145/3731569.3764854](https://doi.org/10.1145/3731569.3764854).
- [Technical report, version 1](https://arxiv.org/html/2509.05759v1), especially
  Algorithms 2, 3, and 5 and the claims in Appendix C.
- [Authors' TLA+ repository](https://github.com/New-Consensus-Concurrency-Control/Tiga-TLA-plus),
  compared at commit `9a4a8c9`; see the audit's source section.
  The paper and technical report remain the model's sources.

## Requested proof goals

1. Per-shard agreement and preservation of committed transaction results.
2. Validity and at-most-once transaction identity handling.
3. Preservation of committed transactions and their ordering during recovery.
4. Serializability across shards, including reads and writes.
5. Real-time consistency of completed transactions, giving strict serializability.

Safety must tolerate delayed, duplicated, and reordered messages. Clock accuracy
must not be a safety precondition. The view manager can be represented as an
abstract consistent configuration service, as permitted by the paper, with that
boundary documented. No proof of a storage implementation, hash collision
resistance, or liveness will be implied by a safety result.

## Execution plan

1. Map the paper's normal-processing and recovery rules to explicit transitions.
   Distinguish transaction submission, optimistic execution, timestamp agreement,
   client completion, replica synchronization, and view changes.
2. Write a distributed model with real sent-message evidence for each receipt,
   per-replica views and queues, explicit transaction operations, and client
   histories. Model hash comparison as exact equality of the relevant history.
3. Check recovery obligations with concrete source-valid traces before investing
   in induction. If a trace contradicts a requested theorem, prove the trace and
   violation and identify the responsible rule. Do not add the safety property
   as a transition guard or silently replace the published algorithm.
4. Establish quorum, reply-binding, ordering, and recovery invariants. Prove the
   goals that follow from the encoded transitions; record any failed goals.
5. Verify every added lemma with pinned Verus, check the repository's trigger
   ceiling, and document the exact coverage and remaining obligations.

## Outcome and remaining work

The paper-based recovery trace and its external strict-serializability violation
are encoded and checked. See [the recovery audit](tiga-safety-audit.md) for the
execution, disputed rule, repair candidate, and model boundaries.

| Work item | Status |
|---|---|
| Normal processing and view-change submodel | Added under `src/protocol/Tiga/` |
| Fast and slow quorum intersection bounds | Proved for arbitrary valid fault bound |
| Reachable changed-result counterexample | Proved from initialization and sent messages |
| External history violation | Proved, allowing pending transactions to complete or be omitted |
| Conservative recovery repair | Separate candidate transition and local preservation theorem |
| Repair regression on the same recovery input | Proved; the candidate installs A before B |
| Published protocol's requested safety theorem | Refuted by the encoded recovery execution |
| Complete safety theorem for the repaired protocol | Open |

The user requested a report for possible bugs and attempts to fix them. The
candidate preserves each reconstructed shard prefix in a common transaction
order before installing imports. It changes the recovery protocol. It is not
presented as the paper's original transition or as a verified runtime fix.

The next full-proof obligations are to establish preservation of completed
prefixes by local reconstruction across arbitrary views, agreement on recovery
payloads and the installed common order, and induction through normal operation
and later recovery. Incompatible reconstruction prefixes currently block the
candidate; a progress-preserving resolution needs its own protocol rule and
proof. Server rejoining, retries, preventive mode, and implementation refinement
remain outside the present submodel.

Verification: 34 verified, 0 errors with pinned Verus and the default resource
limit. The trigger inventory passes the zero-note ceiling.
