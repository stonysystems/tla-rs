# Tiga recovery audit

The published recovery rule has a reachable counterexample in the paper-based
Verus model. It violates preservation of completed results and produces a client
history that is not strictly serializable. A separate recovery candidate fixes
this trace and has a general local result-preservation proof. Whole-protocol
safety for that candidate remains unproved.

## Sources and interpretation

The model follows the [SOSP 2025 paper](https://mpaxos.com/pub/tiga-sosp25.pdf)
and [technical report v1](https://arxiv.org/html/2509.05759v1), Algorithms 2, 3,
and 5. The disputed operation is Algorithm 5, lines 73 through 89. It imports missing
transactions from other shards, takes each transaction's largest reported
timestamp, and sorts the receiving shard's log.

The report's Lemma C.2 excludes a newly preceding transaction by counting local
replicas that held it before recovery. The cross-shard import does not require
that local support. This is the proof obligation exposed below.

This finding concerns the encoded published rule. The authors'
[TLA+ specification](https://github.com/New-Consensus-Concurrency-Control/Tiga-TLA-plus)
(commit `9a4a8c9`) uses the same rule. `HandleCrossShardVerifyRep` adds a
missing transaction at its largest reported timestamp and re-sorts the log. The
requester's `syncedDdl` bound is the timestamp of its last synchronized entry.
In this trace no X entry was ever synchronized, so the bound does not exclude
B. That specification's `CoordSubmitTxn` makes every transaction involve every
shard. The trace needs a transaction that skips shard Y, so it lies outside the
model-checked state space. The C++ implementation was not compared.

## TIGA-001: imported transactions can precede completed conflicting work

Use two shards, X and Y, each with three replicas and failure bound one.
X replicas are 0, 1, 2; Y replicas are 3, 4, 5. Initial leaders are 0 and 3.
Each shard initially stores integer zero. Transactions have fixed participants.

| Name | Model ID | Proposed timestamp | Operation |
|---|---:|---:|---|
| B | 0 | 10 | Write 10 to X and Y |
| A | 1 | 20 | Increment X and return its previous value |
| R | 2 | 30 | Read X |

The execution is constructed from the model's initial state. Every received
message was emitted by an earlier transition.

1. Submit B, then A. Delay B's messages to all X replicas and to Y's leader.
2. Y followers 4 and 5 receive and release B, leaving `[B@10]` in their logs.
3. All three X replicas receive and release A. Leader 0 returns zero. The
   coordinator receives three matching fast replies and completes A with zero.
4. Leader 0 crashes. A global view change selects leaders 1 and 4. Replicas
   1, 2, 4, and 5 enter that view and send their reports. The Y leader change
   follows the report's Algorithm 4. Its `find-new-leaders` chooses the first
   replica index that is alive in every shard. With replica 0 of X down, index 1
   leads both shards. No second crash or false suspicion is required.
5. X rebuilds from replicas 1 and 2, obtaining `[A@20]`. Y rebuilds from 4 and 5,
   obtaining `[B@10]`. Both entries meet the recovery threshold of two. All four
   reports have an empty synchronized prefix and last-normal-view zero.
6. The leaders exchange their reconstructed logs. X imports B at timestamp 10
   and installs `[B@10, A@20]`. Replay now makes A return 10 and leaves X at 11,
   although A already returned zero to its client.
7. Follower 2 installs X's new log. Submit R after A's completion. Leader 1
   executes R, agrees on its timestamp, and synchronizes it to follower 2.
   A leader fast reply and follower slow reply complete R with result 11.

The trace needs no forged packets, hash collisions, clock-bound assumption,
insufficient quorums, duplicate execution, or messages accepted in the wrong
view. B remains pending from its client's perspective.

Even allowing pending B to complete cannot explain the observed history.
Real time requires A before R. The possible serial completions are:

| Serial order | A returns | R returns |
|---|---:|---:|
| A, R, with B omitted | 0 | 1 |
| B, A, R | 10 | 11 |
| A, B, R | 0 | 10 |
| A, R, B | 0 | 1 |

None produces A=0 and R=11. The Verus theorem quantifies over all candidate
serial completions, including omission of pending B; it does not merely check
this table by hand.

## Other pseudocode ambiguities

These are possible specification defects, not additional verified safety
counterexamples:

- Algorithm 5 computes the largest synchronized prefix among reports with the
  greatest last-normal-view, but its following selection line only mentions the
  synchronized-prefix equality. The model also requires the chosen report to
  have the greatest last-normal-view, following the recovery prose.
- Some recovery message handlers compare local views without an explicit global
  view check. Cross-shard local views can differ. The model binds messages to
  the current global view and the destination shard's local view.
- Timestamp-verification pseudocode tests whether a transaction involves shard
  `s` while iterating destination shard `ss`. The model imports only transactions
  whose declared participant set includes the destination shard.

These interpretation choices are explicit model guards. They do not repair
TIGA-001, which still occurs with matching views and valid participants.

## Candidate repair and its limits

The candidate is in `src/protocol/Tiga/repair.rs`. The published transition stays
intact so its counterexample remains reproducible.

Each new leader collects the same per-shard reconstruction payloads. Instead
of sorting their union by old timestamps, it constructs a common transaction
order with these requirements:

- Every recovered transaction occurs once.
- Projecting that order onto each shard starts with that shard's reconstructed
  transaction sequence. Imports therefore follow that prefix.
- All leaders use a deterministic choice over the same normalized payloads.

The abstract transition assigns new timestamps from positions in that common
order and installs each shard's projection. This changes Algorithm 5. These
are model transitions, not changes to runtime or generated implementation code.
The choice is over finite transaction orderings; an implementation would need
a deterministic ordering algorithm and messages that establish identical
reconstruction inputs.

For this trace the order must be `[A, B]`. X replays A with result zero, then B
writes 10. Y replays B. The regression proof reaches the same pre-installation
state as the counterexample and applies the candidate transition successfully.

The general local theorem proves that an enabled candidate transition preserves
the result of every transaction in its reconstructed local prefix, for arbitrary
prefix lengths and the modeled operations. Its precondition uses collected
logs, not a global oracle telling the replica which clients completed.

This is a conservative repair candidate. Incompatible prefix constraints make
it refuse installation. We have not proved that compatible orders always exist,
that local reconstruction always retains every completed prefix across arbitrary
views, or that all leaders always obtain identical normalized payloads. Its
full strict-serializability, durability, retry, and progress proofs remain open.
Raising imported timestamps independently at each shard would not settle those
obligations either; the common order must preserve dependencies across shards.

## Verification boundaries

The model includes routed asynchronous messages, queues, monotone local clocks,
optimistic leader execution, timestamp agreement, fast and slow commit evidence,
view changes, local reconstruction, cross-shard import, and fail-stop crashes.
It models the baseline detective mode with one integer key per shard and fixed
transaction read/write sets. State-machine effects are a deterministic fold of
the log; speculative work remains in the queue until agreement.

Full prefix equality represents collision-free history hashes. The transaction
body dictionary abbreviates bodies carried in requests and recovery messages.
The view manager is an abstract consistent configuration service. The model
binds both global and local views, chooses the maximal last-normal-view before
the synchronized prefix, and allows one reconstruction per leader per view.
These follow the intended prose rather than exploiting pseudocode omissions.

The model does not yet cover server rejoining from Algorithm 6, coordinator
retry, preventive mode, commutativity/hash optimizations, interactive
transactions, persistent storage, or refinement to the C++ implementation.
This is a proof-oriented submodel, not a claim that the entire paper or runtime
has been translated.

`history.rs::theorem_published_recovery_counterexample` proves a reachable
violation of the external history specification. `audit.rs` also exposes the
changed-result theorem corresponding to Lemma C.2. `quorum.rs` proves the
fast/recovery and slow/recovery intersection bounds for arbitrary valid f.
`repair.rs::lemma_repair_preserves_results` and
`repair_audit.rs::theorem_import_regression_fixed` state the candidate's exact
proved guarantees.

Run all Tiga modules with:

```sh
VERUS_PATH=/path/to/verus scripts/verify_tiga.sh
```

The checked run used Verus `0.2026.08.02.b677dd5`, Rust `1.97.1`, and the
default resource limit. Result: **34 verified, 0 errors**. The selective trigger
inventory contains zero automatic trigger notes and passes the repository's
zero-note ceiling. The new Tiga modules contain no `assume`, admitted proof,
trusted body, or external proof declaration. Shell syntax and whitespace checks
also pass; generated files are unchanged.

A successful run verifies the counterexample and the stated local repair
properties. It is not a positive safety theorem for the published protocol.
