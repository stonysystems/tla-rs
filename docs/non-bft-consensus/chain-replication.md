# Chain Replication: history safety

Source: van Renesse and Schneider, [Chain Replication for Supporting High
Throughput and Availability, OSDI 2004](https://www.cs.cornell.edu/home/rvr/papers/OSDI04.pdf),
Section 3.1. The model captures ordered propagation and abstracts membership
changes into atomic steps. The paper's master notification protocol and transfer
handshake still need refinement proofs.

## State and actions

The Verus state has a nonempty sequence of replica histories, an equally long
sequence of live/dead flags, and a set of submitted request identities. Histories
contain identities, not application values. Two different requests may carry the
same value in a later application model.

| Action | State change |
|---|---|
| Write | A live head appends a fresh request identity and records its submission |
| Forward | A live successor appends the next entry from its predecessor's history |
| Crash | Marks one replica dead |
| Remove | Atomically removes a dead replica if at least one replica remains |
| Extend | Atomically installs a fresh tail containing an exact copy of the live old tail |
| Stutter | Leaves state unchanged |

Forwarding abstracts FIFO messages. A dead predecessor can supply a previously
recorded entry, representing a message sent before its crash. Explicit sends,
buffers, acknowledgments and incarnation numbers are absent. Removing a replica
also abstracts retransmission across the new link. There are no competing
configurations or false suspicions. Extension represents completion of state
transfer, with no partially copied tail visible to clients.

The model may reach a state with every replica dead. Safety does not require
continued availability. It does not erase persistent histories, replace the
whole chain, or recover a dead node in place. Fresh tails are the only additions.

## Invariant and proved statements

Let `prefix(x, y)` mean that `x` is an initial segment of `y`, and let `C(s)` be
the last replica's history in state `s`. The inductive invariant asserts:

1. Histories and live flags have the same positive length.
2. For every upstream position `i` and downstream position `j`,
   `prefix(history[j], history[i])` holds.
3. Every history entry belongs to the submitted set.
4. No replica history contains the same request identity twice.

In [paper_model.rs](../../src/protocol/ChainReplication/paper_model.rs), the
verifier checks initialization and preservation for every action. Preservation
also establishes `prefix(C(s), C(t))` and monotonicity of the submitted set.
`reachable_inv` then proves the invariant for every state of any finite behavior
starting with any positive number of replicas. `completed_prefix_never_lost`
proves, for arbitrary positions `i <= j` in that behavior,
`prefix(C(states[i]), C(states[j]))`. `committed_valid_and_unique` derives
validity and uniqueness of tail-history identities.

The proof uses the following arguments. A head append extends an upstream
history. Forwarding extends a successor by precisely its next predecessor entry.
An internal removal preserves the prefix ordering of surviving histories. Tail
removal promotes an upstream history which already extends the old tail. Tail
extension copies the committed history exactly. Prefix transitivity then gives
preservation over arbitrarily many steps. The request-freshness precondition
supports identity uniqueness; it is not a proof of client retry deduplication.

`next` does not test the invariant or assume the theorem it is meant to prove.
The file contains no `assume`, `admit`, or trusted external proof bodies. The
result still trusts Verus, its standard library and solver. It proves safety of
this mathematical transition system, not the network implementation.

## Checks performed

On September 26, 2026, Verus `0.2026.08.02.b677dd5` reported **10 verified,
0 errors**, both for the standalone file and when selected through `src/lib.rs`.
The latter command was:

```bash
verus --crate-type=lib src/lib.rs \
  --verify-only-module protocol::ChainReplication::paper_model \
  --triggers-mode silent
```

The [TLA+ specification](../../models/non_bft/chain_replication/ChainReplication.tla)
and [configuration](../../models/non_bft/chain_replication/ChainReplication.cfg)
use three request identities, three initial replicas and a maximum chain length
of three. TLC reports **12,059 generated states, 2,632 distinct states, depth 13,
and no invariant violation**. The checked properties are type correctness,
propagation, validity, uniqueness and preservation of the previous tail history.
The extra TLA+ variable `previous` is a monitor, not a protocol variable.

Run [verify_consensus_chain.sh](../../scripts/verify_consensus_chain.sh) as shown
in the ledger README. The bounded TLA+ result supports debugging; the Verus
induction supplies the unbounded finite-execution safety result. No fairness
assumption or liveness property was checked for Chain Replication.

Three deliberate mutations were also checked with
[verify_consensus_chain_mutants.py](../../scripts/verify_consensus_chain_mutants.py).
An empty newly installed tail violates `CompletedPrefix`; removing request
freshness violates `Unique`; forwarding the predecessor's last entry instead
of its next entry violates `Propagation`. All three produced the expected TLC
counterexample. Run these controls with:

```bash
TLA2TOOLS=/path/to/tla2tools.jar python3 scripts/verify_consensus_chain_mutants.py
```

## Open obligations

Formalize the master's messages, epochs, acknowledgment tracking and state
transfer, then prove refinement to these atomic actions. Add client invocation
and response events, application state and reads, and prove linearizability
with explicit linearization points. Prove progress under stated delivery,
reconfiguration and failure assumptions. None of those claims follows solely
from the history theorem recorded here.
