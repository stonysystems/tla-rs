# Next five protocol safety results

This batch covers the next five chronological catalog entries without an
existing proof package or counterexample audit. All evidence is deductive Verus
verification. Liveness is excluded at the user's request.

| Protocol | Formally established | Scope and limits |
|---|---|---|
| [Om, NSDI 2004](om.md) | Conditional agreement and input validity; two counterexample witnesses | Agreement requires intersecting quorums and defined mixed-branch lookups. The literal read/write model is non-linearizable. Figure 5 can encounter a missing proposal lookup. |
| [Gaios, NSDI 2011](gaios.md) | Slot agreement, read freshness, register-history linearizability | Fixed membership; explicit recovery-horizon and execution contracts. |
| [CORFU, NSDI 2012](corfu.md) | Per-position agreement, validity, epoch fencing, single-assignment refinement and layout agreement | Atomic full-chain migration; whole-log append and sequencer refinement remain open. |
| [Replicated Commit, VLDB 2013](replicated-commit.md) | Commit agreement, prepared-quorum validity and stable decision refinement | One transaction; explicit classic-Paxos recovery completion. Multi-transaction serializability remains open. |
| [Speculative Paxos, NSDI 2015](speculative-paxos.md) | Fast/slow agreement, recovery preservation, execution consistency and client linearizability | Fixed membership, fenced snapshots, exact prefix hashes and deterministic execution. |

These are scoped protocol models, not proofs of the authors' implementations or
paper-level completion claims. Om cannot receive a positive linearizability
result for the literal normal-case model checked here.

The shared [Paxos kernel](../../src/protocol/ConsensusSafety/paxos.rs) generalizes
the existing Mencius instance proof. It proves agreement from intersecting
quorums, promises and maximum-accepted adoption. Phase 1 collection is atomic;
acceptance is per replica. Gaios, CORFU and Replicated Commit add their own
rules. Om and Speculative Paxos have separate agreement proofs.

[Constructive examples](../../src/protocol/next_five_witnesses.rs) exercise a
nonempty Om decision, a Gaios write and read, CORFU migration after a crash,
Replicated Commit recovery after a chosen commit, and Speculative Paxos fast
completion followed by reconciliation. Their existence is also proved in Verus.
They supplement the general theorems; they do not replace them.

Reproduce from the repository root:

```bash
VERUS_PATH=/path/to/verus scripts/verify_consensus_next_five.sh
VERUS_PATH=/path/to/verus scripts/verify_consensus_next_five.sh --integrated
python3 scripts/consensus_catalog.py --check
```

The script uses `--no-cheating` and verifies every module in this standalone
batch. [Verification metadata](next-five-verification.json) records tool and
source digests, named theorems, commands and logs. The crate integration check
selects only these new modules. No generated code is edited.
