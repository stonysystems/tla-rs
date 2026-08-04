# t1_02_twophase — rewrite notes

**Source**: `tlaplus/Examples` `specifications/transaction_commit/TwoPhase.tla`
**Pinned commit**: `fd8de28dded6278d5091ab981923843aad787a4c`
**Clean-distance at intake**: 2 (C1 on `tmState` and `tmPrepared`)

> Fill this in while writing `clean.tla`. It is the record of what a human decided,
> and it is what makes the rewrite reviewable. Do not leave TODOs in a case that is
> marked `clean` in the manifest.

**Status**: `clean.tla` written, linter accepts, TLC checked side by side with the
original, translated and verus-verified, golden frozen.
**Reference**: `src/protocol/TwoPhase/twophase.rs` (review aid, never byte-diffed)

## Which variable is the network (C4)

`msgs`, already a set. The rewrite adds `src` and `dst`: the original's
`[type |-> "Commit"]` is unaddressed and any RM may read it, which a projected
node cannot do. A broadcast becomes one message per recipient.

Messages are never removed, as in the original.

## The transaction manager (C1) — the decision this case is about

The two C1 violations the linter reported are `tmState` and `tmPrepared`: the
coordinator's state, which in the original belongs to **no node**. 2PC has two
roles, and that is the question the rewrite has to answer.

Three options were considered:

1. **Fold the role into every node**, as Paxos's anonymous leader was folded.
   **Wrong here.** 2PC needs exactly one coordinator; two of them could commit
   and abort the same transaction.
2. **Add the TM to the node set** (`Node == RM \cup {TM}`). Then `rmState` has
   to be defined for a node that is not a resource manager, which is worse than
   the problem it solves.
3. **Make the TM a designated node.** `TM` is a constant drawn from `RM`, every
   node carries `tmState` and `tmPrepared`, and the coordinator actions are
   guarded by `a = TM`. **Chosen.** It is what a real deployment does — the
   coordinator is one of the participants, and everyone knows which — and it
   makes every variable per-node without inventing a role.

Only `TM`'s entries ever change: the other nodes' coordinator fields sit at
their initial values forever. That is the price of the encoding, and it is the
same price a real implementation pays by shipping coordinator code to every
node.

## No counting here (P4 does not apply)

`tmPrepared[a] = RM` stays a comparison against the whole node set.
**2PC needs unanimity, not a majority**, so there is no quorum to count. The
contrast with Paxos's `IsMajority` in `t1_01_paxos` is worth keeping: P4 is a
rule about quorums, not a rule about every guard that mentions a set.

## Instantaneous cross-node reads message-ified (C2)

None were needed. The original already communicates by messages.

## Semantic-fidelity claim (V2) — the strongest in the corpus so far

Unlike Paxos, 2PC's original has a directly checkable safety property, so this
is a genuine side-by-side. TLC 2.19, `RM = {r1, r2, r3}`, `TM = r1`, with the
same `Consistent` invariant added to the original:

| | original | clean |
|---|---|---|
| states generated | 1,146 | 1,146 |
| distinct states | 288 | 288 |
| depth | 11 | 11 |
| type invariant | holds | holds |
| `Consistent` | holds | holds |

**The counts are identical, and that is explained rather than lucky.** The
rewrite is a bijection on reachable states: a broadcast's |RM| messages are
always added together and never removed, so each corresponds to exactly one
message of the original; and the coordinator fields change only at `TM`, so the
per-node functions correspond to the original's scalars. Nothing was added to
or removed from the state space.

This is what a V2 check should look like when the rewrite is structure-
preserving — and it is worth contrasting with LamportMutex, where the state
counts legitimately differ because the rewrite changed the state's shape.

## V2 strong fidelity: the state-set comparison (53.6)

This is the first case run through
[`scripts/tlc_fidelity.sh`](../../scripts/tlc_fidelity.sh), which dumps both
specs' full state spaces and compares them projected onto the observables the
case declares in `observables.toml`.

The observable is **`rmState`**, and it is the whole of 2PC's observable
behaviour: it is what `TCommit`'s `TCConsistent` is stated over, and what a
client of the protocol sees. Everything else is bookkeeping the rewrite
deliberately reshaped — `tmState`/`tmPrepared` became per-node fields of the
designated TM, and `msgs` gained `src`/`dst` — so none of it compares across
the two specs.

At `RM = {r1, r2, r3}`, `TM = r1`:

| | |
|---|---|
| states dumped, clean | 288 |
| states dumped, original | 288 |
| distinct `rmState` values, clean | 34 |
| distinct `rmState` values, original | 34 |
| result | **EQUAL** |

**Read that precisely.** It says the rewrite reaches exactly the same `rmState`
values as the original. It does **not** say the two are behaviourally
equivalent, and this case proves the difference: deleting `RMChooseToAbort` from
`clean.tla` entirely leaves the comparison reporting EQUAL, because an RM still
reaches `"aborted"` by receiving the TM's abort. A path disappears and the tool
is silent. Deleting `RMPrepare`, which does remove states, is caught (8 vs 34,
26 states only in the original) — that is how the check was confirmed
non-vacuous.

## Translator gap this case exposed

One: a receive handler that takes **nothing** beyond the state. A `Commit`
message has no payload and `RMRcvCommitMsg` does not use the sender, so the
generated dispatch produced an empty argument slot (`LRMRcvCommitMsg(s, s_, c, ,
sent_packets)`). Fixed.

## Golden review

The golden is the translator's actual output, verus-verified with 0 errors.
Against the hand-written `src/protocol/TwoPhase/twophase.rs`: the hand-written
spec keeps **global** sets (`tm_prepared`, `rm_prepared`, `rm_committed`,
`rm_aborted`) rather than projecting per node — it is a single-process model of
the *whole* protocol, not of one node. The generated spec is genuinely
per-node, so the two are not in correspondence here, and this is the one tier-1
case where the hand-written reference is **not** a useful review oracle. That
is a fact about the reference, not about the translation.

## Reproducing the TLC runs

```bash
mkdir clean && cp clean.tla clean/TwoPhaseClean.tla
printf 'CONSTANTS\n  RM = {r1, r2, r3}\n  TM = r1\nSPECIFICATION Spec\nINVARIANTS TypeOK Consistent\n' > clean/TwoPhaseClean.cfg
(cd clean && java -cp tla2tools.jar tlc2.TLC -workers 8 TwoPhaseClean)

# the original needs TCommit.tla beside it; add the same Consistent invariant
# to compare like for like.
```
