# Jetpack recovery audit

Figure 14 of the Jetpack paper, read literally, can leave a fast-committed
command out of the recovery set. Two of its recovery rules allow this. Each
yields a counterexample to the completeness half of the paper's Lemma 2, and
with a crash it can lose the command, violating durability claim C1. The
Lemma 2 executions are machine-checked; the C1 consequence is argued.

The merged recovery RPC of Appendix B.2, the authors' TLA+ specification and
their implementation exclude the first execution. None of them has a
FinishRecovery staleness check that stops the second. The repository's Verus
proof of Jetpack recovery covers a model that excludes both, and it remains
sound for that model. A Verus module added with this report checks both
executions against that model with one rule changed at a time.

## Sources

- [OSDI 2026 paper](https://www.usenix.org/system/files/osdi26-tang.pdf),
  SHA-256 `19b480f481b862543cb2270bde0f1d77f9e0c31b6f7f073eb50d0d525191559e`.
  Page numbers are proceedings pages. Bare line numbers refer to Figure 14;
  TLA+ and Rust line numbers name their file. Quotations normalize apostrophes.
- Authors' TLA+ specification at commit `c03e318`, copied byte for byte in
  [`docs/jetpack_reference/`](jetpack_reference/).
- Verified recovery model:
  [`src/protocol/Jetpack/recovery.rs`](../src/protocol/Jetpack/recovery.rs) at
  commit `f82c8ec0`, documented in
  [the Jetpack proof report](non-bft-consensus/jetpack.md). This audit does not
  modify it.

## Rules involved

Quotation marks mark verbatim text; other entries paraphrase.

| Location | Rule | Page |
|---|---|---|
| §2 | "messages can be delayed arbitrarily" | 1300 |
| Fast-path processing | A replica acknowledges a conflict-free command whose view matches its current view. A superquorum of `f + ⌈f/2⌉ + 1` acknowledgments that includes every original-path proposer fast-commits the command. A proposer also proposes the command on the original path. | 1304 |
| Same section | "every message carries the sender's view so receivers can detect stale operations" | 1304 |
| Principle 1 | A command is fast-committed only when both paths are in the same view. The fast path keeps its own view. | 1305 |
| §4.3, Phase 1 | "It retries until a majority of replicas acknowledge." | 1306 |
| B.1 | BeginRecovery freezes the fast path "so that no fast path can succeed during recovery." | 1317 |
| Lines 3-5 | The coordinator sends BeginRecovery to the replica set of `vn`. A replica enters recovery mode and replies. Neither message carries a view. | 1318 |
| Line 6 | After `f + 1` BeginRecoveryOK replies, send Prepare(`vn`) to the replica set of `vn`. | 1318 |
| Lines 7-10 | A replica returns its accepted recovery set, or else its `vn` log. The handler neither checks nor sets recovery mode. | 1318 |
| Lines 11-17; §4.3, Phase 2 | Use any `f + 1` PrepareOK replies ("collects replies from a majority"). A command in `⌈f/2⌉ + 1` replies joins the recovery set. | 1318, 1306 |
| Lines 25-27 | The coordinator sends FinishRecovery with its view. A replica sets its view to that view and returns to normal mode, with no condition. | 1318 |

## JETPACK-001: Prepare answered by a replica that never froze

Take three replicas `R0`, `R1` and `R2` with `f = 1`. A fast commitment then
needs all three acknowledgments, the recovery threshold is two, and a majority
is two. `R0` is the only original-path proposer of view `vn`. Command `x`
carries view `vn`.

| Step | Event | Rule |
|---:|---|---|
| 1 | `R0` and `R1` acknowledge `x` in `vn`. | Fast-path processing |
| 2 | Proposer reelection starts view `v`. The coordinator sends BeginRecovery. `R0` and `R1` enter recovery mode and reply. The copy to `R2` is delayed until after step 5, and retries stop at the majority. | Lines 3-5; §4.3 |
| 3 | The coordinator sends Prepare. `R1` replies with log `{x}`. `R2`, still in normal mode, replies with an empty log. | Lines 6-10 |
| 4 | `x` occurs in one of the two replies, below the threshold. The empty set is proposed, accepted by `R1` and `R2`, and chosen. | Lines 11-20 |
| 5 | `x` reaches `R2`. `R2` is still normal in `vn` and `x` is conflict-free, so `R2` acknowledges it. | Fast-path processing |
| 6 | The client holds same-view acknowledgments from all three replicas, including proposer `R0`. `x` is fast-committed. | Fast-path processing; Principle 1 |

Phase 3 then commits a no-op as the stability marker, and recovery of `vn`
ends without `x`, although the client holds a fast-commit certificate for it.
This is a counterexample to the completeness half of Lemma 2 for Figure 14 as
printed. The certificate completes after the recovery set is chosen. Lemma 2
and B.3.2 cover every command fast-committed in `vn`, without a timing
condition, and B.1 states that freezing exists "so that no fast path can
succeed during recovery." Here one succeeds.

The execution needs three conditions.

- No BeginRecovery for `vn`, from any coordinator, takes effect at `R2` before
  `R2` acknowledges `x` in step 5. The paper's model permits this delay:
  messages can be delayed arbitrarily, and the coordinator retries only until a
  majority acknowledges. Reliable FIFO links would prevent it, even with
  several coordinators, because each sends BeginRecovery (line 3) before Prepare
  (line 6). Under such links, `R2` could answer Prepare in normal mode only after
  a FinishRecovery unfroze it, which is JETPACK-002.
- `R2`'s view is still `vn` at step 5. Under Figure 14 only FinishRecovery sets
  a replica's view (line 26), and FinishRecovery(`v`) has not been sent. If
  fast-path processing instead compares against the replica's original-path
  view (page 1304), `R2` must also not have learned of `v` from the original
  protocol. `R0` and `R1` can elect the new proposer without `R2`.
- Prepare and Accept do not move `R2` out of `vn`. Figure 14 sends Prepare(`vn`)
  and Accept(`vn`, set) (lines 6 and 18), and their handlers (lines 7-10 and
  19-20) change neither view nor mode. §4.3 writes PREPARE(`vn` → `v`) (page
  1306), and every message carries its sender's view (page 1304), but no rule
  has a receiver adopt `v`. A replica that adopted `v` and then refused `vn`
  commands would block step 5. That rule would block every execution of this
  kind, since a command missing from the PrepareOK snapshots but on a
  superquorum at the end must have been acknowledged by some replier after its
  reply.

### Durability

C1 fails only if the original path also drops `x`. `R0` proposed `x` on the
original path (page 1304). In the execution above, the second condition keeps
`R0` in the majority that elects the new proposer if the fast path compares
against the original-path view. Raft, Multi-Paxos and VR then carry `R0`'s
durable copy of `x` forward, and `x` survives unless `R0` had not yet made that
proposal durable. If only FinishRecovery sets a replica's view, `R1` and `R2`
may instead elect a proposer that lacks `x`, and C1 fails.

With `f = 2`, C1 fails under either reading. Take `R0` to `R4`, with `R0` the
proposer. The superquorum is four, a majority three, the threshold two.

1. `R0`, `R1` and `R3` acknowledge `x`. `R0`'s original-path proposal of `x`
   reaches no other replica, and `R0` crashes.
2. `R1`, `R2` and `R3` elect a new proposer, which lacks `x`.
3. BeginRecovery freezes `R1`, `R2` and `R3`. The copy to `R4` is delayed.
4. Prepare replies come from `R2` (empty), `R3` (`{x}`) and `R4` (empty, still
   normal in `vn`). `x` has one supporter, and the empty set is chosen.
5. `R4` acknowledges `x`. With `R0`, `R1` and `R3`, the superquorum is complete
   and includes `R0`. Recovery ends with a no-op, and no live replica's
   original-path log contains `x`.

This `f = 2` execution is argued from the paper's rules, not machine-checked;
the Verus model has no original path.

### Why the paper's proof misses it

The durability proof in B.3.2 (page 1319) counts replicas that store the
command: it "has been stored on `f + ⌈f/2⌉ + 1` replicas", and "[a]mong any
`f + 1` replicas of `vn`'s membership participating in recovery, at least
`⌈f/2⌉ + 1` contain the command." Lemma 2 reuses this argument (page 1320).
A PrepareOK reply is a snapshot, not a replica's final log. A replica that has
not frozen can acknowledge after it replies. Freezing binds only the
BeginRecovery majority, and Figure 14 never requires the PrepareOK replies to
come from that majority.

B.2 says the three operations of its merged RPC "do not depend on one another,
so they can be executed together without changing the protocol's semantics"
(page 1318). Freezing must precede the log snapshot, so they do depend on one
another. The merged RPC excludes this execution, so merging is not a
semantics-preserving change. It does not exclude JETPACK-002.

### What excludes it

- B.2's first merged RPC "performs BEGINRECOVERY, pulls log metadata, and
  executes PREPARE." Every reply then comes from a replica that entered
  recovery mode in the same handler, provided the handler freezes before or
  while it reads its log. B.2 does not state that order.
- In the authors' TLA+, `HandleBeginRecoveryRequest` (`jetpack.tla`, line 469)
  enters recovery and returns the fast log in one step. `CompleteBeginRecovery`
  (line 497) computes the recovery set from those replies. Prepare replies carry
  no fast log; their payload (`PrepResp`, line 130) is the accepted ballot and
  value.
- The Verus model's `prepare` requires `s.frozen.contains(a)`
  (`recovery.rs`, line 130).

A repair consistent with all three: a replica must be frozen for `vn` before it
returns its `vn` log. For example, the Prepare handler can enter recovery mode
before replying, or logs can travel only in BeginRecoveryOK.

## JETPACK-002: a delayed FinishRecovery unfreezes a replica

FinishRecovery carries the coordinator's view (line 25), but lines 26-27 install
it without comparison. A check against the replica's own view would not help.
In the execution below, the delayed message carries `vn` while `R2`'s view is
older, because line 26 is the only assignment to a replica's view and `R2`
missed that copy. Rejecting the message requires `R2` to remember that it has
joined a recovery of `vn`. Prepare carries `vn` (line 6), but no handler stores
it or compares FinishRecovery against it.

Use the same replicas and command. `K1` and `K2` are coordinators.

| Step | Event |
|---:|---|
| 1 | Coordinator `K1` finishes recovering the view before `vn` and sends FinishRecovery(`vn`). `R0` and `R1` receive it. The copy to `R2` is delayed. |
| 2 | `R0` and `R1` acknowledge `x` in `vn`. |
| 3 | View `v` starts. Coordinator `K2` sends BeginRecovery for `vn`. `R1` and `R2` enter recovery mode and reply. |
| 4 | Prepare replies come from `R1`, with `{x}`, and `R2`, with an empty log. The empty set is proposed, accepted by `R1` and `R2`, and chosen. |
| 5 | `K1`'s delayed FinishRecovery(`vn`) reaches `R2`. `R2` sets its view to `vn` and returns to normal mode. |
| 6 | `x` reaches `R2`. `R2` is normal in `vn` and `x` is conflict-free, so `R2` acknowledges it. |
| 7 | With `R0` and `R1`, `x` is fast-committed and missing from the chosen set. |

Every Prepare reply here comes from a frozen replica, so B.2's merged RPC does
not prevent this execution; B.2 leaves FinishRecovery unchanged. The execution
needs these conditions.

- `K1` and `K2` are different coordinators. Otherwise per-link FIFO delivery
  would bring FinishRecovery(`vn`) before BeginRecovery.
- `x`'s copy to `R2` is delivered only after step 5. Before then `R2` is paused
  or in an older view, and with three replicas one rejection ends the fast path.
- `R2` does not reject FinishRecovery using the view carried by `K2`'s messages.
  Figure 14 has no such check.
- As in JETPACK-001, if fast-path processing compares against the
  original-path view, `R2` has not learned of `v` from the original protocol
  before step 6. Durability C1 fails under the same conditions as there.

The authors' TLA+ records the new view and its epoch at BeginRecovery
(`jetpack.tla`, lines 473-474). `HandleFinishRecovery` (line 733) never compares
against them. It sets the replica to `Ready`, overwrites both `jepoch` and
`oepoch` with the message's epoch (lines 736-737), and empties the fast log
(line 740). The Prepare and Accept handlers do compare epochs (lines 530 and
626). In the Raft composition only reconfiguration creates a new Jetpack epoch
(`WRequestReconfig`, `jetpack_raft_composition.tla`, lines 173-186); other
actions copy existing epochs, and leader election leaves them unchanged
(`BecomeToBeLeader`, lines 141-143). For a view
change caused by reelection, a check patterned on lines 530 and 626 would not
distinguish `K1`'s FinishRecovery from `K2`'s. The composition's checked
`Safety` property (lines 428-433) has no conjunct stating that a fast-committed
command reaches the recovery set or the original log. This audit did not run
TLC.

The Verus model excludes the execution by construction. It has no
FinishRecovery transition and no transition that unfreezes a replica, and
`view_change.rs` opens each new view as a fresh recovery instance.

A possible repair: a replica records the view whose recovery it has joined, and
ignores FinishRecovery for that view or an older one. It must record the view
before it sends its Prepare reply. BeginRecovery can carry the view, or Prepare
can, which already carries `vn`, provided the replica is frozen when it replies.
This repair is not verified.

## Authors' implementation

The C++ implementation at `stonysystems/jetpack` commit `c03e318` was read, not
run. Line numbers refer to `src/deptran/scheduler.cc` unless another file is
named.

- JETPACK-001 does not occur. The merged handler `OnJetpackPullRecovery`
  (line 1653) calls `OnJetpackBeginRecovery` (line 1698), which enters recovery
  mode, before it snapshots the command pool. `JetpackCommandPool::push_back`
  rejects fast-path commands in recovery mode (line 822).
- JETPACK-002's missing check is present in another form.
  `OnJetpackFinishRecovery` (line 1991) accepts a message whose `oepoch` is at
  least the replica's. It then clears the command pool, including the recovery
  ballots, accepted set id and commit flag (`reset`, line 1069), and returns
  the replica to normal mode. The comparison does not separate recoveries. Each
  recovery sends the coordinator's current `oepoch_` in PullRecovery and
  FinishRecovery (lines 1160 and 1503), and `OnJetpackBeginRecovery` copies it
  into every replica (line 1702). Raft leader election changes the view and
  starts recovery without changing `oepoch_` (`raft/server.cc`, lines 568-592).
  Successive recoveries therefore normally share one `oepoch`, and a delayed
  FinishRecovery from an earlier recovery can return a replica of a later
  recovery to normal mode and erase its recovery state.

A lost-write schedule follows by the reasoning of JETPACK-002, under the same
delay conditions. It was not executed.

## Machine-checked executions

[`src/protocol/JetpackAudit/figure14.rs`](../src/protocol/JetpackAudit/figure14.rs)
extends the verified model. Every step is a `recovery::next` step except the
one rule under test.

| Theorem | Rule under test | Proved |
|---|---|---|
| `theorem_unmerged_prepare_loses_fast_commit` | `prepare_literal`: any replica, frozen or not, may reply once some `f + 1` replicas have frozen | A reachable state where command 7 is fast-committed and the empty set is chosen. Replica 2 replies without freezing. |
| `theorem_stale_finish_loses_fast_commit` | `resume`: a frozen replica returns to normal mode | The same outcome, with every Prepare reply from a frozen replica |
| `corollary_model_excludes_both` | None | No execution of the verified model reaches that outcome |

Each theorem states that all steps of its execution but one are
`recovery::next` steps, and that no `recovery::next` action produces the
remaining step. The corollary applies `recovery::execution_safety`. Adding
`assert(false)` to either theorem makes verification fail.

The executions use `f = 1`, replicas `{0, 1, 2}`, one command and no
conflicts. The model's fast certificate counts acknowledgments only; each
execution includes the proposer, replica 0, as the paper requires. Ballots and
one value per ballot are the model's Paxos rules, which Figure 14 abbreviates
and B.1 calls "a standard Paxos instance" (page 1317). The model has no message
buffer: each step is one replica handler, and a delayed message is a step not
yet taken. `resume` lets any frozen replica leave recovery; the second execution
uses it once, for replica 2, to stand for `K1`'s delayed FinishRecovery. That
execution starts at table step 2, so replica 2 begins unfrozen, but it
acknowledges nothing before it freezes.

```bash
VERUS_PATH=/path/to/verus scripts/verify_jetpack_recovery_audit.sh
```

Recorded with Verus `0.2026.08.02.b677dd5`: **6 verified, 0 errors**, namely
the two theorems, the corollary, one lemma per out-of-model step, and a
set-size lemma. The run uses `--no-cheating`. `figure14.rs` has no `assume`,
`admit` or trusted body, and produces no automatic-trigger notes; the five
printed notes come from `recovery.rs`. The corollary relies on
`recovery::execution_safety`, which `scripts/verify_consensus_jetpack.sh`
verifies. The module is a standalone crate that includes `recovery.rs` by path,
so each run checks the executions against the current model. It is not part of
`src/lib.rs` or CI. No generated files changed.

A passing run proves that these executions exist in the extended model. It is
not a positive result about any version of the protocol.

## Scope

- These are counterexamples to Figure 14 and §4.3 as printed, under the
  paper's network model. The implementation findings above come from reading
  its source; nothing was compiled or run.
- JETPACK-001 does not apply to B.2's merged RPC, the authors' TLA+ or their
  implementation. B.2's merged RPC does not prevent JETPACK-002. The TLA+ and
  the implementation lack the comparison JETPACK-002 needs; whether TLC or the
  running system can reach the execution was not tested.
- The repository's Verus theorems remain sound for their model. Its proof
  report lists correspondence with unmerged recovery schedules as open;
  JETPACK-001 shows the literal unmerged protocol fails. JETPACK-002 falls under
  that report's open obligation that old-view messages be rejected. It also
  shows that a message's own view tag is not enough: the stale FinishRecovery
  carries a view newer than the receiving replica's.
