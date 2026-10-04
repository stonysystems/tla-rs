# PAC recovery: reproducing a published counterexample

The 2019 paper [Unifying Consensus and Atomic Commitment for Effective Cloud
Data Management](https://www.vldb.org/pvldb/vol12/p611-maiyya.pdf) introduces PAC
and G-PAC. Its [2021 erratum](https://www.vldb.org/pvldb/vol14/p1166-maiyya.pdf)
corrects Algorithms 3 and 4. Keep the versions separate.

The defect is recovery's preference for any accepted `commit`, even when a
response contains a later accepted `abort`. The correction selects the value
with the highest accepted ballot when no responder reports a decision.

## Encoded execution

All five cohorts initially vote commit. The local TLA+ model executes:

| Stage | Quorum or recipient | Result |
|---|---|---|
| Ballot 1 election | 1, 2, 3, 4, 5 | Propose commit |
| Partial acceptance | 1 | Only cohort 1 accepts commit |
| Ballot 2 election | 2, 3, 4 | Propose abort |
| Acceptance and decision | 2, 3, 4 accept; 2 decides | Abort has a quorum |
| Ballot 3 election | 1, 3, 4 | Original rule chooses commit despite later abort votes |
| Acceptance and decision | 1, 3, 4 accept; 3 decides | Cohorts 2 and 3 disagree |

This instantiates the published witness with numbered cohorts. Delays and
incomplete leader actions suffice; no node fabricates a response.

## Local verification

[PACRecovery.tla](../../models/non_bft/gpac/PACRecovery.tla) abstracts quorum
collection into an atomic election and retains accepted votes as certificate
history. It explicitly updates promises, acceptances and decisions. Its replay
selects a fixed sequence of enabled protocol actions; it does not inject the
final conflicting state directly.

On September 26, 2026, TLC 2.19 checked the original-rule configuration and
reported `Invariant Agreement is violated`, exit code 12, after 13 distinct
states. The corrected-rule configuration explored the same 13-state schedule
without disagreement. It also checked `ReplayCompletes` under weak fairness,
so the regression cannot pass merely by blocking before the last action.

```bash
TLA2TOOLS=/path/to/tla2tools.jar scripts/verify_consensus_gpac.sh
```

The script succeeds only if the original produces the expected agreement
counterexample and the corrected replay succeeds. A parser or type error is
not accepted as a counterexample. Logs and hashes appear in
[verification.json](verification.json).

This is a model of the PAC recovery witness, not a full sharded G-PAC model.
The original's failing trace is finite evidence against its modeled agreement
claim. Passing the corrected replay establishes no general safety or liveness
theorem for the repair. Those proofs, and a complete message-level paper/model
correspondence, remain open. This package contains no Verus proof of G-PAC.
