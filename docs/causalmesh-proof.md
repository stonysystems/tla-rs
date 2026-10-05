# CausalMesh safety proof

Verus proves safety for the two-round CausalMesh protocol of arXiv 2508.15647
(v1 and v2). The results hold in every state of every finite execution,
including client migration and fan-out:

- A read's clock dominates every write to its key that happens before it.
- A read dominates every earlier read of its key that happens before it, in
  any session.
- The paper's four session guarantees hold on version clocks.
- Every read returns the initial value or the value of a write that happens
  before it.
- Every C-cache is a strict causal cut of the writes it covers and no longer
  holds pending in I-cache.

The proof allows any number of servers, clients and keys, and arbitrary message
delays on FIFO chains. The tail follows Figure 6 as printed: it integrates the
version's dependencies and then merges the version. The authors' Rust, Dafny
and TLA+ artifacts use the same order. The proof does not show that a read
returns the newest value (Finding 5).

A second theorem runs v2's rules with a single round. It constructs a reachable
execution in which a client observes a write at one server and then misses it
at another. The VLDB version also propagates once, but its server copies a
client's own writes into I-cache, and that blocks this particular execution.
The authors report the single-round bug for that variant with a different
execution: v2 §4.7 (Fig. 9) and §8.1, and v1 §10.1 (Fig. 17).

**Result:** 113 verified, 0 errors, with `--no-cheating` and no
automatic-trigger notes. Scope and exclusions are listed below.

## Sources

| Source | SHA-256 |
|---|---|
| PVLDB 17(13), pp. 4599-4613, 2024 ("VLDB"), 15 pages | `00e9044503aa6165c703bd8239821f91f6de9e327b1be18cb93def16bf0d2931` |
| arXiv 2508.15647v1, 18 pages | `c80d16d0f5ed64cd80ab83ec8e857f3a1eaf6558f454d688314c3062a20a14f8` |
| arXiv 2508.15647v2 ("v2"), 26 pages, the reference for this model | `c94624e992b5aeb5fe4466e4077028c9b729d09aca7353d7b563dc86b18f343d` |
| Authors' artifact, `github.com/eniac/causalmesh` | commit `65a192dcd34d82191e34109a8e468a4343a91fee`: Dafny proof, TLA+ spec, implementations |

v1 and v2 describe the same two-round protocol; v2 is the most complete. Page,
figure and section numbers below are v2's unless stated. v1 numbers them
differently: integration is Fig. 3 there, and propagation is §5.2.

## Which protocol is proved

| Rule | VLDB | v1, v2 | This model |
|---|---|---|---|
| Propagation | One pass around the chain (Fig. 5) | Two passes (Fig. 6; §4.4, p. 9) | A `rounds` parameter; the theorem requires `rounds >= 2` |
| Tail | Merge the clock, integrate `deps`, merge the version (Fig. 7, lines 22-27, p. 4605) | Same (Fig. 6, lines 26-31) | Same. The version is not removed from the tail's I-cache. |
| ClientWrite clock | Increment only; neither `deps` nor `local` is merged into the server clock (Fig. 7, line 8) | Merge `deps` and `local` into the server clock, then increment (Fig. 6, lines 8-14; Fact 3) | As v2 |
| Client's `local` on write | Added to the write's deps, and copied into the receiving server's I-cache (Fig. 7, lines 9-12) | Only added to the write's deps | As v2 |
| Integration match | Fig. 3 filters exact clocks (`vc ∈ vcs`) | Same pseudo-code (v1 Fig. 3, v2 Fig. 7). v2 §4.7 (p. 11) and v1 §10.1 describe integrating all smaller clocks. | A dependency `(k, vc)` matches every version of `k` at or below `vc`; see Finding 2 |

All three artifacts integrate the dependencies before merging the version:

- Rust `server_write` (`ccmesh/ccmesh/src/service.rs:596-613`)
- Dafny `ReceivePropagate` (`cache.dfy:737-753`)
- TLA+ (`causal-tla/mesh.tla:474-481`)

The artifacts differ in details. Dafny re-adds the version to I-cache at the
tail (`cache.dfy:753`); Figure 6 does not, and neither does the model. The Rust
server stamps the merged entry with its whole server clock, and never stores
the version in round one (Finding 6).

## Model

The model lives in [`src/protocol/CausalMesh/`](../src/protocol/CausalMesh/).
It follows Figures 4, 6 and 7 of v2. Server actions are atomic (Fact 1).
Each server's link to its chain successor is a FIFO queue (Fact 2).

| Paper operation | Model | Notes |
|---|---|---|
| `ClientWrite` (Fig. 6) | `client_write` | The clock is the server clock merged with deps and `local`, then incremented. The version enters I-cache and is sent at hop 1. |
| `ServerWrite`, not tail (Fig. 6) | `propagate`, non-tail branch | Store if not already seen, then forward at the next hop |
| `ServerWrite`, tail (Fig. 6, lines 26-31) | `propagate`, tail branch; `merged` | At hop `rounds * n - 1`: integrate the version's deps, then merge the version into C-cache and the server clock |
| `integrate` (Fig. 7) | `integrated` | Remove every I-cache version reachable from the deps through dependency chains; merge each into C-cache and the server clock |
| `ClientRead` and client merge (Figs. 4, 6) | `client_read`, `returned` | Integrate the client's deps, read C-cache, merge with the client's own write |
| Workflow start, fan-out (§2.1, §4.2) | `start_client`, `fork` | A forked function inherits `deps` and `local` |

Modeling choices:

- A C-cache update takes the exact join of the clocks. The stored value may be
  the value of any merged contributor. The paper's tie-break (§3.2) is one
  choice.
- A client read or write is processed and answered atomically. The client waits
  for each reply, so this loses no behavior.
- The model records a ghost history of client events and the set of writes each
  event is causally after. No protocol guard reads any ghost state.

Excluded: eviction and garbage collection, the storage path on a cache miss
(keys start at a zero clock and value 0), server crashes and failure recovery,
membership changes, the optional dissemination from the tail, read transactions
(§4.6), CausalMesh-TCC (§5), joining fan-out branches, and liveness, including
convergence (CC+ clause 4). The proof also assumes FIFO server links, as the
paper does (Fact 2). The authors' Rust server also starts with every key
present (`pull_deps2` panics on a missing key, `service.rs:325`), which matches
the storage-miss exclusion.

## Theorems

`theorem_causalmesh_safety` in
[`safety.rs`](../src/protocol/CausalMesh/safety.rs) holds for every state of
every finite behavior with `rounds >= 2`.

**Happens-before** over the ghost history is the transitive closure of:

- session order;
- fan-out from a fork to the child's later operations;
- a read *observing* a write of its key whose clock is at most the clock the
  server returned.

| Property | Statement |
|---|---|
| Causal visibility | If a write happens before a read of its key, the read's clock dominates the write's clock. This is stronger than CC+ clauses 2-3 (§2.2): a read observes every write of its key that the server's clock covers. |
| Causal monotonic reads | If a read happens before another read of the same key, in any session, the later read's clock dominates the earlier one's. |
| Read your writes (Theorem 1) | A client's read dominates its own earlier writes of that key. |
| Monotonic reads (Theorem 2) | A client's later read of a key dominates its earlier read of the key. |
| Writes follow reads (Theorem 3) | Suppose a client reads version `a`, then writes `w`, and another client observes `w` and then reads `a`'s key. That later read dominates the clock the server returned for `a`. |
| Monotonic writes (Theorem 4) | If a client writes `w1`, then `w2`, and another client observes `w2` and then reads `w1`'s key, that read dominates `w1`. |
| Read validity | A read returns the initial value with a zero clock, or the value of a write to its key that happens before the read and that the read's clock dominates. |
| Causal cut (Definition 1) | At every server, take a write that C-cache covers and that is not pending in I-cache. Every version matching one of its dependencies is covered and not pending. |

Definition 1 is about the set of writes a C-cache holds. A C-cache stores one
merged entry per key, so the theorem uses "covered, and not pending in I-cache"
for membership. Clock coverage alone is not enough (Finding 7). A version merged
at its tail (Fig. 6, line 29) stays in the tail's I-cache. The theorem covers it
only after a later integration pulls it out. Its dependencies were integrated
just before the merge (line 28), but the theorem does not state that.

The paper does not machine-check its client-side theorems (§8.3, "Step 3";
§8.4). Here they are proved from the transition relation.

These guarantees are stated on version clocks: a read reflects a write when the
returned clock dominates it. For values, only validity is proved. The model
lets a merged entry keep any contributor's value, including an older write's
value under a newer clock. §3.2's tie-break forbids some of those choices, but
Finding 5 shows it still allows a stale read. The theorems therefore say that
the right versions have reached the replica, not that the value returned is the
newest.

## Proof structure

| Step | Paper | Invariant or lemma |
|---|---|---|
| Channel dragging | Lemmas 2-3 | `drag_ok`: a version travels ahead of any message whose clock counts it, once the message has visited its origin within the last `n - 1` hops. FIFO and forward-on-first-receipt preserve it. |
| Availability at the tail | Lemmas 1, 3 | `lemma_tail_avail`: at the round-two tail, every write counted by the version's clock has reached every server |
| Availability of shown clocks | Lemmas 4-9 | `avail_ok`: C-cache entries and client deps count only writes that every server has seen |
| Integration | Lemmas 5, 6, 11 | `lemma_integrate`: integrating available deps keeps the cut and makes every write reachable from the deps visible |
| Tail merge | — | `lemma_merge`: every write that the merged clock newly covers was seen at the tail, so it is still pending in I-cache |
| Clients | Theorems 1-4 | `client_ok` and `events_ok`: an event's causal past is covered by the client's own writes or reachable from its deps, and every read dominates its causal past |
| Validity | — | `past_ok`: every write in an event's causal past happens before the event |

The cut invariant (`cut_srv`) excludes versions that are still pending. When a
read integrates its deps, each version on a dependency chain is one of two
things:

- still in I-cache, and reached by the chain, so integration pulls it;
- covered and no longer pending, so the cut makes its own dependencies visible.

The paper's Lemma 4 infers `v.vc ≤ PVC ⊔ v′.vc ⇒ v.vc ≤ PVC ∨ v.vc ≤ v′.vc`
(p. 20). That step is false for arbitrary vectors: `[1,1] ≤ [1,0] ⊔ [0,1]`.
The model avoids it:

- Availability is defined per origin counter, which is closed under join.
- A vector-clock knowledge invariant (`known`) states that a clock counting the
  c-th write of an origin dominates that write.

Together these make "below a join" imply "below a contributor" where the
causal cut needs it.

## Findings

### 1. Single-round propagation is unsafe (checked)

`theorem_single_round_violates_causality`
([`scenarios.rs`](../src/protocol/CausalMesh/scenarios.rs)) uses two servers,
`rounds = 1`, and v2's other rules.

1. Client 0 writes x at server 0. The copy of x to server 1 is delayed.
2. Client 0 moves to server 1 and writes z. x is in client 0's `local`, which
   Fig. 6 lines 8-10 fold into z's deps.
3. Server 0 is z's single-round tail. It integrates z's dependency x and merges
   z.
4. Client 1 reads x = 10 at server 0.
5. Client 1 reads x at server 1, which has not received x, and gets the initial
   value.

The history violates causal visibility and monotonic reads. Under two rounds,
z's second pass waits behind x on the FIFO link from server 0 to server 1.

The VLDB server also copies a client's `local` into the receiving server's
I-cache, which would place x at server 1 in this execution. v2's Figure 9 gives
an execution for that variant, through the smaller-clock implicit dependencies.
That variant was not mechanized here.

### 2. Figure 7's printed exact-match filter would break monotonic reads (argued)

Fig. 7 integrates only I-cache versions whose clock equals a dependency clock.
C-cache entries can hold the join of concurrent versions. A dependency may then
record a clock that no single version has, which §4.7 itself notes (p. 11). One
execution with two servers:

1. x₁ is written at server 0 with clock [1,0], and x₂ at server 1 with [0,1].
   Both finish two rounds, so each server stores both.
2. x₂'s tail, server 0, merges only x₂. x₁'s tail, server 1, merges only x₁.
3. A client reads x₂ at server 0, then reads at server 1. Its dependency [0,1]
   matches x₂ exactly, and server 1's C-cache entry becomes [1,1].
4. Client C reads [1,1] at server 1 and moves to server 0, where x₁ is still
   only in I-cache.
5. C's dependency [1,1] matches no single version. Integration pulls in nothing,
   and C reads an older clock.

The model uses the at-or-below rule of §4.7. Mutation M3 shows the proof
depends on it. The artifact uses the same rule in its TLA+ spec
(`mesh.tla:230`), its Dafny model (`pulldeps.dfy:249`) and its Rust server
(`service.rs:225, 344`). This finding concerns the printed pseudo-code only.

### 3. The authors' Dafny proof does not establish the stated lemmas (source reading)

These observations are from reading the artifact. Dafny was not run; it is not
installed here. Paths are under
`dafny/DistributedSystems/VerifiedDS/src/Dafny/Distributed/Protocol/CausalMesh/`.

**The exported theorem holds because a step guard requires it.**

- `lemma_CausalMesh_correctness` (`proof/proof.dfy:46-54`) ensures
  `AllServersAreCausalCut`, which is `ServerValid` for every server
  (`distributed_system.dfy:112-115`).
- `ServerValid` includes `CausalCut(s.ccache)` (`cache.dfy:575`).
- `CMNextCommon` requires every next-state server to be valid
  (`distributed_system.dfy:56`), so any step that would break the cut is
  excluded from the model.
- `PullDeps2` and `PullDeps3` carry `ensures CausalCut(c.1)`
  (`cache.dfy:454, 495`), but the behavior-level theorem never needs them.

**Two axioms are inconsistent, and two more carry the argument.**

- `lemma_MetaInMetas {:axiom}` (`proof/meta_is_met.dfy:588-589`) ensures
  `meta in metas` for any arguments. With an empty set it proves `false`. It is
  reachable from the exported theorem through this call chain:
  - `lemma_CausalMesh_correctness` calls `lemma_AllServersAreMetPrefix` (`proof.dfy:80`).
  - That leads to `lemma_ServersAreMetForCMNext` (`servers_are_met.dfy:81`), then its `_WithStateChange` variant (:320), then `lemma_PropagationAtTail` (:238).
  - That leads to `lemma_AllServersMetasInCacheSmallThanPVCIsMetOnAllServers` (`propagation.dfy:124`), then `lemma_AllMetasInICacheSmallThanPVCIsMetOnAllServers` (`meta_is_met.dfy:378`).
  - That leads to `lemma_FindTheSourceOfMetaInICache` (:416), then `lemma_FindTheSourceOfAInsertedMeta` (:493), which calls `lemma_MetaInMetas` (:551).
- `lemma_GetMetasOfAllDeps {:axiom}` (`cache.dfy:436-439`) ensures that every
  collected version's clock is at most `vc`, for any valid `vc`. With
  `vc := EmptyVC()` and any valid version with a nonzero clock, it proves
  `false`. `PullDeps3` calls it (`cache.dfy:501`). `PullDeps3` in turn is
  called on the read path (`cache.dfy:612`) and the tail path (`cache.dfy:745`).
- `lemma_AVersionIsPropagatedImpliesAllPreviousVersionsAreMet {:axiom}`
  (`proof/meta_is_met.dfy:593-606`) does not tie `vc` to any propagated
  version. With `vc := vc2`, it asserts that every valid clock of every key is
  met on every server at every step `i > 0`.
- `behaviro_propoties {:axiom}` (`proof/proof.dfy:113-121`) closes the lemma
  cycle and is called at line 70. The `assume`s at lines 71-73 restate it. The
  build verifies `proof.dfy` with `/noCheating:1` (`SConstruct:66, 99, 390`).
  That flag checks those `assume`s as assertions, and the axiom call
  discharges them.

**Clients never migrate.**

- `SendRead` and `SendWrite` choose the key and server with
  `var k :| 0 <= k < MaxKeys as int` and `var server :| 0 <= server < Nodes as int`
  (`cache.dfy:809, 815, 836-837`).
- Each condition mentions no variable, and Dafny's let-such-that is
  deterministic, so each site yields one global value.
- All reads therefore use one (key, server), and all writes one, possibly
  different. No client reads or writes at two servers.

**Other modeling gaps.**

- **The network is not FIFO.** The environment is the standard set of sent
  packets (`Common/Framework/Environment.s.dfy:76-77`), although Fact 2 is
  load-bearing.
- **Integration fabricates versions.** `merged.(vc := deps[k])`
  (`pulldeps.dfy:256`) and `initial.(vc := deps[k])` (line 283) create a
  version with the requested clock whether or not one exists.
- **Server and client counts are fixed** at 3 servers and 5 clients
  (`types.dfy:5-7`). The paper says the proof covers arbitrary numbers
  (p. 3, p. 18).
- **Client-side theorems.** The paper says they were not encoded (§8.4). The
  artifact asserts message-level analogues in the body of
  `lemma_CausalMesh_correctness` (`proof.dfy:97-110`), after the axiom call at
  line 70. Its `ensures` (line 54) exports only `AllServersAreCausalCut`.

### 4. The TLA+ specification (source reading)

`causal-tla/mesh.tla` models the single-round VLDB design: the tail is the
server whose neighbor is the head (line 474). Its invariant `BlacksCoverWhites`
(lines 701-708) folds a merge starting from `white[si][k]` itself. `MetaMerge`
takes a pointwise maximum, so the merged clock always dominates the entry and
the invariant cannot fail. The configuration uses two servers, two clients and
two keys.

### 5. The value tie-break can return a stale value (argued)

§3.2 merges concurrent versions by joining their clocks and keeping "the value
of the larger version by lexicographical ordering". A C-cache entry keeps one
value and one joined clock, so later comparisons use the joined clock, not the
clock of the version whose value is stored. With three servers:

1. x_a = [1,0,0] is written at S0.
2. Client B reads x_a, moves to S2, and writes m′ = [1,0,1].
3. x_b = [0,1,0] is written at S1.
4. S1 merges x_a and x_b: the entry is ([1,1,0], x_a's value).
5. S1 is m′'s tail. [1,1,0] and [1,0,1] are concurrent, and [1,1,0] is
   lexicographically larger, so the entry becomes ([1,1,1], x_a's value).
6. B reads x at S1. The server clock dominates B's local m′, so B receives
   x_a's value, although B wrote m′ after reading x_a.

The clock-level theorems still hold: [1,1,1] dominates m′. The value B
receives is stale, so read-your-writes fails for values. Storing the winning
version's own clock with the entry, and comparing that clock, would avoid this
execution. Neither the trace nor that repair is mechanized. The model's value
rule is looser than §3.2, so it admits this execution too.

### 6. The authors' implementation (source reading)

The server is `ccmesh/ccmesh/src/service.rs`; the Go package
`ccmesh-go/pkg/ccmesh` is the client library. The code was read, not run.

- **Integration matches at or below the dependency clock**
  (`service.rs:225`, `meta.vc <= *vc`), so Finding 2 does not apply.
- **The head does not store its own write in I-cache.** `client_write` sends
  the version to storage and to the successor, and the insert is commented out
  (around lines 457-520).
- **The round-one tail does not store it either.** `server_write` stores only
  when `headid != (id + 1) % T && round == 1` (line 559).
- **Consequence: monotonic reads can fail.** With three servers, a write at S0
  is stored only at S1 before S2 integrates it. A client that reads it at S2
  and then reads at S0 carries it as a dependency. S0 cannot find it and returns
  the initial entry, since keys are pre-populated at clock zero.
- **The write clock ignores deps.** `client_write` increments the server clock
  before parsing deps (lines 448-455), and never merges the deps or `local`
  clocks into it. Fact 3 does not hold.
- **The tail stamps the whole server clock.** The merged entry receives the
  tail's entire server clock (`vc: res_vc`, lines 596-613), not the version's
  own clock.
- **The Go client's `Read` skips the server for its own writes.** It returns
  `Local[k]` without contacting the server or updating `Deps`
  (`client.go:25-27`), unlike Figure 4.

### 7. Clock coverage is not cut membership (argued)

Under Figure 6's tail, a C-cache clock can cover a version whose dependencies
are not visible. With two servers:

1. Client A at S1 writes w (key k2, [0,1]), then u (key k, [0,2], deps
   {k2: [0,1]}).
2. Both writes finish two rounds. Their tail is S0, which integrates and merges
   them. S1, their origin, still holds both in I-cache.
3. Client B at S0 writes v (key k, [1,2], no deps).
4. v's tail is S1. v has no deps to integrate, so S1 merges v and C-cache[k]
   becomes [1,2].

C-cache[k] now covers u, but u's dependency w is not visible at S1, since
C-cache[k2] is still the initial entry. Read as clock dominance, Definition 1
fails at S1. Clients stay safe. A client that reads k at S1 gets [1,2] and
carries it as a dependency. Its next read at S1 integrates that dependency,
which pulls u from I-cache and w with it.

Any invariant or check that treats clock coverage as membership in the cut
therefore needs the pending exclusion used here. This execution is argued, not
mechanized.

## Verification

```bash
VERUS_PATH=/path/to/verus scripts/verify_causalmesh.sh
```

The script verifies the standalone crate `src/protocol/CausalMesh/harness.rs`
with `--no-cheating` and selective trigger reporting. Recorded with Verus
`0.2026.08.02.b677dd5`:

| Run | Result |
|---|---|
| Standalone, `--no-cheating` | 113 verified, 0 errors, 0 automatic-trigger notes |
| Main crate, `src/lib.rs` with every `protocol::CausalMesh` module | 113 verified, 0 errors, 0 automatic-trigger notes |

The crate-level run omits `--no-cheating` because other crate modules use
trusted I/O bodies. The package itself has no `assume`, `admit`,
`external_body` or axiom.

**Non-vacuity:** `theorem_two_round_migrating_reads` constructs a reachable
two-round execution:

1. A write completes both rounds.
2. Its tail merges it; the write stays in the tail's I-cache.
3. A client reads the write at the tail.
4. The client moves and reads it again. The second server integrates it from
   I-cache using the client's deps.

**Mutation controls.** Each mutation was run in a scratch copy, and each broke
the proof. A broken proof is not a demonstrated violation; only M1 has one
(Finding 1).

| Mutation | Failing obligation |
|---|---|
| M1: allow one round | Tail availability (`channels.rs`) |
| M2: VLDB write clock, no merge of deps | New-version facts (`step_write.rs`) |
| M3: exact-match integration | Integration completeness and cut (`integration.rs`) |
| M4: tail merges the version without integrating its deps | Tail step (`step_tail.rs`) |
| M5: reads skip integrating the client's deps | Read step (`step_read.rs`) |
| M8: a client merging concurrent versions may return any value | Read step (`step_read.rs`) |
| M9: a fork event records an empty context | Causal-past invariant (`past.rs`) |
| `assert(false)` in the main theorem, and in the validity lemma | The assertion |

A passing run proves these theorems for the model above. It is not a proof of
the implementations, of the excluded features, or of liveness.
