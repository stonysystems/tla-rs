# tla-rs: TLA-Style Specifications for Verified Rust

**Stop looking for bugs. Start proving your code.**

`tla-rs` lets you write **TLA-style specifications in Rust with
[Verus](https://github.com/verus-lang/verus)** and prove that your Rust code implements
the behavior you specified.
Describe your system's state, initial conditions, and allowed transitions as logical
relations—not just a collection of test cases.

## Specify and prove

1. **Specify the behavior.** Write TLA-style state machines and invariants directly in
   Verus's Rust syntax. You do not need to start with a separate TLA+ file.
2. **Prove your code.** State the contracts your Rust implementation must satisfy
   and use Verus to check them. Supply invariants and lemmas to establish
   system-level safety and refinement properties.

Verification covers the stated properties under explicit preconditions and trusted
boundaries. Testing and model checking still help find specification mistakes and
exercise runtime code outside those boundaries.

For specification and proof techniques, see Chapters 4 and 20 of
[*The tla-rs Book*](docs/tla-rs-book.md).

## Feeling lucky with your agents?

Try this prompt with your coding agent:

- "Verify my code with the approach in tla-rs: <https://github.com/stonysystems/tla-rs>"

## A small example: ping-pong

Two players take turns: Ping starts, then each step passes the turn to the other player.
First, write the specification: `LInit` describes the initial state, and `LNext`
describes the allowed transitions.

```rust
use vstd::prelude::*;

verus! {
    pub enum Turn { Ping, Pong }

    pub open spec fn LInit(turn: Turn) -> bool {
        turn == Turn::Ping
    }

    pub open spec fn LNext(turn: Turn, turn_: Turn) -> bool {
        (turn == Turn::Ping && turn_ == Turn::Pong)
        || (turn == Turn::Pong && turn_ == Turn::Ping)
    }
}
```

Now we can write properties of the model and prove them: every valid step changes
the turn, and any two valid steps return to the starting turn.

```rust
verus! {
    pub proof fn lemma_alternates(turn: Turn, turn_: Turn)
        requires LNext(turn, turn_),
        ensures turn_ != turn,
    {}

    pub proof fn lemma_round_trip(a: Turn, b: Turn, c: Turn)
        requires LNext(a, b), LNext(b, c),
        ensures c == a,
    {}
}
```

The proof bodies are empty because Verus can discharge these small logical
obligations automatically.

Finally, write the implementation and prove that it refines the specification.
The `ensures` contracts establish that `init` satisfies `LInit` and `step` satisfies
`LNext`. For this deterministic model, the implementation's turn transitions
exactly match the specification.

```rust
verus! {
    pub fn init() -> (turn: Turn)
        ensures LInit(turn),
    {
        Turn::Ping
    }

    pub fn step(turn: Turn) -> (turn_: Turn)
        ensures LNext(turn, turn_),
    {
        match turn {
            Turn::Ping => Turn::Pong,
            Turn::Pong => Turn::Ping,
        }
    }
}

// A finite demo driver; printing is outside the verified model.
fn main() {
    let mut turn = init();
    for _ in 0..6 {
        match turn {
            Turn::Ping => println!("Ping"),
            Turn::Pong => println!("Pong"),
        }
        turn = step(turn);
    }
}
```

The driver prints alternating `Ping` and `Pong` lines, three times each.
This example proves turn-taking properties, not network delivery or eventual
progress; the printing driver is not verified.

Copy the three snippets, in order, into `ping_pong.rs`. Install Verus using
Chapter 2 of [*The tla-rs Book*](docs/tla-rs-book.md), then verify and compile with
`"$VERUS_PATH" --compile ping_pong.rs -o ping_pong` and run `./ping_pong`.

## More Examples

| Example folder | Proof coverage |
|---|---|
| [RSL / Multi-Paxos](src/protocol/RSL/) | Protocol-behavior refinement to an abstract replicated state machine. |
| [Raft](src/protocol/Raft/) | Committed-log refinement, agreement, and leader uniqueness, including reboots and joint consensus. |
| [EPaxos*](src/protocol/EPaxos/star/) | Model safety, recovery, and abstract-history refinement; executable refinement remains open. |
| [CausalMesh](src/protocol/CausalMesh/) | Two-round model: causal and session guarantees over arbitrary finite executions. |
| [Mako-v1](src/protocol/Mako/) | Watermark safety and OCC serializability; composition is conditional and C++ refinement remains open. |
| [Consensus studies](docs/non-bft-consensus/) | Chain Replication, Mencius, Jetpack, Om, Gaios, CORFU, Replicated Commit, and SpecPaxos: scoped safety/refinement proofs, with remaining obligations documented. |
| [Other protocols](src/protocol/) | Paxos, PBFT, Primary-Backup, Vertical Paxos, Two-Phase Commit, and Bully election: action-level implementation contracts; proof depth varies. |
| [TLAPS-Bench](src/protocol/TLAPSBench/) | Nine models: 38/47 invariants and 9/9 liveness goals proved; 6 goals refuted and 3 unresolved. |

Coverage is relative to each model's assumptions, not an end-to-end service guarantee.

## More tools

- [**Code generation**](transpiler/) — generate executable Rust and refinement
  contracts from supported, annotated Verus specifications; the output still needs
  verification.
- [**Lion runtime**](runtime/) — native Rust networking and protocol-server
  integration.
- [**TLA+ → tla-rs translator**](transpiler/src/tla/) — import supported TLA+
  specifications as Verus models; translation alone is not a proof.

## Documentation

[*The tla-rs Book*](docs/tla-rs-book.md) is the primary documentation:

- Part I is the user guide: specifications, generation, verification, model checking,
  TLA+ interchange, and running services.
- Part II is the developer guide: architecture, trust boundaries, transpiler internals,
  generated-code maintenance, testing, and releases.
- The appendices contain the CLI, annotation, configuration, support, evidence, and
  proof-pattern references.

Capability claims tied directly to tests remain in
[`docs/model_checker_status.md`](docs/model_checker_status.md), while
[`docs/clean_tla_subset.md`](docs/clean_tla_subset.md) defines the normative clean-TLA
projection contract. RSL's trusted, proved hand-written, and unsupported generated paths
are classified in [`docs/rsl-skip-functions.md`](docs/rsl-skip-functions.md).

## Contributing

Do not hand-edit transpiler-emitted code: change the protocol source, its
`// @automan` annotations, the configuration, or the transpiler, and
regenerate. Files under `src/generated/` can also carry hand-written bodies
that regeneration deliberately preserves (RSL's `skip_functions`, classified
in [`docs/rsl-skip-functions.md`](docs/rsl-skip-functions.md)) — those are
edited in place. When unsure which kind a function is, diff against fresh
transpiler output rather than guessing. See
[`AGENTS.md`](AGENTS.md) for project rules, the book's developer guide for the normal
workflow, and [`TODO.md`](TODO.md) for current work and known gaps.

## Foundations

`tla-rs` brings the methodology of two verified-systems projects to Rust and Verus:

- [**IronFleet: Proving Practical Distributed Systems Correct**](https://doi.org/10.1145/2815400.2815428)
  ([code](https://github.com/microsoft/Ironclad/tree/main/ironfleet)) — the verified
  distributed-systems framework, refinement methodology, and Multi-Paxos replicated state
  machine on which this project is based.
- [**AutoMan: Facilitating Verified Distributed Systems Development Through Automatic Code
  Generation and Manual Optimizations**](https://doi.org/10.1145/3731569.3764822)
  ([code](https://github.com/stonysystems/automan)) — the workflow for generating executable
  implementations and their verification obligations from protocol specifications.

Both original systems use Dafny. This project re-expresses their core ideas in verified Rust:
IronFleet's specifications, proofs, and runtime structure are ported to Verus, while AutoMan's
specification-to-implementation workflow is reimplemented as a Rust/Verus transpiler.

## Attribution and license

Parts of the native I/O, Verus utilities, marshalling, FFI, and C# runtime were adapted
from [IronKV](https://github.com/verus-lang/verified-ironkv). The transpiler reimplements
the [AutoMan](https://github.com/stonysystems/automan) workflow for Rust and Verus.

Licensed under the [MIT License](LICENSE).
