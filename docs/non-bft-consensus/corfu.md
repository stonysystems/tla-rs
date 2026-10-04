# CORFU per-position safety

Verus proves agreement and single-assignment refinement for one logical log
position across writes, reads, crashes, sealing and chain migration. A separate
composition theorem proves agreement on the replacement layout. The source is
[CORFU: A Shared Log Design for Flash Clusters, NSDI 2012](https://www.usenix.org/system/files/conference/nsdi12/nsdi12-final30.pdf),
Sections 3.2 through 3.4.

[chain.rs](../../src/protocol/Corfu/chain.rs) models individual write-once
replica cells. A client issues a payload or the hole-fill value. The head
accepts an issued value; every later write copies its predecessor's value.
A successful read observes the live tail. Sealing disables old-epoch access.
Crashes preserve storage and leave a survivor. Migration copies a surviving
value, or remains empty if all survivors are empty, then advances the epoch
and publishes a new chain.

| Theorem | Property |
|---|---|
| `agreement_and_validity` | Successful observations anywhere in a finite execution agree and return an issued value. |
| `old_epoch_is_fenced` | Old-epoch writes and observations cannot execute after migration. |
| `single_assignment_refinement` | The tail's abstract cell can publish an issued value but cannot change an existing value, including during migration. |
| `successful_read_refines_atomic_cell` | A successful read returns the abstract cell value. |
| `layout::agreed_projection_migration` | Competing Paxos ballots choose the same layout ID; installing it preserves published data. |

The inductive invariant establishes a filled prefix containing one value.
Once the tail is filled, every old-chain cell contains that value, so a
surviving copy preserves it. The refinement gives a linearization point for
single-position publication at the tail write or migration that first fills
the tail. Reads observe that atomic cell. There is no whole-log append-history
linearizability theorem in this package.

Migration seals every live old-chain member and atomically copies the payload
to the entire new chain. This is stronger than the paper's minimal prefix-copy
procedure. The proof does not cover its distributed copy/publication handshake
or every partially copied layout schedule. The layout service uses the shared
Paxos kernel with atomic Phase 1; data-plane migrations are serialized at this
abstraction boundary.

Sequencer allocation, multiple positions, retry/error API histories, trimming,
physical flash behavior and liveness remain open.
`corfu_read_survives_migration` in
[the execution witnesses](../../src/protocol/next_five_witnesses.rs) constructs
a two-node write and read, crashes one node, seals the survivor, migrates to a
new node and reads the same value again. See
[verification metadata](next-five-verification.json) for digests and commands.
