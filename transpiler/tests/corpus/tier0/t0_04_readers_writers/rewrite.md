# t0_04_readers_writers — rewrite notes

**Source**: `tlaplus/Examples` `specifications/ReadersWriters/ReadersWriters.tla`
**Pinned commit**: `ee05f259276db2b878a55a442ea6daa8429db7e9`
**Clean-distance at intake**: unmeasured

> Fill this in while writing `clean.tla`. It is the record of what a human decided,
> and it is what makes the rewrite reviewable. Do not leave TODOs in a case that is
> marked `clean` in the manifest.

## Which variable is the network (C4)

TODO — name the message variable, and the operators used to send/receive it.

## History variables removed (C3)

TODO — list each removed ghost/history variable and why it was safe to drop.

## Instantaneous cross-node reads message-ified (C2)

TODO — for each `x[other]` read: what message now carries that value, who sends it,
and what the receiving action does with it.

## Out-of-subset constructs stripped

TODO — reconfiguration (view/epoch) per Q2, and anything else dropped.

## Semantic-fidelity claim (V2)

TODO — how `clean.tla` was checked against `original.tla` with TLC: config, bounds,
observables compared, result.

## Golden review (before freezing golden.rs)

TODO — what was diffed against `reference.rs` (if any) and what differences were
accepted, with reasons.
