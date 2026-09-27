# Jetpack 原始 TLA+ 规范(参考,勿当输入)

2026-09-26 provenance check: all three files match upstream commit
`c03e318ec355b11edd42aac56c68d0765f88d1d2` byte for byte. The new global
recovery, agreement, execution-consistency and conditional linearizability proofs are documented in
[Jetpack proof report](../non-bft-consensus/jetpack.md). They are separate from
the historical R1 slice described below and do not establish a refinement of
these reference files.

这三个文件从 `stonysystems/jetpack@jetpack:tla/` 拷来,是原始的 **TLC model-checking** 规范:
- `jetpack.tla` — 恢复层本体(808 行)
- `base_raft.tla` — base 协议接口(652 行)
- `jetpack_raft_composition.tla` — 组合模块(437 行)

**用途仅为 R1 单进程重写的参考。** 它们是"全局多-server 数组 + `INSTANCE` 组合"风格,**不能**直接喂给 tla-rs 的 `tla+2tlars` 前端(原因见 `docs/jetpack_verus_feasibility.md`)。

R1 的**产物**是手写的**单进程 Verus spec**,将放在 `src/protocol/Jetpack/`(对标 `src/protocol/Paxos/`),**不在本目录**。这些 `.tla` 文件只是参考,不参与编译、不是 transpiler 输入。
