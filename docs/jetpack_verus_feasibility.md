# Jetpack 演绎验证(tla-rs)可行性评估 & Gap 报告

- **范围**:评估能否用 tla-rs 的 `tla+2tlars` 前端,把 `jetpack.tla` 直接转成可演绎验证(Verus)的实现。
- **方法**:并行深读两边,逐条对照 —— (a) Jetpack 的 TLA+ 用了哪些构造;(b) tla-rs 的 TLA+→Verus 前端(`transpiler/src/tla/{tokenizer,parser,translator}.rs`)实际支持哪些。
- **输入来源**:`stonysystems/jetpack` 仓库 `tla/` 目录:`jetpack.tla`(808 行)、`base_raft.tla`(652)、`jetpack_raft_composition.tla`(437)。**注意:这些文件不在 tla-rs 仓库内。**

---

## TL;DR(结论先行)

**直接 `jetpack.tla → jetpack.rs` 不可行。** 根本原因是**建模范式正交**,叠加十余项前端 gap(部分直接解析报错,部分**静默产出语义错误的 Verus**)。

要让 Jetpack 走 tla-rs 演绎验证,**必须先把三个模块压平、并整体重写成 per-replica 单进程规范**——这是**重写协议模型**,不是转译能自动完成的。

唯一的好消息:Jetpack 是**纯 safety、action-level**(只有 `[]` 不变式,无 `WF_`/`SF_`/`<>` 活性),这一面对 transpiler 友好。

---

## 1. 最根本的 gap:建模范式正交

| | **Jetpack TLA+** | **tla-rs 前端期待的输入** |
|---|---|---|
| 状态 | 全局多-server 数组:`currentTerm[i]`、`log[i][j][k]`、`msgs` 是全网消息袋 | 单进程单状态记录 `s`,每个变量是本 replica 的一个字段 |
| 动作 | 显式带 server 下标:`HandlePreacceptRequest(i, m)`、更新 `arr[i]` | `Next(s, s_, c)`,无 server 下标,本地 `s→s_` 转移 |
| 组合 | 靠 `INSTANCE base + wrapper` 拼装,单文件不可验证 | 单模块自洽 |
| 变量数 | composition 共 **32 个变量**(多为 Map-of-Map / bag) | fixture 通常 4~10 个标量字段 |

**证据**:`jetpack.tla:139-171` 变量经 `[i \in Server \|-> ...]` 初始化;动作 `SendBeginRecovery(i)`(:452)写 `arr[i]`。对照 tla-rs 自带 fixture `transpiler/tests/tla_examples/Raft.tla:12` —— `currentTerm/state` 是**标量**,动作**不带下标**。前端 `translator.rs:4977-4986` 把每个 `VARIABLE` 映射成 `LState` 的一个字段,没有 `[Server -> T]` 每-server 数组的概念。

> 这不是"语法差一点",而是两种不同的协议建模哲学。前端能把 `currentTerm[i]` 塞进去(当成一个 Map 字段),但**语义是"单个全局状态记录里放了一堆 Map",与真实分布式语义不对齐**。

---

## 2. Blocker 清单(直接报错 / 静默错译)

| # | Gap | Jetpack 证据 | transpiler 证据 | 后果 |
|---|---|---|---|---|
| B1 | **全局多-server 数组 vs 单进程** | `jetpack.tla:139-171`, `base_raft.tla:97-109` | `translator.rs:4959-4986` 无 per-server 概念 | 范式不匹配,需整体重写 |
| B2 | **`@`(EXCEPT 旧值引用)解析直接报错** | `[currentTerm EXCEPT ![i] = @ + 1]` 遍布 base_raft | `parser.rs` `parse_primary_expr(659-762)` 对 `At` 无分支 → `Err("Unexpected token: At")` | **整份文件解析失败** |
| B3 | **嵌套 `EXCEPT ![i][j]` 静默错译** | `jetpack.tla:386-388` `[log EXCEPT ![i][j]=..]` | `translator.rs:2078-2119` 生成并列 `f.insert(i,v).insert(j,v)`,而非 `f.insert(i, f[i].insert(j,v))` | **不报错,产出语义错误的 spec** |
| B4 | **`INSTANCE ... WITH` 多模块组合被丢弃** | `composition:86-91` `INSTANCE base_raft` / `INSTANCE jetpack WITH ...` | `parser.rs:277-307` 解析进 `module.instances`,但 `translator.rs:3162-3186` **从不读取它** | 静默丢掉被实例化模块的全部定义 |
| B5 | **消息袋 `@@` / `:>` 无 token** | `msgs @@ (m :> 1)`(`jetpack.tla:201-217`) | `tokenizer.rs` 无 `@@`/`:>` 的 `TokenKind` | 词法层就挂 |
| B6 | **异构 record 合并成单 struct、字段默认 `int`** | 9 种消息 + `View`/`JPool`(含 `SUBSET`/函数值字段) | `generate_record_structs(translator.rs:4913-4946)`,字段类型 `.unwrap_or("int")(:4941)` | 集合/序列/嵌套字段全部错型 |
| B7 | **无任何真实多-server 规约端到端跑通的证据** | — | fixture 全标注 "simplified/for testing";`tla_examples_test.rs:441-660` 只 `assert contains("pub struct LState")` 之类子串,**不验证可编译/可验证** | 绿色测试**不能**作为可行性背书 |

---

## 3. Hard 清单(需逐个补实现)

| # | Gap | 证据 | 说明 |
|---|---|---|---|
| H1 | 数组更新一律 `Map.insert`,丢 `Seq` 类型 | `translator.rs:2083` | `log`(Seq)/`votes`(Set)被当 Map,`.len/.insert` 类型不匹配 |
| H2 | `RECURSIVE` 被静默跳过、无 `decreases` | `parser.rs:161-174` | `AddMessages`/`RemoveCmd`/`Dedup` 等递归 helper 过不了终止性检查 |
| H3 | 集合推导只支持单变量 | `parser.rs:770-828` | `{[a,b] : a \in Q, b \in R}`(`Resubmit`:687)直接解析报错 |
| H4 | `CHOOSE` 在 exec 路径不可执行 | `jetpack.tla:195-196, 597`;`translator.rs:2421` → ghost `choose` | 需替换成确定性可执行搜索(求最值 / tie-break) |
| H5 | `Quorum = SUBSET + Cardinality` | `jetpack.tla:184-193` → `.powerset()` | 幂集不可枚举;需重写成"ack 计数 * 2 > N"判据 |
| H6 | `\o` 序列拼接被当八进制转义 | `tokenizer.rs:741` 报 "Expected octal digits after \\o" | `RemoveCmd`/`Dedup` 依赖它 |
| H7 | `LAMBDA` / `SelectSeq` 无支持 | `FilterNoOps==SelectSeq(seq, LAMBDA ...)`(:243) | 需补 token + 翻译到 `iter().filter()` |
| H8 | 32 变量巨型状态 + 跨模块 `UNCHANGED` | `composition:35-80` | 类型推断/EXCEPT 错误风险随嵌套度放大 |

---

## 4. 对 transpiler 友好的点(可复用)

- **纯读路径可解析**:`f[i][j]` 多维读、`Cardinality`、`SUBSET`/`UNION`/`DOMAIN`、`CHOOSE` 选主、嵌套 record —— 解析层都可用(`parser.rs:1106/1999/588-597`、`translator.rs:2610`)。**前端是"能读不能可靠写"**。
- **纯 safety、无活性**:Jetpack 只有 `[]` 不变式,没有 `WF_`/`SF_`/`<>`。省掉了时序/公平性这一大块。

---

## 5. 结论与路线建议

**核心结论**:两侧独立分析一致 —— **不能拿真实 `jetpack.tla` 直接走这条链**。瓶颈不在"缺几个算符",而在"范式正交 + 写入路径(`@`/嵌套 `EXCEPT`/类型)/多模块 组合 全都不可靠"。

三条可选路线:

| 路线 | 做什么 | 工作量 | 评价 |
|---|---|---|---|
| **R1. 重写 spec 为单进程** | 把 Jetpack 手工降维成 per-replica `s/s_` 规范(去 `[i]` 维、去 `messages` bag、quorum 改计数、CHOOSE 改确定性),再走 tla-rs pipeline | 大 | **推荐的长期路线**,但先做最小切片验证 |
| **R2. 扩展 transpiler 前端** | 给前端补 `@`/嵌套 `EXCEPT`/`INSTANCE` 内联/per-server 数组/类型推断 | 更大(改工具本身) | 通用但回报周期长,可作为副产物 |
| **R3. 绕过 TLA+ 前端,直接手写 Verus spec** | 参照 `src/protocol/Paxos/paxos.rs`,手写 Jetpack 恢复层的最小 Verus spec | 中 | **对"恢复层单值 agreement"最小切片最快** |

**推荐的第一步**:走 **R3 的一个最小切片** —— 手写"恢复层 3-phase 单值 agreement + assumed base 契约"的 Verus spec(单进程 `s/s_` 风格),复用 repo 里已闭合的 Paxos 证明模式。它绕开了本报告列出的**所有 blocker**(不碰 TLA+ 前端、不碰多-server 数组、不碰 INSTANCE),是把"Jetpack-in-Verus"这条路走通的最小可行单元。R1/R2 作为后续放大。

---

## 附:证据来源

- Jetpack TLA+:`stonysystems/jetpack@jetpack` 分支 `tla/{jetpack,base_raft,jetpack_raft_composition}.tla`
- tla-rs 前端:`transpiler/src/tla/{tokenizer,parser,translator}.rs`、`transpiler/src/main.rs`(pipeline 子命令)、`transpiler/tests/tla_examples/*.tla`、`transpiler/tests/.../tla_examples_test.rs`
- tla-rs 输入范式参照:`src/tla+/TwoPhase/Twophase.tla`(verus2tla 反向生成的单进程范式)
