# Infrastructure Type Audit (I2.1)

This document audits all types imported from the manual implementation (`src/implementation/RSL/`) in the generated code, identifying which are pure data types vs. types with marshalling/FFI dependencies.

## Summary

| Category | Count | Types |
|----------|-------|-------|
| Pure Data Types | 12 | CBallot, CRequest, CReply, CVote, CLearnerTuple, COperationNumber, CRequestBatch, CReplyCache, CVotes, CLearnerState, CConstants, CReplicaConstants |
| Message Types (Marshalling) | 3 | CMessage, CPacket, CBroadcast |
| Component Types (State) | 8 | CAcceptor, CProposer, CLearner, CExecutor, CElectionState, CReplica, COutstandingOperation, CIncompleteBatchTimer |
| Configuration Types | 2 | CConfiguration, CParameters |
| App Interface | 2 | CAppMessage, CAppStateInit |
| Utility Types | 2 | OutboundPackets, upper_bound types |

## Detailed Type Analysis

### 1. Pure Data Types (from `types_i.rs`)

These types are pure data structures without marshalling dependencies. They can be generated:

| Type | Definition | Has View | Has Marshalling | Notes |
|------|------------|----------|-----------------|-------|
| `COperationNumber` | `type u64` | N/A | No | Type alias |
| `CBallot` | struct { seqno: u64, proposer_id: u64 } | Yes | No | Pure data |
| `CRequest` | struct { client, seqno, request } | Yes | No | Pure data |
| `CReply` | struct { client, seqno, reply } | Yes | No | Pure data |
| `CRequestBatch` | `type Vec<CRequest>` | N/A | No | Type alias |
| `CReplyCache` | `type HashMap<EndPoint, CReply>` | N/A | No | Type alias |
| `CVote` | struct { max_val_bal, ghost_log_entry, max_val } | Yes | No | Pure data |
| `CVotes` | `type HashMap<COperationNumber, CVote>` | N/A | No | Type alias |
| `CLearnerTuple` | struct with multiple fields | Yes | No | Pure data |
| `CLearnerState` | `type HashMap<...>` | N/A | No | Type alias |

### 2. Message Types (from `cmessage.rs`)

These types have marshalling dependencies in `netrsl_i.rs`:

| Type | Location | Has Marshalling | Notes |
|------|----------|-----------------|-------|
| `CMessage` | cmessage.rs:75 | **Yes** (via `define_enum_and_derive_marshalable!`) | Enum for all RSL message types |
| `CPacket` | cmessage.rs:288 | **Yes** | Contains CMessage + endpoints |

**Marshalling functions in `netrsl_i.rs`:**
- `deserialize_cmessage*` functions
- `rsl_demarshall_data_method`
- Uses `crate::implementation::common::marshalling::*`

### 3. Broadcast Types (from `cbroadcast.rs`)

| Type | Location | Has Marshalling | Notes |
|------|----------|-----------------|-------|
| `CBroadcast` | cbroadcast.rs:21 | No (but references CMessage) | Enum for broadcast kinds |
| `OutboundPackets` | cbroadcast.rs:176 | No | Enum wrapper |

### 4. Configuration Types

| Type | Location | Has Marshalling | Notes |
|------|----------|-----------------|-------|
| `CConstants` | cconstants.rs:21 | No | Static config |
| `CReplicaConstants` | cconstants.rs:68 | No | Static config |
| `CConfiguration` | cconfiguration.rs:17 | No | Endpoint list |
| `CParameters` | cparameters.rs | No | Runtime params |

### 5. Component State Types

These are complex state types with impl blocks containing exec functions:

| Type | Location | Has Marshalling | Notes |
|------|----------|-----------------|-------|
| `CAcceptor` | acceptorimpl.rs | No | Has exec methods |
| `CProposer` | ProposerImpl.rs | No | Has exec methods |
| `CLearner` | learnerimpl.rs | No | Has exec methods |
| `CExecutor` | ExecutorImpl.rs | No | Has exec methods |
| `CElectionState` | ElectionImpl.rs | No | Has exec methods |
| `CReplica` | ReplicaImpl.rs | No | Has exec methods |
| `COutstandingOperation` | ElectionImpl.rs | No | Helper struct |
| `CIncompleteBatchTimer` | ProposerImpl.rs | No | Helper struct |

### 6. App Interface Types (from `appinterface.rs`)

| Type | Location | Has Marshalling | Notes |
|------|----------|-----------------|-------|
| `CAppMessage` | appinterface.rs | **Yes** (via `define_enum_and_derive_marshalable!`) | App-layer message |
| `CAppStateInit` | appinterface.rs | No | Initial state |

### 7. Utility Types (from `common/upper_bound*`)

| Type | Location | Notes |
|------|----------|-------|
| `upper_bound_i::*` | common/ | Upper bound arithmetic |
| `upper_bound::*` | common/ | Upper bound specs |

## Import Dependency Graph

```
Generated Code
├── types_i.rs (Pure Data)
│   ├── CBallot
│   ├── CRequest
│   ├── CReply
│   ├── CVote
│   ├── CLearnerTuple
│   └── type aliases
├── cmessage.rs (Has Marshalling)
│   ├── CMessage ──→ netrsl_i.rs (Marshalling)
│   └── CPacket ──→ netrsl_i.rs (Marshalling)
├── cconstants.rs (Pure)
│   ├── CConstants
│   └── CReplicaConstants
├── cconfiguration.rs (Pure)
│   └── CConfiguration
├── cbroadcast.rs (References CMessage)
│   ├── CBroadcast
│   └── OutboundPackets
├── *Impl.rs files (Exec Functions)
│   ├── CAcceptor
│   ├── CProposer
│   ├── CLearner
│   ├── CExecutor
│   ├── CElectionState
│   └── CReplica
└── appinterface.rs (Has Marshalling)
    ├── CAppMessage
    └── CAppStateInit
```

## Recommendations

### Types to Generate
These pure data types can be auto-generated from specs:
1. `CBallot`, `CRequest`, `CReply`, `CVote`, `CLearnerTuple`
2. Type aliases: `COperationNumber`, `CRequestBatch`, `CReplyCache`, etc.
3. `CConstants`, `CReplicaConstants`, `CConfiguration`

### Types Requiring Manual Implementation
These need to stay in manual implementation due to marshalling/FFI:
1. `CMessage` - Has marshalling via `define_enum_and_derive_marshalable!`
2. `CPacket` - Contains CMessage
3. `CAppMessage` - Has marshalling

### Types Requiring Both
Component types (`CAcceptor`, `CProposer`, etc.) need:
- Generated View impl (maps to spec types)
- Manual exec methods (protocol logic)
- Potentially split into data struct + impl block

## Files to Modify

1. **transpile.toml** - Update `custom_imports` section
2. **src/generated/RSL/*.rs** - Change import paths
3. **src/common/rsl_types/** - New shared types module (optional)

## Current Generated Code Imports

All generated files in `src/generated/RSL/` have identical imports:
```rust
use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::cmessage::*;
use crate::implementation::RSL::cbroadcast::*;
use crate::implementation::RSL::cconfiguration::*;
use crate::implementation::RSL::acceptorimpl::{CAcceptor, CIsLogTruncationPointValid};
use crate::implementation::RSL::ProposerImpl::{CProposer, CIncompleteBatchTimer};
use crate::implementation::RSL::learnerimpl::CLearner;
use crate::implementation::RSL::ExecutorImpl::CExecutor;
use crate::implementation::RSL::ReplicaImpl::CReplica;
use crate::implementation::RSL::ElectionImpl::{CElectionState, COutstandingOperation};
use crate::implementation::RSL::CStateMachine::CHandleRequestBatch;
use crate::implementation::RSL::appinterface::CAppStateInit;
use crate::implementation::common::upper_bound_i::*;
use crate::implementation::common::upper_bound::*;
```
