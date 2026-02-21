// Manual helper code for RSL concrete types generation.
//
// This file is intended to be injected by transpiler generate-types via
// `output.manual_code` in `types_transpile.toml`.
//
// IMPORTANT: Contents here live inside an existing `verus! { ... }` block in
// generated output. Do not add `use` statements or a nested `verus!` block.
//
// Helper functions shared with types_i.rs (COperationNumber helpers, CBalLt/Leq/Eq,
// CRequestBatch helpers, CReplyCache helpers, CVotes helpers, CLearnerTuple,
// CLearnerState helpers) are defined in types_i.rs and bulk re-exported via:
//   pub use crate::implementation::RSL::types_i::*;
// in the re_exports section of types_transpile.toml.
//
// CRslIo is generated via [extra_type_aliases] in types_transpile.toml.

// =============================================================================
// CParameters (manual validity/view + static defaults)
// =============================================================================

impl CParameters{
    pub open spec fn valid(self) -> bool
    {
        &&& self.max_integer_val > self.max_log_length > 0
        &&& self.max_integer_val > self.max_batch_delay
        &&& self.max_integer_val < 0x8000_0000_0000_0000
        &&& self.baseline_view_timeout_period > 0
        &&& self.max_integer_val > self.heartbeat_period > 0
        &&& self.max_batch_size > 0
    }

    pub open spec fn view(self) -> LParameters
    {
        LParameters{
            max_log_length: self.max_log_length as int,
            baseline_view_timeout_period: self.baseline_view_timeout_period as int,
            heartbeat_period: self.heartbeat_period as int,
            max_integer_val: UpperBound::UpperBoundFinite{n: self.max_integer_val as int},
            max_batch_size: self.max_batch_size as int,
            max_batch_delay: self.max_batch_delay as int,
        }
    }
}

impl View for CParameters {
    type V = LParameters;

    open spec fn view(&self) -> LParameters {
        LParameters {
            max_log_length: self.max_log_length as int,
            baseline_view_timeout_period: self.baseline_view_timeout_period as int,
            heartbeat_period: self.heartbeat_period as int,
            max_integer_val: UpperBound::UpperBoundFinite{n: self.max_integer_val as int},
            max_batch_size: self.max_batch_size as int,
            max_batch_delay: self.max_batch_delay as int,
        }
    }
}

// Foundational type blocks (`CConfiguration`, `CConstants`, `CReplicaConstants`)
// have been re-homed to implementation/RSL/{cconfiguration,cconstants}.rs.

// Component block A (`CAcceptor`, `CLearner`, `CElectionState`, `COutstandingOperation`)
// has been re-homed to implementation/RSL/{acceptorimpl,learnerimpl,ElectionImpl}.rs.

// =============================================================================
// Component extension section (part 2 extraction)
// =============================================================================
// Component block B (`CExecutor`, `CIncompleteBatchTimer`, `CProposer`, `CReplica`,
// `CScheduler`, CRslIo abstractify helpers) has been re-homed to
// implementation/RSL/{ExecutorImpl,ProposerImpl,ReplicaImpl}.rs.
