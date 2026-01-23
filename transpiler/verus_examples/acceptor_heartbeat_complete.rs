// Complete RSL AcceptorProcessHeartbeat example with both spec and exec
// Tests: Sequence update pattern, nested conditionals, index computation
// Based on RSL acceptor.rs LAcceptorProcessHeartbeat predicate

use vstd::prelude::*;
use vstd::seq::*;

verus! {
    // === SPEC TYPES ===

    #[derive(PartialEq, Eq, Structural)]
    pub struct AbstractEndPoint {
        pub id: int,
    }

    #[derive(PartialEq, Eq, Structural)]
    pub struct Ballot {
        pub seqno: int,
        pub proposer_id: int,
    }

    pub type OperationNumber = int;
    pub type ReplicaIds = Seq<AbstractEndPoint>;

    pub struct LConfiguration {
        pub replica_ids: ReplicaIds,
    }

    pub struct LConstants {
        pub config: LConfiguration,
        pub my_index: int,
    }

    pub struct LAcceptor {
        pub constants: LConstants,
        pub max_bal: Ballot,
        pub last_checkpointed_operation: Seq<OperationNumber>,
    }

    #[derive(PartialEq, Eq, Structural)]
    pub enum RslMessage {
        RslMessageHeartbeat {
            opn_ckpt: OperationNumber,
        },
        Other,
    }

    pub struct RslPacket {
        pub src: AbstractEndPoint,
        pub dst: AbstractEndPoint,
        pub msg: RslMessage,
    }

    // Helper: Find index of endpoint in sequence
    pub open spec fn FindIndexInSeq(seq: ReplicaIds, ep: AbstractEndPoint) -> int
    {
        choose |i: int| 0 <= i < seq.len() && seq[i] == ep
    }

    pub open spec fn GetReplicaIndex(ep: AbstractEndPoint, config: LConfiguration) -> int
        recommends config.replica_ids.contains(ep)
    {
        FindIndexInSeq(config.replica_ids, ep)
    }

    // === SPEC PREDICATE (from RSL acceptor.rs) ===

    pub open spec fn LAcceptorProcessHeartbeat(
        s: LAcceptor,
        s_: LAcceptor,
        inp: RslPacket
    ) -> bool
        recommends inp.msg is RslMessageHeartbeat
    {
        if s.constants.config.replica_ids.contains(inp.src) {
            let sender_index = GetReplicaIndex(inp.src, s.constants.config);
            if 0 <= sender_index < s.last_checkpointed_operation.len()
                && inp.msg->opn_ckpt > s.last_checkpointed_operation[sender_index]
            {
                &&& s_.last_checkpointed_operation == s.last_checkpointed_operation.update(sender_index, inp.msg->opn_ckpt)
                &&& s_.constants == s.constants
                &&& s_.max_bal == s.max_bal
            } else {
                s_ == s
            }
        } else {
            s_ == s
        }
    }

    // === EXEC TYPES ===

    pub struct CEndPoint {
        pub id: i64,
    }

    impl CEndPoint {
        pub open spec fn well_formed(&self) -> bool {
            self.id >= 0
        }

        pub fn clone_for_view(&self) -> (result: CEndPoint)
            ensures result@ == self@
        {
            CEndPoint { id: self.id }
        }

        pub fn eq(&self, other: &CEndPoint) -> (result: bool)
            ensures result == (self@ == other@)
        {
            self.id == other.id
        }
    }

    impl View for CEndPoint {
        type V = AbstractEndPoint;
        open spec fn view(&self) -> AbstractEndPoint {
            AbstractEndPoint { id: self.id as int }
        }
    }

    pub struct CBallot {
        pub seqno: i64,
        pub proposer_id: i64,
    }

    impl CBallot {
        pub open spec fn well_formed(&self) -> bool {
            self.seqno >= 0 && self.proposer_id >= 0
        }

        pub fn clone_for_view(&self) -> (result: CBallot)
            ensures result@ == self@
        {
            CBallot { seqno: self.seqno, proposer_id: self.proposer_id }
        }
    }

    impl View for CBallot {
        type V = Ballot;
        open spec fn view(&self) -> Ballot {
            Ballot { seqno: self.seqno as int, proposer_id: self.proposer_id as int }
        }
    }

    pub struct CConfiguration {
        pub replica_ids: Vec<CEndPoint>,
    }

    impl CConfiguration {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.replica_ids@.len() > 0
            &&& forall |i: int| #![auto] 0 <= i < self.replica_ids@.len() ==> self.replica_ids@[i].well_formed()
        }

        pub fn len(&self) -> (result: usize)
            ensures result == self@.replica_ids.len()
        {
            self.replica_ids.len()
        }

        pub fn contains(&self, ep: &CEndPoint) -> (result: bool)
            requires self.well_formed()
            ensures result == self@.replica_ids.contains(ep@)
        {
            let mut i: usize = 0;
            while i < self.replica_ids.len()
                invariant
                    i <= self.replica_ids@.len(),
                    forall |j: int| #![auto] 0 <= j < i ==> self.replica_ids@[j]@ != ep@,
                decreases self.replica_ids@.len() - i
            {
                if self.replica_ids[i].eq(ep) {
                    proof {
                        assert(self.replica_ids@[i as int]@ == ep@);
                        assert(self@.replica_ids[i as int] == ep@);
                    }
                    return true;
                }
                i = i + 1;
            }
            proof {
                assert(forall |j: int| #![auto] 0 <= j < self.replica_ids@.len() ==> self.replica_ids@[j]@ != ep@);
                assert(forall |k: int| #![auto] 0 <= k < self@.replica_ids.len() ==> self@.replica_ids[k] == self.replica_ids@[k]@);
            }
            false
        }

        pub fn find_index(&self, ep: &CEndPoint) -> (result: i64)
            requires
                self.well_formed(),
                self@.replica_ids.contains(ep@),
                self.replica_ids@.len() < i64::MAX as int,
            ensures
                0 <= result,
                result < self@.replica_ids.len(),
                self@.replica_ids[result as int] == ep@,
        {
            let mut i: usize = 0;
            while i < self.replica_ids.len()
                invariant
                    i <= self.replica_ids@.len(),
                    forall |j: int| #![auto] 0 <= j < i ==> self.replica_ids@[j]@ != ep@,
                    self@.replica_ids.contains(ep@),
                    self.replica_ids@.len() < i64::MAX as int,
                decreases self.replica_ids@.len() - i
            {
                if self.replica_ids[i].eq(ep) {
                    proof {
                        // This is the first index where we found ep
                        assert(self.replica_ids@[i as int]@ == ep@);
                        assert(self@.replica_ids[i as int] == ep@);
                    }
                    return i as i64;
                }
                i = i + 1;
            }
            // We know ep is in replica_ids, so this is unreachable
            proof { assert(false); }
            0 // unreachable
        }

        pub fn clone_for_view(&self) -> (result: CConfiguration)
            requires self.well_formed()
            ensures result@ == self@, result.well_formed()
        {
            let mut new_ids: Vec<CEndPoint> = Vec::new();
            let mut i: usize = 0;
            while i < self.replica_ids.len()
                invariant
                    i <= self.replica_ids@.len(),
                    new_ids@.len() == i,
                    forall |j: int| #![auto] 0 <= j < i ==> new_ids@[j]@ == self.replica_ids@[j]@,
                    forall |j: int| #![auto] 0 <= j < i ==> new_ids@[j].well_formed(),
                    self.well_formed(),
                decreases self.replica_ids@.len() - i
            {
                new_ids.push(self.replica_ids[i].clone_for_view());
                i = i + 1;
            }
            let result = CConfiguration { replica_ids: new_ids };
            proof {
                // Show the view of result equals self@
                // result@.replica_ids = Seq::new(result.replica_ids@.len(), |i| result.replica_ids@[i]@)
                // self@.replica_ids = Seq::new(self.replica_ids@.len(), |i| self.replica_ids@[i]@)
                assert(result.replica_ids@.len() == self.replica_ids@.len());
                assert(forall |j: int| #![auto] 0 <= j < result.replica_ids@.len() ==> result.replica_ids@[j]@ == self.replica_ids@[j]@);
                // Use extensional equality
                assert(result@.replica_ids =~= self@.replica_ids);
            }
            result
        }
    }

    impl View for CConfiguration {
        type V = LConfiguration;
        open spec fn view(&self) -> LConfiguration {
            LConfiguration {
                replica_ids: Seq::new(self.replica_ids@.len(), |i: int| self.replica_ids@[i]@),
            }
        }
    }

    pub struct CConstants {
        pub config: CConfiguration,
        pub my_index: i64,
    }

    impl CConstants {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.config.well_formed()
            &&& 0 <= self.my_index < self.config@.replica_ids.len()
        }

        pub fn clone_for_view(&self) -> (result: CConstants)
            requires self.well_formed()
            ensures result@ == self@, result.well_formed()
        {
            CConstants {
                config: self.config.clone_for_view(),
                my_index: self.my_index,
            }
        }
    }

    impl View for CConstants {
        type V = LConstants;
        open spec fn view(&self) -> LConstants {
            LConstants {
                config: self.config@,
                my_index: self.my_index as int,
            }
        }
    }

    // Operation numbers as sequence
    pub struct COpnSeq {
        pub data: Vec<i64>,
    }

    impl COpnSeq {
        pub open spec fn well_formed(&self) -> bool {
            forall |i: int| #![auto] 0 <= i < self.data@.len() ==> self.data@[i] >= 0
        }

        pub fn len(&self) -> (result: usize)
            ensures result == self@.len()
        {
            self.data.len()
        }

        pub fn get(&self, idx: usize) -> (result: i64)
            requires idx < self@.len()
            ensures result as int == self@[idx as int]
        {
            self.data[idx]
        }

        pub fn update(&self, idx: i64, val: i64) -> (result: COpnSeq)
            requires
                self.well_formed(),
                0 <= idx,
                idx < self@.len(),
                val >= 0,
                self.data@.len() < usize::MAX as int,
            ensures
                result@ == self@.update(idx as int, val as int),
                result.well_formed(),
        {
            let mut new_data: Vec<i64> = Vec::new();
            let mut i: usize = 0;
            let idx_usize = idx as usize;
            while i < self.data.len()
                invariant
                    i <= self.data@.len(),
                    new_data@.len() == i,
                    idx_usize == idx as usize,
                    forall |j: int| #![auto] 0 <= j < i && j != idx as int ==> new_data@[j] == self.data@[j],
                    (idx as int) < (i as int) ==> new_data@[idx as int] == val,
                    self.well_formed(),
                    0 <= idx,
                    idx < self@.len(),
                    val >= 0,
                decreases self.data@.len() - i
            {
                if i == idx_usize {
                    new_data.push(val);
                } else {
                    new_data.push(self.data[i]);
                }
                i = i + 1;
            }
            proof {
                // Show the result matches update semantics
                assert(new_data@.len() == self.data@.len());
                assert(new_data@[idx as int] == val);
                assert(forall |j: int| #![auto] 0 <= j < new_data@.len() && j != idx as int ==> new_data@[j] == self.data@[j]);
            }
            COpnSeq { data: new_data }
        }

        pub fn clone_for_view(&self) -> (result: COpnSeq)
            requires self.well_formed()
            ensures result@ == self@, result.well_formed()
        {
            let mut new_data: Vec<i64> = Vec::new();
            let mut i: usize = 0;
            while i < self.data.len()
                invariant
                    i <= self.data@.len(),
                    new_data@.len() == i,
                    forall |j: int| #![auto] 0 <= j < i ==> new_data@[j] == self.data@[j],
                    self.well_formed(),
                decreases self.data@.len() - i
            {
                new_data.push(self.data[i]);
                i = i + 1;
            }
            COpnSeq { data: new_data }
        }
    }

    impl View for COpnSeq {
        type V = Seq<OperationNumber>;
        open spec fn view(&self) -> Seq<OperationNumber> {
            Seq::new(self.data@.len(), |i: int| self.data@[i] as int)
        }
    }

    pub struct CAcceptor {
        pub constants: CConstants,
        pub max_bal: CBallot,
        pub last_checkpointed_operation: COpnSeq,
    }

    impl CAcceptor {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.constants.well_formed()
            &&& self.max_bal.well_formed()
            &&& self.last_checkpointed_operation.well_formed()
            &&& self.last_checkpointed_operation@.len() == self.constants.config@.replica_ids.len()
        }
    }

    impl View for CAcceptor {
        type V = LAcceptor;
        open spec fn view(&self) -> LAcceptor {
            LAcceptor {
                constants: self.constants@,
                max_bal: self.max_bal@,
                last_checkpointed_operation: self.last_checkpointed_operation@,
            }
        }
    }

    // Message types
    pub enum CRslMessage {
        CRslMessageHeartbeat { opn_ckpt: i64 },
        COther,
    }

    impl CRslMessage {
        pub open spec fn well_formed(&self) -> bool {
            match self {
                CRslMessage::CRslMessageHeartbeat { opn_ckpt } => *opn_ckpt >= 0,
                CRslMessage::COther => true,
            }
        }

        pub fn is_heartbeat(&self) -> (result: bool)
            ensures result == (self@ is RslMessageHeartbeat)
        {
            matches!(self, CRslMessage::CRslMessageHeartbeat { .. })
        }

        pub fn get_opn_ckpt(&self) -> (result: i64)
            requires self@ is RslMessageHeartbeat
            ensures result as int == self@->opn_ckpt
        {
            match self {
                CRslMessage::CRslMessageHeartbeat { opn_ckpt } => *opn_ckpt,
                _ => 0, // unreachable
            }
        }
    }

    impl View for CRslMessage {
        type V = RslMessage;
        open spec fn view(&self) -> RslMessage {
            match self {
                CRslMessage::CRslMessageHeartbeat { opn_ckpt } =>
                    RslMessage::RslMessageHeartbeat { opn_ckpt: *opn_ckpt as int },
                CRslMessage::COther => RslMessage::Other,
            }
        }
    }

    pub struct CRslPacket {
        pub src: CEndPoint,
        pub dst: CEndPoint,
        pub msg: CRslMessage,
    }

    impl CRslPacket {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.src.well_formed()
            &&& self.dst.well_formed()
            &&& self.msg.well_formed()
        }
    }

    impl View for CRslPacket {
        type V = RslPacket;
        open spec fn view(&self) -> RslPacket {
            RslPacket {
                src: self.src@,
                dst: self.dst@,
                msg: self.msg@,
            }
        }
    }

    // === EXEC FUNCTION ===

    // Note: This example demonstrates the difficulty of matching spec-level `choose`
    // with exec-level deterministic index computation. The spec uses GetReplicaIndex
    // which is defined via `choose`, making the index non-deterministic.
    // In practice, replica IDs should be unique, making the choice deterministic.
    //
    // For this example, we assume unique replica IDs by adding a precondition.

    pub open spec fn unique_replica_ids(config: LConfiguration) -> bool {
        forall |i: int, j: int|
            #![auto]
            0 <= i < config.replica_ids.len() && 0 <= j < config.replica_ids.len() && i != j
            ==> config.replica_ids[i] != config.replica_ids[j]
    }

    pub fn c_acceptor_process_heartbeat(s: &CAcceptor, inp: &CRslPacket) -> (result: CAcceptor)
        requires
            s.well_formed(),
            inp.well_formed(),
            inp.msg@ is RslMessageHeartbeat,
            s.constants.config.replica_ids@.len() < i64::MAX as int,  // for find_index
            s.last_checkpointed_operation.data@.len() < usize::MAX as int,  // for update
            unique_replica_ids(s@.constants.config),  // Needed to match spec's choose
        ensures
            result.well_formed(),
            LAcceptorProcessHeartbeat(s@, result@, inp@),
    {
        if s.constants.config.contains(&inp.src) {
            let sender_index = s.constants.config.find_index(&inp.src);
            let opn_ckpt = inp.msg.get_opn_ckpt();

            proof {
                // Our sender_index matches GetReplicaIndex because IDs are unique
                assert(s.constants.config@.replica_ids[sender_index as int] == inp.src@);
                assert(0 <= sender_index);
                assert(sender_index < s.constants.config@.replica_ids.len());

                // With unique IDs, GetReplicaIndex must return the same index
                let spec_sender_idx = GetReplicaIndex(inp@.src, s@.constants.config);
                // spec_sender_idx satisfies: 0 <= spec_sender_idx < len && replica_ids[spec_sender_idx] == src
                // Our sender_index also satisfies this
                // Since IDs are unique, spec_sender_idx == sender_index
            }

            if 0 <= sender_index && (sender_index as usize) < s.last_checkpointed_operation.len()
                && opn_ckpt > s.last_checkpointed_operation.get(sender_index as usize)
            {
                let new_last_ckpt = s.last_checkpointed_operation.update(sender_index, opn_ckpt);

                CAcceptor {
                    constants: s.constants.clone_for_view(),
                    max_bal: s.max_bal.clone_for_view(),
                    last_checkpointed_operation: new_last_ckpt,
                }
            } else {
                // No update needed - either index out of bounds or opn_ckpt not greater
                CAcceptor {
                    constants: s.constants.clone_for_view(),
                    max_bal: s.max_bal.clone_for_view(),
                    last_checkpointed_operation: s.last_checkpointed_operation.clone_for_view(),
                }
            }
        } else {
            // Source not in config, no change
            CAcceptor {
                constants: s.constants.clone_for_view(),
                max_bal: s.max_bal.clone_for_view(),
                last_checkpointed_operation: s.last_checkpointed_operation.clone_for_view(),
            }
        }
    }
}

fn main() {}
