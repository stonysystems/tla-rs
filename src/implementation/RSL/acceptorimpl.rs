use super::types_i::COperationNumber;
use vstd::prelude::*;

use crate::implementation::RSL::acceptor_helpers;
use crate::implementation::RSL::cconfiguration::*;
use crate::implementation::RSL::cconstants::*;
use crate::implementation::RSL::types_i::*;
use crate::protocol::RSL::{acceptor::*, types::*};

verus! {
    #[derive(Clone)]
    pub struct CAcceptor {
        pub constants: CReplicaConstants,
        pub max_bal: CBallot,
        pub votes: CVotes,
        pub last_checkpointed_operation: Vec<COperationNumber>,
        pub log_truncation_point: COperationNumber,
        pub min_vote_opn: COperationNumber,
    }

    impl CAcceptor{
        pub open spec fn abstractable(self) -> bool
        {
            &&& self.constants.abstractable()
            &&& self.max_bal.abstractable()
            &&& cvotes_is_abstractable(&self.votes)
            &&& (forall |i:int| 0 <= i < self.last_checkpointed_operation.len() ==> COperationNumberIsAbstractable(self.last_checkpointed_operation[i]))
            &&& COperationNumberIsAbstractable(self.log_truncation_point)
        }

        pub open spec fn valid(self) -> bool {
            &&& self.abstractable()
            &&& self.constants.valid()
            &&& self.max_bal.valid()
            &&& cvotes_is_valid(&self.votes)
            &&& (forall |i:int| 0 <= i < self.last_checkpointed_operation.len() ==> COperationNumberIsValid(self.last_checkpointed_operation[i]))
            &&& COperationNumberIsValid(self.log_truncation_point)
            &&& self.last_checkpointed_operation.len() == self.constants.all.config.replica_ids.len()
        }

        pub open spec fn view(self) -> LAcceptor
            recommends self.abstractable()
        {
            LAcceptor {
                constants: self.constants.view(),
                max_bal: self.max_bal.view(),
                votes: abstractify_cvotes(&self.votes),
                last_checkpointed_operation:self.last_checkpointed_operation@.map(|i,c:COperationNumber| AbstractifyCOperationNumberToOperationNumber(c)),
                log_truncation_point: AbstractifyCOperationNumberToOperationNumber(self.log_truncation_point),
            }
        }

        pub fn clone_up_to_view(&self) -> (result: Self)
            ensures
                result@ == self@,
                result.valid() == self.valid(),
        {
            let constants_clone = self.constants.clone();
            // Clone impl ensures: constants_clone == self.constants, constants_clone@ == self.constants@
            let votes_clone = clone_cvotes_up_to_view(&self.votes);
            // ensures: votes_clone == self.votes
            let ckpt_clone = self.last_checkpointed_operation.clone();
            // Vec<u64>::clone — for Copy elements, clone preserves all values
            proof {
                assert(self.last_checkpointed_operation@ =~= ckpt_clone@);
            }
            CAcceptor {
                constants: constants_clone,
                max_bal: self.max_bal,
                votes: votes_clone,
                last_checkpointed_operation: ckpt_clone,
                log_truncation_point: self.log_truncation_point,
                min_vote_opn: self.min_vote_opn,
            }
        }
    }

    impl View for CAcceptor {
        type V = LAcceptor;

        open spec fn view(&self) -> LAcceptor {
            LAcceptor {
                constants: self.constants.view(),
                max_bal: self.max_bal.view(),
                votes: abstractify_cvotes(&self.votes),
                last_checkpointed_operation: self.last_checkpointed_operation@.map(|i, c: COperationNumber| AbstractifyCOperationNumberToOperationNumber(c)),
                log_truncation_point: AbstractifyCOperationNumberToOperationNumber(self.log_truncation_point),
            }
        }
    }

    // Compatibility wrappers: log-truncation helper implementation lives in
    // implementation/RSL/acceptor_helpers.rs. Keep these symbols here so
    // existing imports/tests that key on acceptorimpl symbol presence stay stable.

    pub fn CIsLogTruncationPointValid(log_truncation_point: COperationNumber,last_checkpointed_operation:&Vec<COperationNumber>,config:&CConfiguration) -> (isValid: bool)
        requires
            COperationNumberIsValid(log_truncation_point),
            forall |i: int| 0 <= i < last_checkpointed_operation.len() ==> COperationNumberIsValid(last_checkpointed_operation[i]),
            config.valid()
        ensures
            isValid == IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(log_truncation_point),last_checkpointed_operation@.map(|i, x| (x as int)), config@)
    {
        acceptor_helpers::CIsLogTruncationPointValid(log_truncation_point, last_checkpointed_operation, config)
    }

    #[allow(dead_code)]
    fn CCountLargerInSeq(s:&Vec<u64>, target:u64) -> (res:u64) {
        acceptor_helpers::CCountLargerInSeq(s, target)
    }


    #[allow(dead_code)]
    fn CCountLargerOrEqualInSeq(s:&Vec<u64>, target:u64) -> (res:u64) {
        acceptor_helpers::CCountLargerOrEqualInSeq(s, target)
    }

    #[allow(dead_code)]
    fn CIsNthHighestValueInSequence(v:u64, s:&Vec<u64>, n:u64) -> (res:bool) {
        acceptor_helpers::CIsNthHighestValueInSequence(v, s, n)
    }

}
