use super::types_i::COperationNumber;
use vstd::prelude::*;

use crate::common::collections::{count_matches::*, vecs::*};
use crate::implementation::RSL::types_i::*;
use crate::implementation::RSL::cconfiguration::*;
use crate::implementation::RSL::cconstants::*;
use crate::protocol::RSL::{
    acceptor::*, types::*,
};

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

        #[verifier(external_body)]
        pub fn clone_up_to_view(&self) -> (result: Self)
            ensures
                result@ == self@,
                result.valid() == self.valid(),
        {
            self.clone()
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

    // Standalone helper functions used by replica_gen.rs for log truncation validation.

    pub fn CIsLogTruncationPointValid(log_truncation_point: COperationNumber,last_checkpointed_operation:&Vec<COperationNumber>,config:&CConfiguration) -> (isValid: bool)
        requires
            COperationNumberIsValid(log_truncation_point),
            forall |i: int| 0 <= i < last_checkpointed_operation.len() ==> COperationNumberIsValid(last_checkpointed_operation[i]),
            config.valid()
        ensures
            isValid == IsLogTruncationPointValid(AbstractifyCOperationNumberToOperationNumber(log_truncation_point),last_checkpointed_operation@.map(|i, x| (x as int)), config@)
    {
        let quorum = config.CMinQuorumSize();
        CIsNthHighestValueInSequence(log_truncation_point, last_checkpointed_operation, quorum as u64)
    }

    fn CCountLargerInSeq(s:&Vec<u64>, target:u64) -> (res:u64)
        ensures
        ({
            let ss = s@.map(|i, t:u64| t as int);
            && res < 0xffff_ffff_ffff_ffff
            && res as int == CountMatchesInSeq(ss, |x:int| x > target as int)
        })
        decreases s.len(),
    {
        let ghost ss = s@.map(|i, t:u64| t as int);
        if s.len() == 0 {
            assert(ss.len() == 0);
            assert(CountMatchesInSeq(ss, |x:int| x > target as int) == 0);
            0
        } else {
            let rest = truncate_vecu64(s, 1, s.len());
            assert(rest@.map(|i, t:u64| t as int) == ss.subrange(1, ss.len() as int));
            let temp = CCountLargerInSeq(&rest, target);
            assert(temp == CountMatchesInSeq(ss.subrange(1, ss.len() as int), |x:int| x > target as int));
            if s[0] > target {
                assume(temp + 1 < 0xffff_ffff_ffff_ffff);
                temp + 1
            } else
            {
                temp
            }
        }
    }


    fn CCountLargerOrEqualInSeq(s:&Vec<u64>, target:u64) -> (res:u64)
        ensures
        ({
            let ss = s@.map(|i, t:u64| t as int);
            && res < 0xffff_ffff_ffff_ffff
            && res as int == CountMatchesInSeq(ss, |x:int| x >= target as int)
        })
        decreases s.len(),
    {
        let ghost ss = s@.map(|i, t:u64| t as int);
        if s.len() == 0 {
            assert(ss.len() == 0);
            assert(CountMatchesInSeq(ss, |x:int| x > target as int) == 0);
            0
        } else {
            let rest = truncate_vecu64(s, 1, s.len());
            let temp = CCountLargerOrEqualInSeq(&rest, target);
            assert(temp == CountMatchesInSeq(ss.subrange(1, ss.len() as int), |x:int| x >= target as int));
            if s[0] >= target {
                assume(temp + 1 < 0xffff_ffff_ffff_ffff);
                temp + 1
            } else
            {
                temp
            }
        }
    }

    fn CIsNthHighestValueInSequence(v:u64, s:&Vec<u64>, n:u64) -> (res:bool)
        ensures
        ({
            let ss = s@.map(|i, t:u64| t as int);
            && res == IsNthHighestValueInSequence(v as int, ss, n as int)
        })
    {
        let ghost ss = s@.map(|i, t:u64| t as int);
        let len = s.len();
        let b1 = (0 < n) && (n < len as u64);
        assert(b1 == (0 < n < ss.len()));
        let b2 = contains_u64(s, &v);
        assert(b2 == ss.contains(v as int));
        let b3 = CCountLargerInSeq(s, v) < n;
        assert(b3 == (CountMatchesInSeq(ss, |x:int| x > v) < n as int));
        let b4 = CCountLargerOrEqualInSeq(s, v) >= n;
        assert(b4 == (CountMatchesInSeq(ss, |x:int| x >= v) >= n));
        b1 && b2 && b3 && b4
    }

}
