use super::cconstants::CReplicaConstants;
use crate::common::native::io_s::*;
use crate::implementation::RSL::ReplicaImpl::*;
use crate::protocol::RSL::replica::LReplica;
use vstd::prelude::*;

verus! {

    pub struct ReplicaImpl{
        pub replica: CReplica,
        pub nextActionIndex: u64,
        pub localAddr: EndPoint,
    }

    impl ReplicaImpl{

    pub open spec fn valid(&self) -> bool
    {
        &&& self.replica.abstractable()
        &&& self.replica.valid()
        &&& 0 <= self.nextActionIndex
        &&& self.nextActionIndex < 10
        &&& self.localAddr@ === self.replica.constants.all.config.replica_ids[self.replica.constants.my_index as int]@
    }

    pub open spec fn view(&self) -> LReplica
        recommends self.replica.valid()
    {
        self.replica@
    }

    pub fn Replica_Init(constants:CReplicaConstants) -> (rc:Self)
        requires constants.valid(),
        ensures
            rc.replica.constants@ == constants@,
            rc.valid(),
    {
        let c_clone = constants.clone_up_to_view();
        // c_clone@ == constants@, c_clone.valid(), lengths preserved
        let r = CReplica::CReplicaInit(c_clone);
        // r.valid(), r.constants@ == c_clone@ == constants@
        let local = constants.all.config.replica_ids[constants.my_index as usize].clone_up_to_view();
        // local@ == constants.all.config.replica_ids[constants.my_index as int]@
        proof {
            // Bridge: r.constants@ == constants@ gives us field-level view equality
            // r.constants.my_index as int == constants.my_index as int
            // r.constants.all.config@ == constants.all.config@
            // So replica_ids views are equal at the same index
            let ghost rc_ids = r.constants.all.config.replica_ids@.map(|i, e: crate::common::native::io_s::EndPoint| e@);
            let ghost c_ids = constants.all.config.replica_ids@.map(|i, e: crate::common::native::io_s::EndPoint| e@);
            assert(rc_ids =~= c_ids);
            assert(r.constants.my_index as int == constants.my_index as int);
            assert(rc_ids[constants.my_index as int] == c_ids[constants.my_index as int]);
            assert(r.constants.all.config.replica_ids[r.constants.my_index as int]@ == constants.all.config.replica_ids[constants.my_index as int]@);
            assert(local@ == constants.all.config.replica_ids[constants.my_index as int]@);
            assert(local@ === r.constants.all.config.replica_ids[r.constants.my_index as int]@);
        }
        ReplicaImpl{
            replica:r,
            nextActionIndex:0,
            localAddr:local,
        }
    }

    }

}
