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

    #[verifier::external_body]
    pub fn Replica_Init(constants:CReplicaConstants) -> (rc:Self)
        requires constants.valid(),
        ensures
            rc.replica.constants == constants,
            rc.valid(),
    {
        let r = CReplica::CReplicaInit(constants.clone_up_to_view());
        ReplicaImpl{
            replica:r,
            nextActionIndex:0,
            localAddr:constants.all.config.replica_ids[constants.my_index as usize].clone_up_to_view(),
        }
    }

    }

}
