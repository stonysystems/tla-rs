// Manual helper code for RSL concrete types generation.
//
// This file is intended to be injected by transpiler generate-types via
// `output.manual_code` in `types_transpile.toml`.
//
// IMPORTANT: Contents here live inside an existing `verus! { ... }` block in
// generated output. Do not add `use` statements or a nested `verus!` block.

// =============================================================================
// COperationNumber helpers
// =============================================================================

pub open spec fn AbstractifyCOperationNumberToOperationNumber(s:COperationNumber) -> int
    recommends
        COperationNumberIsAbstractable(s)
{
    s as int
}

pub open spec fn COperationNumberIsAbstractable(s:COperationNumber) -> bool {
    true
}

pub open spec fn COperationNumberIsValid(s:COperationNumber) -> bool {
    COperationNumberIsAbstractable(s)
}

// CBallot — defined in types_i.rs via define_struct_and_derive_marshalable! macro
// (imported above; struct, impl, View are all in types_i.rs)

// Ballot comparison functions

pub fn CBalLt(ba:&CBallot, bb:&CBallot) -> (r:bool)
    requires
        ba.valid(),
        bb.valid(),
    ensures r == BalLt(ba@, bb@)
{
    ba.seqno < bb.seqno
    || (ba.seqno == bb.seqno && ba.proposer_id < bb.proposer_id)
}

pub fn CBalLeq(ba:&CBallot, bb:&CBallot) -> (r:bool)
    requires
        ba.valid(),
        bb.valid(),
    ensures r == BalLeq(ba@, bb@)
{
    ba.seqno < bb.seqno
    || (ba.seqno == bb.seqno && ba.proposer_id <= bb.proposer_id)
}

pub fn CBalEq(ba:&CBallot, bb:&CBallot) -> (r:bool)
    requires
        ba.valid(),
        bb.valid(),
    ensures r == (ba@ == bb@)
{
    ba.seqno == bb.seqno
    && ba.proposer_id == bb.proposer_id
}

// CRequest — defined in types_i.rs via define_struct_and_derive_marshalable! macro
// CReply — defined in types_i.rs via define_struct_and_derive_marshalable! macro

// =============================================================================
// CRequestBatch helpers
// =============================================================================

#[verifier(external_body)]
pub fn clone_request_batch_up_to_view(batch: &CRequestBatch) -> (res: CRequestBatch)
    ensures
        res@ == batch@,
        res@.len() == batch@.len(),
        forall |i: int| 0 <= i < batch.len() ==> res[i]@ == batch[i]@,
        crequestbatch_is_valid(&res) == crequestbatch_is_valid(batch),
        crequestbatch_is_abstractable(&res) == crequestbatch_is_abstractable(batch),
{
    let mut cloned:Vec<CRequest> = Vec::new();
    let mut i = 0;
    while i < batch.len()
        invariant
            cloned.len() == i,
            forall |j: int| 0 <= j < i ==> cloned[j]@ == batch[j]@
    {
        assert (forall |i: int| 0 <= i < cloned.len() ==> cloned[i]@ == batch[i]@);
        cloned.push(batch[i].clone_up_to_view());
        i += 1;
    }
    cloned
}

pub open spec fn crequestbatch_is_abstractable(s:&CRequestBatch) -> bool {
    forall |i:int| #![auto] 0 <= i < s.len() ==> s[i].abstractable()
}

pub open spec fn crequestbatch_is_valid(s:&CRequestBatch) -> bool {
    &&& crequestbatch_is_abstractable(s)
    &&& (forall |i:int| #![auto] 0 <= i < s.len() ==> s[i].valid())
}

pub open spec fn abstractify_crequestbatch(s:&CRequestBatch) -> RequestBatch
    recommends crequestbatch_is_abstractable(s)
{
    s@.map(|i, r:CRequest| r@)
}

pub open spec fn RequestBatchSizeLimit() -> int { 1000 }

// =============================================================================
// CReplyCache helpers
// =============================================================================

#[verifier(external_body)]
pub fn clone_creply_cache_up_to_view(cache: &CReplyCache) -> (res: CReplyCache)
    ensures
        res@ == cache@,
        forall |k| cache@.contains_key(k) ==> res@.contains_key(k),
        forall |k| res@.contains_key(k) ==> cache@.contains_key(k),
        forall |k| res@.contains_key(k) ==> res@[k] == cache@[k]
{
    let mut cloned:HashMap<EndPoint, CReply> = HashMap::new();

    // Manually collect keys to avoid iterator issues
    let mut keys: Vec<EndPoint> = Vec::new();

    for k in cache.keys() {
        keys.push(k.clone_up_to_view());
    }

    let mut j = 0;
    while j < keys.len()
        invariant
            0 <= j <= keys.len(),
            forall |k: int| 0 <= k < j ==> cloned.contains_key(&keys[k]) && cloned@[keys[k]] == cache@[keys[k]]
    {
        let key = keys[j].clone_up_to_view();
        let val = cache.get(&key).unwrap();
        cloned.insert(key, val.clone_up_to_view());
        j += 1;
    }

    cloned
}

pub open spec fn creplycache_is_abstractable(m:&CReplyCache) -> bool {
    forall |i| #![auto] m@.contains_key(i) ==> i.abstractable() && m@[i].abstractable()
}

pub open spec fn creplycache_is_valid(m:&CReplyCache) -> bool {
    &&& creplycache_is_abstractable(m)
    &&& (forall |i| #![auto] m@.contains_key(i) ==> m@[i].valid())
}

pub open spec fn abstractify_creplycache(m:&CReplyCache) -> ReplyCache
    recommends creplycache_is_abstractable(m)
{
    Map::new(
        |ak: AbstractEndPoint| exists |k:EndPoint| m@.contains_key(k) && k@ == ak,
        |ak: AbstractEndPoint| {
            let k = choose |k: EndPoint| m@.contains_key(k) && k@ == ak;
            m@[k]@
        }
    )
}

// CVote — defined in types_i.rs via define_struct_and_derive_marshalable! macro

// =============================================================================
// CVotes helpers
// =============================================================================

#[verifier(external_body)]
pub fn clone_cvotes_up_to_view(votes: &CVotes) -> (res: CVotes)
    ensures
        res@ == votes@,
        res == votes,
        forall |k| votes@.contains_key(k) ==> res@.contains_key(k),
        forall |k| res@.contains_key(k) ==> votes@.contains_key(k),
        forall |k| res@.contains_key(k) ==> res@.index(k) == votes@.index(k)
{
    let mut cloned:HashMap<COperationNumber, CVote> = HashMap::new();

    // Avoid borrow issues by collecting keys separately
    let mut keys: Vec<COperationNumber> = Vec::new();
    for &k in votes.keys() {
        keys.push(k);
    }

    let mut i = 0;
    while i < keys.len()
        invariant
            i <= keys.len(),
            forall |j: int| 0 <= j < i ==> {
                let k = keys[j];
                cloned.contains_key(&k) && cloned@.index(k) == votes@.index(k)
            }
    {
        let k = keys[i];
        let v = votes.get(&k).unwrap();
        cloned.insert(k, v.clone_up_to_view());
        i += 1;
    }
    cloned
}

pub open spec fn cvotes_is_abstractable(m:&CVotes) -> bool {
    forall |i| #![auto] m@.contains_key(i) ==> COperationNumberIsAbstractable(i) && m@[i].abstractable()
}

pub open spec fn cvotes_is_valid(m:&CVotes) -> bool {
    &&& cvotes_is_abstractable(m)
    &&& (forall |i| #![auto] m@.contains_key(i) ==> COperationNumberIsValid(i) && m@[i].valid())
}

pub open spec fn abstractify_cvotes(m:&CVotes) -> Votes
    recommends cvotes_is_abstractable(m)
{
    Map::new(
        |ak: int| exists |k: u64| m@.contains_key(k) && k@ == ak,
        |ak: int| {
            let k = choose |k: u64| m@.contains_key(k) && k@ == ak;
            m@[k]@
        }
    )
}

pub open spec fn max_votes_len() -> int{1001}

// =============================================================================
// CLearnerState helpers
// =============================================================================

pub open spec fn clearnerstate_is_abstractable(m:CLearnerState) -> bool {
    forall |i| #![auto] m@.contains_key(i) ==> COperationNumberIsAbstractable(i) && m@[i].abstractable()
}

pub open spec fn clearnerstate_is_valid(m:CLearnerState) -> bool {
    &&& clearnerstate_is_abstractable(m)
    &&& (forall |i| #![auto] m@.contains_key(i) ==> COperationNumberIsValid(i) && m@[i].valid())
}

pub open spec fn abstractify_clearnerstate(m:CLearnerState) -> LearnerState
    recommends clearnerstate_is_abstractable(m)
{
    Map::new(
        |ak: int| exists |k: u64| m@.contains_key(k) && k@ == ak,
        |ak: int| {
            let k = choose |k: u64| m@.contains_key(k) && k@ == ak;
            m@[k]@
        }
    )
}

#[verifier(external_body)]
pub fn clone_vec_coperationnumber(v: &Vec<COperationNumber>) -> (res: Vec<COperationNumber>)
    ensures
        res==v,
        res@ == v@,
        res.len() == v.len(),
{
    let mut result:Vec<COperationNumber> = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            result.len() == i,
            result@ == v@.subrange(0, i as int),
            forall |j: int| 0 <= j < i ==> result@[j] == v@[j]
    {
        let item = v[i];
        result.push(item);
        i += 1;
        assert(result@ == v@.subrange(0, i as int));
    }

    result
}

// =============================================================================
// CParameters extension section
// =============================================================================

// =============================================================================
// CParameters (generated + impl methods)
// =============================================================================

#[derive(Clone, Copy)]
pub struct CParameters {
    pub max_log_length: u64,
    pub baseline_view_timeout_period: u64,
    pub heartbeat_period: u64,
    pub max_integer_val: u64,
    pub max_batch_size: u64,
    pub max_batch_delay: u64,
}

impl CParameters{
    pub fn clone_up_to_view(&self) -> (result:Self)
    ensures self@ == result@
    {
        CParameters {
            max_log_length: self.max_log_length,
            baseline_view_timeout_period: self.baseline_view_timeout_period,
            heartbeat_period: self.heartbeat_period,
            max_integer_val: self.max_integer_val,
            max_batch_size: self.max_batch_size,
            max_batch_delay: self.max_batch_delay,
        }
    }

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

pub fn StaticParams() -> (p:CParameters)
    ensures
        p.max_log_length > 0,
        p.max_log_length < 10000,
        p.valid(),
        p.max_log_length < max_votes_len(),
        0 < p.max_batch_size <= RequestBatchSizeLimit(),
{
    CParameters{
        max_log_length: 1000,
        baseline_view_timeout_period: 400,
        heartbeat_period: 30,
        max_integer_val: 0x8000_0000_0000_0000 - 1,
        max_batch_size: 32,
        max_batch_delay: 30,
    }
}

// =============================================================================
// CConfiguration (generated + impl methods)
// =============================================================================

#[derive(Clone)]
pub struct CConfiguration {
    pub replica_ids: Vec<EndPoint>,
}

impl CConfiguration {
    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (res:CConfiguration)
    ensures
        self@ == res@,
        self == res,
        res.valid(),
    {
        let mut newVec:Vec<EndPoint> = Vec::new();
        let mut i = 0;
        let len = self.replica_ids.len();
        while i<len
        {
            assert(i >= 0);
            assert(i < self.replica_ids@.len());
            newVec.push(self.replica_ids[i].clone_up_to_view());
            i += 1;
        }
        CConfiguration {
            replica_ids: newVec,
        }
    }

    pub open spec fn abstractable(self) -> bool
    {
        &&& (forall |i:int| 0 <= i < self.replica_ids.len() ==> self.replica_ids[i].abstractable())
        &&& seq_is_unique(self.replica_ids@)
    }

    pub open spec fn valid(self) -> bool
    {
        &&& self.abstractable()
        &&& (forall |i:int| 0 <= i < self.replica_ids.len() ==> self.replica_ids[i].abstractable() && self.replica_ids[i].valid_public_key())
        &&& (0 < self.replica_ids.len() < 0xffff_ffff_ffff_ffff)
    }

    pub open spec fn view(self) -> LConfiguration
    {
        LConfiguration{
            clientIds: Set::<AbstractEndPoint>::empty(),
            replica_ids: self.replica_ids@.map(|i, e:EndPoint| e@)
        }
    }

    pub fn CMinQuorumSize(&self) -> (q:usize)
        requires
            self.valid()
        ensures
            q as int == LMinQuorumSize(self@)
    {
        self.replica_ids.len()/2 + 1
    }

    pub open spec fn CReplicaDistinct(&self, i:int, j:int) -> bool
    {
        &&& 0 <= i < self.replica_ids.len()
        &&& 0 <= j < self.replica_ids.len()
        &&& self.replica_ids[i] == self.replica_ids[j] ==> i == j
    }

    pub open spec fn CReplicasIsUnique(&self) -> bool
    {
        forall |i:int, j:int| 0 <= i < self.replica_ids.len() && 0 <= j < self.replica_ids.len() && self.replica_ids[i] == self.replica_ids[j] ==> i == j
    }

    pub open spec fn CWellFormedCConfiguration(&self) -> bool
    {
        &&& 0 < self.replica_ids.len()
        &&& (forall |i:int, j:int| self.CReplicaDistinct(i, j))
        &&& self.CReplicasIsUnique()
    }

    pub open spec fn CIsReplicaIndex(&self, idx:usize, id:EndPoint) -> bool
    {
        &&& 0 <= idx < self.replica_ids.len()
        &&& self.replica_ids[idx as int] == id
    }

    pub fn CGetReplicaIndex( &self, id:&EndPoint) -> (rc:(bool, usize))
        requires
            self.valid(),
            id.valid_public_key(),
        ensures
            ({
                let found = rc.0;
                let index = rc.1;
                &&& found ==> self.CIsReplicaIndex(index, *id)
                &&& found ==> GetReplicaIndex(id@, self@) == index as int /* refinement */
                &&& !found ==> !(self.replica_ids@.contains(*id))
                &&& !found ==> !(self@.replica_ids.contains(id@))
            })
    {
        let mut i = 0;
        assert(self.valid());

        while i < self.replica_ids.len()
            invariant
                i < self.replica_ids.len(),
                forall |j:int| 0 <= j < i ==> self.replica_ids[j] != id,
                self.valid()
            decreases self.replica_ids.len() - i,
        {
            if do_end_points_match(&id, &self.replica_ids[i]) {
                let found = true;
                let idx = i;

                assert(id@ == self.replica_ids[i as int]@);

                let ghost sid = id@;
                let ghost sreplicas = self@.replica_ids;
                assert(sid == sreplicas[i as int]);
                assert(0 <= idx < sreplicas.len());
                assert(sreplicas[idx as int] == sid);
                assert(ItemAtPositionInSeq(sreplicas, sid, idx as int));
                assert(self.valid());
                assert(self.abstractable());
                assert(seq_is_unique(self.replica_ids@));


                assert(self.replica_ids[i as int] == id);
                assert(forall |j:int| 0 <= j < self.replica_ids.len() && j != i as int ==> self.replica_ids[j] != id);

                proof {
                    lemma_AbstractifyEndpoints_properties(self.replica_ids);
                }

                assert(seq_is_unique(sreplicas));
                assert(sreplicas[i as int] == sid);
                assert(forall |j:int| 0 <= j < sreplicas.len() && j != i as int ==> sreplicas[j] != sid);

                proof {
                    lemma_FindIndexInSeq(sreplicas, sid);
                }
                assert(idx >= 0 && sreplicas[idx as int] == sid);
                assert(FindIndexInSeq(sreplicas, sid) == idx as int);
                return (found, idx);
            }

            if i == self.replica_ids.len() - 1 {
                let found = false;
                let idx = 0;
                assert(!self.replica_ids@.contains(*id));
                proof {
                    lemma_AbstractifyEndpoints_properties(self.replica_ids);
                }
                return (found, idx);
            }
            i = i + 1;
        }

        (false, 0)
    }
}

impl View for CConfiguration {
    type V = LConfiguration;

    open spec fn view(&self) -> LConfiguration {
        LConfiguration {
            clientIds: Set::<AbstractEndPoint>::empty(),
            replica_ids: self.replica_ids@.map(|i, e:EndPoint| e@),
        }
    }
}

pub open spec fn ReplicaIndexValid(index:u64, config:CConfiguration) -> bool
{
    0 <= index < config.replica_ids.len()
}

#[verifier::external_body]
pub proof fn lemma_AbstractifyEndpoints_properties(s:Vec<EndPoint>)
    requires
        seq_is_unique(s@),
        (forall |i:int| 0 <= i < s.len() ==> s[i].abstractable()),
    ensures
        ({
            let ss = s@.map(|i, e:EndPoint| e@);
            &&& s.len() ==  ss.len()
            &&& (forall |i:int| 0 <= i < s.len() ==> ss[i] == s[i]@)
            &&& (forall |i:AbstractEndPoint| ss.contains(i) ==> exists |x:int| 0 <= x < s.len() && i == s[x]@)
            &&& (forall |i:EndPoint| ss.contains(i@) ==> exists |x:int| 0 <= x < s.len() && i == s[x])
            &&& seq_is_unique(ss) /* this one cannot be verified */
        })
{
    lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
}

#[verifier::external_body]
pub proof fn lemma_AbstractifyEndPointToNodeIdentity_injective(x:EndPoint, y:EndPoint)
    requires
        x@ == y@
    ensures
        x == y
{

}

pub proof fn lemma_AbstractifyEndPointToNodeIdentity_injective_forall()
    ensures forall |e1:EndPoint, e2:EndPoint| #![trigger e1@, e2@] e1@ == e2@ ==> e1 == e2
{
    assert forall |e1:EndPoint, e2:EndPoint| #![trigger e1@, e2@] e1@ == e2@ implies e1 == e2 by
    {
        lemma_AbstractifyEndPointToNodeIdentity_injective(e1, e2);
    }
}

pub fn CFindIndexInSeq(s:Vec<EndPoint>, v:EndPoint, start:usize) -> (rc:(bool, usize))
    requires s.len() < 0xffff_ffff_ffff_ffff
    decreases s.len() - start,
{
    let ghost ss = s@.map(|i, e:EndPoint| e@);
    let ghost vv = v@;
    if start >= s.len() {
        (false, 0)
    } else if do_end_points_match(&v, &s[start]) {
        (true, start)
    } else {
        CFindIndexInSeq(s, v, start+1)
    }
}

// =============================================================================
// CConstants (generated + impl methods)
// =============================================================================

#[derive(Clone)]
pub struct CConstants {
    pub config: CConfiguration,
    pub params: CParameters,
}

impl CConstants {
    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result:Self)
    ensures
        self == result,
        self@ == result@,
        result.valid()
    {
        CConstants {
            config: self.config.clone_up_to_view(),
            params: self.params.clone_up_to_view(),
        }
    }

    pub open spec fn abstractable(self) -> bool
    {
        self.config.abstractable()
    }

    pub open spec fn valid(self) -> bool
    {
        &&& self.config.valid()
        &&& self.params.valid()
        &&& self.abstractable()
        &&& (0 <= self.params.heartbeat_period < self.params.max_integer_val)
        &&& (0 < self.params.max_batch_size as int <= RequestBatchSizeLimit())
        &&& (self.params.max_log_length < max_votes_len())
    }

    pub open spec fn view(self) -> LConstants
        recommends self.abstractable()
    {
        LConstants{
            config:self.config@,
            params:self.params@,
        }
    }
}

impl View for CConstants {
    type V = LConstants;

    open spec fn view(&self) -> LConstants {
        LConstants {
            config: self.config@,
            params: self.params@,
        }
    }
}

// =============================================================================
// CReplicaConstants (generated + impl methods)
// =============================================================================

#[derive(Clone)]
pub struct CReplicaConstants {
    pub my_index: u64,
    pub all: CConstants,
}

impl CReplicaConstants {
    #[verifier(external_body)]
    pub fn clone_up_to_view(&self) -> (result:Self)
    ensures
        self@ == result@,
        result.valid()
    {
        CReplicaConstants {
            my_index: self.my_index,
            all: self.all.clone_up_to_view(),
        }
    }

    pub open spec fn abstractable(self) -> bool
    {
        &&& self.all.abstractable()
        &&& ReplicaIndexValid(self.my_index, self.all.config)
    }

    pub open spec fn valid(self) -> bool
    {
        &&& self.abstractable()
        &&& self.all.valid()
    }

    pub open spec fn view(self) -> LReplicaConstants
        recommends self.abstractable()
    {
        LReplicaConstants{
            my_index: self.my_index as int,
            all: self.all@,
        }
    }

    pub fn CReplicaConstantsValid(&self) -> (res:bool)
        requires self.valid(),
        ensures res == LReplicaConstantsValid(self@)
    {
        self.my_index >= 0 && self.my_index < self.all.config.replica_ids.len() as u64
    }
}

impl View for CReplicaConstants {
    type V = LReplicaConstants;

    open spec fn view(&self) -> LReplicaConstants {
        LReplicaConstants {
            my_index: self.my_index as int,
            all: self.all@,
        }
    }
}

pub fn InitReplicaConstants(end:&EndPoint, config:&CConfiguration) -> (rc:CReplicaConstants)
    requires
        config.valid(),
        end.valid_public_key(),
        config.replica_ids@.contains(*end),
    ensures
        rc.valid(),
        rc.all.config.replica_ids[rc.my_index as int] == end,
        rc.all.config == config,
        rc.all.params.max_log_length > 0,
        rc.all.params.max_log_length < 10000,
{
    let params = StaticParams();
    let (found, index) = config.CGetReplicaIndex(end);
    let constants = CConstants{config:config.clone_up_to_view(), params:params};
    assert(constants.config.valid());
    assert(constants.params.valid());
    assert(0 <= constants.params.heartbeat_period < constants.params.max_integer_val);
    assert(0 < constants.params.max_batch_size as int <= RequestBatchSizeLimit());
    assert(constants.params.max_log_length < max_votes_len());

    let rconstants = CReplicaConstants{my_index:index as u64, all:constants};
    assert(rconstants.abstractable());
    assert(rconstants.all.valid());
    rconstants
}
