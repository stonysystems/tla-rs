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
