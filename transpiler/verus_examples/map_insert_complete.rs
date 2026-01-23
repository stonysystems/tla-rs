// Test for spec predicates with map.insert() and seq concatenation
// Tests: Map.insert(key, value), Seq + seq![element]
// These patterns are used in LProposerProcessRequest

use vstd::prelude::*;
use vstd::map::*;
use vstd::seq::*;

verus! {
    // === SPEC TYPES ===

    pub type ClientId = int;

    pub struct Request {
        pub client: ClientId,
        pub seqno: int,
    }

    pub struct LState {
        pub request_queue: Seq<Request>,
        pub highest_seqno_by_client: Map<ClientId, int>,
    }

    // === SPEC PREDICATE ===
    // Pattern from LProposerProcessRequest:
    // - s_.request_queue == s.request_queue + seq![val]
    // - s_.highest_seqno_by_client == s.highest_seqno_by_client.insert(client, seqno)

    pub open spec fn LProcessRequest(
        s: LState,
        s_: LState,
        req: Request,
        should_add: bool
    ) -> bool
    {
        if should_add {
            &&& s_.request_queue == s.request_queue.push(req)
            &&& s_.highest_seqno_by_client == s.highest_seqno_by_client.insert(req.client, req.seqno)
        } else {
            s_ == s
        }
    }

    // === EXEC TYPES ===

    pub struct CRequest {
        pub client: i64,
        pub seqno: i64,
    }

    impl CRequest {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn clone_for_view(&self) -> (result: CRequest)
            ensures result@ == self@
        {
            CRequest { client: self.client, seqno: self.seqno }
        }
    }

    impl View for CRequest {
        type V = Request;
        open spec fn view(&self) -> Request {
            Request { client: self.client as int, seqno: self.seqno as int }
        }
    }

    // Request queue using Vec
    pub struct CRequestQueue {
        pub data: Vec<CRequest>,
    }

    impl CRequestQueue {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn clone_for_view(&self) -> (result: CRequestQueue)
            ensures result@ == self@
        {
            let mut new_data: Vec<CRequest> = Vec::new();
            let mut i: usize = 0;
            while i < self.data.len()
                invariant
                    i <= self.data@.len(),
                    new_data@.len() == i,
                    forall |j: int| 0 <= j < i ==> new_data@[j]@ == self.data@[j]@,
                decreases self.data@.len() - i
            {
                new_data.push(self.data[i].clone_for_view());
                i = i + 1;
            }
            CRequestQueue { data: new_data }
        }

        pub fn push(&self, req: CRequest) -> (result: CRequestQueue)
            ensures result@ == self@.push(req@)
        {
            let mut new_data = self.clone_for_view().data;
            new_data.push(req);
            CRequestQueue { data: new_data }
        }
    }

    impl View for CRequestQueue {
        type V = Seq<Request>;
        open spec fn view(&self) -> Seq<Request> {
            Seq::new(self.data@.len(), |i: int| self.data@[i]@)
        }
    }

    // Seqno map using ghost state (would be HashMap in real impl)
    pub struct CSeqnoMap {
        pub ghost_state: Ghost<Map<ClientId, int>>,
    }

    impl CSeqnoMap {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn clone_for_view(&self) -> (result: CSeqnoMap)
            ensures result@ == self@
        {
            CSeqnoMap { ghost_state: Ghost(self.ghost_state@) }
        }

        #[verifier::external_body]
        pub fn insert(&self, client: i64, seqno: i64) -> (result: CSeqnoMap)
            ensures result@ == self@.insert(client as int, seqno as int)
        {
            // Real impl would use HashMap.insert
            unimplemented!()
        }
    }

    impl View for CSeqnoMap {
        type V = Map<ClientId, int>;
        open spec fn view(&self) -> Map<ClientId, int> {
            self.ghost_state@
        }
    }

    pub struct CState {
        pub request_queue: CRequestQueue,
        pub highest_seqno_by_client: CSeqnoMap,
    }

    impl CState {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.request_queue.well_formed()
            &&& self.highest_seqno_by_client.well_formed()
        }

        pub fn clone_for_view(&self) -> (result: CState)
            requires self.well_formed()
            ensures result@ == self@, result.well_formed()
        {
            CState {
                request_queue: self.request_queue.clone_for_view(),
                highest_seqno_by_client: self.highest_seqno_by_client.clone_for_view(),
            }
        }
    }

    impl View for CState {
        type V = LState;
        open spec fn view(&self) -> LState {
            LState {
                request_queue: self.request_queue@,
                highest_seqno_by_client: self.highest_seqno_by_client@,
            }
        }
    }

    // === EXEC FUNCTION ===

    pub fn c_process_request(s: &CState, req: &CRequest, should_add: bool) -> (result: CState)
        requires
            s.well_formed(),
            req.well_formed(),
        ensures
            result.well_formed(),
            LProcessRequest(s@, result@, req@, should_add),
    {
        if should_add {
            CState {
                request_queue: s.request_queue.push(req.clone_for_view()),
                highest_seqno_by_client: s.highest_seqno_by_client.insert(req.client, req.seqno),
            }
        } else {
            s.clone_for_view()
        }
    }
}

fn main() {}
