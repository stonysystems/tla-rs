// Complete Lock service NodeInit example with both spec and exec
// Tests: conditional initialization based on index
// Based on Lock protocol node.rs NodeInit predicate

use vstd::prelude::*;
use vstd::seq::*;

verus! {
    // === SPEC TYPES ===

    pub struct AbstractEndPoint {
        pub id: int,  // Simplified
    }

    pub type AbstractConfig = Seq<AbstractEndPoint>;

    pub struct AbstractNode {
        pub held: bool,
        pub epoch: nat,
        pub my_index: nat,
        pub config: AbstractConfig,
    }

    // === SPEC PREDICATE (from Lock node.rs) ===

    pub open spec fn NodeInit(s: AbstractNode, my_index: nat, config: AbstractConfig) -> bool
    {
        &&& s.epoch == (if my_index == 0 { 1nat } else { 0nat })
        &&& 0 <= my_index < config.len() as nat
        &&& s.my_index == my_index
        &&& s.held == (my_index == 0)
        &&& s.config =~= config
    }

    // === EXEC TYPES ===

    pub struct CEndPoint {
        pub id: i64,
    }

    impl CEndPoint {
        pub open spec fn well_formed(&self) -> bool { true }

        pub fn clone_for_view(&self) -> (result: CEndPoint)
            ensures result@ == self@
        {
            CEndPoint { id: self.id }
        }
    }

    impl View for CEndPoint {
        type V = AbstractEndPoint;
        open spec fn view(&self) -> AbstractEndPoint {
            AbstractEndPoint { id: self.id as int }
        }
    }

    // Config as Vec of endpoints
    pub struct CConfig {
        pub endpoints: Vec<CEndPoint>,
    }

    impl CConfig {
        pub open spec fn well_formed(&self) -> bool {
            self.endpoints@.len() > 0
        }

        pub fn len(&self) -> (result: usize)
            ensures result == self@.len()
        {
            self.endpoints.len()
        }

        pub fn clone_for_view(&self) -> (result: CConfig)
            ensures result@ == self@
        {
            let mut new_endpoints: Vec<CEndPoint> = Vec::new();
            let mut i: usize = 0;
            while i < self.endpoints.len()
                invariant
                    i <= self.endpoints@.len(),
                    new_endpoints@.len() == i,
                    forall |j: int| 0 <= j < i ==> new_endpoints@[j]@ == self.endpoints@[j]@,
                decreases self.endpoints@.len() - i
            {
                new_endpoints.push(self.endpoints[i].clone_for_view());
                i = i + 1;
            }
            CConfig { endpoints: new_endpoints }
        }
    }

    impl View for CConfig {
        type V = AbstractConfig;
        open spec fn view(&self) -> AbstractConfig {
            Seq::new(self.endpoints@.len(), |i: int| self.endpoints@[i]@)
        }
    }

    pub struct CNode {
        pub held: bool,
        pub epoch: u64,
        pub my_index: u64,
        pub config: CConfig,
    }

    impl CNode {
        pub open spec fn well_formed(&self) -> bool {
            self.config.well_formed()
        }
    }

    impl View for CNode {
        type V = AbstractNode;
        open spec fn view(&self) -> AbstractNode {
            AbstractNode {
                held: self.held,
                epoch: self.epoch as nat,
                my_index: self.my_index as nat,
                config: self.config@,
            }
        }
    }

    // === EXEC FUNCTION ===

    pub fn c_node_init(my_index: u64, config: &CConfig) -> (result: CNode)
        requires
            config.well_formed(),
            my_index < config@.len(),
        ensures
            result.well_formed(),
            NodeInit(result@, my_index as nat, config@),
    {
        CNode {
            held: my_index == 0,
            epoch: if my_index == 0 { 1 } else { 0 },
            my_index: my_index,
            config: config.clone_for_view(),
        }
    }
}

fn main() {}
