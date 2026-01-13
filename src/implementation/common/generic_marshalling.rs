use vstd::prelude::*;
use vstd::seq::*;

verus! {
    pub enum G {
        GUint64,
        GArray { elt: Box<G> },
        GTuple { t: Seq<G> },
        GByteArray,
        GTaggedUnion { cases: Seq<G> },
    }

//     impl G {
//         pub open spec fn size(&self) -> nat
//             decreases self
//         {
//             match self {
//                 G::GUint64 => 1,
//                 G::GByteArray => 1,
//                 G::GArray { elt } => 1 + elt.size(),
//                 G::GTuple { t } => 1 + t.fold_left(0, |acc: nat, g: G| acc + g.size()),
//                 G::GTaggedUnion { cases } => 1 + cases.fold_left(0, |acc: nat, g: G| acc + g.size()),
//             }
//         }

//         pub open spec fn valid(&self) -> bool
//     decreases self.size()
// {
//     match self {
//         G::GUint64 => true,
//         G::GArray { elt } => {
//             // assert(elt.size() < self.size());
//             elt.valid()
//         },
//         G::GTuple { t } => {
//             // assert(forall|i: int| 0 <= i && i < t.len() ==> t.index(i).size() < self.size());
//             t.len() < 0xFFFF_FFFF_FFFF_FFFFu64 &&
//             forall|i: int| 0 <= i && i < t.len() ==> t.index(i).valid()
//         },
//         G::GByteArray => true,
//         G::GTaggedUnion { cases } => {
//             // assert(forall|i: int| 0 <= i && i < cases.len() ==> cases.index(i).size() < self.size());
//             cases.len() < 0xFFFF_FFFF_FFFF_FFFFu64 &&
//             forall|i: int| 0 <= i && i < cases.len() ==> cases.index(i).valid()
//         },
//     }
// }

//     }
}
