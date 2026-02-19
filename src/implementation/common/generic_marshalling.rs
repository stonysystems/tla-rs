use vstd::prelude::*;

verus! {
    pub enum G {
        GUint64,
        GArray { elt: Box<G> },
        GTuple { t: Seq<G> },
        GByteArray,
        GTaggedUnion { cases: Seq<G> },
    }
}
