//! Nonempty, enabled initial configurations for each port. These are smoke
//! witnesses; the benchmark theorems quantify over arbitrary constants/traces.
use vstd::prelude::*;
use super::{open_addressing as oa, flash as fl, tlb, etcd, hashicorp as hc};
verus! {
pub open spec fn oa_constants() -> oa::Constants {
    oa::Constants { k: 4,limit: 1,fps: set![1int,2int],writers: set![0int],readers: Set::empty() }
}
pub proof fn open_addressing_starts()
    ensures oa::valid_constants(oa_constants()),
        oa::enabled(oa::initial(oa_constants()),oa_constants(),oa::Action::Writer { p: 0,pick: 1 })
{ reveal(oa::enabled); }
pub open spec fn flash_constants() -> fl::Constants {
    fl::Constants { nodes: set![0int],data: ISet::empty().insert(1int).insert(2int) }
}
pub proof fn flash_can_write()
    ensures fl::valid_constants(flash_constants()),
        fl::enabled(fl::initial(flash_constants(),0,1),flash_constants(),fl::Action::LocalGetX),
        fl::enabled(fl::apply(fl::initial(flash_constants(),0,1),flash_constants(),fl::Action::LocalGetX),flash_constants(),fl::Action::Store { src: 0,data: 2 })
{
    reveal(fl::enabled); reveal(fl::apply);
    assert(flash_constants().data.contains(1));
}
pub open spec fn tlb_constants() -> tlb::Constants {
    tlb::Constants { processors: ISet::empty().insert(0int),pmaps: ISet::empty().insert(1int),entries: ISet::empty().insert(2int) }
}
pub open spec fn tlb_initial() -> tlb::LState {
    let c=tlb_constants();
    tlb::LState { procs: IMap::new(|i: int| c.processors.contains(i), |i: int| tlb::LProcessor {
        pc: tlb::Pc::Boot,userpmap: 1,writepmap: 1,currentcpu: 0,actionlock: false,actionneeded: false,
        active: true,interrupt: false,tlb: 2,todo: ISet::empty(),
    }),plock: IMap::new(|m: int| c.pmaps.contains(m), |m: int| false),pentry: IMap::new(|m: int| c.pmaps.contains(m), |m: int| 2),error: false }
}
pub proof fn tlb_can_boot()
    ensures tlb::valid_constants(tlb_constants()),tlb::init(tlb_initial(),tlb_constants()),
        tlb::enabled_step(tlb_initial(),tlb_constants(),0,tlb::Step::Boot(1))
{
    reveal(tlb::enabled_step);
    assert(tlb_constants().processors.contains(0));
    assert(tlb_constants().pmaps.contains(1));
    assert(tlb_constants().entries.contains(2));
    assert(tlb_initial().procs.dom() =~= tlb_constants().processors);
    assert(tlb_initial().plock.dom() =~= tlb_constants().pmaps);
    assert(tlb_initial().pentry.dom() =~= tlb_constants().pmaps);
}
pub open spec fn etcd_constants() -> etcd::Constants {
    etcd::Constants { servers: ISet::empty().insert(0int),voters: set![0int] }
}
pub proof fn etcd_can_campaign()
    ensures etcd::valid_constants(etcd_constants()),
        etcd::enabled(etcd::initial(etcd_constants()),etcd_constants(),etcd::Action::Timeout(0)),
        etcd::enabled(etcd::apply(etcd::initial(etcd_constants()),etcd_constants(),etcd::Action::Timeout(0)),etcd_constants(),etcd::Action::RequestVote { i: 0,j: 0 })
{ reveal(etcd::enabled); reveal(etcd::apply); }
pub open spec fn hashicorp_constants() -> hc::Constants {
    hc::Constants { servers: set![0int],values: ISet::empty().insert(1int) }
}
pub proof fn hashicorp_can_elect()
    ensures hc::valid_constants(hashicorp_constants()),
        hc::enabled(hc::initial(hashicorp_constants()),hashicorp_constants(),hc::Action::Timeout(0)),
        hc::enabled(hc::apply(hc::initial(hashicorp_constants()),hashicorp_constants(),hc::Action::Timeout(0)),hashicorp_constants(),hc::Action::BecomeLeader(0))
{
    reveal(hc::enabled); reveal(hc::protocol_apply);
    assert(hashicorp_constants().values.contains(1));
    let u=hc::apply(hc::initial(hashicorp_constants()),hashicorp_constants(),hc::Action::Timeout(0));
    assert(u.nodes[0].granted.intersect(u.nodes[0].latest_config) =~= set![0int]);
}
} // verus!
