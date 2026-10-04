//! A concrete application satisfying the generic execution theorem's contract.
//! Commands are reads or atomic exchanges on independent integer registers.
use vstd::prelude::*;
use super::application as a;
use super::recovery as r;

verus! {

pub struct Operation { pub key: int, pub write: Option<int> }
pub open spec fn read(s: Map<int, int>, key: int) -> int {
    if s.dom().contains(key) { s[key] } else { 0 }
}
pub open spec fn step(ops: Map<int, Operation>, s: Map<int, int>, x: int) -> Map<int, int> {
    match ops[x].write { Some(v) => s.insert(ops[x].key, v), None => s }
}
pub open spec fn machine(ops: Map<int, Operation>) -> a::Machine<Map<int, int>, int> {
    a::Machine { initial: Map::<int, int>::empty(),
        step: |s: Map<int, int>, x: int| step(ops, s, x),
        output: |s: Map<int, int>, x: int| read(s, ops[x].key) }
}
pub open spec fn config_ok(ops: Map<int, Operation>, c: r::Config) -> bool {
    c.commands == ops.dom()
        && forall|x: int, y: int| c.commands.contains(x) && c.commands.contains(y)
            && x != y && ops[x].key == ops[y].key ==> c.conflict.contains((x, y))
}
pub proof fn distinct_registers_commute(ops: Map<int, Operation>, s: Map<int, int>, x: int, y: int)
    requires ops.dom().contains(x), ops.dom().contains(y), ops[x].key != ops[y].key,
    ensures a::commutes_at(machine(ops), s, x, y),
{
    match (ops[x].write, ops[y].write) {
        (Some(v), Some(w)) => {
            assert(step(ops, step(ops, s, x), y) =~= step(ops, step(ops, s, y), x));
        },
        _ => {},
    }
}
pub proof fn machine_ok(ops: Map<int, Operation>, c: r::Config)
    requires r::config_ok(c), config_ok(ops, c),
    ensures a::machine_ok(machine(ops), c),
{
    assert forall|s: Map<int, int>, x: int, y: int| c.commands.contains(x) && c.commands.contains(y)
        && a::independent(c, x, y) implies #[trigger] a::commutes_at(machine(ops), s, x, y) by {
        assert(ops[x].key != ops[y].key);
        distinct_registers_commute(ops, s, x, y);
    }
}
pub open spec fn example_config() -> r::Config {
    r::Config { nodes: set![0int, 1int, 2int], commands: set![0int, 1int, 2int],
        conflict: set![(0int, 2int), (2int, 0int)], f: 1 }
}
pub open spec fn example_operations() -> Map<int, Operation> {
    Map::<int, Operation>::empty()
        .insert(0, Operation { key: 0, write: Some(5) })
        .insert(1, Operation { key: 1, write: Some(9) })
        .insert(2, Operation { key: 0, write: None })
}
pub proof fn example_application_is_valid()
    ensures r::config_ok(example_config()), config_ok(example_operations(), example_config()),
        a::machine_ok(machine(example_operations()), example_config()),
{
    assert(example_operations().dom() =~= example_config().commands);
    assert(r::config_ok(example_config()));
    machine_ok(example_operations(), example_config());
}

} // verus!
