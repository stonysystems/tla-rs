Compiling

`verus --crate-type=dylib --expand-errors --compile lib.rs`

`dotnet bin/CreateIronServiceCerts.dll outputdir=certs name=MyLock type=IronLock addr1=127.0.0.1 port1=4001 addr2=127.0.0.1 port2=4002 addr3=127.0.0.1 port3=4003`

---

Qs:
    - don't understand the syntax of the OkState class


imply() in the ironfleet code is temporal_imply() because verus has a imply function
show:
    - EXAMPLE: Recursive spec with proofs to a lemma + spec

----

Qs:

- Opaque functions?
- Are functions from modules in Dafny "open" or "closed"?
- Porting the IO code
- How does C# connect to Dafny code? Io Framework example
- what does reveals do
  -  export All reveals *

---

predicate => proof function that returns bool
Coding this in two parts:
    - a spec function to implement the ghost code
    - a proof function for the spec
    - Caveat: would need to call the proof as a lemma every time you use the predicate?

Issues with using enums as datatypes - extracting and matching is very verbose

----

```rust
    spec fn extract_sent_lpackets_from_ios<IdType, MessageType>(ios: LIoOp<IdType, MessageType>) -> Option<LPacket<IdType, MessageType>> {
    match ios {
        LIoOp::Send { s } => Some(s),
        _ => None,
    }
    }

    spec fn match_ios_recv<IdType, MessageType>(io: LIoOp<IdType, MessageType>, sentPackets: Set<LPacket<IdType, MessageType>>) -> bool {
    match io {
        LIoOp::Receive { r } => sentPackets.contains(r),
        _ => true,
    }
    }

    spec fn LEnvironment_PerformIos<IdType, MessageType>(
    {
    &&& e_.sentPackets =~= e.sentPackets.union(
                                    ios.map_values(|io| extract_sent_lpackets_from_ios(io))
                                        .filter(|io: Option<LPacket<IdType, MessageType>>| io.is_some())
                                        .map_values(|io:  Option<LPacket<IdType, MessageType>>| io.unwrap())
                                        .to_set())
    }
```

---

What's a trigger, how does it help?
Need to work on writing TLA logic, IO code