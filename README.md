# IronFleet Verus

# Building and running Verification

## Requirements

* Verus (Last build was using verus - release/rolling/0.2024.09.05.29e4da0)
* rustc (Last build was using rustc - 1.80.1 (3f5fd8dd4 2024-08-06))
* .NET 6.0 SDK (https://dotnet.microsoft.com/download)
* scons (`pip install scons`)
* python 3 (for running scons)

```shell
scons --verus-path="$VERUS_PATH"
```

This should run verus verification and create .dlls/.so in a bin/ folder for the C# files, and at the root of the project for Rust files. To only run the build without verification use `--no-verify`.

# Running

## IronRSL

### Generate Certs

Each IronRSL host has a unique public key as an identifier. Generate these with the CreateIronServiceCerts dll.

```shell
dotnet bin/CreateIronServiceCerts.dll outputdir=certs name=MyCounter type=IronRSL addr1=127.0.0.1 port1=4001 addr2=127.0.0.1 port2=4002 addr3=127.0.0.1 port3=4003
```

### Running the IronRSL servers

Run these lines in separate terminals to run the 3 servers.

```shell
dotnet bin/IronRSLServer.dll certs/MyCounter.IronRSL.service.txt certs/MyCounter.IronRSL.server1.private.txt
dotnet bin/IronRSLServer.dll certs/MyCounter.IronRSL.service.txt certs/MyCounter.IronRSL.server2.private.txt
dotnet bin/IronRSLServer.dll certs/MyCounter.IronRSL.service.txt certs/MyCounter.IronRSL.server3.private.txt
```


## IronLock

### Generate Certs

Each IronLock host has a unique public key as an identifier. Generate these with the CreateIronServiceCerts dll.

```shell
dotnet bin/CreateIronServiceCerts.dll outputdir=certs name=MyLock type=IronLock addr1=127.0.0.1 port1=4001 addr2=127.0.0.1 port2=4002 addr3=127.0.0.1 port3=4003
```

### Running the IronLock servers

Run these lines in separate terminals to run the 3 servers. Note that the protocol only starts working once the first server (server1) is online.

```shell
dotnet bin/IronLockServer.dll certs/MyLock.IronLock.service.txt certs/MyLock.IronLock.server2.private.txt
dotnet bin/IronLockServer.dll certs/MyLock.IronLock.service.txt certs/MyLock.IronLock.server3.private.txt
dotnet bin/IronLockServer.dll certs/MyLock.IronLock.service.txt certs/MyLock.IronLock.server1.private.txt
```

# Notes on porting

- Verus spec functions cannot have any mutable variables or iteration. Any code that depends on iteration in a Dafny (ghost) function needs to be written recursively or in a proof function. However, you can't call proof functions in pre/post-condition clauses.  
- Verus doesn't support adding additional conditions on anything implementing a trait. I'm not sure how to implement the IronFleet structure of having a base, more abstract module and then refining it in each subclass. That's why the clauses from the framework abstract classes are just copied over into the lock functions.
- Verus doesn't support using addition/other operations in a forall clause. For example, trying to state something about two adjacent items in a Dafny function usually looks like:

```
forall i :: 0 <= i < |s| - 1 ==> foo(s[i], s[i+1])
```

This will fail in Verus, and you need to introduce another variable j, with the value for i+1, i.e.

```
forall |i: int| 0 <= i < s.len() - 1 && j == i+1 ==> foo(s[i], s[j])
```

- Verus maps and sets are infinite by default. In Dafny, there are imaps, isets, maps and sets. All verus maps are imaps, and need to be bounded with m.dom().finite() if required.
- Verus has a handy View trait for mapping a concrete type to a ghost type. This is used a lot for the protocol->host implementation. To use it, the struct needs a spec function called view() that returns the ghost type. The shortcut to call the view function is `@`, e.g. host_protocol@ returns an abstract node (The abstract protocol struct).
- Marshalling has a flaw - there's no spec function to check whether something is not deserializable. This makes it hard to assign something like a "CInvalid" message type for non-deserializable message, because I can't prove it's not a valid message. So, these packets are currently just ignored. 

# Code borrowed from IronKV

Some of the code in [IronKV](https://github.com/verus-lang/verified-ironkv) has been directly used:

- NetClient code (src/common/framework/native/io_s.rs)
  - Depends on the verus_extra code as well: (src/verus_extra/...)
- C# code (slightly modified to use Lock)
- Binding to C# code (src/lib.rs)
- The common marshalling library (src/implementation/common/marshalling.rs)

# Code organization

- I've tried to follow the code organization of the original ironfleet code, but there are some changes:
  - "Common" classes and methods for IronFleet main, Host etc. aren't present. I've copied over all the clauses into the lock classes/methods because traits don't allow adding additional lock-specific post/pre conditions.
- Marshalling is completely different, and uses the IronKV code
- Collection functions aren't necessary to always port, since Verus has many in-built collection functions in the library.