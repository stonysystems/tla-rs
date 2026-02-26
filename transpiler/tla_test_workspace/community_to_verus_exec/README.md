# Community-to-Verus-Exec (D2 on community-authored D1 output)

**Status**: BLOCKED — D2 requires `.automan` annotation files which are not
available for the community-authored D1 specs. Only 3/4 community TLA+ specs
produce D1 output, and those are minimal struct skeletons (EPaxos, Paxos, Raft).

To unblock: generate `.automan` annotations for D1 specs, either manually
or via the transpiler's `--gen-modes` flag during D1 translation.
