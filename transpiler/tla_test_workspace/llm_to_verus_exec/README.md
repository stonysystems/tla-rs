# LLM-to-Verus-Exec (D2 on LLM-generated D1 output)

**Status**: BLOCKED — D2 requires `.automan` annotation files which are not
available for the LLM-generated D1 specs. Only 3/12 LLM TLA+ specs produce
D1 output, and those are minimal flat-variable specs (SimpleConsensus,
SimpleLeader, SimplePrimary).

To unblock: generate `.automan` annotations for D1 specs, either manually
or via the transpiler's `--gen-modes` flag during D1 translation.
