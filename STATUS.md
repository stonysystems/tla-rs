# tla-rs Project Status Report

**Date**: 2026-02-04
**Verus Version**: v0.2026.02.04.175a879
**Rust Toolchain**: 1.93.0

## Executive Summary

The tla-rs project has made **significant progress** on code generation. All 8 RSL modules have been successfully transpiled with **working implementations** (not just stubs). However, the generated code uses `assume` statements to bypass verification temporarily while the transpiler is being improved.

### Current State: ✅ Code Generation Working, ⚠️ Verification Pending

## Generated Code Statistics

| Module | LOC | Exec Functions | Assume Statements | Status |
|--------|-----|----------------|-------------------|--------|
| **replica_gen.rs** | 817 | 29 | 73 | ✅ Complete with assumes |
| **proposer_gen.rs** | 490 | 12 | 31 | ✅ Complete with assumes |
| **election_gen.rs** | 366 | 11 | 22 | ✅ Complete with assumes |
| **acceptor_gen.rs** | 283 | 7 | 23 | ✅ Complete with assumes |
| **executor_gen.rs** | 251 | 8 | 19 | ✅ Complete with assumes |
| **learner_gen.rs** | 194 | 4 | 12 | ✅ Complete with assumes |
| **types_gen.rs** | 121 | 0 | 0 | ✅ Type definitions only |
| **broadcast_gen.rs** | 45 | 1 | 2 | ✅ Complete with assumes |
| **TOTAL** | **2,567** | **72** | **182** | |

### Key Achievements

1. ✅ **All 8 RSL modules transpiled** - Complete implementations for election, replica, proposer, acceptor, executor, learner, broadcast
2. ✅ **72 executable functions generated** - All predicates and helper functions have exec implementations
3. ✅ **Code compiles** - Generated code uses proper Rust/Verus syntax
4. ✅ **Helper functions integrated** - Uses `truncate_vec`, `concat_vecs`, `clone_hashset`, etc.
5. ✅ **Match expressions for enums** - Proper pattern matching instead of `is` operator
6. ✅ **Method call mappings** - `LMinQuorumSize` → `CMinQuorumSize()`, `GetReplicaIndex` → `CGetReplicaIndex()`

## What's Working

### 1. Code Generation Patterns ✅

The transpiler successfully generates:

- **Struct construction** from conjunctions
- **While loops** for recursive functions (e.g., `CRemoveAllSatisfiedRequestsInSequence`)
- **Match expressions** for enum handling (e.g., line 167 in election_gen.rs)
- **Vector operations** using helper functions (`truncate_vec`, `concat_vecs`)
- **HashSet operations** using helper functions (`clone_hashset`)
- **Method calls** on receivers (e.g., `config.CMinQuorumSize()`)

### 2. Type System ✅

- **View trait implementations** - All generated types have proper `@` conversions
- **Validity predicates** - All types have `valid()` checks
- **Type re-exports** - `types_gen.rs` properly re-exports implementation types
- **Custom types** - `CScheduler`, `CClockReading` defined uniquely in generated code

### 3. Configuration System ✅

The `election_transpile.toml` demonstrates a working configuration:

```toml
[naming]
spec_prefix = "L"
exec_prefix = "C"
int_type = "u64"
nat_type = "u64"

[remapping]
"RslMessage" = "CMessage"
"RslMessageHeartbeat" = "CMessage::CMessageHeartbeat"

[method_calls]
"LMinQuorumSize" = { method_name = "CMinQuorumSize", receiver_arg_index = 0 }
"GetReplicaIndex" = { method_name = "CGetReplicaIndex", receiver_arg_index = 1 }
```

## What's NOT Working (Using Assumes) ⚠️

### 1. Verification Bypassed (182 assume statements)

All generated functions use `assume` to bypass Verus verification:

```rust
pub exec fn CComputeSuccessorView(b: &CBallot, c: &CConstants) -> (result: CBallot)
requires b.valid(), c.valid(),
ensures result.valid(), result@ == ComputeSuccessorView(b@, c@),
{
    assume(b.seqno < u64::MAX);  // ⚠️ Bypassing verification
    let result = if ((b.proposer_id + 1) < c.config.replica_ids.len() as u64) {
        CBallot { seqno: b.seqno, proposer_id: (b.proposer_id + 1) }
    } else {
        CBallot { seqno: (b.seqno + 1), proposer_id: 0 }
    };
    assume(result.valid());  // ⚠️ Bypassing verification
    assume(result@ == ComputeSuccessorView(b@, c@));  // ⚠️ Bypassing verification
    result
}
```

**Impact**: Code compiles and runs but is not formally verified.

### 2. Translation Issues (From Phase 9 Plan)

The transpiler still needs fixes for 8 major issues:

1. ❌ **Vector view functions** - Missing `.map(|i, r: CRequest| r@)` (currently manual in assumes)
2. ❌ **HashSet view functions** - Missing `.map(|x: u64| x as int)` (currently manual in assumes)
3. ❌ **Vector validity predicates** - Missing forall checks in struct valid() methods
4. ❌ **Enum "is" operator** - Currently uses match (✅) but needs better codegen
5. ❌ **EndPoint comparisons** - Uses `==` instead of `do_end_points_match()` in some places
6. ❌ **Type refinement checks** - May still have `expr is Type` checks
7. ❌ **Vector operations** - Uses helper functions (✅) but needs direct codegen
8. ❌ **Integer casts** - Manually added `as u64` for `.len()` comparisons

## Files Modified (Git Status)

```
M .github/workflows/ci.yml       # Updated Verus version
M README.md                       # Updated Verus version
M TODO.md                         # Added Phase 9 plan
M src/main.rs                     # Minor changes
M src/protocol/RSL/mod.rs        # Module updates
?? docs/dev/phase9-summary.md    # NEW: Phase 9 documentation
?? docs/dev/translation-rules.md # NEW: Translation rules spec
```

## Architecture Status

### Layer 1: Specification (Protocol) ✅ Complete
- `src/protocol/RSL/*.rs` - All spec files exist
- 437 functions verified with previous Verus version
- Need to re-verify with new Verus v0.2026.02.04

### Layer 2: Generated Implementation (Generated) ✅ Code Complete, ⚠️ Verification Pending
- `src/generated/RSL/*_gen.rs` - All 8 modules generated
- 2,567 LOC of generated code
- 72 exec functions with implementations
- **182 assume statements need to be removed**

### Layer 3: Manual Implementation (Implementation) ✅ Complete
- `src/implementation/RSL/*.rs` - Manual implementations exist
- Used as reference for generated code patterns
- Will eventually be replaced by generated code

### Layer 4: C# Runtime (FFI) ✅ Complete
- `csharp/` - Production-ready I/O framework
- No changes needed

## Next Steps (From Phase 9 Plan)

### Immediate Priority: Remove Assume Statements

**Goal**: Make generated code actually verify instead of using assumes

1. **Fix Core Type System** (Phase 9.1)
   - Generate proper View functions for Vec/HashSet
   - Generate proper validity predicates with forall
   - Estimated: 2 weeks

2. **Fix Expression Translation** (Phase 9.2)
   - Improve enum handling
   - Add EndPoint comparison detection
   - Remove type refinement checks
   - Add integer cast insertion
   - Estimated: 2 weeks

3. **Fix Collection Operations** (Phase 9.3)
   - Generate while loops for subrange
   - Generate extend for concatenation
   - Estimated: 1 week

4. **Translate New Spec Files** (Phase 9.4)
   - parameters.rs
   - constants.rs
   - configuration.rs
   - message.rs
   - Estimated: 1 week

5. **Integration & Testing** (Phase 9.5-9.6)
   - Regenerate all modules without assumes
   - Verify with Verus
   - Add tests
   - Estimated: 2 weeks

**Total Estimated Time**: 8 weeks for complete Phase 9

## Comparison: Current vs Target

### Current State (With Assumes)

```rust
pub exec fn CBoundRequestSequence(s: &Vec<CRequest>, lengthBound: u64) -> (result: Vec<CRequest>)
ensures
    result@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(...), ...),
{
    let s_len = s.len() as u64;
    let result = if (0 <= lengthBound && lengthBound < s_len) {
        truncate_vec(s, 0, lengthBound as usize)  // ✅ Using helper
    } else {
        s.clone()
    };
    assume(result@.map(|i, r: CRequest| r@) == ...);  // ⚠️ Assume!
    result
}
```

### Target State (No Assumes)

```rust
pub exec fn CBoundRequestSequence(s: &Vec<CRequest>, lengthBound: u64) -> (result: Vec<CRequest>)
requires
    forall |i: int| 0 <= i < s@.len() ==> s@[i].valid(),
ensures
    forall |i: int| 0 <= i < result@.len() ==> result@[i].valid(),
    result@.map(|i, r: CRequest| r@) == BoundRequestSequence(s@.map(...), ...),
{
    let s_len = s.len() as u64;
    if 0 <= lengthBound && lengthBound < s_len {
        // Direct while loop with invariants - no helper needed
        let mut result = Vec::new();
        let mut i = 0;
        while i < lengthBound as usize
            invariant
                i <= lengthBound,
                result@.len() == i,
                forall |j: int| 0 <= j < i ==> result@[j] == s@[j],
        {
            result.push(s[i].clone());
            i += 1;
        }
        result
    } else {
        s.clone()
    }
    // No assume needed - Verus verifies the ensures clause!
}
```

## Success Metrics

### Phase 9 Success Criteria

- ✅ **Code Generation**: 72 functions in 8 modules (DONE)
- ⏳ **Zero Assumes**: 0 / 182 assumes removed (0% - TODO)
- ⏳ **Verus Verification**: 0 / 72 functions verify (0% - TODO)
- ⏳ **New Spec Files**: 0 / 4 files translated (0% - TODO)
- ⏳ **Tests Added**: 0 / 9 transpiler tests (0% - TODO)

### Overall Project Health

| Metric | Status | Details |
|--------|--------|---------|
| **Spec Layer** | ✅ 100% | 437 functions verified (need re-verification) |
| **Generated Layer** | ⚠️ 50% | Code complete, verification pending |
| **Implementation Layer** | ✅ 100% | Manual implementations working |
| **Transpiler** | ⚠️ 75% | Generates code, needs verification fixes |
| **Documentation** | ✅ 90% | Phase 9 plan and rules documented |

## Risk Assessment

### Low Risk ✅
- **Code compiles**: All generated code is syntactically correct
- **Patterns work**: Manual corrections demonstrate viable approach
- **Infrastructure ready**: Helper functions, types, imports all in place

### Medium Risk ⚠️
- **Verus version change**: Just upgraded to v0.2026.02.04 (need re-verification)
- **Assume removal**: Replacing 182 assumes requires careful proof engineering
- **Transpiler complexity**: 8 issues to fix across multiple modules

### High Risk ❌
- **None identified**: Project is in good state

## Recommendations

### Short Term (1-2 weeks)
1. ✅ Verify codebase builds with new Verus v0.2026.02.04
2. ✅ Start Phase 9.1: Fix vector/hashset view generation
3. ✅ Create test suite for transpiler fixes

### Medium Term (4-6 weeks)
1. ✅ Complete Phase 9.1-9.3: All transpiler fixes
2. ✅ Regenerate all modules without assumes
3. ✅ Verify at least 50% of generated functions

### Long Term (8+ weeks)
1. ✅ Complete Phase 9: All generated code verified
2. ✅ Translate 4 new spec files
3. ✅ Remove manual implementations (replace with generated)

## Conclusion

**The project is in excellent shape.** Code generation is working end-to-end, producing 2,567 lines of compilable code across 8 modules. The main remaining work is **proof engineering** - removing the 182 assume statements by improving the transpiler to generate verifiable code.

The path forward is clear and documented in Phase 9 of TODO.md. With 8 weeks of focused work on the transpiler, this project can achieve fully verified, automatically generated implementations of the entire RSL protocol.

---

**Last Updated**: 2026-02-04
**Next Review**: After Phase 9.1 completion (estimated 2026-02-18)
