# Migration Guide: Manual to Transpiled Implementations

This guide helps you migrate manually written Verus exec functions to transpiler-generated code.

## Overview

The transpiler converts TLA-style spec predicates into verified exec functions. If you have existing manual implementations, you can gradually migrate to transpiler-generated code.

## Step 1: Analyze Existing Code

### Identify Spec-Exec Pairs

Look for patterns like:
```rust
// Spec predicate
spec fn LAcceptorProcess1a(s: LAcceptor, s_: LAcceptor, inp: RslPacket, out: Seq<RslPacket>) -> bool {
    // ...spec body...
}

// Manual exec implementation
exec fn CAcceptorProcess1a(s: &CAcceptor, inp: &CRslPacket) -> (CAcceptor, Vec<CRslPacket>) {
    // ...impl body...
}
```

### Check for Verification Linkage

Verify that exec functions have ensures clauses linking to specs:
```rust
ensures
    LAcceptorProcess1a(s@, result.0@, inp@, result.1@),
```

## Step 2: Create Annotation Files

### Map Parameters to Modes

Analyze the spec function signature:
- Parameters passed by reference in exec → Input (`+`)
- Parameters returned by exec → Output (`-`)

Create `.automan` file:
```
# RSL/acceptor.automan
module RSL::Acceptor {
    # LAcceptorProcess1a(s, s_, inp, sent_packets)
    # s: input (current state)
    # s_: output (new state)
    # inp: input (incoming packet)
    # sent_packets: output (packets to send)
    LAcceptorProcess1a(+, -, +, -);
}
```

## Step 3: Run Transpiler in Dry-Run Mode

Test that the transpiler can process your spec:
```bash
verus-transpile --input src/protocol/acceptor.rs \
                --annotations src/protocol/acceptor.automan \
                --dry-run
```

Review the generated output and compare with your manual implementation.

## Step 4: Compare Generated vs Manual Code

### Common Differences

1. **Clone vs Borrow:**
   Manual code may use complex borrowing; generated code uses `.clone()` for safety.

2. **Iterator patterns:**
   Manual: `for i in 0..n { ... }`
   Generated: `(0..n).map(|i| ...).collect()`

3. **Error handling:**
   Generated code may have different panic/error patterns.

### Verify Semantic Equivalence

Both implementations should:
- Accept the same inputs
- Produce the same outputs (modulo representation)
- Satisfy the same spec predicate

## Step 5: Gradual Migration

### Option A: Replace Incrementally

1. Generate code for one function
2. Replace manual implementation
3. Run Verus to verify
4. Repeat for next function

### Option B: Parallel Implementations

1. Generate all code to a separate directory
2. Create test harness comparing outputs
3. Verify both pass the same specs
4. Switch over atomically

## Step 6: Update Build System

### Cargo Integration

Add to `build.rs`:
```rust
fn main() {
    let config = verus_transpiler::build_integration::BuildConfig::new(
        "src/protocol",
        "src/generated"
    );
    verus_transpiler::build_integration::run_build(&config).unwrap();
    verus_transpiler::build_integration::print_rerun_instructions(&config.input_dir);
}
```

### SCons Integration

Add to `SConstruct`:
```python
env.Transpile('src/generated', 'src/protocol')
```

## Common Migration Issues

### Issue 1: Custom Cloning

**Manual code:**
```rust
fn custom_clone(&self) -> Self {
    // special cloning logic
}
```

**Solution:** Implement `DeepClone` trait:
```rust
impl DeepClone for MyType {
    fn deep_clone(&self) -> Self {
        // your logic
    }
}
```

### Issue 2: Proof Annotations

**Manual code has proof blocks:**
```rust
proof {
    reveal_my_lemma();
    assert(condition);
}
```

**Solution:** Proof blocks must be added manually after generation. Consider:
- Adding a `// TODO: add proofs` comment
- Creating a wrapper function that adds proofs

### Issue 3: External Function Calls

**Manual code:**
```rust
let result = external_fn(args);
```

**Solution:** Mark external functions and provide trusted specs:
```rust
#[verifier(external)]
fn external_fn(args: T) -> R { ... }
```

### Issue 4: Invariant Assertions

**Manual code:**
```rust
assert(invariant_holds());
```

**Solution:** Add invariants to the spec's requires/ensures or add manually after generation.

## Verification Checklist

Before switching to generated code:

- [ ] Generated code compiles
- [ ] Verus verifies all functions
- [ ] Unit tests pass
- [ ] Integration tests pass
- [ ] Performance is acceptable
- [ ] Code review approved

## Rollback Plan

Keep manual implementations in a separate branch or directory until:
1. Generated code is verified by Verus
2. All tests pass
3. Production validation complete

## Example Migration

### Before (Manual)

```rust
// acceptor.rs
pub exec fn CAcceptorProcess1a(
    s: &CAcceptor,
    inp: &CRslPacket,
) -> (result: (CAcceptor, Vec<CRslPacket>))
    requires
        s.well_formed(),
        inp.well_formed(),
        inp.msg is CRslMessage1a,
    ensures
        result.0.well_formed(),
        LAcceptorProcess1a(s@, result.0@, inp@, result.1@),
{
    let bal = &inp.msg.get_bal_1a();
    if ballot_lt(&s.max_bal, bal) {
        let s_ = CAcceptor {
            max_bal: bal.clone(),
            votes: s.votes.clone(),
        };
        let packets = vec![make_1b_reply_impl(s, bal, &inp.src)];
        (s_, packets)
    } else {
        (s.clone(), vec![])
    }
}
```

### After (Transpiled)

```rust
// acceptor_gen.rs (auto-generated)
// DO NOT EDIT MANUALLY

verus! {
pub exec fn CAcceptorProcess1a(
    s: &CAcceptor,
    inp: &CRslPacket,
) -> (result: (CAcceptor, Vec<CRslPacket>))
    requires
        s.well_formed(),
        inp.well_formed(),
    ensures
        result.0.well_formed(),
        LAcceptorProcess1a(s@, result.0@, inp@, result.1@),
{
    let bal = &inp.msg.get_bal_1a();
    if ballot_lt(&s.max_bal, bal) {
        (CAcceptor {
            max_bal: bal.clone(),
            votes: s.votes.clone(),
        }, vec![make_1b_reply_impl(s, bal, &inp.src)])
    } else {
        (s.clone(), vec![])
    }
}
} // verus!
```

## Getting Help

- Check the [Limitations](LIMITATIONS.md) document
- Run `verus-transpile list-templates` for supported patterns
- Run `verus-transpile check --annotations file.automan` to validate annotations
- File issues at the project repository
