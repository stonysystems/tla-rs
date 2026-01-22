# Performance Optimization Plan

## Goal
Add benchmarking infrastructure and optimize critical paths in the transpiler.

## Components

### 1. Benchmarking Infrastructure
- Add `criterion` dev-dependency for benchmarking
- Create benchmark suite in `transpiler/benches/`
- Benchmarks:
  - Parser performance on various spec sizes
  - Template matching performance
  - Code generation performance
  - Full transpilation pipeline

### 2. Potential Optimization Areas
Based on code review:
- **String allocation**: Many `.to_string()` calls could use `Cow<str>` or string interning
- **HashMap lookups**: Consider using `FxHashMap` for smaller keys
- **Clone operations**: Review clone patterns in AST traversal
- **Regex compilation**: Cache compiled patterns if any

### 3. Implementation Steps
1. Add criterion to Cargo.toml
2. Create `benches/transpiler_benchmarks.rs`
3. Add basic benchmarks for parser, matcher, generator
4. Run benchmarks to establish baseline
5. Profile with `cargo flamegraph` if needed
6. Implement targeted optimizations

### 4. Success Criteria
- Benchmarks show measurable baseline
- Any optimizations maintain all test passing
- Document any significant improvements
