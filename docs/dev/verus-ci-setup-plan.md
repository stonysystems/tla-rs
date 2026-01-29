# Verus CI Setup Plan

## Status: COMPLETE [26:01:29]

## Goal
Add Verus verification to the CI pipeline to verify generated code.

## Current State
- CI currently only tests the transpiler (Rust tests, clippy, fmt)
- Generated code in `src/generated/RSL/` is guarded by `#[cfg(test)]`
- Full codebase verifies locally with Verus: 437+ verified, 0 errors

## Requirements

### Verus Installation
Based on [Verus INSTALL.md](https://github.com/verus-lang/verus/blob/main/INSTALL.md):
- Pre-built binaries available for Ubuntu 22.04 (x86_64)
- Requires specific Rust toolchain (currently 1.86.0)
- Rolling releases track main branch

### Dependencies
- `scons` for build system
- Verus binary from GitHub releases
- Correct Rust toolchain version

## Implementation Plan

### Step 1: Add Verus Installation Job (~40 LOC)
Add a new job `verify` that:
1. Downloads Verus binary from releases
2. Installs required Rust toolchain
3. Runs Verus verification

### Step 2: Cache Verus Binary
Cache the Verus installation to speed up subsequent runs.

### Step 3: Run Verification
Run `scons --verus-path=/path/to/verus` to verify the codebase.

## Proposed CI Workflow Addition

```yaml
  verify:
    name: Verus Verification
    runs-on: ubuntu-22.04
    steps:
      - uses: actions/checkout@v4

      - name: Install Python and scons
        run: |
          sudo apt-get update
          sudo apt-get install -y python3-pip
          pip3 install scons

      - name: Cache Verus
        id: cache-verus
        uses: actions/cache@v4
        with:
          path: ~/verus
          key: verus-ubuntu-22.04-rolling

      - name: Download Verus
        if: steps.cache-verus.outputs.cache-hit != 'true'
        run: |
          VERUS_RELEASE="rolling"
          wget https://github.com/verus-lang/verus/releases/download/${VERUS_RELEASE}/verus-x86_64-unknown-linux-gnu.zip
          unzip verus-x86_64-unknown-linux-gnu.zip -d ~/
          mv ~/verus-x86_64-unknown-linux-gnu ~/verus

      - name: Install Rust toolchain for Verus
        run: |
          # Get required toolchain version from Verus
          TOOLCHAIN=$(~/verus/verus --version 2>&1 | grep -oP 'toolchain \K[\d.]+' || echo "1.86.0")
          rustup install ${TOOLCHAIN}-x86_64-unknown-linux-gnu
          rustup default ${TOOLCHAIN}-x86_64-unknown-linux-gnu

      - name: Verify with Verus
        run: |
          scons --verus-path=$HOME/verus
```

## Considerations

### CI Time
- Verus verification may take significant time (10+ minutes)
- Consider running on schedule (nightly) rather than every PR

### Caching Strategy
- Cache Verus binary (stable across builds)
- Cache vstd build artifacts if possible

### Failure Handling
- Verification failures should block merges
- Clear error messages for verification failures

## Next Steps
1. Create the workflow file update
2. Test locally with act or similar
3. Push and verify CI runs

## References
- [Verus GitHub](https://github.com/verus-lang/verus)
- [Verus Releases](https://github.com/verus-lang/verus/releases)
- [Verus Installation Guide](https://github.com/verus-lang/verus/blob/main/INSTALL.md)
