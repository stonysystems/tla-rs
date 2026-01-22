# IDE Support / LSP Integration Plan

## Overview

This plan outlines the implementation of IDE support for the Verus transpiler, focusing on LSP (Language Server Protocol) integration.

## Scope Analysis

### Full LSP Implementation
A complete LSP server would involve:
- textDocument/definition - Jump to definition
- textDocument/hover - Hover information
- textDocument/diagnostic - Real-time error reporting
- textDocument/completion - Code completion
- textDocument/references - Find all references

**Estimated LOC**: 2000+ lines
**Complexity**: High
**External Dependencies**: tower-lsp or lsp-server crate

### Minimal Viable LSP
A basic LSP server providing just diagnostics:
- Parse spec files on save
- Report validation errors with source locations
- Link to generated code locations

**Estimated LOC**: ~500 lines
**Complexity**: Medium

### Alternative: Editor Plugin Without LSP
- VS Code extension using CLI tool
- Run transpiler on save
- Show output in problems panel

**Estimated LOC**: ~200 lines
**Complexity**: Low

## Recommendation

Given the current state of the project (Milestone 5 complete, blocking on Verus integration), the IDE support task should be:

1. **Deferred** until Verus integration testing is complete (Milestone 4)
2. When implemented, start with **minimal VS Code extension** that:
   - Runs `verus-transpile check` on save
   - Displays errors in the Problems panel
   - Uses JSON output from CLI for structured errors

## Breakdown (if implementing now)

### Phase 1: CLI Diagnostics Output (~100 LOC)
- Add `--output-format json` flag to CLI
- Output structured diagnostic JSON with source spans
- Include severity (error/warning/info)

### Phase 2: VS Code Extension (~200 LOC)
- Create basic VS Code extension
- Watch .rs and .automan files
- Run CLI check command
- Parse JSON output and create diagnostics

### Phase 3: Enhanced Features (Future)
- Hover information
- Go to definition
- Code actions (quick fixes)

## Current Status

**Recommendation**: Mark this task as "deferred pending Verus integration" since:
1. Full value comes from integration with Verus verifier
2. Current infrastructure is sufficient for CLI usage
3. Limited resources better spent on Verus integration testing

## Files to Create (if implementing Phase 1-2)

```
transpiler/
├── src/
│   └── cli/
│       └── diagnostics.rs  # JSON diagnostic output
└── vscode-extension/       # VS Code extension (separate package)
    ├── package.json
    ├── src/
    │   └── extension.ts
    └── tsconfig.json
```
