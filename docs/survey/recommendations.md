# Recommendations

## Overview

Based on the survey findings, this section proposes concrete architecture options for a future text→TLA+ front-end, assessed for strengths, risks, and compatibility with the existing downstream TLA+ pipeline. These are documentation-only recommendations; implementation is deferred to a future phase.

---

## Option A: LLM-First Direct Generation + Checker/Repair Loop

### Architecture

```
Source Text → LLM (with TLA+ grammar constraint) → Candidate TLA+ → SANY check → TLC/Apalache check → Error feedback → LLM repair → ... → Validated TLA+
```

### Components
- **LLM**: General-purpose (GPT-4o, Claude, etc.) with TLA+ documentation in context
- **Grammar enforcement**: tree-sitter-tlaplus grammar via constrained decoding (GBNF/Guidance) or post-hoc SANY validation
- **Verification loop**: TLC or Apalache for model checking, with error messages fed back to LLM
- **Few-shot retrieval**: tlaplus/Examples as RAG corpus for similar specs

### Strengths
- Simplest architecture. Minimal custom engineering.
- Leverages existing LLM capabilities for pattern translation.
- Grammar-constrained decoding ensures syntactic validity (demonstrated in TLAi Challenge).
- Verification loop is well-established pattern (SpecGen, SYNTHTL, Alloy repair all demonstrate effectiveness).

### Risks
- **HIGH**: LLMs currently fail at TLA+ syntax without constraints (Shan 2024). Even with grammar constraints, semantic quality is unproven.
- **MEDIUM**: Verification loop may not converge for complex specs (4/delta bound applies but practical convergence unknown for TLA+).
- **MEDIUM**: Requirement coverage difficult to guarantee — LLM may silently drop requirements.

### Evaluation Strategy
- D1 (syntax) guaranteed by grammar constraints
- D2 (model-check) enforced by verification loop
- D3-D7 require human review (traceability matrix, scenario checks)

### Engineering Effort
- LOW-MEDIUM: Mostly prompt engineering + integration of existing tools
- Prototype in days, production quality in weeks-months

### Downstream Compatibility
- Generated TLA+ must match the structural conventions expected by the transpiler (state variables, action decomposition, etc.)
- May need post-processing to conform to specific module structure requirements

---

## Option B: Text → Structured IR → Deterministic TLA+ Emitter

### Architecture

```
Source Text → LLM (semantic extraction) → Structured IR (protocol elements) → Deterministic TLA+ Emitter → TLA+ Module → SANY/TLC validation
```

### Components
- **LLM stage**: Extract protocol elements from text: state variables, message types, actions (guards + updates), invariants, constants
- **Intermediate representation**: JSON/YAML schema describing protocol structure (inspired by OnionL for LTL, AutoSpec for I/O grammars)
- **Deterministic emitter**: Template-based or rule-based TLA+ code generator from IR
- **Validation**: SANY + TLC on generated output

### Strengths
- **Separation of concerns**: LLM handles NL understanding; emitter handles TLA+ syntax. No LLM syntax errors.
- **100% syntactic correctness**: Emitter is deterministic, template-based. Guaranteed to produce valid TLA+.
- **Traceability**: IR preserves mapping from text elements to spec elements.
- **Reproducibility**: Same IR always produces same TLA+. No LLM nondeterminism in final output.
- Aligns with strongest adjacent work (OnionL achieves 88.4% semantic + 100% syntactic; AutoSpec achieves 92.8% element recovery).

### Risks
- **MEDIUM**: IR design is the critical challenge — must be expressive enough for diverse protocols but structured enough for deterministic emission.
- **LOW-MEDIUM**: LLM semantic extraction quality determines overall quality. But errors are inspectable in the IR.
- **LOW**: Template coverage — may need many templates for diverse protocol patterns.

### Evaluation Strategy
- D1 guaranteed by deterministic emitter
- D3 directly measurable from IR (check which text elements are extracted)
- D4-D5 assessable at IR level (inspect extracted elements before TLA+ generation)
- Human effort focused on IR validation, not TLA+ review

### Engineering Effort
- MEDIUM: IR schema design + emitter + LLM integration
- Prototype in weeks, production quality in months

### Downstream Compatibility
- **BEST**: Deterministic emitter can be designed to produce TLA+ in exactly the structure the transpiler expects.
- IR can be extended to emit transpiler-compatible annotations or TOML configs.

---

## Option C: Human-in-the-Loop Template-Driven Extraction + Assisted Completion

### Architecture

```
Source Text → LLM (candidate extraction) → Human Review/Edit → Template Selection → TLA+ Scaffolding → Human Completion → SANY/TLC validation
```

### Components
- **LLM pre-processing**: Extract candidate state variables, message types, actions from text
- **Human review**: Domain expert reviews and corrects extracted elements
- **Template library**: Predefined TLA+ module templates for common protocol patterns (consensus, leader election, replication, etc.)
- **Assisted completion**: LLM suggests action bodies, guards, invariants for human to accept/reject/modify
- **Validation**: SANY + TLC

### Strengths
- **Highest quality**: Human-in-the-loop catches all failure types (F1-F8)
- **Lowest risk**: No fully automated generation — human validates every element
- **Practical today**: Can be implemented immediately with existing LLMs + templates

### Risks
- **HIGH human effort**: Not scalable for large numbers of specs.
- **LOW automation**: Defeats the purpose if human does most of the work.
- **MEDIUM**: Template library may not cover all protocol patterns.

### Evaluation Strategy
- Human review inherently covers D3-D7
- D1, D2 validated by SANY/TLC
- Evaluation rubric serves as reviewer checklist

### Engineering Effort
- LOW: Template library + LLM prompt engineering
- Prototype in days

### Downstream Compatibility
- GOOD: Templates can be designed for transpiler compatibility
- Human ensures structural correctness

---

## Comparison of Options

| Dimension | Option A (Direct LLM) | Option B (IR + Emitter) | Option C (Human-in-Loop) |
|-----------|----------------------|------------------------|-------------------------|
| Automation | High | High | Low |
| Syntax correctness | Medium-High (with GCD) | Guaranteed | Guaranteed |
| Semantic quality | Low-Medium | Medium-High | High |
| Traceability | Low | High | High |
| Scalability | High | High | Low |
| Engineering effort | Low-Medium | Medium | Low |
| Downstream compatibility | Medium | Best | Good |
| Risk level | High | Medium | Low |

### Recommended Approach

**Option B (Structured IR + Deterministic Emitter)** is the recommended starting point, because:
1. It separates the hard problem (NL understanding) from the mechanical problem (TLA+ syntax), playing to LLM strengths
2. It guarantees syntactic correctness by construction
3. The IR is inspectable, traceable, and version-controllable
4. It aligns with the strongest patterns from adjacent work (OnionL, AutoSpec)
5. It has the best downstream compatibility with the transpiler

Option A can serve as a **rapid prototyping baseline** for comparison. Option C is the **fallback** if automated approaches prove insufficient.

---

## Text-First, PDF-Later Note

### Current Phase: Text-First
This survey and these recommendations assume the input is plain text (protocol descriptions, RFC excerpts, design documents as text). This is the right starting point because:
1. NL understanding is the core challenge — PDF parsing is a solved-ish preprocessing step
2. Text-first allows focused evaluation of semantic quality without layout/OCR noise
3. All surveyed adjacent work uses text input

### What Changes with PDF Support
When extending to PDF input in a future phase:
- **Preprocessing candidates**: PyMuPDF, pdfplumber, marker (for academic papers), nougat (for equations/formulas)
- **Layout challenges**: Multi-column layouts, figures/diagrams, tables, mathematical notation
- **Text extraction quality**: OCR errors can propagate through the pipeline
- **Additional evaluation dimension**: Faithfulness to the original PDF (not just extracted text)

### Why PDF Is Deferred
PDF parsing is deferred because:
1. It adds preprocessing complexity without affecting the core NL→TLA+ problem
2. Text extraction quality varies widely by PDF source
3. The evaluation framework should be validated on clean text first

---

## Recommended Next Step After Survey

**Documentation-only recommendation (not execution):**

Create a minimal pilot benchmark and evaluation harness:

1. **Select 3 protocol descriptions** from the repository's existing protocols (e.g., Two-Phase Commit, Raft leader election, Paxos single-decree) — use the original paper descriptions as source text
2. **Validate reference TLA+ specs** against these descriptions using the evaluation rubric (D1-D8)
3. **Implement Option B prototype**: Design a minimal IR schema for these 3 protocols, build a template-based emitter
4. **Baseline Option A**: Run GPT-4o / Claude with grammar-constrained decoding on the same 3 descriptions
5. **Compare**: Measure D1-D8 scores for both options
6. **Publish evaluation results** as the first data point for text→TLA+ generation quality

This pilot would require ~2-4 weeks of effort and would produce:
- A reusable evaluation harness
- First quantitative data on text→TLA+ generation quality
- A validated IR schema design for Option B
- Evidence for whether automated generation is viable at acceptable quality levels
