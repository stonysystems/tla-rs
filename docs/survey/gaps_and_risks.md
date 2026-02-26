# Gaps and Risks

## Overview

This document catalogs known unknowns, blockers, and risks identified during the survey, along with proposed mitigations.

---

## Known Gaps

### G1: No NL→TLA+ Training Data

- **Gap**: No large-scale dataset of (natural language description, TLA+ specification) pairs exists. TLAiBench and SysMoBench provide evaluation benchmarks but not training data in the supervised learning sense.
- **Impact**: Fine-tuning LLMs for TLA+ is impractical. Must rely on few-shot learning, prompt engineering, and constrained decoding.
- **Mitigation**: Use existing TLA+ specs (tlaplus/Examples, community specs) + their paper descriptions as weak supervision. Build a small hand-curated dataset as part of the pilot benchmark.

### G2: LLMs Fail at TLA+ Syntax

- **Gap**: Open-source LLMs cannot produce SANY-parsable TLA+ (Shan 2024). Commercial models are better but not reliable.
- **Impact**: Direct LLM→TLA+ generation has a high syntax error rate.
- **Mitigation**: Grammar-constrained decoding (demonstrated in TLAi Challenge). OR: Generate via structured IR + deterministic emitter (Option B).

### G3: No Faithfulness Evaluation Framework for TLA+

- **Gap**: No published methodology specifically evaluates whether generated TLA+ matches source NL text. SysMoBench evaluates code→TLA+ conformance but not text→TLA+.
- **Impact**: Cannot objectively measure system quality.
- **Mitigation**: Proposed evaluation rubric (D1-D8) in this survey. Needs validation through pilot benchmark.

### G4: State Machine Structure Extraction is Uncharted

- **Gap**: NL→LTL/CTL work extracts temporal properties. But TLA+ requires extracting state variables, initialization, next-state relations, and action decomposition — a structurally richer extraction task with no published solutions.
- **Impact**: The hardest technical challenge in text→TLA+.
- **Mitigation**: Two-stage approach (Option B): Extract protocol elements into structured IR first, then emit TLA+. Leverage AutoSpec's element extraction approach.

### G5: Downstream Pipeline Structural Requirements

- **Gap**: Generated TLA+ must conform to specific structural conventions to work with the repository's TLA+→Verus spec→verified Rust pipeline. No surveyed work considers this constraint.
- **Impact**: Even "correct" TLA+ may be incompatible with downstream tools.
- **Mitigation**: Deterministic emitter (Option B) can be designed to produce pipeline-compatible output. Add D8 (downstream compatibility) to evaluation.

---

## Known Risks

### R1: Partial Correctness Is Worse Than No Spec

- **Risk**: A generated spec that captures 90% of requirements creates false confidence. The missing 10% may be the safety-critical parts.
- **Likelihood**: HIGH (current LLM accuracy on formal specs is 49-93% depending on formalism)
- **Impact**: HIGH (downstream verified Rust would be "verified against a wrong spec")
- **Mitigation**: Mandatory human review of traceability matrix (M1). Fail-gate at <80% requirement coverage.

### R2: Silent Hallucinations in Generated TLA+

- **Risk**: LLM adds constraints or behaviors not in the source text. These are hard to detect because they look reasonable.
- **Likelihood**: MEDIUM-HIGH (demonstrated across all NL→formal-spec work)
- **Impact**: MEDIUM (spec is "more restrictive" or "more permissive" than intended)
- **Mitigation**: Precision evaluation (D5). Round-trip summarization (M4). Mutation testing (M7).

### R3: Evaluation Bottleneck

- **Risk**: Human review effort (30-60 minutes per spec) limits throughput. If generating specs is fast but evaluation is slow, the bottleneck shifts to evaluation.
- **Likelihood**: HIGH
- **Impact**: MEDIUM (limits practical scalability)
- **Mitigation**: Invest in automated evaluation (M5 differential comparison, M6 model-checking, M7 mutation testing). Reduce human-in-the-loop to spot-checking.

### R4: TLA+ Complexity Ceiling

- **Risk**: Simple protocols (Two-Phase Commit) may be tractable, but complex protocols (Multi-Paxos, EPaxos) may be beyond current LLM capabilities regardless of architecture.
- **Likelihood**: MEDIUM
- **Impact**: HIGH (limits practical applicability)
- **Mitigation**: Start with simple protocols. Measure complexity scaling. Use human-assisted completion (Option C) for complex protocols.

### R5: Grammar-Constrained Decoding Quality Degradation

- **Risk**: GCD enforces syntax but may degrade semantic quality. The LLM's conditional distribution may shift under grammar constraints.
- **Likelihood**: LOW-MEDIUM (Grammar-Aligned Decoding paper shows this can be controlled)
- **Impact**: MEDIUM
- **Mitigation**: Use Grammar-Aligned Decoding approach. Evaluate both constrained and unconstrained generation quality.

---

## Blockers

### B1: No Existing NL→TLA+ System to Compare Against

- **Status**: No baseline system exists. All quality measurements will be absolute, not relative.
- **Impact**: Hard to claim "improvement" without a baseline.
- **Mitigation**: Use Option A (direct LLM generation) as the baseline. Compare Option B against it.

### B2: IR Schema Design

- **Status**: No published IR schema for TLA+-style specifications from NL. OnionL is for LTL only.
- **Impact**: Core engineering challenge for Option B.
- **Mitigation**: Start with a minimal schema covering 3 simple protocols. Iterate based on pilot results.

### B3: Evaluation Rubric Validation

- **Status**: The proposed rubric (D1-D8) is untested. Needs inter-rater reliability assessment.
- **Impact**: Evaluation results may be inconsistent across reviewers.
- **Mitigation**: Pilot benchmark with 2+ reviewers on same specs. Measure agreement.
