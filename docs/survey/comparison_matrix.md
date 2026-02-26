# Comparison Matrix

## Introduction

This matrix compares all surveyed works (direct + adjacent) across standardized dimensions to enable quick comparison and identify gaps. Works are ordered by directness to the text→TLA+ problem, then by year.

The matrix includes 16 entries covering the most relevant papers and tools from the survey. A machine-readable CSV version is available at `artifacts/comparison_matrix.csv`.

## Comparison Table

| Name | Type | Year | Task Solved | Directness | Input | Output | Check? | Method | Eval Style | Faithfulness | OSS? | Artifact | License | Strengths | Limitations | Reuse | Conf |
|------|------|------|-------------|------------|-------|--------|--------|--------|------------|-------------|------|----------|---------|-----------|-------------|-------|------|
| Specula | tool | 2025 | code→TLA+ | direct | Source code (Go/Rust) | TLA+ specs | Yes (trace validation) | LLM + CFA + trace | Trace conformance on 2 systems | Trace validation | Yes | Working tool | Open | First code→TLA+ tool; trace validation | Code input only, not NL | Code→TLA+ component | High |
| SysMoBench | benchmark | 2025 | TLA+ modeling eval | direct | System artifacts | TLA+ (evaluated) | Yes (automated metrics) | Benchmark | Syntax/runtime/conformance/invariant | Automated metrics | Yes | Public benchmark | Open | Automated TLA+ evaluation; real systems | Evaluates, doesn't generate | Evaluation metrics | High |
| TLAiBench | benchmark | 2025 | LLM TLA+ eval | direct | Task descriptions | TLA+ (expected) | Yes | Benchmark | Standardized | Varied | Yes | Public repo | Open | TLA+-specific AI benchmark | Benchmark only | Evaluation benchmark | High |
| TLA+ Proof Auto | paper | 2024 | TLA+ proofs | direct | TLA+ claims | TLA+ proofs | Yes | LLM recursive decomp | Decomposition verified | Each step verified | Partial | arXiv paper | Unknown | Demonstrates LLM TLA+ understanding | Proofs not specs | TLA+ LLM capability evidence | Med |
| SYNTHTL | paper | 2024 | NL→LTL/CTL | adjacent | Natural language | LTL/CTL formulas | Yes (model checker) | LLM + model checker + oracle | Model checker validation | Model checker + oracle | Partial | FMCAD paper | Unknown | Decomposition + model checker loop | Oracle needed; LTL not TLA+ | Architecture pattern | High |
| Req2LTL/OnionL | paper | 2025 | NL→LTL | adjacent | NL requirements | LTL formulas | Yes (100% syntactic) | LLM + OnionL IR + rules | 88.4% semantic accuracy | Rule-based synthesis | Partial | arXiv paper | Unknown | Hierarchical IR; near-perfect syntax | LTL simpler than TLA+ | IR design pattern | High |
| AutoSpec | paper | 2025 | NL RFC→protocol spec | adjacent | RFC text (NL) | I/O grammars | Yes (fuzzer tested) | Two-stage LLM | 92.8% msg type recovery | Traceability preserved | Partial | arXiv paper | Unknown | NL→spec pipeline; traceability | I/O grammars not TLA+ | Two-stage pipeline | High |
| SpecGen | paper | 2025 | Program spec gen | adjacent | Programs | Pre/postconditions | Yes (verifier) | LLM + verifier loop + mutation | 279/385 verified | Verifier feedback loop | Yes | ICSE paper | Unknown | Verifier-in-the-loop; outperforms classical | Function-level not system-level | Verifier loop pattern | High |
| nl2spec | paper | 2023 | NL→temporal logic | adjacent | Unstructured NL | Temporal logic | Partial | LLM subformula decomp | 36 expert benchmarks | Subformula traceability | Partial | CAV paper | Unknown | Traceability methodology; expert benchmark | Small benchmark; interactive | Traceability method | Med |
| NL2LTL | tool | 2023 | NL→LTL | adjacent | NL instructions | LTL formulas | Yes | NLU + LLM | AAAI demo | Automated | Yes | Python package | Open | Open-source; mature package | Robot domain narrow | Package architecture | Med |
| LLM Alloy Gen | paper | 2025 | NL→Alloy | adjacent | NL descriptions | Alloy formulas | Yes (Alloy checker) | Direct LLM | Multiple solutions | Alloy checker | Partial | arXiv paper | Unknown | Shows LLM can handle formal DSLs | Alloy simpler than TLA+ | DSL generation evidence | Med |
| LLM Alloy Repair | paper | 2024 | Alloy spec repair | adjacent | Defective Alloy specs | Repaired specs | Yes (Alloy checker) | Dual-agent + auto-prompt | 106K attempts on 1974 models | Alloy checker | Yes | arXiv + Springer | Unknown | Best repair architecture found | Alloy-specific | Dual-agent repair pattern | High |
| GCD for Logic | paper | 2025 | Grammar-constrained LLM | adjacent | Prompts | Logical formulas | Yes (grammar) | Constrained decoding | Syntax+semantic accuracy | Grammar enforcement | Partial | ACL paper | Unknown | Syntax guarantee; semantic improvement | Grammar-level only | GCD for TLA+ syntax | Med |
| DafnyBench | benchmark | 2024 | Dafny verification | far-adjacent | Dafny programs | Annotations | Yes (Dafny verifier) | Benchmark | 68%→96% over 1 year | Dafny verifier | Yes | Public benchmark | Open | Rapid LLM improvement evidence | Dafny not TLA+ | Benchmark methodology | Med |
| Symboleo NL→spec | paper | 2024 | NL→Symboleo | adjacent | Legal contract text | Symboleo specs | Partial (49% syntax) | LLM + grammar guidance | 38 prompt combos | Manual review | Partial | arXiv paper | Unknown | NL→DSL feasibility evidence | 49% grammar adherence | DSL challenges evidence | Med |
| 4/δ Bound | paper | 2025 | LLM-verifier theory | far-adjacent | Theoretical | Convergence guarantees | N/A | Mathematical framework | Formal proofs | N/A | Partial | arXiv paper | Unknown | First convergence guarantees | Theory only | Architecture design basis | Med |

## Synthesis

### What Is Already Solved Well

1. **NL → temporal logic (LTL/CTL/STL)**: Multiple mature systems with good accuracy (88-93%). Well-defined problem with benchmark datasets.
2. **Grammar-constrained decoding**: Reliable syntax enforcement for formal languages. Demonstrated for TLA+ in TLAi Challenge.
3. **Verifier-in-the-loop patterns**: Well-established for Dafny, Alloy, and Coq. Clear evidence that verification feedback dramatically improves LLM output quality.
4. **TLA+ tooling ecosystem**: Parsers (SANY, tree-sitter-tlaplus), model checkers (TLC, Apalache with JSON-RPC API), benchmarks (TLAiBench, SysMoBench) are all available and active.

### What Is Partially Solved

1. **Code → TLA+ generation**: Specula demonstrates feasibility but only from code, not NL.
2. **NL → rich formal specifications** (beyond temporal logic): Works for Alloy (simpler than TLA+) and Symboleo (domain-specific), but not for general-purpose specification languages with TLA+'s expressiveness.
3. **LLM understanding of TLA+ semantics**: Proof automation paper shows some capability, but LLMs still fail at basic TLA+ syntax generation (Shan 2024 negative result).

### What Appears Unsolved

1. **End-to-end NL → machine-checkable TLA+ specification generation**: No published system.
2. **Evaluation of generated TLA+ against source text**: SysMoBench evaluates code→TLA+, but no framework evaluates NL→TLA+ faithfulness.
3. **LLM fine-tuning or specialization for TLA+**: Insufficient training data in TLA+. No published fine-tuned model.
4. **Automatic invariant/property extraction from NL**: Can extract temporal logic properties (LTL/CTL) but not TLA+-specific invariant forms.

### Gaps Unique to Text → TLA+

1. **State machine structure extraction**: TLA+ requires explicit state variables, initialization, and next-state relations — not just temporal properties. No NL→LTL tool handles this.
2. **Action decomposition**: TLA+ specs decompose system behavior into named actions with guards and updates. This structural decomposition from NL is unique to TLA+.
3. **Type/constant/variable declarations**: TLA+ modules have rich declaration structure that must be synthesized from NL descriptions.
4. **Integration with downstream pipeline**: Generated TLA+ must be compatible with the repository's existing TLA+→Verus spec→verified Rust workflow, adding structural constraints beyond standard TLA+.

## Decision Lenses

### Best Near-Term Building Blocks

1. **Two-stage pipeline architecture** (from AutoSpec + OnionL): NL → intermediate representation → TLA+ emitter. Use LLMs for semantic extraction, deterministic rules for TLA+ emission.
2. **Grammar-constrained decoding** (from GCD + TLAi Challenge): Use tree-sitter-tlaplus grammar to enforce syntax validity during generation.
3. **TLC/Apalache verification loop** (from SpecGen + SYNTHTL): Generate candidate TLA+ → model check → feed errors back to LLM → iterate.
4. **tlaplus/Examples + TLAiBench for few-shot retrieval**: Use existing TLA+ specs as RAG retrieval corpus for in-context learning.

### High-Risk Research Bets

1. **Direct NL → TLA+ generation without intermediate representation**: LLMs currently fail at TLA+ syntax (Shan 2024). May improve with scale but high risk.
2. **Fine-tuning on TLA+ corpus**: Small corpus (hundreds of specs, not thousands). May not be enough for reliable fine-tuning.
3. **Fully automated pipeline without human review**: Given current accuracy levels (49-93% depending on formalism), fully automated generation is premature for safety-critical specs.

### Likely Dead Ends / Low ROI Options

1. **Pure template-based generation**: Too rigid for diverse protocol descriptions. Templates can't capture the breadth of TLA+ specs.
2. **Training a TLA+-specific LLM from scratch**: Insufficient data. Better to leverage general LLMs with constrained decoding + retrieval.
3. **Ignoring syntax enforcement**: Direct prompting without grammar constraints fails for TLA+ (demonstrated). Not worth pursuing.
