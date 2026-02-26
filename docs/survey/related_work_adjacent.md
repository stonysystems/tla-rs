# Adjacent Work: Building Blocks for Text → TLA+

## Overview

Since no direct text→TLA+ system exists, the strongest path forward combines techniques from adjacent research areas. This section surveys these areas as separate categories, identifying what transfers to TLA+ and what doesn't.

---

## Category 1: Natural Language → Temporal Logic (LTL/CTL/STL)

This is the closest adjacent area. TLA+ is based on temporal logic of actions, making NL→LTL/CTL work directly relevant.

### SYNTHTL (FMCAD 2024)
- **Task**: NL → LTL/CTL with model checker guidance
- **Method**: Decomposes NL→TL into sub-translation trees. LLM generates candidate sub-translations, model checker validates, oracle (human) resolves ambiguities.
- **Key insight**: Decomposition into composable sub-problems + model checker feedback catches errors early
- **Transferability to TLA+**: HIGH. The sub-translation tree approach could work for TLA+ actions. TLC/Apalache could serve as the model checker in the loop. TLA+ temporal formulas are more complex than LTL but the decomposition strategy transfers.
- **Limitations**: Requires an oracle for ambiguity resolution; not fully automated.

### Req2LTL with OnionL (arXiv, Dec 2025)
- **Task**: NL software requirements → LTL via hierarchical intermediate representation
- **Method**: OnionL is a tree-structured IR that decomposes requirements into scopes, relations, and atomic propositions. LLMs extract semantics into OnionL; deterministic rules translate OnionL→LTL.
- **Results**: 88.4% semantic accuracy, 100% syntactic correctness on aerospace requirements
- **Transferability to TLA+**: MEDIUM-HIGH. The "LLM extracts structure, rules emit formal output" pattern is very promising. Would need a TLA+-specific IR analogous to OnionL (e.g., decomposing protocol descriptions into state variables, actions, guards, updates).
- **Limitations**: LTL is simpler than TLA+ (no explicit state variables, data types). The IR would need to be significantly richer for TLA+.

### NL2CTL (Springer, 2024)
- **Task**: NL requirements → CTL formulas using LLMs
- **Method**: Direct LLM translation with CTL-specific prompting
- **Transferability to TLA+**: MEDIUM. CTL branching logic is closer to TLA+'s expressiveness than LTL, but still lacks state/action structure.

### nl2spec (CAV 2023)
- **Task**: Interactive NL → temporal logic with LLM subformula decomposition
- **Method**: LLM maps subformulas back to NL fragments for human validation
- **Key insight**: Subformula-level traceability between NL and formal spec
- **Transferability to TLA+**: HIGH for the traceability methodology. The approach of mapping each formal element back to its NL source is directly applicable to text→TLA+ evaluation.
- **Benchmark**: 36 expert-crafted instances (expanded to 43 in VLTL-Bench)

### NL2LTL (IBM, AAAI 2023)
- **Task**: NL instructions → LTL formulas
- **Method**: NLU + LLM pipeline. Open-source Python package.
- **Transferability to TLA+**: LOW-MEDIUM. Robot task specification is a narrow domain. But the Python package architecture (parse NL → intermediate → emit formal) is reusable.

### Lang2LTL (CoRL 2023)
- **Task**: NL navigation commands → LTL for robots
- **Results**: Largest NL→LTL dataset (2,125 unique formulas, 40x previous)
- **Transferability to TLA+**: LOW. Domain too narrow (robot navigation). But the dataset construction methodology transfers.

### KGST: Knowledge-Guided STL Transformation (ACL Findings 2025)
- **Task**: NL → Signal Temporal Logic using external knowledge
- **Method**: Generate-then-refine with knowledge repository guidance
- **Transferability to TLA+**: MEDIUM. The knowledge-guided refinement approach could use TLA+ documentation/examples as external knowledge.

### VLTL-Bench (arXiv, 2025)
- **Task**: Benchmark for verifiable NL→LTL translation
- **Contribution**: 43 template-based benchmark instances with verification suite
- **Transferability to TLA+**: HIGH for benchmark design methodology. Shows how to construct NL→formal-spec benchmarks with automated verification.

### ConformalNL2LTL (arXiv, 2025)
- **Task**: NL → LTL with conformal prediction correctness guarantees
- **Method**: Statistical guarantees on translation success rate for unseen inputs
- **Transferability to TLA+**: MEDIUM. The idea of providing statistical confidence bounds on translation quality is novel and applicable.

---

## Category 2: Natural Language → Other Formal Specifications (Alloy, Symboleo, UCLID5)

### LLMs for Alloy Formula Generation (arXiv, Feb 2025)
- **Task**: NL descriptions → Alloy specifications
- **Results**: LLMs performed "quite well" at synthesizing complete Alloy formulas; able to enumerate multiple unique solutions
- **Transferability to TLA+**: MEDIUM. Alloy is relational/declarative like TLA+ in some respects. Shows that LLMs can handle formal spec DSLs with small training corpora.
- **Limitation**: Alloy's constraint language is structurally simpler than TLA+'s temporal actions.

### LLM Repair of Alloy Specifications (arXiv, 2024; Springer 2025)
- **Task**: Repair defective Alloy specifications using LLMs
- **Method**: 12 settings (single/dual agent, feedback levels, auto-prompting). 106,596 repair attempts on 1,974 defective models.
- **Key finding**: Dual-agent with auto-prompting outperforms all other settings and state-of-the-art Alloy APR techniques.
- **Transferability to TLA+**: HIGH for the repair methodology. Generated TLA+ specs will need iterative repair. The dual-agent architecture transfers directly.

### Symboleo: NL Legal Contracts → Formal Specs (arXiv, Nov 2024)
- **Task**: English legal contract text → Symboleo formal specifications
- **Method**: 38 prompt combinations (with/without grammar, 0-3 examples, emotional prompts) tested on GPT-4o + 4 other LLMs
- **Results**: Promising but grammar adherence only 49% — significant syntax issues
- **Key insight**: Even well-prompted LLMs struggle with DSL syntax adherence without constrained decoding
- **Transferability to TLA+**: MEDIUM. Demonstrates that NL→DSL is feasible with LLMs but syntax enforcement is critical. TLA+ has richer syntax than Symboleo.

### Auto-Formalization to UCLID5 (Berkeley, 2025)
- **Task**: Auto-formalize requirements into UCLID5 verification language
- **Transferability to TLA+**: MEDIUM. UCLID5 has some overlap with TLA+ (state machines, temporal properties). Techniques may transfer.

---

## Category 3: LLM-Based Spec/Code Synthesis with Verification Loops

### SpecGen (ICSE 2025)
- **Task**: Automated generation of formal program specifications (pre/postconditions) via LLMs
- **Method**: Two-phase: (1) conversational LLM generation with verifier feedback, (2) mutation operators + heuristic selection for failed cases
- **Results**: 279/385 programs verified, outperforming Houdini and Daikon
- **Key insight**: Verification feedback as prompt input dramatically improves specification quality
- **Transferability to TLA+**: HIGH. The verifier-in-the-loop pattern (generate→check→feedback→regenerate) directly applies. TLC/Apalache can serve as the verifier.

### DafnyBench (2024)
- **Task**: Benchmark for LLM-generated Dafny verification annotations
- **Scale**: 750+ programs, 53K LOC. LLM success rate improved from 68%→96% in one year.
- **Transferability to TLA+**: MEDIUM. Dafny annotations are simpler than TLA+ full spec generation. But the benchmark methodology and rapid LLM improvement trajectory are encouraging.

### dafny-annotator (2025)
- **Task**: Multi-model LLM approach for generating Dafny verification annotations
- **Results**: 98.2% success rate (Claude Opus 4.5 + GPT-5.2, up to 8 repair iterations)
- **Transferability to TLA+**: MEDIUM. Multi-model + iterative repair approach could work for TLA+.

### Agentic Program Verification (arXiv, 2025)
- **Task**: Iterative proof improvement with Rocq (Coq) theorem prover feedback
- **Method**: Agentic LLM communicates with verifier, gets context and feedback
- **Transferability to TLA+**: MEDIUM-HIGH. The agentic loop with TLC/TLAPS feedback is a natural architecture.

### AutoSpec: NL RFC → Protocol Specifications (arXiv, Nov 2025)
- **Task**: Natural language RFC specifications → I/O grammar formal protocol specs → fuzz testing
- **Method**: Two-stage LLM (extract protocol elements → synthesize/repair grammar)
- **Results**: 92.8% client message type recovery, 81.5% message acceptance rate on 5 protocols
- **Key insight**: Going through an inspectable intermediate specification preserves traceability and makes testing reproducible
- **Transferability to TLA+**: HIGH. The two-stage pipeline (extract elements → synthesize spec) is the most relevant architecture pattern. Would need adaptation from I/O grammars to TLA+ state machines.

---

## Category 4: Grammar-Constrained and Syntax-Constrained Generation

### Grammar-Constrained Decoding for Logical Parsing (ACL Industry 2025)
- **Task**: Enforce grammar constraints during LLM decoding for logical formulas
- **Results**: Consistently improves both syntactic correctness and semantic accuracy
- **Key insight**: Grammar constraints serve as effective substitute for in-context examples
- **Transferability to TLA+**: HIGH. TLA+ has a well-defined grammar (SANY, tree-sitter-tlaplus). GCD could enforce syntactic validity of generated TLA+. The TLAi Challenge already demonstrated this with GBNF.

### Grammar-Aligned Decoding (NeurIPS 2024)
- **Task**: Provably preserve conditional probability distribution under grammar constraints
- **Theoretical result**: GAD guarantees grammatical outputs while matching the LLM's conditional distribution
- **Transferability to TLA+**: MEDIUM-HIGH. Theoretical foundation for using GCD with TLA+ grammar without degrading output quality.

---

## Category 5: Retrieval-Augmented Generation for Formal Tasks

No dedicated paper found for RAG + formal specification generation, but the following techniques transfer:

- **TLA+ documentation as retrieval corpus**: The TLA+ book, Specifying Systems, and tlaplus/Examples provide high-quality reference material for RAG retrieval
- **Few-shot retrieval from spec corpus**: The tlaplus/Examples repository (100+ specs) and TLAiBench provide retrieval candidates for similar specification patterns
- **Tool-augmented generation**: Apalache's new JSON-RPC API enables LLM agents to invoke model checking as a tool during generation

Speculative reuse — no published system demonstrates RAG specifically for TLA+ generation.

---

## Category 6: Program Repair and Verifier-in-the-Loop Refinement

### The 4/δ Bound: Predictable LLM-Verifier Systems (arXiv, 2025)
- **Task**: Provide formal convergence guarantees for iterative LLM-verifier refinement
- **Key result**: First mathematical framework proving when LLM-verifier loops terminate
- **Transferability to TLA+**: HIGH for architecture design. Provides theoretical justification for generate→verify→repair loops with TLC/Apalache.

### PREFACE: RL-based Prompt Repair for Code Verification (GLSVLSI 2025)
- **Task**: RL agent selects corrective prompts to minimize verification iterations
- **Results**: Up to 21% improvement in verification success rate
- **Transferability to TLA+**: MEDIUM. RL-based prompt optimization could improve TLA+ generation quality over time.

### LLM Repair of Alloy Specifications (covered in Category 2)
- Dual-agent setup with auto-prompting is the strongest repair architecture found.

---

## Cross-Category Synthesis

The strongest transferable patterns for text→TLA+ are:

1. **Two-stage pipeline** (AutoSpec pattern): NL → intermediate representation → formal spec
2. **Verifier-in-the-loop** (SpecGen pattern): Generate → TLC/Apalache check → feedback → regenerate
3. **Grammar-constrained decoding**: Enforce TLA+ syntax via tree-sitter-tlaplus or GBNF grammar
4. **Dual-agent repair** (Alloy repair pattern): Generator + repair agent with auto-prompting
5. **Hierarchical decomposition** (OnionL/SYNTHTL): Break NL into composable sub-problems
