# Evaluating Text → TLA+ Output Quality

## LLM Primer: Why LLMs and Why They Need Stronger Evaluation

### What LLMs Are Good At

Large Language Models (LLMs) are neural networks trained on massive text corpora that excel at pattern-based translation tasks. For formal specification generation, they are good at:

- **Pattern translation**: Converting between structured formats when examples are provided (few-shot learning)
- **Boilerplate generation**: Producing syntactically regular code structure (module declarations, variable blocks, standard TLA+ scaffolding)
- **Reformulation**: Paraphrasing requirements into more structured intermediate forms
- **Domain transfer**: Adapting techniques from one formal language (e.g., Alloy, LTL) to another (TLA+), given sufficient context

### What LLMs Are Bad At

- **Silent omissions**: Dropping requirements without warning. An LLM may generate a spec that looks complete but misses a guard condition mentioned in the source text.
- **Hallucinated constraints**: Inventing behavior not present in the source text. The LLM may add "reasonable-looking" guards or transitions that were never specified.
- **Unstable semantics**: Small prompt changes can produce semantically different specs. The same requirement described slightly differently may yield different TLA+ formulations.
- **Formal syntax unfamiliarity**: LLMs have very limited training data on TLA+ specifically. Testing shows that open-source LLMs (Llama3, Phi3, Mistral, CodeLlama) cannot produce SANY-parsable TLA+ output (Shan 2024). Even commercial models struggle with TLA+'s unusual operator syntax.

### Why Formal Outputs Need Stronger Evaluation

Code generation demos typically measure "does it compile and pass tests." This is insufficient for formal specifications because:

1. **Syntactically valid ≠ semantically correct**: A TLA+ spec can parse and even model-check without errors while completely misrepresenting the intended system.
2. **Partial correctness is dangerous**: A spec that captures 90% of the requirements may be worse than no spec at all, because it creates false confidence.
3. **TLA+'s expressiveness enables subtle errors**: The difference between `x' = x + 1` and `x' \in {x, x + 1}` (deterministic vs. nondeterministic) is a single character but fundamentally changes the spec's meaning.
4. **Downstream trust chain**: In this repository's context, generated TLA+ feeds into an automated pipeline (TLA+→Verus spec→verified Rust). Errors in the TLA+ spec propagate silently through the entire chain, resulting in a "verified" system that doesn't match its requirements.

---

## Evaluation Dimensions

Each dimension is defined separately to enable independent assessment and to avoid conflating different quality aspects.

### D1: Syntax Validity

- **What it measures**: Does the generated TLA+ parse without errors?
- **How to check**: Run SANY (`java -jar tla2tools.jar -SANY Module.tla`). Binary pass/fail.
- **What it catches**: Malformed operators, missing declarations, invalid syntax
- **What it misses**: Everything semantic. A syntactically valid spec can be completely wrong.
- **Automation potential**: Fully automated. SANY is deterministic.
- **Required human effort**: None.

### D2: Semantic / Model-Check Readiness

- **What it measures**: Can the generated spec be model-checked with TLC or Apalache?
- **How to check**: Provide a TLC config with finite parameter instantiation. Run `java -jar tla2tools.jar -modelcheck`. Check for (1) no evaluation errors, (2) no deadlocks unless expected.
- **What it catches**: Undefined operators, infinite state spaces without proper bounding, type errors (with Apalache)
- **What it misses**: Specs can model-check cleanly while being wrong (no invariant violations doesn't mean correctness if the invariants themselves are wrong).
- **Automation potential**: High, but requires a TLC config (which may also need to be generated).
- **Required human effort**: Low (writing TLC config) to medium (interpreting counterexamples).

### D3: Requirement Coverage

- **What it measures**: Does the spec include all stated requirements from the source text?
- **How to check**: Extract a numbered list of requirements from the source text (manually or with an LLM). For each requirement, identify which TLA+ action(s) or invariant(s) implement it. Mark uncovered requirements.
- **What it catches**: Missing actions, missing state variables, omitted requirements
- **What it misses**: Subtle misinterpretations where the requirement is "covered" but with wrong semantics
- **Automation potential**: Medium. Requirement extraction can be LLM-assisted. Traceability mapping requires human review or nl2spec-style subformula decomposition.
- **Required human effort**: Medium (verify traceability matrix).
- **Failure example**: Source text says "the leader sends heartbeats every 100ms." Generated spec has no heartbeat action. Requirement coverage check catches this.

### D4: Faithfulness (No Contradictions)

- **What it measures**: Is every behavior allowed by the spec consistent with the source text?
- **How to check**: For each action in the generated spec, verify that its guard and update are consistent with the source text. Look for contradictions: "text says X, but spec does not-X."
- **What it catches**: Inverted conditions, wrong variable updates, contradictory guards
- **What it misses**: Omissions (covered by D3), over-generalization (covered by D5)
- **Automation potential**: Low-Medium. Can use entailment checking (LLM-assisted) on structured claims.
- **Required human effort**: High (requires understanding both text and spec).
- **Failure example**: Source says "a node votes for at most one candidate per term." Spec allows voting for multiple candidates. Faithfulness check catches this.

### D5: Precision (No Invented Behavior)

- **What it measures**: Does the spec avoid adding behavior not present in the source text?
- **How to check**: For each action and invariant in the spec, trace it back to source text. Flag elements with no textual basis.
- **What it catches**: Hallucinated variables, invented transitions, added constraints not in text
- **What it misses**: Reasonable inferences that are debatable
- **Automation potential**: Low. Requires human judgement about what is "invented" vs. "reasonably inferred."
- **Required human effort**: High.
- **Failure example**: Source describes a consensus protocol. Generated spec includes a "garbage collection" action not mentioned anywhere in the text. Precision check catches this.

### D6: Ambiguity Handling

- **What it measures**: Does the spec make its assumptions explicit when the source text is ambiguous?
- **How to check**: Identify ambiguous passages in the source text. Check whether the spec (a) resolves the ambiguity with an explicit assumption (documented in comments), (b) introduces nondeterminism to cover multiple interpretations, or (c) silently picks one interpretation.
- **What it catches**: Silent interpretation choices that may be wrong
- **What it misses**: Ambiguities that the reviewer also misses
- **Automation potential**: Low. Ambiguity detection in NL is an open research problem.
- **Required human effort**: High.

### D7: Safety Property Completeness

- **What it measures**: If the source text states safety properties (invariants, "must never" clauses), are they present as invariants in the spec?
- **How to check**: Extract safety claims from text. Check for corresponding `Inv == ...` definitions and `INVARIANT Inv` in the TLC config.
- **What it catches**: Missing invariants, incomplete safety specifications
- **What it misses**: Safety properties not explicitly stated in text
- **Automation potential**: Medium (safety claim extraction can be LLM-assisted).
- **Required human effort**: Medium.

### D8: Downstream Compatibility

- **What it measures**: Is the generated TLA+ compatible with this repository's downstream pipeline (TLA+→tla-rs/Verus spec→Verus implementation)?
- **How to check**: Verify (a) module structure matches expected input format, (b) state variables use types that map to Verus types, (c) actions are structured as `Action(s, s', ...) == guard /\ updates` which the transpiler can consume, (d) constants and parameters are declared in the expected way.
- **What it catches**: Structural incompatibilities that would block downstream processing
- **What it misses**: Semantic issues that pass through the pipeline
- **Automation potential**: High (structural checks can be automated).
- **Required human effort**: Low.

---

## Concrete Evaluation Methods

### M1: Requirement Extraction and Traceability Matrix

- **Process**: (1) Number each requirement sentence in the source text. (2) For each requirement, identify the TLA+ element(s) that implement it. (3) Build a requirements-to-spec traceability matrix. (4) Flag uncovered requirements and untraceable spec elements.
- **What it catches**: Missing coverage (D3) and invented behavior (D5)
- **What it misses**: Subtle semantic mismatches within traced pairs
- **Human effort**: Medium (manual matrix construction, ~30 min per spec)
- **Automation potential**: LLM can assist with requirement extraction and initial mapping. Human validates.
- **Failure example**: Source has 15 numbered requirements. Matrix shows 12 mapped, 3 unmapped. Those 3 are missing from the spec.

### M2: Scenario-Based Conformance Checks

- **Process**: (1) From the source text, derive 5-10 expected scenarios (sequences of events/states). (2) Encode each scenario as a TLC assertion or trace constraint. (3) Run TLC to check if the spec allows/disallows each scenario as expected.
- **What it catches**: Wrong behavior on concrete examples (D4, D5)
- **What it misses**: Behaviors not covered by scenarios
- **Human effort**: Medium-High (scenario design requires domain understanding)
- **Automation potential**: Scenario extraction can be LLM-assisted. TLC checking is automated.
- **Failure example**: Scenario says "node 1 sends a vote request, node 2 grants it, node 1 becomes leader." TLC check shows the spec doesn't allow this valid scenario.

### M3: Entailment / Contradiction Checks on Structured Claims

- **Process**: (1) Extract structured claims from source text (e.g., "if X then Y", "only Z can W"). (2) Formalize each claim as a TLA+ property or assertion. (3) Check with TLC/Apalache whether the spec satisfies or violates each claim.
- **What it catches**: Faithfulness violations (D4)
- **What it misses**: Claims that can't be easily formalized
- **Human effort**: High (claim extraction and formalization)
- **Automation potential**: Medium (LLM-assisted claim extraction, automated checking)

### M4: Round-Trip Summarization

- **Process**: (1) Give the generated TLA+ spec to an LLM and ask it to describe the system in natural language. (2) Compare the LLM's description with the original source text. (3) Identify mismatches.
- **What it catches**: Major semantic mismatches (D3, D4) visible at the natural language level
- **What it misses**: Subtle formal issues not captured in NL summary
- **Human effort**: Low-Medium (comparison task)
- **Automation potential**: High (fully LLM-based, with human spot-checking)
- **Failure example**: Original text describes "at-most-once delivery." LLM summary of generated spec says "exactly-once delivery." Mismatch detected.

### M5: Differential Comparison Against Reference Spec

- **Process**: When a trusted reference TLA+ spec exists (e.g., from tlaplus/Examples or manually written), (1) compare the generated spec structurally (same state variables, same actions, same invariants), (2) check behavioral equivalence via TLC (same reachable states under same parameters).
- **What it catches**: Structural and behavioral differences from ground truth
- **What it misses**: Only applicable when reference exists
- **Human effort**: Low (automated comparison)
- **Automation potential**: High
- **Limitation**: Reference specs are expensive to create. Only useful for benchmarking, not production.

### M6: Model-Checking Derived Invariants

- **Process**: (1) Extract invariant candidates from source text. (2) Add them to TLC config. (3) Run TLC bounded model checking. (4) A violation indicates either a bad invariant (ambiguous text) or a bad spec.
- **What it catches**: Safety violations (D7), subtle behavioral errors
- **What it misses**: Invariants not mentioned in text; liveness properties (need fairness)
- **Human effort**: Medium (invariant extraction)
- **Automation potential**: Medium-High (invariant extraction LLM-assisted, checking automated)

### M7: Mutation Testing on Source Requirements

- **Process**: (1) Systematically modify one requirement in the source text (negate a condition, remove a constraint, change a value). (2) Regenerate the TLA+ spec. (3) Check that the spec changes correspondingly. If the spec doesn't change, the pipeline fails to capture that requirement.
- **What it catches**: Requirements that the pipeline ignores (D3)
- **What it misses**: Requirements that change but in the wrong way
- **Human effort**: Low (systematic mutation is automatable)
- **Automation potential**: High (fully automatable pipeline test)
- **Failure example**: Negate "leader must have a quorum" to "leader does not need a quorum." If the generated spec is identical, the quorum requirement was never captured.

---

## Failure Taxonomy for LLM-Generated TLA+

### F1: Omitted Guards
The generated action lacks a guard condition present in the source text.
- Example: Source says "only the leader can commit." Generated `Commit` action has no `state[node] = "leader"` guard.

### F2: Incorrect Priming / State-Update Semantics
Wrong use of primed variables or confusion about what changes.
- Example: `x' = x + 1 /\ y' = x` should update y with old x, but LLM may write `y' = x'` (using new x).

### F3: Underconstrained Transitions
Action allows more behaviors than intended.
- Example: Source says "increment counter by 1." Generated spec says `counter' > counter` (allows incrementing by any amount).

### F4: Overconstrained Transitions
Action is more restrictive than the source text.
- Example: Source describes nondeterministic timeout. Generated spec uses a fixed deterministic timeout value.

### F5: Invented Variables / Constants / Messages
Spec introduces elements not grounded in the source text.
- Example: Source describes a 2-phase commit. Generated spec adds a `recovery_timeout` variable never mentioned.

### F6: Hidden Assumptions
Spec resolves ambiguity silently without documentation.
- Example: Source doesn't specify message ordering. Generated spec assumes FIFO delivery without stating this assumption.

### F7: Property / Spec Mismatch
Invariant doesn't match the prose requirement it's supposed to formalize.
- Example: Source says "at most one leader per term." Invariant checks "at most one leader at any time" (different -- allows multiple leaders in different terms, which the source intended to allow).

### F8: Syntax-Valid but Semantically Wrong
Spec parses and model-checks without error but doesn't match the system described.
- Example: An action that does nothing (UNCHANGED <<all_vars>>) where the source text describes a state transition. Syntactically valid, semantically empty.

---

## Proposed Evaluation Rubric

### Scoring Categories

For each generated TLA+ module, score independently on:

| Category | Weight | Pass Gate | Scoring |
|----------|--------|-----------|---------|
| D1: Syntax Validity | Required | SANY passes | Binary: 0 or 1 |
| D2: Model-Check Readiness | Required | TLC runs without eval errors | Binary: 0 or 1 |
| D3: Requirement Coverage | 30% | >=80% requirements traced | 0-100% (fraction covered) |
| D4: Faithfulness | 25% | No contradictions found | 0-100% (fraction of actions faithful) |
| D5: Precision | 15% | <=2 invented elements | 0-100% (fraction of elements traced) |
| D6: Ambiguity Handling | 10% | Explicit assumptions documented | 0-100% (fraction of ambiguities addressed) |
| D7: Safety Properties | 10% | >=50% properties present | 0-100% (fraction present) |
| D8: Downstream Compatibility | 10% | Structural format matches | Binary: 0 or 1 |

### Pass/Fail Gates

A generated spec **fails** if:
- D1 (Syntax): Does not parse with SANY
- D2 (Model-Check): TLC evaluation errors
- D3 (Coverage): <50% of requirements traced
- D4 (Faithfulness): Any contradiction with source text

### Reviewer Instructions

1. Read the source text. Number each requirement.
2. Run SANY and TLC (gates D1, D2).
3. Build traceability matrix (D3, D5). Time budget: 30 minutes per spec.
4. Check each traced pair for faithfulness (D4). Time budget: 20 minutes per spec.
5. Identify ambiguities in source text and check handling (D6). Time budget: 10 minutes.
6. Check safety properties (D7). Time budget: 10 minutes.
7. Run downstream pipeline compatibility check (D8). Automated.

### Evidence to Save Per Sample

- Source text (with numbered requirements)
- Generated TLA+ module
- SANY output (pass/fail + any errors)
- TLC output (with config used)
- Traceability matrix (CSV: requirement_id, spec_element, status)
- Faithfulness notes (per-action review)
- Scores per dimension
- Reviewer ID and time spent
- Any failure taxonomy labels (F1-F8)

---

## Benchmark / Data Limitations

### Does a standard text-to-TLA+ benchmark exist?

**No.** As of February 2026, no standard benchmark exists for evaluating text-to-TLA+ generation systems. The closest are:
- **TLAiBench** (2025): Evaluates LLMs on TLA+ tasks but doesn't specifically test NL-to-TLA+ with standardized text inputs
- **SysMoBench** (2025): Evaluates code/docs-to-TLA+ with automated metrics, but inputs are system artifacts not free-form text
- **nl2spec benchmark** (2023): 36 NL-to-temporal-logic pairs, but for LTL not TLA+

### What a minimal internal benchmark should contain

Without creating the benchmark yet, the minimum viable benchmark for this repository would need:

1. **5-10 protocol descriptions** in plain English (covering varying complexity)
2. **Reference TLA+ specs** for each description (manually validated, SANY/TLC checked)
3. **Numbered requirements** per description (for traceability)
4. **Expected invariants** per description (for D7 evaluation)
5. **TLC configs** per spec (for D2 evaluation)
6. **Known edge cases** per description (for scenario-based evaluation M2)

The repository's existing protocol specs (Raft, Paxos, TwoPhase, etc.) provide natural candidates -- their natural language descriptions from the original papers could serve as source texts, with the existing TLA+ specs as reference.
