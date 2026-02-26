# Evaluation Methods for Text-to-TLA+ Output Quality

How to evaluate whether LLM-generated (or otherwise automatically generated) TLA+ specifications are correct, complete, and faithful to their natural-language source.

## Why This Matters

Generating TLA+ from text is harder to evaluate than typical code generation. A syntactically valid TLA+ module can silently omit critical safety properties, invent nonexistent constraints, or model fundamentally different behavior than intended. Standard code-generation metrics (BLEU, pass@k, execution accuracy) are insufficient for formal specifications.

## LLM Primer: Why LLMs Are Relevant Here

### What LLMs Are Good At
- Pattern translation between structured formats
- Boilerplate generation for repetitive specification idioms
- Reformulating informal descriptions into structured notation
- Few-shot learning from example specifications

### What LLMs Are Bad At
- Silent omissions of subtle requirements
- Hallucinated constraints not present in the source
- Unstable semantics across minor prompt variations
- Maintaining consistency across multi-module specifications
- Reasoning about temporal properties and fairness

### Why Formal Outputs Need Stronger Evaluation
- A TLA+ spec that parses but violates invariants is worse than a compilation error
- Silent semantic errors are not caught by syntax checking
- Standard code-generation benchmarks do not measure specification faithfulness

## Evaluation Dimensions

Each dimension is separate and should be evaluated independently:

### 1. Syntax Validity
- Does the output parse with SANY?
- Are all operators and module references well-formed?
- **Method**: Automated SANY check (binary pass/fail)

### 2. Semantic / Model-Check Readiness
- Can TLC or Apalache model-check the output with appropriate configuration?
- Are initial states finite? Are state variables bounded?
- **Method**: Automated TLC run with small model parameters

### 3. Requirement Coverage
- Does the spec address every functional requirement stated in the source text?
- **Method**: Requirement extraction from source text, then traceability matrix mapping each requirement to spec elements

### 4. Faithfulness
- Does the spec contradict any statement in the source text?
- **Method**: Cross-reference checking, adversarial invariant testing, expert review

### 5. Precision (No Invented Behavior)
- Does the spec add constraints, transitions, or invariants not supported by the source text?
- **Method**: Diff against source requirements, flagging any spec element without a source justification

### 6. Ambiguity Handling
- When the source text is ambiguous, does the spec make explicit assumptions?
- Are assumptions documented rather than silently resolved?
- **Method**: Manual review of assumption documentation

### 7. Safety Property Completeness
- If the source text states safety properties (e.g., "at most one leader per term"), are they captured as invariants?
- **Method**: Extract safety claims from text, check for corresponding `Invariant` declarations

### 8. Downstream Compatibility
- Is the output compatible with the existing TLA+ -> Verus conversion workflow?
- Does it use the `Init/Next/Spec` idiom expected by the pipeline?
- **Method**: Attempt downstream conversion, check for pipeline errors

## Concrete Evaluation Methods

### Requirement-to-Spec Traceability Matrix

*(Detailed method description for mapping source requirements to spec elements.)*

### Mutation Testing of Generated Specs

*(Using specification mutations to test whether the evaluation catches semantic errors.)*

### Differential Model Checking

*(Comparing model-checking results of the generated spec against a reference spec.)*

### Human Expert Review Protocol

*(Structured review process for domain experts to evaluate generated specifications.)*

### Automated Semantic Checks

*(Invariant injection, trace comparison, and property-based evaluation.)*
