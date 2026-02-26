# Glossary

Beginner-friendly definitions for terms used throughout this survey, organized by domain.

## Formal Methods and TLA+

**TLA+**
: Temporal Logic of Actions Plus. A formal specification language created by Leslie Lamport for describing and reasoning about concurrent and distributed systems. Specifications are mathematical state machines with an `Init` predicate (initial states) and a `Next` relation (valid transitions).

**TLC**
: The TLA+ model checker. Exhaustively explores the state space of a finite-instance TLA+ specification to check invariants and temporal properties. Reports counterexample traces when violations are found.

**SANY**
: Syntactic Analyzer for TLA+. The standard parser/type-checker for TLA+ modules. A specification that passes SANY is syntactically valid TLA+.

**Apalache**
: A symbolic model checker for TLA+ that uses SMT solvers instead of explicit state enumeration. Scales better than TLC for some specifications but requires type annotations.

**State machine**
: A mathematical model defined by a set of states, an initial-state predicate, and a transition relation. TLA+ specifications are state machines. A protocol is correct if every reachable state satisfies the desired invariants.

**Safety property**
: A property asserting that "nothing bad ever happens" -- formally, every reachable state satisfies an invariant. Example: "no two nodes believe they are leader for the same term."

**Liveness property**
: A property asserting that "something good eventually happens" -- formally, the system eventually reaches a desired state. Example: "every client request eventually receives a response." Liveness is harder to verify and typically requires fairness assumptions.

**Invariant**
: A predicate that must hold in every reachable state of the system. Invariants are the primary safety property checked by TLC.

**Formal specification**
: A mathematically precise description of a system's behavior, written in a language with well-defined semantics (e.g., TLA+, Alloy, Event-B). Unlike code, a formal spec describes *what* the system should do, not *how*.

**Semantic equivalence**
: Two specifications are semantically equivalent if they describe exactly the same set of behaviors (same initial states and same transitions). This is the gold standard for evaluating whether a generated spec matches the source, but is generally undecidable for infinite-state systems.

**Trace**
: A sequence of states representing one possible execution of a system. TLC produces traces as counterexamples when an invariant is violated.

**Counterexample**
: A specific trace that demonstrates a property violation. The most useful output of model checking -- it shows exactly how the system can reach a bad state.

## LLM and Machine Learning

**LLM (Large Language Model)**
: A neural network trained on large text corpora that can generate, complete, and transform text. Examples: GPT-4, Claude, Llama. Relevant here because LLMs can potentially translate natural-language protocol descriptions into formal specifications.

**Prompting**
: Providing instructions and context to an LLM to guide its output. Techniques include zero-shot (no examples), few-shot (with examples), and chain-of-thought (asking the model to reason step by step).

**RAG (Retrieval-Augmented Generation)**
: A technique that augments LLM generation by first retrieving relevant documents from a knowledge base. For text-to-TLA+, this could mean retrieving similar existing TLA+ specs to guide generation.

**Constrained decoding**
: Restricting an LLM's output to conform to a formal grammar or schema during generation. For TLA+, this could enforce syntactic validity at generation time rather than checking after the fact.

**Fine-tuning**
: Training a pre-trained LLM on a smaller domain-specific dataset to improve performance on a particular task. For text-to-TLA+, this would involve training on pairs of (natural-language description, TLA+ spec).

## Software Engineering and Verification

**Verus**
: A deductive program verifier for Rust. Uses SMT solvers to prove that Rust code satisfies its specifications. The downstream target for this repository's pipeline.

**Verified implementation**
: Code that has been mathematically proven to satisfy its specification. In this repo, Verus proves that Rust exec functions implement TLA+-derived specs correctly.

**Transpiler**
: A source-to-source compiler. This repository's transpiler converts Verus spec functions into verified exec functions. The survey's concern is the upstream step: converting text to TLA+ that feeds this pipeline.

**Requirement coverage**
: The degree to which a formal specification captures all requirements stated in the source text. A generated TLA+ spec with high requirement coverage addresses every functional requirement mentioned in the input.

**Faithfulness**
: The degree to which a generated specification accurately reflects the source text without introducing contradictions, omissions, or invented behavior.
