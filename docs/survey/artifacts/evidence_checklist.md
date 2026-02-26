# Evidence Checklist

Completeness checklist for all survey deliverables. Each item must be checked before the survey is considered complete.

## 28.1 Deliverables and File Layout

- [x] **28.1.1** Directory structure and file skeletons created with section headers (no empty files)
- [x] **28.1.2** `README.md` includes: survey scope, "text" definition, compatibility target, reading order
- [x] **28.1.3** `glossary.md` defines all required terms (TLA+, TLC, SANY, state machine, safety, liveness, invariant, LLM, prompting, RAG, constrained decoding, fine-tuning, formal specification, semantic equivalence, trace, counterexample)
- [x] **28.1.4** `comparison_matrix.md` and `artifacts/comparison_matrix.csv` have matching columns/rows

## 28.2 Survey Methodology

- [x] **28.2.1** `methodology.md` includes explicit research questions (RQ1-RQ4)
- [x] **28.2.2** Inclusion/exclusion criteria are explicit and distinguish direct/adjacent/not applicable
- [x] **28.2.3** Search sources are defined (scholarly indexes, PL/FM venues, NLP/LLM venues, GitHub, community)
- [x] **28.2.4** `search_log.md` has reproducible entries (date, engine, query, results, kept/rejected)
- [x] **28.2.5** Screening logs exist: `artifacts/papers_screened.csv`, `artifacts/repos_screened.csv` with required columns
- [x] **28.2.6** Minimum evidence thresholds met: 30+ candidates screened (36), 12+ deep reviewed (16), 8+ in matrix (16)

## 28.3 Direct Prior Art

- [x] **28.3.1** `related_work_direct.md` created
- [x] **28.3.2** Each direct work has: input, output, machine-checkable?, source available?, evaluation
- [x] **28.3.3** Each direct work has claim verification: claims vs. demonstrated vs. missing
- [x] **28.3.4/5** "No direct NL→TLA+ works found" justified with search evidence; nearest works (D1-D7) listed with details

## 28.4 Adjacent Work and Tooling

- [x] **28.4.1** `related_work_adjacent.md` and `tooling_landscape.md` created
- [x] **28.4.2** Adjacent research areas surveyed as separate sections (6 categories, not blended)
- [x] **28.4.3** TLA+-adjacent tooling surveyed with integration notes
- [x] **28.4.4** Each tool has: license, maintenance, install friction, API, CI, role
- [x] **28.4.5** Speculative vs. demonstrated reuse explicitly labeled

## 28.5 Comparison Matrix

- [x] **28.5.1** `comparison_matrix.md` has concise intro and human-readable table
- [x] **28.5.2** `artifacts/comparison_matrix.csv` matches (16 entries, 18 columns)
- [x] **28.5.3** All required columns present (Name, Type, Year, Task Solved, Directness, Input Assumptions, Output Formalism, Machine-Checkable?, Method Family, Evaluation Style, Faithfulness Check, Open-Source?, Artifact Status, License, Strengths, Limitations, Potential Reuse, Confidence)
- [x] **28.5.4** Synthesis section covers: solved, partially solved, unsolved, TLA+-unique gaps
- [x] **28.5.5** Decision lens: near-term building blocks, high-risk bets, dead ends

## 28.6 LLM Methods and Evaluation

- [x] **28.6.1** `evaluation_of_text_to_tla.md` created
- [x] **28.6.2** Beginner-friendly LLM primer included (what LLMs are good/bad at, why formal outputs need stronger evaluation)
- [x] **28.6.3** Evaluation dimensions defined: D1 syntax, D2 semantics, D3 coverage, D4 faithfulness, D5 precision, D6 ambiguity, D7 properties, D8 compatibility
- [x] **28.6.4** Concrete evaluation methods documented: M1 traceability matrix, M2 scenario conformance, M3 entailment checks, M4 round-trip summarization, M5 differential comparison, M6 model-checking invariants, M7 mutation testing
- [x] **28.6.5** Each evaluation method has: what it catches, what it misses, human effort, automation potential, failure examples
- [x] **28.6.6** Failure taxonomy: F1-F8 (omitted guards, incorrect priming, under/overconstrained, invented variables, hidden assumptions, property mismatch, syntax-valid-but-wrong)
- [x] **28.6.7** Evaluation rubric with scoring categories, pass/fail gates, reviewer instructions, evidence to save
- [x] **28.6.8** Benchmark/data limitations noted: no standard text→TLA+ benchmark; minimal internal benchmark requirements defined

## 28.7 Recommendations and Gaps

- [x] **28.7.1** `recommendations.md` with 3 architecture options (A: LLM-first, B: IR+emitter, C: human-in-loop)
- [x] **28.7.2** `gaps_and_risks.md` with known unknowns (G1-G5), risks (R1-R5), blockers (B1-B3) and mitigations
- [x] **28.7.3** Each option has: inputs/outputs, components, strengths/risks, evaluation strategy, engineering effort, downstream compatibility
- [x] **28.7.4** Text-first/PDF-later note included with preprocessing candidates and deferral rationale
- [x] **28.7.5** Recommended next step: pilot benchmark with 3 protocols
