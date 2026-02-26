# Evidence Checklist

Completeness checklist for all survey deliverables. Each item must be checked before the survey is considered complete.

## 28.1 Deliverables and File Layout

- [ ] **28.1.1** Directory structure and file skeletons created with section headers (no empty files)
- [ ] **28.1.2** `README.md` includes: survey scope, "text" definition, compatibility target, reading order
- [ ] **28.1.3** `glossary.md` defines all required terms (TLA+, TLC, SANY, state machine, safety, liveness, invariant, LLM, prompting, RAG, constrained decoding, fine-tuning, formal specification, semantic equivalence, trace, counterexample)
- [ ] **28.1.4** `comparison_matrix.md` and `artifacts/comparison_matrix.csv` have matching columns/rows

## 28.2 Survey Methodology

- [ ] **28.2.1** `methodology.md` includes explicit research questions (RQ1-RQ4)
- [ ] **28.2.2** Inclusion/exclusion criteria are explicit and distinguish direct/adjacent/not applicable
- [ ] **28.2.3** Search sources are defined (scholarly indexes, PL/FM venues, NLP/LLM venues, GitHub, community)
- [ ] **28.2.4** `search_log.md` has reproducible entries (date, engine, query, results, kept/rejected)
- [ ] **28.2.5** Screening logs exist: `artifacts/papers_screened.csv`, `artifacts/repos_screened.csv` with required columns
- [ ] **28.2.6** Minimum evidence thresholds met: 30+ candidates screened, 12+ deep reviewed, 8+ in matrix

## 28.3 Direct Prior Art

- [ ] **28.3.1** `related_work_direct.md` created
- [ ] **28.3.2** Each direct work has: input, output, machine-checkable?, source available?, evaluation
- [ ] **28.3.3** Each direct work has claim verification: claims vs. demonstrated vs. missing
- [ ] **28.3.4/5** Either "no direct works found" is justified or direct works are listed with details

## 28.4 Adjacent Work and Tooling

- [ ] **28.4.1** `related_work_adjacent.md` and `tooling_landscape.md` created
- [ ] **28.4.2** Adjacent research areas surveyed as separate sections (not blended)
- [ ] **28.4.3** TLA+-adjacent tooling surveyed with integration notes
- [ ] **28.4.4** Each tool has: license, maintenance, install friction, API, CI, role
- [ ] **28.4.5** Speculative vs. demonstrated reuse explicitly labeled

## 28.5 Comparison Matrix

- [ ] **28.5.1** `comparison_matrix.md` has concise intro and human-readable table
- [ ] **28.5.2** `artifacts/comparison_matrix.csv` matches
- [ ] **28.5.3** All required columns present
- [ ] **28.5.4** Synthesis section covers: solved, partially solved, unsolved, TLA+-unique gaps
- [ ] **28.5.5** Decision lens: near-term blocks, high-risk bets, dead ends

## 28.6 LLM Methods and Evaluation

- [ ] **28.6.1** `evaluation_of_text_to_tla.md` created
- [ ] **28.6.2** Beginner-friendly LLM primer included
- [ ] **28.6.3** Evaluation dimensions defined (syntax, semantics, coverage, faithfulness, precision, ambiguity, properties, compatibility)
- [ ] **28.6.4** Concrete evaluation methods documented (not just "manual review")

## 28.7 Recommendations and Gaps

- [ ] **28.7.1** `recommendations.md` with near-term, medium-term, long-term categories
- [ ] **28.7.2** `gaps_and_risks.md` with known unknowns and mitigations
