# Search Log

Reproducible record of all searches performed for this survey. Each entry records the date, engine/site, exact query string, number of results screened, and disposition.

## Format

Each search entry follows this template:

```
### [Search ID] YYYY-MM-DD | Source
- **Query**: exact query string
- **Results screened**: N
- **Kept**: [list of IDs from papers_screened.csv / repos_screened.csv]
- **Rejected**: [count] (reasons summarized)
- **Notes**: any observations about result quality or gaps
```

## Searches

### S01 2026-02-26 | Google Scholar / Web Search
- **Query**: "text to TLA+ natural language formal specification generation 2024 2025 2026"
- **Results screened**: 15
- **Kept**: P01 (SYNTHTL/FMCAD24), P02 (Req2LTL/OnionL), P03 (AutoSpec), P04 (SysMoBench), P05 (TLA+ Proof Automation), P06 (KGST/STL), T01 (TLAi Challenge/Specula), T02 (TLA+ AI Linter)
- **Rejected**: 7 (generic LLM surveys, TLA+ tutorials, Lamport's original TLA+ papers — not relevant to generation)
- **Notes**: Direct text→TLA+ work is sparse; most results are code→TLA+ or adjacent NL→temporal-logic

### S02 2026-02-26 | Google Scholar / Web Search
- **Query**: "LLM generate TLA+ specification from natural language"
- **Results screened**: 12
- **Kept**: P04 (SysMoBench — duplicate), P05 (TLA+ Proof Automation — duplicate), T01 (Specula — duplicate), T03 (TLAiBench), R01 (Shan 2024 tech report)
- **Rejected**: 7 (duplicate results from S01, general code generation, Lamport writings)
- **Notes**: Confirmed scarcity of direct NL→TLA+ work. TLAiBench is a new benchmark find.

### S03 2026-02-26 | Google Scholar / Web Search
- **Query**: "natural language to formal specification LLM temporal logic LTL CTL 2024 2025"
- **Results screened**: 12
- **Kept**: P01 (SYNTHTL — duplicate), P02 (Req2LTL — duplicate), P07 (NL2CTL), P08 (VLTL-Bench), P09 (ConformalNL2LTL), P06 (KGST — duplicate)
- **Rejected**: 6 (robot planning papers without formal spec focus, generic NLP)
- **Notes**: Rich area for NL→LTL/CTL. Multiple benchmarks emerging (VLTL-Bench, Natural2CTL).

### S04 2026-02-26 | Google Scholar / Web Search
- **Query**: "natural language to Alloy Event-B formal specification generation LLM"
- **Results screened**: 10
- **Kept**: P10 (LLM Alloy generation), P11 (LLM Alloy repair), P12 (Symboleo NL→contract spec), P13 (Alloy test case generation)
- **Rejected**: 6 (Event-B not well covered by LLMs yet, generic RE surveys)
- **Notes**: Alloy has more LLM tooling than other specification languages. Symboleo is interesting NL→formal-spec for legal contracts.

### S05 2026-02-26 | Google Scholar / Web Search
- **Query**: "NL2LTL lang2ltl natural language linear temporal logic robot planning"
- **Results screened**: 10
- **Kept**: P14 (NL2LTL/IBM), P15 (Lang2LTL), P16 (nl2spec), P09 (ConformalNL2LTL — duplicate)
- **Rejected**: 6 (robot navigation papers without formal logic focus)
- **Notes**: NL2LTL (IBM) and Lang2LTL are mature tools with datasets. nl2spec has expert-crafted benchmark.

### S06 2026-02-26 | Google Scholar / Web Search
- **Query**: "LLM Dafny Coq Isabelle formal verification code generation spec synthesis 2024 2025"
- **Results screened**: 12
- **Kept**: P17 (SpecGen), P18 (DafnyBench), P19 (dafny-annotator), P20 (Agentic Program Verification), P21 (CLEVER benchmark)
- **Rejected**: 7 (general theorem proving surveys, educational papers)
- **Notes**: Dafny has the most mature LLM-assisted pipeline. SpecGen's verification loop is transferable.

### S07 2026-02-26 | Google Scholar / Web Search
- **Query**: "grammar constrained decoding LLM formal language TLA+ GBNF guidance 2024 2025"
- **Results screened**: 10
- **Kept**: P22 (Grammar-Constrained Decoding/ACL 2025), P23 (Grammar-Aligned Decoding/NeurIPS 2024)
- **Rejected**: 8 (generic JSON/SQL constrained decoding, performance papers)
- **Notes**: GCD is well-studied for JSON/SQL but not yet applied to TLA+ specifically. TLAi Challenge entry used GBNF.

### S08 2026-02-26 | Google Scholar / Web Search
- **Query**: "TLA+ parser AST library tool SANY Apalache tree-sitter-tlaplus"
- **Results screened**: 10
- **Kept**: T04 (tree-sitter-tlaplus), T05 (Apalache), T06 (Quint), T07 (Spectacle), T08 (tlaplus/Examples), T03 (TLAiBench — duplicate)
- **Rejected**: 4 (TLA+ Toolbox GUI docs, old papers)
- **Notes**: tree-sitter-tlaplus has Rust bindings. Apalache has JSON-RPC API. Quint is engineer-friendly TLA+ alternative.

### S09 2026-02-26 | Google Scholar / Web Search
- **Query**: "verifier in the loop LLM self-repair formal specification refinement 2024 2025"
- **Results screened**: 10
- **Kept**: P24 (4/δ Bound LLM-Verifier convergence), P25 (PREFACE RL prompt repair), P11 (LLM Alloy repair — duplicate), P26 (UCLID5 auto-formalization)
- **Rejected**: 6 (generic self-repair/unit test papers, not formal spec focused)
- **Notes**: The 4/δ Bound paper provides first formal convergence guarantees for LLM-verifier loops.

### S10 2026-02-26 | Google Scholar / Web Search
- **Query**: "Symboleo legal contract formal specification LLM generation 2024"
- **Results screened**: 8
- **Kept**: P12 (Symboleo — duplicate)
- **Rejected**: 7 (smart contract verification, not NL→spec)
- **Notes**: Only one paper on LLM→Symboleo. Legal contracts are a niche NL→formal-spec domain.

### S11 2026-02-26 | Google Scholar / Web Search
- **Query**: "OnionL hierarchical intermediate representation natural language LTL"
- **Results screened**: 8
- **Kept**: P02 (Req2LTL/OnionL — duplicate)
- **Rejected**: 7 (duplicate results, generic NLP)
- **Notes**: OnionL achieves 88.4% semantic accuracy + 100% syntactic correctness on aerospace requirements.

### S12 2026-02-26 | Google Scholar / Web Search
- **Query**: "DafnyBench benchmark formal verification LLM code generation 2024"
- **Results screened**: 10
- **Kept**: P18 (DafnyBench — duplicate), P27 (VeriCoding benchmark), P21 (CLEVER — duplicate)
- **Rejected**: 7 (generic code benchmarks, contamination studies)
- **Notes**: DafnyBench: 750+ programs, 53K LOC. LLM progress from 68%→96% on Dafny verification annotations.

### S13 2026-02-26 | GitHub Repository Search
- **Query**: "tlaplus examples", "TLAiBench", "Quint"
- **Results screened**: 8
- **Kept**: T08 (tlaplus/Examples — duplicate), T03 (TLAiBench — duplicate), T06 (Quint — duplicate), T09 (tlaplus/CommunityModules)
- **Rejected**: 4 (personal forks, abandoned repos)
- **Notes**: tlaplus/Examples has diverse specs. TLAiBench is the primary AI benchmark.

## Summary Statistics
- **Total searches**: 13
- **Total results screened**: 135
- **Unique candidates kept**: 36 (P01-P27 papers, T01-T09 tools, R01 tech report)
- **Evidence threshold**: 30+ candidates screened, meets 28.2.6 minimum
