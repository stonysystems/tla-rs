# Survey Methodology

## Research Questions

This survey is structured around four research questions:

**RQ1: Direct prior art** -- Are there published papers, repositories, or systems that directly perform `text -> TLA+` generation?

**RQ2: Adjacent building blocks** -- If direct text-to-TLA+ work is sparse or nonexistent, which adjacent methods, tools, and techniques are the strongest building blocks for constructing such a system?

**RQ3: Evaluation of faithfulness** -- How do existing works evaluate whether generated formal artifacts faithfully represent their natural-language source? What methods transfer to text-to-TLA+?

**RQ4: Evaluation plan** -- What concrete evaluation plan is appropriate for a text-to-TLA+ system in this repository's context, given the downstream pipeline (TLA+ -> Verus spec -> verified Rust)?

## Inclusion Criteria

A work is **included** if it meets any of the following:

1. **Directly targets NL/text -> TLA+**: Any system, paper, or tool that takes natural-language input and produces TLA+ output.
2. **Adjacent formal spec generation**: Work that generates formal specifications (LTL, CTL, Alloy, Event-B, Z, Dafny, Coq, Isabelle, etc.) from natural language, and whose methods could plausibly transfer to TLA+.
3. **LLM-based code/spec synthesis with formal targets**: LLM methods that generate formally structured outputs (state machines, automata, temporal logic formulas) from text.
4. **Evaluation methods for generated formal artifacts**: Work that proposes or demonstrates methods for checking whether generated specifications match their source text.
5. **TLA+-adjacent tooling**: Parsers, AST libraries, model checkers, or benchmark corpora that could serve as components in a text-to-TLA+ pipeline.

## Exclusion Criteria

A work is **excluded** if:

1. It is a **generic LLM survey** that does not contribute concrete methods or evaluation relevant to formal spec generation.
2. It is a **blog post** used as primary evidence (acceptable only as secondary evidence when no paper/repo exists, and must be marked as such).
3. It targets **code generation without formal structure** (e.g., Copilot-style code completion for general-purpose languages without verification).
4. It is **purely theoretical** with no artifact, implementation, or experimental evaluation.
5. It addresses **PDF parsing, OCR, or document layout** exclusively (out of scope for this survey's text-first focus).

## Categorization

Each included work is categorized as:

- **Direct**: Specifically targets text/NL -> TLA+ generation.
- **Adjacent**: Targets a closely related problem (NL -> other formal spec, LLM -> verified code, etc.) with transferable methods.
- **Far-adjacent**: Addresses a more distant problem but contributes specific techniques or evaluation methods relevant to our context.
- **Tooling**: Not a research contribution but a practical tool/component reusable in a pipeline.

## Search Sources

The following sources are searched (dates and queries logged in [search_log.md](search_log.md)):

### Scholarly Indexes
- arXiv (cs.SE, cs.FL, cs.AI, cs.CL, cs.PL)
- Google Scholar
- Semantic Scholar
- DBLP
- ACM Digital Library
- IEEE Xplore

### Venue-Specific Searches
- **PL/FM**: CAV, FMCAD, FM, POPL, OOPSLA, PLDI, ICSE, FSE, ASE, TACAS, NFM
- **NLP/LLM**: ACL, EMNLP, NAACL, NeurIPS, ICLR, ICML (where relevant to formal output generation)

### Code and Tool Searches
- GitHub (repository and code search)
- HuggingFace (model/dataset search for TLA+ related resources)

### Community Resources
- TLA+ community resources (learntla.com, tla+ google group, Lamport's writings)
- Formal methods community forums and mailing lists

## Evidence Thresholds

To prevent a shallow survey:

- **Minimum screening**: At least 30 candidates total (papers + repos/tools combined), unless the search space is demonstrably smaller (justified in this document).
- **Deep review**: At least 12 included items receive deep review (beyond abstract skim), with source-specific notes.
- **Comparison matrix**: At least 8 items in the final comparison matrix (direct + adjacent combined), unless fewer are genuinely relevant (justified).

## Evidence Quality Rules

- Claims must be supported by the actual paper/repo content, not by secondary summaries.
- "Claim verification" subsections document what a work claims vs. what is demonstrated.
- Speculative reuse is explicitly labeled distinct from demonstrated reuse.
- Search completeness is bounded by date and scope, never stated as absolute.
