# Text-to-TLA+ Survey: Related Work and Evaluation Methods

## Scope

This survey covers prior work and practical tool options for generating TLA+ formal specifications from natural-language text descriptions. The focus is on **plain text input** (not PDF ingestion or structured templates); PDF preprocessing is noted as future/deferred work.

The generated TLA+ should be compatible with this repository's existing downstream workflow:

```
text  -->  TLA+  -->  tla-rs / Verus spec  -->  Verus verified implementation
           ^^^^^
     (this survey's scope)
```

The survey does **not** build or prototype the `text -> TLA+` system itself. It produces a grounded analysis of what exists, what is adjacent, and how to evaluate outputs.

## What "Text" Means in This Phase

- **Included**: Natural-language protocol descriptions, algorithm pseudocode, RFC-style requirement prose, design documents in plain text.
- **Excluded (deferred)**: PDF parsing, LaTeX source extraction, image/diagram understanding. These are noted as future engineering work but are out of scope for this survey.

## Compatibility Target

Output TLA+ modules should be consumable by the existing downstream conversion pipeline:
- Parse with SANY (TLA+ syntax checker)
- Optionally model-check with TLC or Apalache
- Convert to tla-rs/Verus spec via the `verus2tla` / `tla2verus` tooling in this repo
- Transpile to verified Rust exec functions

This means the generated TLA+ must follow standard TLA+ syntax conventions and should ideally use the state-machine idiom (`Init` / `Next` / `vars` / `Spec`) that the downstream pipeline expects.

## Reading Order

For readers unfamiliar with the domain, we recommend:

1. **[glossary.md](glossary.md)** -- Key terms from formal methods, TLA+, and LLM research
2. **[methodology.md](methodology.md)** -- How the survey was conducted (search protocol, inclusion/exclusion)
3. **[related_work_direct.md](related_work_direct.md)** -- Works that directly target text -> TLA+
4. **[related_work_adjacent.md](related_work_adjacent.md)** -- Adjacent methods (NL -> formal spec, NL -> code)
5. **[tooling_landscape.md](tooling_landscape.md)** -- Practical tools and components for reuse
6. **[comparison_matrix.md](comparison_matrix.md)** -- Side-by-side comparison table and synthesis
7. **[evaluation_of_text_to_tla.md](evaluation_of_text_to_tla.md)** -- How to evaluate generated TLA+ quality
8. **[recommendations.md](recommendations.md)** -- Concrete next steps for this repository
9. **[gaps_and_risks.md](gaps_and_risks.md)** -- Known unknowns and research risks

## Summary

*(To be filled after the survey is complete.)*

## File Index

| File | Purpose |
|------|---------|
| `README.md` | This file: scope, reading order, summary |
| `glossary.md` | Beginner-friendly definitions of key terms |
| `methodology.md` | Search protocol, inclusion/exclusion criteria, evidence rules |
| `search_log.md` | Reproducible record of searches performed |
| `related_work_direct.md` | Works directly targeting NL/text -> TLA+ |
| `related_work_adjacent.md` | Adjacent work: NL -> formal spec, NL -> code, etc. |
| `tooling_landscape.md` | Practical tools/repos/components for reuse |
| `comparison_matrix.md` | Human-readable comparison table and synthesis |
| `evaluation_of_text_to_tla.md` | Evaluation methods for text-to-TLA+ output quality |
| `recommendations.md` | Next-step options for this repository |
| `gaps_and_risks.md` | Known unknowns, blockers, research risks |
| `references.md` | Normalized bibliography and links |
| `artifacts/papers_screened.csv` | Paper screening log |
| `artifacts/repos_screened.csv` | Repo/tool screening log |
| `artifacts/comparison_matrix.csv` | Machine-readable comparison table |
| `artifacts/evidence_checklist.md` | Completeness checklist for all deliverables |
