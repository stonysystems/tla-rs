# Tooling Landscape: Practical Tools and Components

Practical tools, repositories, and components that may be reusable in a future text-to-TLA+ pipeline.

## Evaluation Criteria

For each tool/repo, we document:
- **License**: Open-source license type
- **Maintenance status**: Last commit / recent activity
- **Install friction**: Dependencies, platform requirements
- **API/CLI availability**: Programmatic interface
- **CI scriptability**: Whether it can be automated in CI pipelines
- **Likely role**: Where it fits in a `text -> TLA+` workflow

## TLA+ Syntax and Semantic Tools

### Parsers and AST Libraries

*(Tools for parsing, manipulating, and pretty-printing TLA+ modules.)*

### Model Checkers

*(TLC, Apalache, and other tools that can provide verification feedback.)*

### Trace and Counterexample Tools

*(Tools for working with TLC traces, counterexample visualization, etc.)*

## Benchmark and Corpora

*(TLA+ specification corpora, benchmark suites, and datasets that can serve as training data, evaluation references, or few-shot examples.)*

## LLM Infrastructure

*(Relevant LLM tooling for constrained generation, structured output, and formal-language-aware prompting.)*

## Integration Notes

*(For each tool, notes on speculative vs. demonstrated reuse. Speculative reuse is explicitly labeled.)*
