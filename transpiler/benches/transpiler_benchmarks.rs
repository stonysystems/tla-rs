//! Performance benchmarks for the Verus transpiler.
//!
//! Run with: cargo bench

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use verus_transpiler::annotation::AnnotationParser;
use verus_transpiler::moder::ModeAnalyzer;
use verus_transpiler::parser::VerusParser;
use verus_transpiler::templates::match_expression;
use verus_transpiler::translator::{Translator, TranslatorConfig};

/// Simple spec function for benchmarking
const SIMPLE_SPEC: &str = r#"
verus! {
    pub open spec fn SimpleInit(s: LState, s_: LState) -> bool {
        s_.value == 0
    }
}
"#;

/// Medium complexity spec function with conditional
const MEDIUM_SPEC: &str = r#"
verus! {
    pub open spec fn MediumProcess(
        s: LState,
        s_: LState,
        inp: LInput,
        out: LOutput
    ) -> bool {
        if inp.kind == 1 {
            &&& s_.value == s.value + inp.delta
            &&& out.result == true
        } else {
            &&& s_ == s
            &&& out.result == false
        }
    }
}
"#;

/// Complex spec function with nested conditionals and multiple fields
const COMPLEX_SPEC: &str = r#"
verus! {
    pub open spec fn ComplexProcess(
        s: LReplica,
        s_: LReplica,
        inp: LPacket,
        sent_packets: Seq<LPacket>
    ) -> bool {
        let msg = inp.msg;
        if msg.kind == 1 {
            if s.counter < msg.threshold {
                &&& s_.counter == s.counter + 1
                &&& s_.votes == s.votes
                &&& s_.max_bal == msg.ballot
                &&& sent_packets == seq![make_reply(s, msg)]
            } else {
                &&& s_ == s
                &&& sent_packets == Seq::empty()
            }
        } else if msg.kind == 2 {
            &&& s_.counter == 0
            &&& s_.votes == Seq::empty()
            &&& s_.max_bal == s.max_bal
            &&& sent_packets == seq![make_ack(s)]
        } else {
            &&& s_ == s
            &&& sent_packets == Seq::empty()
        }
    }
}
"#;

/// Annotation for simple spec
const SIMPLE_ANNOTATION: &str = r#"
module Test {
    SimpleInit(+, -);
}
"#;

/// Annotation for medium spec
const MEDIUM_ANNOTATION: &str = r#"
module Test {
    MediumProcess(+, -, +, -);
}
"#;

fn bench_parser(c: &mut Criterion) {
    let mut group = c.benchmark_group("parser");

    group.bench_function("simple_spec", |b| {
        b.iter(|| {
            let parser = VerusParser::new(black_box(SIMPLE_SPEC.to_string()));
            parser.parse_spec_functions()
        })
    });

    group.bench_function("medium_spec", |b| {
        b.iter(|| {
            let parser = VerusParser::new(black_box(MEDIUM_SPEC.to_string()));
            parser.parse_spec_functions()
        })
    });

    group.bench_function("complex_spec", |b| {
        b.iter(|| {
            let parser = VerusParser::new(black_box(COMPLEX_SPEC.to_string()));
            parser.parse_spec_functions()
        })
    });

    group.finish();
}

fn bench_annotation_parser(c: &mut Criterion) {
    let mut group = c.benchmark_group("annotation_parser");

    group.bench_function("simple", |b| {
        b.iter(|| {
            let parser = AnnotationParser::new(black_box(SIMPLE_ANNOTATION.to_string()));
            parser.parse()
        })
    });

    group.bench_function("medium", |b| {
        b.iter(|| {
            let parser = AnnotationParser::new(black_box(MEDIUM_ANNOTATION.to_string()));
            parser.parse()
        })
    });

    // Larger annotation file simulation
    let large_annotation = (0..50)
        .map(|i| format!("    Function{}(+, -, +, -);", i))
        .collect::<Vec<_>>()
        .join("\n");
    let large_annotation = format!("module LargeModule {{\n{}\n}}", large_annotation);

    group.bench_function("large_50_functions", |b| {
        let annotation = large_annotation.clone();
        b.iter(|| {
            let parser = AnnotationParser::new(black_box(annotation.clone()));
            parser.parse()
        })
    });

    group.finish();
}

fn bench_mode_analyzer(c: &mut Criterion) {
    let mut group = c.benchmark_group("mode_analyzer");

    // Parse specs once
    let parser = VerusParser::new(SIMPLE_SPEC.to_string());
    let simple_funcs = parser.parse_spec_functions().unwrap();

    let parser = VerusParser::new(MEDIUM_SPEC.to_string());
    let medium_funcs = parser.parse_spec_functions().unwrap();

    // Parse annotations
    let simple_parser = AnnotationParser::new(SIMPLE_ANNOTATION.to_string());
    let simple_annotations = simple_parser.parse().unwrap();
    let medium_parser = AnnotationParser::new(MEDIUM_ANNOTATION.to_string());
    let medium_annotations = medium_parser.parse().unwrap();

    // Get function annotations from the parsed module
    let simple_fn_ann = simple_annotations[0]
        .functions
        .get("SimpleInit")
        .cloned()
        .unwrap();
    let medium_fn_ann = medium_annotations[0]
        .functions
        .get("MediumProcess")
        .cloned()
        .unwrap();

    group.bench_function("annotate_simple", |b| {
        b.iter(|| {
            let mut analyzer = ModeAnalyzer::new();
            analyzer.annotate(
                black_box(simple_funcs[0].clone()),
                black_box(&simple_fn_ann),
            )
        })
    });

    group.bench_function("annotate_medium", |b| {
        b.iter(|| {
            let mut analyzer = ModeAnalyzer::new();
            analyzer.annotate(
                black_box(medium_funcs[0].clone()),
                black_box(&medium_fn_ann),
            )
        })
    });

    group.finish();
}

fn bench_template_matcher(c: &mut Criterion) {
    let mut group = c.benchmark_group("template_matcher");

    // Parse specs and get expressions for matching
    let parser = VerusParser::new(MEDIUM_SPEC.to_string());
    let medium_funcs = parser.parse_spec_functions().unwrap();

    let parser = VerusParser::new(COMPLEX_SPEC.to_string());
    let complex_funcs = parser.parse_spec_functions().unwrap();

    group.bench_function("match_medium_expr", |b| {
        let outputs = vec!["s_".to_string()];
        b.iter(|| match_expression(black_box(&medium_funcs[0].body), black_box(&outputs)))
    });

    group.bench_function("match_complex_expr", |b| {
        let outputs = vec!["s_".to_string(), "sent_packets".to_string()];
        b.iter(|| match_expression(black_box(&complex_funcs[0].body), black_box(&outputs)))
    });

    group.finish();
}

fn bench_translator(c: &mut Criterion) {
    let mut group = c.benchmark_group("translator");

    let config = TranslatorConfig::default();

    // Parse and annotate specs
    let parser = VerusParser::new(SIMPLE_SPEC.to_string());
    let simple_funcs = parser.parse_spec_functions().unwrap();
    let simple_parser = AnnotationParser::new(SIMPLE_ANNOTATION.to_string());
    let simple_annotations = simple_parser.parse().unwrap();

    let parser = VerusParser::new(MEDIUM_SPEC.to_string());
    let medium_funcs = parser.parse_spec_functions().unwrap();
    let medium_parser = AnnotationParser::new(MEDIUM_ANNOTATION.to_string());
    let medium_annotations = medium_parser.parse().unwrap();

    // Get function annotations
    let simple_fn_ann = simple_annotations[0]
        .functions
        .get("SimpleInit")
        .cloned()
        .unwrap();
    let medium_fn_ann = medium_annotations[0]
        .functions
        .get("MediumProcess")
        .cloned()
        .unwrap();

    // Create annotated functions
    let mut analyzer = ModeAnalyzer::new();
    let simple_annotated = analyzer
        .annotate(simple_funcs[0].clone(), &simple_fn_ann)
        .unwrap();
    let mut analyzer = ModeAnalyzer::new();
    let medium_annotated = analyzer
        .annotate(medium_funcs[0].clone(), &medium_fn_ann)
        .unwrap();

    group.bench_function("translate_simple", |b| {
        let translator = Translator::new(config.clone());
        b.iter(|| translator.translate(black_box(&simple_annotated)))
    });

    group.bench_function("translate_medium", |b| {
        let translator = Translator::new(config.clone());
        b.iter(|| translator.translate(black_box(&medium_annotated)))
    });

    group.finish();
}

fn bench_full_pipeline(c: &mut Criterion) {
    let mut group = c.benchmark_group("full_pipeline");

    // Measure throughput in bytes
    group.throughput(Throughput::Bytes(MEDIUM_SPEC.len() as u64));

    group.bench_function("parse_annotate_translate", |b| {
        let config = TranslatorConfig::default();

        b.iter(|| {
            // Parse spec
            let parser = VerusParser::new(black_box(MEDIUM_SPEC.to_string()));
            let funcs = parser.parse_spec_functions().unwrap();

            // Parse annotations
            let ann_parser = AnnotationParser::new(black_box(MEDIUM_ANNOTATION.to_string()));
            let annotations = ann_parser.parse().unwrap();
            let fn_ann = annotations[0]
                .functions
                .get("MediumProcess")
                .cloned()
                .unwrap();

            // Annotate
            let mut analyzer = ModeAnalyzer::new();
            let annotated = analyzer.annotate(funcs[0].clone(), &fn_ann).unwrap();

            // Translate
            let translator = Translator::new(config.clone());
            translator.translate(black_box(&annotated))
        })
    });

    group.finish();
}

fn bench_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("scaling");

    // Generate specs of varying sizes
    for size in [1, 5, 10, 20].iter() {
        let spec = generate_spec_with_n_fields(*size);

        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::new("parse", size), &spec, |b, spec| {
            b.iter(|| {
                let parser = VerusParser::new(black_box(spec.clone()));
                parser.parse_spec_functions()
            })
        });
    }

    group.finish();
}

/// Generate a spec function with n field assignments
fn generate_spec_with_n_fields(n: usize) -> String {
    let field_assignments: Vec<String> = (0..n)
        .map(|i| format!("        &&& s_.field{} == s.field{} + 1", i, i))
        .collect();

    format!(
        r#"
verus! {{
    pub open spec fn GeneratedSpec(s: LState, s_: LState) -> bool {{
{}
    }}
}}
"#,
        field_assignments.join("\n")
    )
}

fn bench_set_repr(c: &mut Criterion) {
    use std::collections::BTreeSet;
    use std::sync::Arc;
    use verus_transpiler::modelcheck::small_int_set::SmallIntSet;
    use verus_transpiler::modelcheck::value::{RuntimeValue, SetRepr};

    let mut group = c.benchmark_group("set_repr");

    // Typical Paxos quorum sizes
    for &size in &[4u64, 6, 8] {
        let ints: Vec<i128> = (0..size as i128).collect();
        let values: Vec<RuntimeValue> = ints.iter().map(|&n| RuntimeValue::Int(n)).collect();

        // Construction: from_values (auto-promotes to SmallInt)
        group.bench_with_input(
            BenchmarkId::new("from_values_auto", size),
            &values,
            |b, vals| {
                b.iter(|| SetRepr::from_values(black_box(vals.clone())))
            },
        );

        // Construction: BTreeSet baseline
        group.bench_with_input(
            BenchmarkId::new("btreeset_collect", size),
            &values,
            |b, vals| {
                b.iter(|| {
                    let set: BTreeSet<RuntimeValue> = black_box(vals.clone()).into_iter().collect();
                    set
                })
            },
        );

        // Contains lookup
        let small_repr = SetRepr::from_values(values.clone());
        let general_repr = SetRepr::General(values.iter().cloned().collect());
        let lookup_val = RuntimeValue::Int(size as i128 / 2);

        group.bench_with_input(
            BenchmarkId::new("contains_smallint", size),
            &(&small_repr, &lookup_val),
            |b, &(repr, val)| {
                b.iter(|| repr.contains(black_box(val)))
            },
        );

        group.bench_with_input(
            BenchmarkId::new("contains_general", size),
            &(&general_repr, &lookup_val),
            |b, &(repr, val)| {
                b.iter(|| repr.contains(black_box(val)))
            },
        );

        // Union of two sets
        let half = size as i128 / 2;
        let set_a = SetRepr::from_values((0..half).map(RuntimeValue::Int));
        let set_b = SetRepr::from_values((half..size as i128).map(RuntimeValue::Int));
        let gen_a = SetRepr::General((0..half).map(RuntimeValue::Int).collect());
        let gen_b = SetRepr::General((half..size as i128).map(RuntimeValue::Int).collect());

        group.bench_with_input(
            BenchmarkId::new("union_smallint", size),
            &(&set_a, &set_b),
            |b, &(a, bb)| {
                b.iter(|| a.union(black_box(bb)))
            },
        );

        group.bench_with_input(
            BenchmarkId::new("union_general", size),
            &(&gen_a, &gen_b),
            |b, &(a, bb)| {
                b.iter(|| a.union(black_box(bb)))
            },
        );

        // Iteration
        group.bench_with_input(
            BenchmarkId::new("iter_smallint", size),
            &small_repr,
            |b, repr| {
                b.iter(|| {
                    let mut sum = 0i128;
                    for v in black_box(repr).iter() {
                        if let RuntimeValue::Int(n) = v {
                            sum += n;
                        }
                    }
                    sum
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("iter_general", size),
            &general_repr,
            |b, repr| {
                b.iter(|| {
                    let mut sum = 0i128;
                    for v in black_box(repr).iter() {
                        if let RuntimeValue::Int(n) = v {
                            sum += n;
                        }
                    }
                    sum
                })
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_parser,
    bench_annotation_parser,
    bench_mode_analyzer,
    bench_template_matcher,
    bench_translator,
    bench_full_pipeline,
    bench_scaling,
    bench_set_repr,
);
criterion_main!(benches);
