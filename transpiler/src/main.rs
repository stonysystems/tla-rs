//! CLI entry point for the Verus transpiler.
//!
//! Usage:
//! ```bash
//! # Single file mode (Verus spec to exec)
//! verus-transpile \
//!     --input src/protocol/RSL/acceptor.rs \
//!     --annotations src/protocol/RSL/acceptor.automan \
//!     --config transpile.toml \
//!     --output src/implementation/RSL/acceptor_gen.rs
//!
//! # Batch mode
//! verus-transpile --project . --output-dir src/generated/
//!
//! # TLA+ to Verus translation (T7.1)
//! verus-transpile translate-tla --input spec.tla --output spec.rs
//!
//! # Full pipeline: TLA+ → Verus spec → Verus exec (T7.2)
//! verus-transpile pipeline --tla-input spec.tla --exec-output impl.rs
//!
//! # List supported templates
//! verus-transpile --list-templates
//! ```

use clap::{Parser, Subcommand};
use miette::Result;
use serde::Serialize;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use verus_transpiler::annotation::parse_annotation_file;
use verus_transpiler::spec_analyzer::{
    analyze_spec_file, analyze_spec_files, merge_configs, ConfigInferer, SpecSchema,
};
use verus_transpiler::{FileConfig, TranslatorConfig, Transpiler, TranspilerConfig};

#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
enum CliSearchMode {
    Bfs,
    Dfs,
    /// Phase 38.18.10: invoke the DPOR sleep-set explorer (relocated
    /// from the prototype crate `dpor-checker` into
    /// `transpiler/src/modelcheck/dpor/`). Reduces transition count
    /// and reachable distinct-state count substantially on protocols
    /// with concurrent independent actions (e.g. Paxos 8/5: BFS finds
    /// 6,033 states / 206 s; this strategy finds 153 / 30 s).
    Dpor,
}

impl CliSearchMode {
    fn as_str(self) -> &'static str {
        match self {
            Self::Bfs => "bfs",
            Self::Dfs => "dfs",
            Self::Dpor => "dpor",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
enum CliPacketProjectionMode {
    None,
    AppendSeq,
    ReplaceSeq,
}

impl CliPacketProjectionMode {
    fn as_internal(self) -> verus_transpiler::tla::PacketProjectionMode {
        use verus_transpiler::tla::PacketProjectionMode;
        match self {
            Self::None => PacketProjectionMode::None,
            Self::AppendSeq => PacketProjectionMode::AppendSeq,
            Self::ReplaceSeq => PacketProjectionMode::ReplaceSeq,
        }
    }
}

/// Verus Spec-to-Implementation Transpiler
///
/// Transforms Verus spec functions into verified exec implementations
/// with proof linkage to the original specifications.
#[derive(Parser, Debug)]
#[command(name = "verus-transpile")]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,

    /// Input Verus spec file (.rs)
    #[arg(short, long)]
    input: Option<PathBuf>,

    /// Annotation file (.automan) with mode specifications
    #[arg(short, long)]
    annotations: Option<PathBuf>,

    /// Output file for generated exec code
    #[arg(short, long)]
    output: Option<PathBuf>,

    /// Configuration file (TOML)
    #[arg(short, long)]
    config: Option<PathBuf>,

    /// Project directory for batch processing
    #[arg(long)]
    project: Option<PathBuf>,

    /// Output directory for batch mode
    #[arg(long)]
    output_dir: Option<PathBuf>,

    /// Print output to stdout instead of file
    #[arg(long)]
    stdout: bool,

    /// Verbose output
    #[arg(short, long)]
    verbose: bool,

    /// Dry run - show what would be generated without writing
    #[arg(long)]
    dry_run: bool,

    /// Auto-skip mode: catch transpilation errors per-function and continue.
    /// Skipped functions are reported to stderr. Use with --verbose for details.
    #[arg(long)]
    auto_skip: bool,

    /// Proof-fallback mode: instead of skipping untranslatable functions,
    /// emit them as #[verifier(external_body)] stubs. Implies --auto-skip.
    #[arg(long)]
    proof_fallback: bool,

    /// Dump the fully-resolved configuration (auto-derived + TOML overrides) as TOML.
    /// Useful for debugging what config the transpiler will use.
    #[arg(long)]
    dump_config: bool,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// List supported quantifier templates
    ListTemplates,

    /// Check annotation file for errors
    Check {
        /// Annotation file to check
        #[arg(short, long)]
        annotations: PathBuf,
    },

    /// Load model.toml, apply CLI overrides for key limits/domains, and print
    /// the resolved model config.
    ModelConfig {
        /// Input model-check config (model.toml)
        #[arg(long)]
        model: PathBuf,

        /// Override [search].max_depth
        #[arg(long)]
        max_depth: Option<usize>,

        /// Override [search].max_states
        #[arg(long)]
        max_states: Option<usize>,

        /// Override [search].timeout_ms
        #[arg(long)]
        timeout_ms: Option<u64>,

        /// Override [collections].max_seq_len
        #[arg(long)]
        max_seq_len: Option<usize>,

        /// Override [collections].max_set_len
        #[arg(long)]
        max_set_len: Option<usize>,

        /// Override [collections].max_map_len
        #[arg(long)]
        max_map_len: Option<usize>,

        /// Override quantifier int domain as MIN..MAX (or MIN:MAX)
        #[arg(long, value_name = "MIN..MAX", allow_hyphen_values = true)]
        int_range: Option<String>,

        /// Override [quantifiers.nat].max
        #[arg(long)]
        nat_max: Option<u64>,

        /// Override [search].candidate_eval_guardrail
        #[arg(long)]
        candidate_eval_guardrail: Option<usize>,
    },

    /// Run source-first model checking for one protocol spec.
    ///
    /// This command:
    /// - ingests protocol sources (`types.rs` + protocol file),
    /// - validates required entrypoints (`LInit`, `LNext`),
    /// - parses/validates `model.toml`,
    /// - resolves configured invariants,
    /// - performs bounded BFS/DFS exploration,
    /// - reports summary metrics (states, transitions, depth, elapsed, result).
    ModelCheck {
        /// Protocol spec file (e.g., src/protocol/TwoPhase/twophase.rs)
        #[arg(long)]
        input: PathBuf,

        /// Optional explicit types spec file (defaults to sibling types.rs)
        #[arg(long)]
        types: Option<PathBuf>,

        /// Init entrypoint function name (default: LInit)
        #[arg(long, default_value = "LInit")]
        init: String,

        /// Next entrypoint function name (default: LNext)
        #[arg(long, default_value = "LNext")]
        next: String,

        /// Invariant name override (repeatable). If provided, overrides
        /// `properties.invariants` from model.toml.
        #[arg(long, action = clap::ArgAction::Append)]
        invariant: Vec<String>,

        /// Search strategy override (default: bfs)
        #[arg(long, value_enum)]
        search: Option<CliSearchMode>,

        /// Override [search].max_depth
        #[arg(long)]
        max_depth: Option<usize>,

        /// Override [search].max_states
        #[arg(long)]
        max_states: Option<usize>,

        /// Override [search].timeout_ms (milliseconds)
        #[arg(long = "timeout", alias = "timeout-ms")]
        timeout_ms: Option<u64>,

        /// Emit machine-readable JSON model-check report
        #[arg(long)]
        json_report: bool,

        /// Export parity JSONL files (states + edges) to the given directory.
        /// Used for cross-engine state-set comparison (Phase 36.1).
        #[arg(long)]
        export_parity: Option<PathBuf>,

        /// Export streaming debug JSONL files during exploration (Phase 36.1.7).
        /// Writes generated_states.jsonl, distinct_states.jsonl, and edges.jsonl
        /// with per-state provenance (predecessor, branch_label, classification).
        #[arg(long)]
        export_parity_debug: Option<PathBuf>,

        /// Model-check config (model.toml)
        #[arg(long)]
        model: PathBuf,

        /// Disable bytecode VM and fall back to AST interpreter for expression
        /// evaluation. By default, the bytecode VM is enabled (compiles
        /// expressions on first use and caches the result for ~2x speedup).
        #[arg(long)]
        no_bytecode: bool,

        /// Enable native codegen (opt-in). Compiles spec expressions to
        /// native cdylibs via rustc for ~100-200x speedup over AST
        /// interpretation. Adds startup latency for initial compilation.
        /// Requires `transpiler-runtime` rlib to be buildable.
        #[arg(long)]
        native_codegen: bool,

        /// Number of parallel worker threads for exploration.
        /// Default 1 (sequential). When >1: BFS uses level-synchronous
        /// parallel BFS with rayon; DPOR collects frontier states at
        /// depth 2 then dispatches to worker threads via std::thread::scope.
        #[arg(long, default_value_t = 1)]
        workers: usize,

        /// Emit a conflict profile report to stderr after DPOR exploration.
        /// Shows which field pairs cause the most independence check failures,
        /// ranked by frequency, with suggestions for keyed-path refinement.
        /// Only meaningful with `--search dpor` (ignored for BFS/DFS).
        #[arg(long)]
        conflict_profile: bool,
    },

    /// Emit a machine-readable JSON report of `assume(...)` sites in generated files.
    ///
    /// Intended for tracking deferred proof gaps in generated RSL modules.
    ReportAssumes {
        /// Directory containing generated modules (typically `src/generated/RSL`)
        #[arg(long, default_value = "src/generated/RSL")]
        input_dir: PathBuf,

        /// Optional output path for JSON report (defaults to stdout)
        #[arg(long)]
        output: Option<PathBuf>,
    },

    /// Generate a generic TLC wrapper from a relational TLA+ module (`Init/Next`).
    ///
    /// Produces `<module><suffix>.tla` and a matching `.cfg` skeleton.
    GenerateMcWrapper {
        /// Input relational TLA+ module
        #[arg(long)]
        input: PathBuf,

        /// Output wrapper file (.tla)
        #[arg(long)]
        output: PathBuf,

        /// Optional explicit cfg output path (defaults to output with .cfg extension)
        #[arg(long)]
        cfg_output: Option<PathBuf>,

        /// Init operator name (default: Init)
        #[arg(long, default_value = "Init")]
        init: String,

        /// Next operator name (default: Next)
        #[arg(long, default_value = "Next")]
        next: String,

        /// Wrapper module suffix (default: _MC)
        #[arg(long, default_value = "_MC")]
        module_suffix: String,

        /// Packet projection mode for relational `sent_packets`-style branches.
        #[arg(long, value_enum, default_value = "none")]
        packet_mode: CliPacketProjectionMode,

        /// Packet variable name used in Next-branch quantifiers.
        #[arg(long, default_value = "sent_packets")]
        packet_var: String,

        /// Invariant names to include in generated cfg (repeatable)
        #[arg(long, action = clap::ArgAction::Append)]
        invariant: Vec<String>,
    },

    /// Generate type definitions from spec types
    GenerateTypes {
        /// Input spec file(s) - can be specified multiple times for multi-file generation.
        /// Files are processed in the order provided (use dependency order).
        #[arg(short, long, action = clap::ArgAction::Append)]
        input: Vec<PathBuf>,

        /// Output file
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Configuration file (TOML) with type remappings
        #[arg(short, long)]
        config: Option<PathBuf>,
    },

    /// Translate TLA+ specification to Verus code (T7.1)
    TranslateTla {
        /// Input TLA+ file (.tla)
        #[arg(short, long)]
        input: PathBuf,

        /// Output Verus file (.rs)
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Type annotations file (.tla-types)
        #[arg(short, long)]
        types: Option<PathBuf>,

        /// Generate mode annotations file (.automan) alongside output
        #[arg(long)]
        gen_modes: bool,

        /// Module configuration: spec prefix (default: "L")
        #[arg(long, default_value = "L")]
        spec_prefix: String,

        /// Module configuration: state struct name (default: "State")
        #[arg(long, default_value = "State")]
        state_name: String,
    },

    /// Convert Verus spec to TLA+ (verus2tla)
    Verus2Tla {
        /// Input Verus spec file (.rs) or directory for batch mode
        #[arg(short, long)]
        input: PathBuf,

        /// Output TLA+ file (.tla) or directory for batch mode
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Spec prefix to strip from names (default: "L")
        #[arg(long, default_value = "L")]
        spec_prefix: String,

        /// Include recommends as ASSUME statements
        #[arg(long)]
        include_recommends: bool,

        /// Generate type definitions (default: true)
        #[arg(long, default_value = "true")]
        generate_types: bool,

        /// Batch mode: process all .rs files in the input directory
        #[arg(long)]
        batch: bool,
    },

    /// Full pipeline: TLA+ → Verus spec → Verus exec (T7.2)
    Pipeline {
        /// Input TLA+ file (.tla)
        #[arg(long)]
        tla_input: PathBuf,

        /// Output Verus exec file (.rs)
        #[arg(long)]
        exec_output: PathBuf,

        /// Type annotations file (.tla-types) for TLA+ type hints
        #[arg(long)]
        types: Option<PathBuf>,

        /// Keep intermediate files (spec.rs, spec.automan)
        #[arg(long)]
        keep_intermediate: bool,

        /// Intermediate spec output file (default: derived from exec_output)
        #[arg(long)]
        spec_output: Option<PathBuf>,

        /// Module configuration: spec prefix (default: "L")
        #[arg(long, default_value = "L")]
        spec_prefix: String,

        /// Module configuration: exec prefix (default: "C")
        #[arg(long, default_value = "C")]
        exec_prefix: String,

        /// Module configuration: state struct name (default: "State")
        #[arg(long, default_value = "State")]
        state_name: String,

        /// Configuration file (TOML) for transpiler settings
        #[arg(short, long)]
        config: Option<PathBuf>,
    },

    /// Generate ProtocolMessage impl from config
    GenerateMessages {
        /// Configuration file (TOML) with [messages] section
        #[arg(short, long)]
        config: PathBuf,

        /// Output file (message.rs)
        #[arg(short, long)]
        output: Option<PathBuf>,
    },

    /// Generate Marshalable impls for struct types from config
    GenerateMarshalable {
        /// Configuration file (TOML) with [marshalable] section
        #[arg(short, long)]
        config: PathBuf,

        /// Output file (marshalable_gen.rs)
        #[arg(short, long)]
        output: Option<PathBuf>,
    },

    /// Analyze LNext function to extract scheduler action structure
    AnalyzeLnext {
        /// Spec file containing LNext function (e.g., src/protocol/Paxos/paxos.rs)
        #[arg(short, long)]
        input: PathBuf,

        /// Optional TOML config with [messages] section for action classification
        #[arg(short, long)]
        config: Option<PathBuf>,

        /// Name of the Next function (default: "LNext")
        #[arg(long, default_value = "LNext")]
        next_fn: String,

        /// Spec function name prefix (default: "L")
        #[arg(long, default_value = "L")]
        spec_prefix: String,

        /// Exec function name prefix (default: "C")
        #[arg(long, default_value = "C")]
        exec_prefix: String,

        /// Output file for TOML config (prints to stdout if not specified)
        #[arg(short, long)]
        output: Option<PathBuf>,
    },

    /// Generate host.rs scaffold from protocol config
    GenerateHost {
        /// Configuration file (TOML) with [messages] and [scheduler] sections
        #[arg(short, long)]
        config: PathBuf,

        /// Protocol name in PascalCase (e.g., "Paxos")
        #[arg(short, long)]
        protocol: String,

        /// Generated module name (e.g., "paxos_gen"). Defaults to "<module>_gen"
        #[arg(long)]
        gen_module: Option<String>,

        /// Output file (host.rs). Prints to stdout if not specified
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
}

fn strip_spec_prefix<'a>(name: &'a str, spec_prefix: &str) -> &'a str {
    if let Some(rest) = name.strip_prefix(spec_prefix) {
        if rest.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
            return rest;
        }
    }
    name
}

fn has_uppercase_prefixed_name(name: &str, prefix: &str) -> bool {
    if !name.starts_with(prefix) {
        return false;
    }
    name[prefix.len()..]
        .chars()
        .next()
        .is_some_and(|c| c.is_ascii_uppercase())
}

fn collect_called_functions_from_expr(expr: &verus_transpiler::Expr, out: &mut HashSet<String>) {
    use verus_transpiler::Expr;

    match expr {
        Expr::Call { func, args } => {
            if func.segments.len() == 1 {
                out.insert(func.segments[0].clone());
            }
            for arg in args {
                collect_called_functions_from_expr(arg, out);
            }
        }
        Expr::MethodCall { receiver, args, .. } => {
            collect_called_functions_from_expr(receiver, out);
            for arg in args {
                collect_called_functions_from_expr(arg, out);
            }
        }
        Expr::Conjunction(parts)
        | Expr::Disjunction(parts)
        | Expr::SeqLit(parts)
        | Expr::SetLit(parts) => {
            for part in parts {
                collect_called_functions_from_expr(part, out);
            }
        }
        Expr::MapLit(entries) => {
            for (k, v) in entries {
                collect_called_functions_from_expr(k, out);
                collect_called_functions_from_expr(v, out);
            }
        }
        Expr::Binary(lhs, _, rhs)
        | Expr::Eq(lhs, rhs)
        | Expr::Ne(lhs, rhs)
        | Expr::Lt(lhs, rhs)
        | Expr::Le(lhs, rhs)
        | Expr::Gt(lhs, rhs)
        | Expr::Ge(lhs, rhs)
        | Expr::Implies(lhs, rhs)
        | Expr::Iff(lhs, rhs)
        | Expr::Index(lhs, rhs) => {
            collect_called_functions_from_expr(lhs, out);
            collect_called_functions_from_expr(rhs, out);
        }
        Expr::Not(inner)
        | Expr::Field(inner, _)
        | Expr::Arrow(inner, _)
        | Expr::View(inner)
        | Expr::Cast(inner, _)
        | Expr::Unary(_, inner)
        | Expr::Is(inner, _) => collect_called_functions_from_expr(inner, out),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_called_functions_from_expr(cond, out);
            collect_called_functions_from_expr(then_branch, out);
            if let Some(e) = else_branch {
                collect_called_functions_from_expr(e, out);
            }
        }
        Expr::Match { scrutinee, arms } => {
            collect_called_functions_from_expr(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_called_functions_from_expr(guard, out);
                }
                collect_called_functions_from_expr(&arm.body, out);
            }
        }
        Expr::Let { value, body, .. } => {
            collect_called_functions_from_expr(value, out);
            collect_called_functions_from_expr(body, out);
        }
        Expr::Forall { triggers, body, .. } => {
            for trigger in triggers {
                for expr in &trigger.exprs {
                    collect_called_functions_from_expr(expr, out);
                }
            }
            collect_called_functions_from_expr(body, out);
        }
        Expr::Exists { body, .. } | Expr::Closure { body, .. } | Expr::Choose { body, .. } => {
            collect_called_functions_from_expr(body, out);
        }
        Expr::Struct { fields, .. } => {
            for (_, value) in fields {
                collect_called_functions_from_expr(value, out);
            }
        }
        Expr::StructUpdate { base, fields, .. } => {
            collect_called_functions_from_expr(base, out);
            for (_, value) in fields {
                collect_called_functions_from_expr(value, out);
            }
        }
        Expr::SeqEmpty
        | Expr::SetEmpty
        | Expr::MapEmpty
        | Expr::Ident(_)
        | Expr::Literal(_)
        | Expr::ConstantValue(_) => {}
    }
}

fn collect_called_functions_from_spec_file(spec_file: &Path) -> HashSet<String> {
    let mut called = HashSet::new();
    let Ok(spec_functions) = verus_transpiler::parse_file(spec_file) else {
        return called;
    };

    for spec_fn in &spec_functions {
        for req in &spec_fn.requires {
            collect_called_functions_from_expr(req, &mut called);
        }
        for ens in &spec_fn.ensures {
            collect_called_functions_from_expr(ens, &mut called);
        }
        for rec in &spec_fn.recommends {
            collect_called_functions_from_expr(rec, &mut called);
        }
        for dec in &spec_fn.decreases {
            collect_called_functions_from_expr(dec, &mut called);
        }
        collect_called_functions_from_expr(&spec_fn.body, &mut called);
    }

    called
}

fn extract_c_function_name(line: &str) -> Option<String> {
    let idx = line.find("fn C")?;
    let rest = &line[idx + 3..];
    let mut chars = rest.chars();
    if chars.next()? != 'C' {
        return None;
    }
    let mut name = String::from("C");
    for ch in chars {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            name.push(ch);
        } else {
            break;
        }
    }
    if name.chars().nth(1).is_some_and(|c| c.is_ascii_uppercase()) {
        Some(name)
    } else {
        None
    }
}

fn extract_prefixed_function_name(line: &str, prefix: &str) -> Option<String> {
    let needle = format!("fn {}", prefix);
    let idx = line.find(&needle)?;
    let rest = &line[idx + 3..];
    if !rest.starts_with(prefix) {
        return None;
    }
    let mut name = String::new();
    for ch in rest.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            name.push(ch);
        } else {
            break;
        }
    }
    if name.starts_with(prefix) && name.len() > prefix.len() {
        Some(name)
    } else {
        None
    }
}

fn insert_symbol(symbols: &mut HashMap<String, Vec<String>>, name: String, path: String) {
    let entry = symbols.entry(name).or_default();
    if !entry.contains(&path) {
        entry.push(path);
    }
}

fn collect_generated_symbols(
    protocol_name: &str,
    generated_dir: &Path,
    symbols: &mut HashMap<String, Vec<String>>,
) {
    if !generated_dir.exists() {
        return;
    }

    let Ok(entries) = std::fs::read_dir(generated_dir) else {
        return;
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("rs") {
            continue;
        }
        let Some(module_name) = path.file_stem().and_then(|s| s.to_str()) else {
            continue;
        };
        let Ok(content) = std::fs::read_to_string(&path) else {
            continue;
        };

        for line in content.lines() {
            let code = line.split("//").next().unwrap_or("").trim();
            if let Some(func) = extract_c_function_name(code) {
                let symbol_path = format!(
                    "crate::generated::{}::{}::{}",
                    protocol_name, module_name, func
                );
                insert_symbol(symbols, func, symbol_path);
            }
        }
    }
}

fn parse_impl_type(line: &str) -> Option<String> {
    if !line.starts_with("impl ") {
        return None;
    }
    let rest = line.trim_start_matches("impl ").trim_start();
    if rest.starts_with('<') {
        return None;
    }
    let ty: String = rest
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect();
    if ty.starts_with('C') && ty.len() > 1 {
        Some(ty)
    } else {
        None
    }
}

fn count_braces(line: &str) -> (i32, i32) {
    let opens = line.chars().filter(|c| *c == '{').count() as i32;
    let closes = line.chars().filter(|c| *c == '}').count() as i32;
    (opens, closes)
}

fn collect_implementation_symbols(
    implementation_dir: &Path,
    symbols: &mut HashMap<String, Vec<String>>,
) {
    if !implementation_dir.exists() {
        return;
    }

    let Ok(entries) = std::fs::read_dir(implementation_dir) else {
        return;
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("rs") {
            continue;
        }
        let Ok(content) = std::fs::read_to_string(&path) else {
            continue;
        };

        let mut brace_depth: i32 = 0;
        let mut impl_stack: Vec<(i32, String)> = Vec::new();

        for line in content.lines() {
            let code = line.split("//").next().unwrap_or("").trim();
            if code.is_empty() {
                continue;
            }

            if code.starts_with("impl ") && code.contains('{') {
                if let Some(impl_ty) = parse_impl_type(code) {
                    impl_stack.push((brace_depth + 1, impl_ty));
                }
            }

            if let Some(func) = extract_c_function_name(code) {
                let current_impl = impl_stack
                    .iter()
                    .rev()
                    .find(|(depth, _)| brace_depth >= *depth)
                    .map(|(_, ty)| ty.clone());
                let symbol_path = if let Some(impl_ty) = current_impl {
                    format!("{}::{}", impl_ty, func)
                } else {
                    func.clone()
                };
                insert_symbol(symbols, func, symbol_path);
            }

            let (opens, closes) = count_braces(code);
            brace_depth += opens - closes;
            impl_stack.retain(|(depth, _)| brace_depth >= *depth);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ImplementationMethodSymbol {
    impl_type: String,
    tuple_return_types: Option<Vec<String>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EqHelperSymbol {
    function_name: String,
    exec_type: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TypeViewHelperSymbol {
    function_name: String,
    param_exec_type: String,
    spec_type: String,
}

fn insert_method_symbol(
    symbols: &mut HashMap<String, Vec<ImplementationMethodSymbol>>,
    method_name: String,
    symbol: ImplementationMethodSymbol,
) {
    let entry = symbols.entry(method_name).or_default();
    if !entry.contains(&symbol) {
        entry.push(symbol);
    }
}

fn extract_parenthesized_inner(text: &str) -> Option<String> {
    let mut depth: i32 = 0;
    let mut start: Option<usize> = None;
    for (i, ch) in text.char_indices() {
        if ch == '(' {
            depth += 1;
            if depth == 1 {
                start = Some(i + 1);
            }
        } else if ch == ')' {
            depth -= 1;
            if depth == 0 {
                return start.map(|s| text[s..i].to_string());
            }
            if depth < 0 {
                return None;
            }
        }
    }
    None
}

fn split_top_level_csv(text: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut start = 0usize;
    let mut paren_depth: i32 = 0;
    let mut angle_depth: i32 = 0;
    let mut bracket_depth: i32 = 0;
    for (i, ch) in text.char_indices() {
        match ch {
            '(' => paren_depth += 1,
            ')' => paren_depth -= 1,
            '<' => angle_depth += 1,
            '>' => angle_depth -= 1,
            '[' => bracket_depth += 1,
            ']' => bracket_depth -= 1,
            ',' if paren_depth == 0 && angle_depth == 0 && bracket_depth == 0 => {
                parts.push(text[start..i].trim().to_string());
                start = i + 1;
            }
            _ => {}
        }
    }
    let tail = text[start..].trim();
    if !tail.is_empty() {
        parts.push(tail.to_string());
    }
    parts
}

fn parse_tuple_return_types(signature_line: &str) -> Option<Vec<String>> {
    let arrow_idx = signature_line.find("->")?;
    let mut return_part = signature_line[arrow_idx + 2..].trim();
    if let Some(block_idx) = return_part.find('{') {
        return_part = return_part[..block_idx].trim();
    }
    if !return_part.starts_with('(') {
        return None;
    }

    // Parses named return style like `(rc:(bool, usize))` and unnamed `(bool, usize)`.
    let outer = extract_parenthesized_inner(return_part)?;
    let mut tuple_expr = outer.trim();
    if let Some(colon_idx) = tuple_expr.find(':') {
        let (lhs, rhs) = tuple_expr.split_at(colon_idx);
        if lhs.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
            tuple_expr = rhs[1..].trim();
        }
    }
    if !tuple_expr.starts_with('(') {
        return None;
    }
    let inner = extract_parenthesized_inner(tuple_expr)?;
    let elems: Vec<String> = split_top_level_csv(&inner)
        .into_iter()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect();
    if elems.is_empty() {
        None
    } else {
        Some(elems)
    }
}

fn parse_param_exec_type(param: &str) -> Option<String> {
    let (_, raw_ty) = param.split_once(':')?;
    let mut ty = raw_ty.trim();
    while let Some(rest) = ty.strip_prefix('&') {
        ty = rest.trim_start();
    }
    if let Some(rest) = ty.strip_prefix("mut ") {
        ty = rest.trim_start();
    }

    let token: String = ty
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == ':')
        .collect();
    if token.is_empty() {
        return None;
    }
    let base = token.rsplit("::").next()?.to_string();
    if base.starts_with('C') && base.len() > 1 {
        Some(base)
    } else {
        None
    }
}

fn signature_returns_bool(signature_line: &str) -> bool {
    let Some(arrow_idx) = signature_line.find("->") else {
        return false;
    };
    let mut return_part = signature_line[arrow_idx + 2..].trim();
    if let Some(block_idx) = return_part.find('{') {
        return_part = return_part[..block_idx].trim();
    }
    if return_part.starts_with('(') {
        let Some(inner) = extract_parenthesized_inner(return_part) else {
            return false;
        };
        let mut candidate = inner.trim();
        if let Some(colon_idx) = candidate.find(':') {
            let (lhs, rhs) = candidate.split_at(colon_idx);
            if lhs.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
                candidate = rhs[1..].trim();
            }
        }
        is_bool_like_type(candidate)
    } else {
        is_bool_like_type(return_part)
    }
}

fn parse_eq_helper_exec_type(signature_line: &str) -> Option<String> {
    if !signature_returns_bool(signature_line) {
        return None;
    }
    let params_inner = extract_parenthesized_inner(signature_line)?;
    let params = split_top_level_csv(&params_inner);
    if params.len() < 2 {
        return None;
    }
    let lhs = parse_param_exec_type(&params[0])?;
    let rhs = parse_param_exec_type(&params[1])?;
    if lhs == rhs {
        Some(lhs)
    } else {
        None
    }
}

fn parse_return_named_type(signature_line: &str) -> Option<String> {
    let arrow_idx = signature_line.find("->")?;
    let mut return_part = signature_line[arrow_idx + 2..].trim();
    if let Some(block_idx) = return_part.find('{') {
        return_part = return_part[..block_idx].trim();
    }
    if return_part.starts_with('(') {
        return None;
    }
    let token: String = return_part
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == ':')
        .collect();
    if token.is_empty() {
        return None;
    }
    token.rsplit("::").next().map(|s| s.to_string())
}

fn parse_type_view_helper_symbol(signature_line: &str) -> Option<TypeViewHelperSymbol> {
    let function_name = extract_prefixed_function_name(signature_line, "abstractify_")?;
    let params_inner = extract_parenthesized_inner(signature_line)?;
    let params = split_top_level_csv(&params_inner);
    if params.len() != 1 {
        return None;
    }
    let (_, raw_ty) = params[0].split_once(':')?;
    if !raw_ty.trim_start().starts_with('&') {
        return None;
    }
    let param_exec_type = parse_param_exec_type(&params[0])?;
    let spec_type = parse_return_named_type(signature_line)?;
    Some(TypeViewHelperSymbol {
        function_name,
        param_exec_type,
        spec_type,
    })
}

fn collect_implementation_method_symbols(
    implementation_dir: &Path,
) -> HashMap<String, Vec<ImplementationMethodSymbol>> {
    let mut symbols = HashMap::new();
    if !implementation_dir.exists() {
        return symbols;
    }

    let Ok(entries) = std::fs::read_dir(implementation_dir) else {
        return symbols;
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("rs") {
            continue;
        }
        let Ok(content) = std::fs::read_to_string(&path) else {
            continue;
        };

        let mut brace_depth: i32 = 0;
        let mut impl_stack: Vec<(i32, String)> = Vec::new();

        for line in content.lines() {
            let code = line.split("//").next().unwrap_or("").trim();
            if code.is_empty() {
                continue;
            }

            if code.starts_with("impl ") && code.contains('{') {
                if let Some(impl_ty) = parse_impl_type(code) {
                    impl_stack.push((brace_depth + 1, impl_ty));
                }
            }

            if let Some(method_name) = extract_c_function_name(code) {
                let current_impl = impl_stack
                    .iter()
                    .rev()
                    .find(|(depth, _)| brace_depth >= *depth)
                    .map(|(_, ty)| ty.clone());
                if let Some(impl_ty) = current_impl {
                    insert_method_symbol(
                        &mut symbols,
                        method_name,
                        ImplementationMethodSymbol {
                            impl_type: impl_ty,
                            tuple_return_types: parse_tuple_return_types(code),
                        },
                    );
                }
            }

            let (opens, closes) = count_braces(code);
            brace_depth += opens - closes;
            impl_stack.retain(|(depth, _)| brace_depth >= *depth);
        }
    }

    symbols
}

fn collect_implementation_eq_helper_symbols(implementation_dir: &Path) -> Vec<EqHelperSymbol> {
    let mut helpers = Vec::new();
    if !implementation_dir.exists() {
        return helpers;
    }

    let Ok(entries) = std::fs::read_dir(implementation_dir) else {
        return helpers;
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("rs") {
            continue;
        }
        let Ok(content) = std::fs::read_to_string(&path) else {
            continue;
        };

        for line in content.lines() {
            let code = line.split("//").next().unwrap_or("").trim();
            if code.is_empty() {
                continue;
            }
            let Some(function_name) = extract_c_function_name(code) else {
                continue;
            };
            if !function_name.ends_with("Eq") {
                continue;
            }
            let Some(exec_type) = parse_eq_helper_exec_type(code) else {
                continue;
            };
            let symbol = EqHelperSymbol {
                function_name,
                exec_type,
            };
            if !helpers.contains(&symbol) {
                helpers.push(symbol);
            }
        }
    }

    helpers
}

fn collect_implementation_type_view_helper_symbols(
    implementation_dir: &Path,
) -> Vec<TypeViewHelperSymbol> {
    let mut helpers = Vec::new();
    if !implementation_dir.exists() {
        return helpers;
    }

    let Ok(entries) = std::fs::read_dir(implementation_dir) else {
        return helpers;
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) != Some("rs") {
            continue;
        }
        let Ok(content) = std::fs::read_to_string(&path) else {
            continue;
        };

        for line in content.lines() {
            let code = line.split("//").next().unwrap_or("").trim();
            if code.is_empty() {
                continue;
            }
            let Some(symbol) = parse_type_view_helper_symbol(code) else {
                continue;
            };
            if !helpers.contains(&symbol) {
                helpers.push(symbol);
            }
        }
    }

    helpers
}

fn choose_symbol_path(exec_name: &str, symbols: &HashMap<String, Vec<String>>) -> Option<String> {
    let candidates = symbols.get(exec_name)?;
    let mut unique = candidates.clone();
    unique.sort();
    unique.dedup();

    if unique.len() == 1 {
        return unique.first().cloned();
    }

    let generated: Vec<&String> = unique
        .iter()
        .filter(|p| p.starts_with("crate::generated::"))
        .collect();
    if generated.len() == 1 {
        return Some(generated[0].to_string());
    }

    let associated: Vec<&String> = unique
        .iter()
        .filter(|p| p.contains("::") && !p.starts_with("crate::generated::"))
        .collect();
    if associated.len() == 1 {
        return Some(associated[0].to_string());
    }

    None
}

fn infer_function_paths_from_generated_symbols(
    input: &Path,
    schema: &SpecSchema,
    naming: &verus_transpiler::NamingConfig,
) -> HashMap<String, String> {
    let mut inferred = HashMap::new();

    let called = collect_called_functions_from_spec_file(input);
    if called.is_empty() {
        return inferred;
    }

    let local_functions: HashSet<String> = schema.functions.keys().cloned().collect();

    let Some(protocol_dir) = input.parent() else {
        return inferred;
    };
    let Some(protocol_name) = protocol_dir.file_name().and_then(|s| s.to_str()) else {
        return inferred;
    };
    let Some(protocol_root) = protocol_dir.parent() else {
        return inferred;
    };
    if protocol_root.file_name().and_then(|s| s.to_str()) != Some("protocol") {
        return inferred;
    }
    let Some(src_root) = protocol_root.parent() else {
        return inferred;
    };

    let generated_dir = src_root.join("generated").join(protocol_name);
    let implementation_dir = src_root.join("implementation").join(protocol_name);

    let mut symbols: HashMap<String, Vec<String>> = HashMap::new();
    collect_generated_symbols(protocol_name, &generated_dir, &mut symbols);
    collect_implementation_symbols(&implementation_dir, &mut symbols);

    for call_name in called {
        if local_functions.contains(&call_name) {
            continue;
        }
        let base_name = strip_spec_prefix(&call_name, &naming.spec_prefix).to_string();
        if local_functions.contains(&base_name) {
            continue;
        }

        let exec_name = format!("{}{}", naming.exec_prefix, base_name);
        if let Some(path) = choose_symbol_path(&exec_name, &symbols) {
            inferred.entry(base_name).or_insert(path);
        }
    }

    inferred
}

fn infer_function_paths_from_spec_paths(
    spec_paths: &[&Path],
    schema: &SpecSchema,
    naming: &verus_transpiler::NamingConfig,
) -> HashMap<String, String> {
    let mut hints = HashMap::new();
    for path in spec_paths {
        let inferred = infer_function_paths_from_generated_symbols(path, schema, naming);
        for (name, symbol_path) in inferred {
            hints.entry(name).or_insert(symbol_path);
        }
    }
    hints
}

fn infer_exec_function_name(spec_name: &str, naming: &verus_transpiler::NamingConfig) -> String {
    if has_uppercase_prefixed_name(spec_name, &naming.exec_prefix) {
        return spec_name.to_string();
    }
    let base = strip_spec_prefix(spec_name, &naming.spec_prefix);
    format!("{}{}", naming.exec_prefix, base)
}

fn is_int_like_type_name(name: &str) -> bool {
    matches!(
        name,
        "int" | "nat" | "u64" | "u32" | "u16" | "u8" | "usize" | "i64" | "i32"
    )
}

fn infer_exec_type_name_from_named(
    name: &str,
    schema: &SpecSchema,
    naming: &verus_transpiler::NamingConfig,
) -> Option<String> {
    if name == "bool" || is_int_like_type_name(name) {
        return None;
    }
    if has_uppercase_prefixed_name(name, &naming.exec_prefix) {
        return Some(name.to_string());
    }
    if let Some(alias) = schema.aliases.get(name) {
        return infer_exec_type_name_from_type(&alias.ty, schema, naming);
    }
    if has_uppercase_prefixed_name(name, &naming.spec_prefix) {
        return Some(format!(
            "{}{}",
            naming.exec_prefix,
            strip_spec_prefix(name, &naming.spec_prefix)
        ));
    }
    if schema.structs.contains_key(name) || schema.enums.contains_key(name) {
        return Some(format!("{}{}", naming.exec_prefix, name));
    }
    None
}

fn infer_exec_type_name_from_type(
    ty: &verus_transpiler::ast::Type,
    schema: &SpecSchema,
    naming: &verus_transpiler::NamingConfig,
) -> Option<String> {
    use verus_transpiler::ast::Type;
    match ty {
        Type::Reference { ty, .. } => infer_exec_type_name_from_type(ty, schema, naming),
        Type::Named(path) | Type::Generic(path, _) => path
            .segments
            .last()
            .and_then(|name| infer_exec_type_name_from_named(name, schema, naming)),
        _ => None,
    }
}

fn find_receiver_arg_index(
    sig: &verus_transpiler::types::FunctionSig,
    impl_type: &str,
    schema: &SpecSchema,
    naming: &verus_transpiler::NamingConfig,
) -> Option<usize> {
    let receiver_idxs: Vec<usize> = sig
        .params
        .iter()
        .enumerate()
        .filter_map(|(idx, param)| {
            infer_exec_type_name_from_type(&param.ty, schema, naming)
                .filter(|exec_ty| exec_ty == impl_type)
                .map(|_| idx)
        })
        .collect();
    if receiver_idxs.len() == 1 {
        receiver_idxs.first().copied()
    } else {
        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ReturnKind {
    Bool,
    IntLike,
    Named(String),
    Unknown,
}

fn classify_spec_return_kind(
    ty: &verus_transpiler::ast::Type,
    schema: &SpecSchema,
    naming: &verus_transpiler::NamingConfig,
) -> ReturnKind {
    use verus_transpiler::ast::Type;
    match ty {
        Type::Bool => ReturnKind::Bool,
        Type::Int | Type::Nat => ReturnKind::IntLike,
        Type::Reference { ty, .. } => classify_spec_return_kind(ty, schema, naming),
        Type::Named(path) => {
            if let Some(name) = path.segments.last() {
                if name == "bool" {
                    ReturnKind::Bool
                } else if is_int_like_type_name(name) {
                    ReturnKind::IntLike
                } else if let Some(alias) = schema.aliases.get(name) {
                    classify_spec_return_kind(&alias.ty, schema, naming)
                } else if let Some(exec_name) =
                    infer_exec_type_name_from_named(name, schema, naming)
                {
                    ReturnKind::Named(exec_name)
                } else {
                    ReturnKind::Unknown
                }
            } else {
                ReturnKind::Unknown
            }
        }
        _ => ReturnKind::Unknown,
    }
}

fn normalize_type_text(type_text: &str) -> String {
    type_text
        .chars()
        .filter(|c| !c.is_ascii_whitespace())
        .collect::<String>()
}

fn is_bool_like_type(type_text: &str) -> bool {
    let normalized = normalize_type_text(type_text);
    normalized == "bool" || normalized.ends_with("::bool")
}

fn tuple_element_matches_return_kind(type_text: &str, kind: &ReturnKind) -> bool {
    let normalized = normalize_type_text(type_text);
    match kind {
        ReturnKind::Bool => is_bool_like_type(&normalized),
        ReturnKind::IntLike => {
            normalized.contains("u64")
                || normalized.contains("u32")
                || normalized.contains("u16")
                || normalized.contains("u8")
                || normalized.contains("usize")
                || normalized.contains("i64")
                || normalized.contains("i32")
                || normalized.contains("int")
                || normalized.contains("nat")
        }
        ReturnKind::Named(expected) => normalized.ends_with(expected),
        ReturnKind::Unknown => false,
    }
}

fn infer_destructure_index(
    spec_return: &verus_transpiler::ast::Type,
    tuple_return_types: Option<&Vec<String>>,
    schema: &SpecSchema,
    naming: &verus_transpiler::NamingConfig,
) -> Option<usize> {
    let tuple_return_types = tuple_return_types?;
    if tuple_return_types.len() < 2 {
        return None;
    }
    let return_kind = classify_spec_return_kind(spec_return, schema, naming);
    if return_kind == ReturnKind::Unknown {
        return None;
    }

    let matching_indices: Vec<usize> = tuple_return_types
        .iter()
        .enumerate()
        .filter_map(|(idx, ty)| tuple_element_matches_return_kind(ty, &return_kind).then_some(idx))
        .collect();

    if matching_indices.len() == 1 {
        return matching_indices.first().copied();
    }

    if matching_indices.is_empty()
        && tuple_return_types.len() == 2
        && is_bool_like_type(&tuple_return_types[0])
        && return_kind != ReturnKind::Bool
    {
        return Some(1);
    }

    None
}

fn infer_method_calls_from_spec_paths(
    spec_paths: &[&Path],
    schema: &SpecSchema,
    naming: &verus_transpiler::NamingConfig,
) -> HashMap<String, verus_transpiler::config::MethodCallConfig> {
    let mut inferred = HashMap::new();

    let mut called_funcs = HashSet::new();
    for path in spec_paths {
        called_funcs.extend(collect_called_functions_from_spec_file(path));
    }
    if called_funcs.is_empty() {
        return inferred;
    }

    let mut seen_impl_dirs = HashSet::new();
    let mut method_symbols: HashMap<String, Vec<ImplementationMethodSymbol>> = HashMap::new();
    for path in spec_paths {
        let Some(protocol_dir) = path.parent() else {
            continue;
        };
        let Some(protocol_name) = protocol_dir.file_name().and_then(|s| s.to_str()) else {
            continue;
        };
        let Some(protocol_root) = protocol_dir.parent() else {
            continue;
        };
        if protocol_root.file_name().and_then(|s| s.to_str()) != Some("protocol") {
            continue;
        }
        let Some(src_root) = protocol_root.parent() else {
            continue;
        };
        let implementation_dir = src_root.join("implementation").join(protocol_name);
        if !seen_impl_dirs.insert(implementation_dir.clone()) {
            continue;
        }

        for (method_name, symbols) in collect_implementation_method_symbols(&implementation_dir) {
            let entry = method_symbols.entry(method_name).or_default();
            for symbol in symbols {
                if !entry.contains(&symbol) {
                    entry.push(symbol);
                }
            }
        }
    }

    for call_name in called_funcs {
        let Some(sig) = schema.functions.get(&call_name) else {
            continue;
        };
        let exec_method_name = infer_exec_function_name(&call_name, naming);
        let Some(candidates) = method_symbols.get(&exec_method_name) else {
            continue;
        };

        let mut matches: Vec<(usize, &ImplementationMethodSymbol)> = candidates
            .iter()
            .filter_map(|candidate| {
                find_receiver_arg_index(sig, &candidate.impl_type, schema, naming)
                    .map(|idx| (idx, candidate))
            })
            .collect();
        matches.sort_by(|a, b| {
            a.0.cmp(&b.0)
                .then_with(|| a.1.impl_type.cmp(&b.1.impl_type))
        });
        matches.dedup_by(|a, b| a.0 == b.0 && a.1.impl_type == b.1.impl_type);

        if matches.len() != 1 {
            continue;
        }

        let (receiver_arg_index, selected_method) = matches[0];
        let destructure_index = infer_destructure_index(
            &sig.return_type,
            selected_method.tuple_return_types.as_ref(),
            schema,
            naming,
        );
        inferred.insert(
            call_name,
            verus_transpiler::config::MethodCallConfig {
                method_name: exec_method_name,
                receiver_arg_index,
                destructure_index,
            },
        );
    }

    inferred
}

fn infer_eq_function_fields_from_schema(
    schema: &SpecSchema,
    naming: &verus_transpiler::NamingConfig,
    eq_by_type: &HashMap<String, String>,
) -> HashMap<String, String> {
    let mut inferred = HashMap::new();
    let mut ambiguous_fields: HashSet<String> = HashSet::new();

    let mut maybe_insert_field = |field_name: &str, ty: &verus_transpiler::ast::Type| {
        let Some(exec_type) = infer_exec_type_name_from_type(ty, schema, naming) else {
            return;
        };
        let Some(eq_fn) = eq_by_type.get(&exec_type) else {
            return;
        };
        if ambiguous_fields.contains(field_name) {
            return;
        }
        if let Some(existing) = inferred.get(field_name) {
            if existing != eq_fn {
                inferred.remove(field_name);
                ambiguous_fields.insert(field_name.to_string());
            }
            return;
        }
        inferred.insert(field_name.to_string(), eq_fn.clone());
    };

    for struct_name in &schema.struct_order {
        let Some(struct_def) = schema.structs.get(struct_name) else {
            continue;
        };
        for field in &struct_def.fields {
            maybe_insert_field(&field.name, &field.ty);
        }
    }

    for enum_name in &schema.enum_order {
        let Some(enum_def) = schema.enums.get(enum_name) else {
            continue;
        };
        for variant in &enum_def.variants {
            if let verus_transpiler::types::VariantFields::Struct(fields) = &variant.fields {
                for field in fields {
                    maybe_insert_field(&field.name, &field.ty);
                }
            }
        }
    }

    inferred
}

fn infer_eq_function_fields_from_spec_paths(
    spec_paths: &[&Path],
    schema: &SpecSchema,
    naming: &verus_transpiler::NamingConfig,
) -> HashMap<String, String> {
    let mut seen_impl_dirs = HashSet::new();
    let mut eq_symbols: Vec<EqHelperSymbol> = Vec::new();

    for path in spec_paths {
        let Some(protocol_dir) = path.parent() else {
            continue;
        };
        let Some(protocol_name) = protocol_dir.file_name().and_then(|s| s.to_str()) else {
            continue;
        };
        let Some(protocol_root) = protocol_dir.parent() else {
            continue;
        };
        if protocol_root.file_name().and_then(|s| s.to_str()) != Some("protocol") {
            continue;
        }
        let Some(src_root) = protocol_root.parent() else {
            continue;
        };
        let implementation_dir = src_root.join("implementation").join(protocol_name);
        if !seen_impl_dirs.insert(implementation_dir.clone()) {
            continue;
        }
        eq_symbols.extend(collect_implementation_eq_helper_symbols(
            &implementation_dir,
        ));
    }

    let mut eq_by_type: HashMap<String, String> = HashMap::new();
    let mut ambiguous_types: HashSet<String> = HashSet::new();
    for symbol in eq_symbols {
        if ambiguous_types.contains(&symbol.exec_type) {
            continue;
        }
        if let Some(existing) = eq_by_type.get(&symbol.exec_type) {
            if existing != &symbol.function_name {
                eq_by_type.remove(&symbol.exec_type);
                ambiguous_types.insert(symbol.exec_type);
            }
            continue;
        }
        eq_by_type.insert(symbol.exec_type, symbol.function_name);
    }

    if eq_by_type.is_empty() {
        return HashMap::new();
    }

    infer_eq_function_fields_from_schema(schema, naming, &eq_by_type)
}

fn infer_expected_exec_type_for_type_view(
    spec_type: &str,
    schema: &SpecSchema,
    naming: &verus_transpiler::NamingConfig,
) -> Option<String> {
    if let Some(exec_type) = infer_exec_type_name_from_named(spec_type, schema, naming) {
        return Some(exec_type);
    }
    if spec_type == "bool" || is_int_like_type_name(spec_type) {
        return None;
    }
    let base = strip_spec_prefix(spec_type, &naming.spec_prefix);
    if base.is_empty() {
        return None;
    }
    Some(format!("{}{}", naming.exec_prefix, base))
}

fn infer_type_view_exprs_from_spec_paths(
    spec_paths: &[&Path],
    schema: &SpecSchema,
    naming: &verus_transpiler::NamingConfig,
) -> HashMap<String, String> {
    let mut seen_impl_dirs = HashSet::new();
    let mut type_view_symbols: Vec<TypeViewHelperSymbol> = Vec::new();

    for path in spec_paths {
        let Some(protocol_dir) = path.parent() else {
            continue;
        };
        let Some(protocol_name) = protocol_dir.file_name().and_then(|s| s.to_str()) else {
            continue;
        };
        let Some(protocol_root) = protocol_dir.parent() else {
            continue;
        };
        if protocol_root.file_name().and_then(|s| s.to_str()) != Some("protocol") {
            continue;
        }
        let Some(src_root) = protocol_root.parent() else {
            continue;
        };
        let implementation_dir = src_root.join("implementation").join(protocol_name);
        if !seen_impl_dirs.insert(implementation_dir.clone()) {
            continue;
        }
        type_view_symbols.extend(collect_implementation_type_view_helper_symbols(
            &implementation_dir,
        ));
    }

    if type_view_symbols.is_empty() {
        return HashMap::new();
    }

    let known_spec_types: HashSet<&str> = schema
        .aliases
        .keys()
        .chain(schema.structs.keys())
        .chain(schema.enums.keys())
        .map(|k| k.as_str())
        .collect();

    let mut inferred = HashMap::new();
    let mut ambiguous_types: HashSet<String> = HashSet::new();

    for symbol in type_view_symbols {
        if !known_spec_types.contains(symbol.spec_type.as_str()) {
            continue;
        }
        let Some(expected_exec_type) =
            infer_expected_exec_type_for_type_view(&symbol.spec_type, schema, naming)
        else {
            continue;
        };
        if symbol.param_exec_type != expected_exec_type {
            continue;
        }

        let view_expr = format!("{}({{param}})", symbol.function_name);
        if ambiguous_types.contains(&symbol.spec_type) {
            continue;
        }
        if let Some(existing) = inferred.get(&symbol.spec_type) {
            if existing != &view_expr {
                inferred.remove(&symbol.spec_type);
                ambiguous_types.insert(symbol.spec_type.clone());
            }
            continue;
        }
        inferred.insert(symbol.spec_type, view_expr);
    }

    inferred
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    // Handle subcommands first
    if let Some(command) = &cli.command {
        return handle_command(command, &cli);
    }

    // Require input and annotations for single-file mode
    let input = cli
        .input
        .as_ref()
        .ok_or_else(|| miette::miette!("--input is required for single-file mode"))?;
    let annotations = cli
        .annotations
        .as_ref()
        .ok_or_else(|| miette::miette!("--annotations is required for single-file mode"))?;

    if cli.verbose {
        eprintln!("Input: {}", input.display());
        eprintln!("Annotations: {}", annotations.display());
        if let Some(ref output) = cli.output {
            eprintln!("Output: {}", output.display());
        }
    }

    // Load TOML configuration (user overrides)
    let config_path = cli.config.as_deref();
    let mut file_config = if let Some(cfg_path) = config_path {
        FileConfig::from_file(cfg_path)
            .map_err(|e| miette::miette!("Failed to load config: {}", e))?
    } else {
        FileConfig::default()
    };

    // Auto-infer config from spec file (+ sibling types.rs if present)
    {
        let mut spec_paths: Vec<&Path> = Vec::new();
        // Check for sibling types.rs in the same directory as input
        let types_path = input.parent().map(|dir| dir.join("types.rs"));
        if let Some(ref tp) = types_path {
            if tp.exists() && tp != input {
                spec_paths.push(tp.as_path());
            }
        }
        spec_paths.push(input);

        let analysis_result = if spec_paths.len() > 1 {
            analyze_spec_files(&spec_paths)
        } else {
            analyze_spec_file(input)
        };

        match analysis_result {
            Ok(schema) => {
                let annotation_modules = parse_annotation_file(annotations).ok();
                let function_path_hints =
                    infer_function_paths_from_spec_paths(&spec_paths, &schema, &file_config.naming);
                let method_call_hints =
                    infer_method_calls_from_spec_paths(&spec_paths, &schema, &file_config.naming);
                let eq_function_field_hints = infer_eq_function_fields_from_spec_paths(
                    &spec_paths,
                    &schema,
                    &file_config.naming,
                );
                let type_view_expr_hints = infer_type_view_exprs_from_spec_paths(
                    &spec_paths,
                    &schema,
                    &file_config.naming,
                );
                let inferer = if let Some(modules) = annotation_modules.as_ref() {
                    ConfigInferer::with_annotations(&schema, &file_config.naming, modules)
                } else {
                    ConfigInferer::new(&schema, &file_config.naming)
                }
                .with_function_path_hints(function_path_hints)
                .with_method_call_hints(method_call_hints)
                .with_eq_function_field_hints(eq_function_field_hints)
                .with_type_view_expr_hints(type_view_expr_hints);
                let inferred = inferer.infer();
                merge_configs(&mut file_config, &inferred);
                if cli.verbose {
                    eprintln!(
                        "Auto-inferred config from {} file(s): {} structs, {} enums, {} type aliases",
                        spec_paths.len(),
                        schema.structs.len(),
                        schema.enums.len(),
                        schema.aliases.len()
                    );
                }
            }
            Err(e) => {
                if cli.verbose {
                    eprintln!("Note: spec analysis skipped ({})", e);
                }
            }
        }
    }

    // --dump-config: print the resolved config and exit
    if cli.dump_config {
        let toml_str = toml::to_string_pretty(&file_config)
            .map_err(|e| miette::miette!("Failed to serialize config: {}", e))?;
        println!("{}", toml_str);
        return Ok(());
    }

    // Convert FileConfig to internal TranspilerConfig
    let effective_config_path = config_path.unwrap_or(Path::new("."));
    let mut config = convert_file_config(file_config, effective_config_path)?;

    // Apply --auto-skip and --proof-fallback flags
    if cli.auto_skip || cli.proof_fallback {
        config.auto_skip = true;
    }
    if cli.proof_fallback {
        config.proof_fallback = true;
    }

    // Create transpiler
    let transpiler = Transpiler::new(config);

    // Run transpilation
    let (result, skipped) = transpiler
        .transpile_file_with_report(input, annotations)
        .map_err(|e| miette::miette!("{}", e))?;

    // Report auto-skipped / proof-fallback functions
    if !skipped.is_empty() {
        if cli.proof_fallback {
            eprintln!("\n=== Proof Gap Report ===");
            let mut translate_gaps = 0;
            let mut proof_gaps = 0;
            for sf in &skipped {
                if sf.reason.starts_with("transpilation error")
                    || sf.reason.starts_with("annotation error")
                    || sf.reason.starts_with("not functionalizable")
                {
                    eprintln!("TRANSLATE-GAP: {} — {}", sf.name, sf.reason);
                    translate_gaps += 1;
                } else {
                    eprintln!("PROOF-GAP: {} — {}", sf.name, sf.reason);
                    proof_gaps += 1;
                }
            }
            eprintln!(
                "Total: {} proof gaps, {} translation gaps",
                proof_gaps, translate_gaps
            );
        } else {
            eprintln!("Auto-skipped {} function(s):", skipped.len());
            for sf in &skipped {
                eprintln!("  - {}: {}", sf.name, sf.reason);
            }
        }
    }

    // Output result
    if cli.stdout || cli.output.is_none() {
        println!("{}", result);
    } else if let Some(output_path) = cli.output {
        std::fs::write(&output_path, &result)
            .map_err(|e| miette::miette!("Failed to write output file: {}", e))?;
        if cli.verbose {
            eprintln!("Written to: {}", output_path.display());
        }
    }

    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ModelCheckExecutionSummary {
    result: String,
    states: usize,
    transitions: usize,
    depth: usize,
    elapsed_ms: u128,
    constants_valuations_total: usize,
    constants_valuations_explored: usize,
    timing: ModelCheckPhaseTimingSummary,
    enumeration: ModelCheckEnumerationSummary,
    branch_telemetry: Vec<ModelCheckBranchTelemetrySummary>,
    liveness: Option<ModelCheckLivenessSummary>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
struct ModelCheckPhaseTimingSummary {
    source_ingestion_parsing_ms: u128,
    model_config_resolution_ms: u128,
    initial_state_construction_ms: u128,
    successor_solving_ms: u128,
    candidate_generation_evaluation_ms: u128,
    dedup_hashing_normalization_ms: u128,
    invariant_evaluation_ms: u128,
    report_serialization_output_ms: u128,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ModelCheckEnumerationSummary {
    direct_assignment_branch_solves: usize,
    enumeration_fallback_branch_solves: usize,
    enumeration_candidate_evaluations: usize,
    guard_pruned_candidate_evaluations: usize,
    candidate_evaluation_guardrail_per_state_branch: usize,
    successor_cache_hits: usize,
    successor_cache_misses: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ModelCheckBranchTelemetrySummary {
    branch_label: String,
    invocations: usize,
    existential_assignment_count: usize,
    candidate_state_count: usize,
    direct_solver_hits: usize,
    enumeration_fallback_hits: usize,
    guard_pruned_candidate_evaluations: usize,
    successful_successors: usize,
    cumulative_solve_elapsed_ms: u128,
    // Phase 36.3.2 finer-grained telemetry
    direct_assigned_fields: usize,
    deferred_constraint_evaluations: usize,
    evaluator_calls: usize,
    // Phase 36.3.7.c guard-first telemetry
    guard_pruned_assignments: usize,
    // Phase 38.17.1 constraint classification telemetry
    eq_constraints: usize,
    predicate_constraints: usize,
    /// 0 = direct, 1 = no next-state assignment, 2 = not all fields assigned
    fallback_reason: u8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ModelCheckLivenessSummary {
    obligations: usize,
    fairness_weak: usize,
    fairness_strong: usize,
    checked: bool,
    violation_found: bool,
    skipped_reason: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ModelCheckExecution {
    summary: ModelCheckExecutionSummary,
    exploration: verus_transpiler::modelcheck::explorer::ExplorationResult,
    por_pruned_branches: Vec<String>,
    leads_to_violation: Option<verus_transpiler::modelcheck::liveness::LeadsToViolation>,
}

struct ModelCheckCommandExecution {
    bundle: verus_transpiler::spec_analyzer::ProtocolSourceBundle,
    model_config: verus_transpiler::modelcheck::config::ModelConfig,
    selected_search: CliSearchMode,
    resolved_invariant_names: Vec<String>,
    execution: ModelCheckExecution,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct AssumeSiteReport {
    module: String,
    function: Option<String>,
    line: usize,
    text: String,
    assume_false: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct AssumeFileReport {
    module: String,
    assume_count: usize,
    assume_false_count: usize,
    assume_sites: Vec<AssumeSiteReport>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct AssumeReportSummary {
    files_scanned: usize,
    files_with_assumes: usize,
    assume_count: usize,
    assume_false_count: usize,
    non_fallback_assume_count: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct AssumeReportOutput {
    generated_dir: String,
    summary: AssumeReportSummary,
    files: Vec<AssumeFileReport>,
}

fn parse_function_name_from_signature(line: &str) -> Option<String> {
    let trimmed = line.trim_start();
    for prefix in ["pub exec fn ", "pub fn ", "exec fn ", "fn "] {
        if let Some(rest) = trimmed.strip_prefix(prefix) {
            let candidate = rest.split('(').next()?.trim();
            if !candidate.is_empty() {
                return Some(candidate.to_string());
            }
        }
    }
    None
}

fn collect_assume_report_for_file(module: &str, source: &str) -> AssumeFileReport {
    let mut current_fn: Option<String> = None;
    let mut assume_sites = Vec::new();

    for (idx, line) in source.lines().enumerate() {
        if let Some(name) = parse_function_name_from_signature(line) {
            current_fn = Some(name);
        }

        let trimmed = line.trim_start();
        if trimmed.starts_with("//") || !line.contains("assume(") {
            continue;
        }

        let normalized = trimmed.to_string();
        let assume_false = normalized.contains("assume(false);");
        assume_sites.push(AssumeSiteReport {
            module: module.to_string(),
            function: current_fn.clone(),
            line: idx + 1,
            text: normalized,
            assume_false,
        });
    }

    let assume_count = assume_sites.len();
    let assume_false_count = assume_sites.iter().filter(|site| site.assume_false).count();

    AssumeFileReport {
        module: module.to_string(),
        assume_count,
        assume_false_count,
        assume_sites,
    }
}

fn collect_assume_report(generated_dir: &Path) -> Result<AssumeReportOutput> {
    if !generated_dir.exists() {
        return Err(miette::miette!(
            "Generated directory `{}` does not exist.",
            generated_dir.display()
        ));
    }
    if !generated_dir.is_dir() {
        return Err(miette::miette!(
            "Generated path `{}` is not a directory.",
            generated_dir.display()
        ));
    }

    let mut files = Vec::new();
    let mut files_scanned = 0usize;

    for entry in std::fs::read_dir(generated_dir).map_err(|e| {
        miette::miette!(
            "Failed to read generated directory `{}`: {}",
            generated_dir.display(),
            e
        )
    })? {
        let entry = entry.map_err(|e| {
            miette::miette!(
                "Failed to iterate generated directory `{}`: {}",
                generated_dir.display(),
                e
            )
        })?;
        let path = entry.path();
        if !path.is_file() {
            continue;
        }
        let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if !file_name.ends_with("_gen.rs") {
            continue;
        }

        files_scanned += 1;
        let source = std::fs::read_to_string(&path).map_err(|e| {
            miette::miette!("Failed to read generated file `{}`: {}", path.display(), e)
        })?;
        files.push(collect_assume_report_for_file(file_name, &source));
    }

    files.sort_by(|left, right| left.module.cmp(&right.module));

    let files_with_assumes = files.iter().filter(|file| file.assume_count > 0).count();
    let assume_count = files.iter().map(|file| file.assume_count).sum::<usize>();
    let assume_false_count = files
        .iter()
        .map(|file| file.assume_false_count)
        .sum::<usize>();
    let non_fallback_assume_count = assume_count.saturating_sub(assume_false_count);

    Ok(AssumeReportOutput {
        generated_dir: generated_dir.display().to_string(),
        summary: AssumeReportSummary {
            files_scanned,
            files_with_assumes,
            assume_count,
            assume_false_count,
            non_fallback_assume_count,
        },
        files,
    })
}

fn model_check_result_label(
    reason: verus_transpiler::modelcheck::explorer::ExplorationStopReason,
) -> &'static str {
    use verus_transpiler::modelcheck::explorer::ExplorationStopReason;
    match reason {
        ExplorationStopReason::FrontierExhausted => "ok",
        ExplorationStopReason::MaxStatesReached => "max_states_reached",
        ExplorationStopReason::TimeoutReached => "timeout_reached",
        ExplorationStopReason::InvariantViolated => "invariant_violated",
        ExplorationStopReason::DeadlockDetected => "deadlock_detected",
    }
}

fn cli_search_to_explorer_mode(
    mode: CliSearchMode,
) -> verus_transpiler::modelcheck::explorer::SearchMode {
    use verus_transpiler::modelcheck::explorer::SearchMode;
    match mode {
        CliSearchMode::Bfs => SearchMode::Bfs,
        CliSearchMode::Dfs => SearchMode::Dfs,
        // Phase 38.18.10: Dpor doesn't go through the explorer's
        // SearchMode dispatch — it has its own DFS+sleep-set engine.
        // The fallback Bfs is used only by code paths that touch
        // the SearchMode enum before the strategy branch.
        CliSearchMode::Dpor => SearchMode::Bfs,
    }
}

fn successor_semantics_to_solver_semantics(
    semantics: verus_transpiler::modelcheck::config::SuccessorSemantics,
) -> verus_transpiler::modelcheck::solver::EmptySuccessorSemantics {
    use verus_transpiler::modelcheck::config::SuccessorSemantics;
    use verus_transpiler::modelcheck::solver::EmptySuccessorSemantics;
    match semantics {
        SuccessorSemantics::Deadlock => EmptySuccessorSemantics::Deadlock,
        SuccessorSemantics::Stuttering => EmptySuccessorSemantics::Stuttering,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SearchEvidenceMode {
    class: &'static str,
    proof_strength: bool,
    lossy_reasons: Vec<&'static str>,
    guidance: &'static str,
}

fn classify_search_evidence_mode(
    search: &verus_transpiler::modelcheck::config::SearchLimits,
) -> SearchEvidenceMode {
    use verus_transpiler::modelcheck::config::StateDedupMode;

    let mut lossy_reasons = Vec::new();
    if matches!(search.state_dedup, StateDedupMode::HashCompaction64) {
        lossy_reasons.push("hash_compaction64_collision_risk");
    }
    if !search.symmetry_fields.is_empty() {
        lossy_reasons.push("symmetry_fields_state_merging");
    }

    if lossy_reasons.is_empty() {
        SearchEvidenceMode {
            class: "exact_proof_strength",
            proof_strength: true,
            lossy_reasons,
            guidance:
                "Exact search settings preserve explored-state distinctions for proof-strength bounded evidence.",
        }
    } else {
        SearchEvidenceMode {
            class: "lossy_bug_finding_accelerator",
            proof_strength: false,
            lossy_reasons,
            guidance:
                "Lossy search settings can merge distinct states and miss behaviors; use only as bug-finding acceleration.",
        }
    }
}

fn validate_fairness_labels_against_lnext_branches(
    fairness: &verus_transpiler::modelcheck::config::FairnessConfig,
    available_labels: &std::collections::BTreeSet<String>,
) -> Result<()> {
    fn unknown_labels(
        configured: &[String],
        available: &std::collections::BTreeSet<String>,
    ) -> Vec<String> {
        let mut unknown = configured
            .iter()
            .filter(|label| !available.contains(*label))
            .cloned()
            .collect::<Vec<_>>();
        unknown.sort();
        unknown.dedup();
        unknown
    }

    let unknown_weak = unknown_labels(&fairness.weak, available_labels);
    let unknown_strong = unknown_labels(&fairness.strong, available_labels);
    if unknown_weak.is_empty() && unknown_strong.is_empty() {
        return Ok(());
    }

    let mut sections = Vec::new();
    if !unknown_weak.is_empty() {
        sections.push(format!(
            "properties.fairness.weak = [{}]",
            unknown_weak
                .iter()
                .map(|label| format!("`{}`", label))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    if !unknown_strong.is_empty() {
        sections.push(format!(
            "properties.fairness.strong = [{}]",
            unknown_strong
                .iter()
                .map(|label| format!("`{}`", label))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }

    let available_rendered = if available_labels.is_empty() {
        "<none>".to_string()
    } else {
        available_labels
            .iter()
            .map(|label| format!("`{}`", label))
            .collect::<Vec<_>>()
            .join(", ")
    };

    Err(miette::miette!(
        "Invalid model.toml: unknown fairness branch label(s): {}. Available LNext branch labels: {}.",
        sections.join("; "),
        available_rendered
    ))
}

// expand_type_domain_candidates moved to verus_transpiler::modelcheck::domain
// (Phase 38.8.2.c library extraction)
fn expand_type_domain_candidates(
    label: &str,
    var_name: &str,
    ty: &verus_transpiler::ast::Type,
    schema: &verus_transpiler::spec_analyzer::SpecSchema,
    model_config: &verus_transpiler::modelcheck::config::ModelConfig,
) -> Result<Vec<verus_transpiler::modelcheck::value::RuntimeValue>> {
    verus_transpiler::modelcheck::domain::expand_type_domain_candidates(
        label,
        var_name,
        ty,
        schema,
        model_config,
    )
    .map_err(|e| miette::miette!("{}", e))
}

// expand_type_domain_candidates_internal and find_struct_definition
// removed — now in verus_transpiler::modelcheck::domain (Phase 38.8.2.c)

fn infer_init_state_param_name(init_fn: &verus_transpiler::ast::SpecFunction) -> Option<&str> {
    use verus_transpiler::ast::Type;

    let mut state_param: Option<&str> = None;
    for param in &init_fn.params {
        let is_lconstants = matches!(
            &param.ty,
            Type::Named(path) if path.last() == Some("LConstants")
        );
        if is_lconstants {
            continue;
        }
        if state_param.is_some() {
            return None;
        }
        state_param = Some(param.name.as_str());
    }
    if state_param.is_none() {
        return init_fn.params.first().map(|param| param.name.as_str());
    }
    state_param
}

fn infer_init_constants_param_name(init_fn: &verus_transpiler::ast::SpecFunction) -> Option<&str> {
    use verus_transpiler::ast::Type;

    init_fn.params.iter().find_map(|param| {
        if matches!(&param.ty, Type::Named(path) if path.last() == Some("LConstants")) {
            Some(param.name.as_str())
        } else {
            None
        }
    })
}

fn state_struct_definition_from_type<'a>(
    ty: &verus_transpiler::ast::Type,
    schema: &'a verus_transpiler::spec_analyzer::SpecSchema,
) -> Option<&'a verus_transpiler::types::StructDef> {
    use verus_transpiler::ast::Type;

    match ty {
        Type::Reference { ty, .. } => state_struct_definition_from_type(ty, schema),
        Type::Named(path) => {
            verus_transpiler::modelcheck::domain::find_struct_definition(schema, path)
        }
        _ => None,
    }
}

fn match_state_field_access(
    expr: &verus_transpiler::ast::Expr,
    state_param: &str,
) -> Option<String> {
    use verus_transpiler::ast::Expr;

    match expr {
        Expr::Field(base, field_name) => match base.as_ref() {
            Expr::Ident(name) if name == state_param => Some(field_name.clone()),
            _ => None,
        },
        Expr::Cast(inner, _) | Expr::View(inner) => match_state_field_access(inner, state_param),
        _ => None,
    }
}

fn match_constants_field_access(
    expr: &verus_transpiler::ast::Expr,
    constants_param: &str,
) -> Option<String> {
    use verus_transpiler::ast::Expr;

    match expr {
        Expr::Field(base, field_name) => match base.as_ref() {
            Expr::Ident(name) if name == constants_param => Some(field_name.clone()),
            _ => None,
        },
        Expr::Cast(inner, _) | Expr::View(inner) => {
            match_constants_field_access(inner, constants_param)
        }
        _ => None,
    }
}

fn expr_to_static_runtime_value(
    expr: &verus_transpiler::ast::Expr,
) -> Option<verus_transpiler::modelcheck::value::RuntimeValue> {
    use std::collections::BTreeMap;
    use std::sync::Arc;
    use verus_transpiler::ast::{Expr, Literal, UnaryOp};
    use verus_transpiler::modelcheck::value::{RuntimeValue, SetRepr};

    fn call_empty_constructor_kind(path: &verus_transpiler::ast::Path) -> Option<&'static str> {
        if path.last() != Some("empty") || path.segments.len() < 2 {
            return None;
        }
        let receiver = &path.segments[path.segments.len() - 2];
        let normalized = receiver.replace(' ', "");
        if normalized.starts_with("Seq")
            || normalized.ends_with("::Seq")
            || normalized.contains("::Seq::<")
        {
            return Some("seq");
        }
        if normalized.starts_with("Set")
            || normalized.ends_with("::Set")
            || normalized.contains("::Set::<")
        {
            return Some("set");
        }
        if normalized.starts_with("Map")
            || normalized.ends_with("::Map")
            || normalized.contains("::Map::<")
        {
            return Some("map");
        }
        None
    }

    match expr {
        Expr::Literal(Literal::Bool(value)) => Some(RuntimeValue::Bool(*value)),
        Expr::Literal(Literal::Int(value)) => Some(RuntimeValue::Int(*value)),
        Expr::Literal(Literal::String(value)) => Some(RuntimeValue::String(value.clone())),
        Expr::Unary(UnaryOp::Neg, inner) => match expr_to_static_runtime_value(inner)? {
            RuntimeValue::Int(value) => Some(RuntimeValue::Int(-value)),
            _ => None,
        },
        Expr::Cast(inner, _) => expr_to_static_runtime_value(inner),
        Expr::SeqEmpty => Some(RuntimeValue::Seq(Arc::new(Vec::new()))),
        Expr::SetEmpty => Some(RuntimeValue::Set(Arc::new(SetRepr::new()))),
        Expr::MapEmpty => Some(RuntimeValue::Map(Arc::new(BTreeMap::new()))),
        Expr::Call { func, args } if args.is_empty() => match call_empty_constructor_kind(func) {
            Some("seq") => Some(RuntimeValue::Seq(Arc::new(Vec::new()))),
            Some("set") => Some(RuntimeValue::Set(Arc::new(SetRepr::new()))),
            Some("map") => Some(RuntimeValue::Map(Arc::new(BTreeMap::new()))),
            _ => None,
        },
        Expr::SeqLit(items) => {
            let mut out = Vec::with_capacity(items.len());
            for item in items {
                out.push(expr_to_static_runtime_value(item)?);
            }
            Some(RuntimeValue::Seq(Arc::new(out)))
        }
        Expr::SetLit(items) => {
            let mut vals = Vec::with_capacity(items.len());
            for item in items {
                vals.push(expr_to_static_runtime_value(item)?);
            }
            Some(RuntimeValue::Set(Arc::new(SetRepr::from_values(vals))))
        }
        Expr::MapLit(entries) => {
            #[allow(clippy::mutable_key_type)]
            let mut out = BTreeMap::new();
            for (key, value) in entries {
                let key_value = expr_to_static_runtime_value(key)?;
                let value_value = expr_to_static_runtime_value(value)?;
                if out.insert(key_value, value_value).is_some() {
                    return None;
                }
            }
            Some(RuntimeValue::Map(Arc::new(out)))
        }
        Expr::ConstantValue(v) => Some(v.clone()),
        _ => None,
    }
}

#[derive(Clone, Debug)]
enum PinnedStateFieldAssignment {
    Literal(verus_transpiler::modelcheck::value::RuntimeValue),
    ConstantsField(String),
    ConstantsExpr(verus_transpiler::ast::Expr),
}

#[derive(Clone, Debug)]
struct PinnedStateFieldConstraint {
    condition: Option<verus_transpiler::ast::Expr>,
    assignment: PinnedStateFieldAssignment,
}

#[derive(Clone, Debug)]
struct PinnedStateTemplate {
    struct_name: String,
    constants_param: Option<String>,
    fields: Vec<(String, Vec<PinnedStateFieldConstraint>)>,
}

fn expr_mentions_identifier(expr: &verus_transpiler::ast::Expr, ident: &str) -> bool {
    use verus_transpiler::ast::Expr;

    match expr {
        Expr::Ident(name) => name == ident,
        Expr::Conjunction(items) | Expr::Disjunction(items) => items
            .iter()
            .any(|item| expr_mentions_identifier(item, ident)),
        Expr::Implies(lhs, rhs)
        | Expr::Iff(lhs, rhs)
        | Expr::Eq(lhs, rhs)
        | Expr::Ne(lhs, rhs)
        | Expr::Lt(lhs, rhs)
        | Expr::Le(lhs, rhs)
        | Expr::Gt(lhs, rhs)
        | Expr::Ge(lhs, rhs)
        | Expr::Binary(lhs, _, rhs)
        | Expr::Index(lhs, rhs) => {
            expr_mentions_identifier(lhs, ident) || expr_mentions_identifier(rhs, ident)
        }
        Expr::Not(inner)
        | Expr::View(inner)
        | Expr::Cast(inner, _)
        | Expr::Unary(_, inner)
        | Expr::Field(inner, _)
        | Expr::Arrow(inner, _)
        | Expr::Is(inner, _) => expr_mentions_identifier(inner, ident),
        Expr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            expr_mentions_identifier(cond, ident)
                || expr_mentions_identifier(then_branch, ident)
                || else_branch
                    .as_deref()
                    .map(|branch| expr_mentions_identifier(branch, ident))
                    .unwrap_or(false)
        }
        Expr::Match { scrutinee, arms } => {
            expr_mentions_identifier(scrutinee, ident)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .map(|guard| expr_mentions_identifier(guard, ident))
                        .unwrap_or(false)
                        || expr_mentions_identifier(&arm.body, ident)
                })
        }
        Expr::Let {
            binding,
            value,
            body,
        } => {
            expr_mentions_identifier(value, ident)
                || (binding.name() != Some(ident) && expr_mentions_identifier(body, ident))
        }
        Expr::Forall {
            vars,
            triggers,
            body,
        } => {
            let shadowed = vars.iter().any(|var| var.name() == Some(ident));
            triggers.iter().any(|trigger| {
                trigger
                    .exprs
                    .iter()
                    .any(|expr| expr_mentions_identifier(expr, ident))
            }) || (!shadowed && expr_mentions_identifier(body, ident))
        }
        Expr::Exists { vars, body } | Expr::Choose { vars, body } => {
            let shadowed = vars.iter().any(|var| var.name() == Some(ident));
            !shadowed && expr_mentions_identifier(body, ident)
        }
        Expr::Closure { params, body } => {
            let shadowed = params.iter().any(|p| p.name() == Some(ident));
            !shadowed && expr_mentions_identifier(body, ident)
        }
        Expr::Struct { fields, .. } => fields
            .iter()
            .any(|(_, value)| expr_mentions_identifier(value, ident)),
        Expr::StructUpdate { base, fields, .. } => {
            expr_mentions_identifier(base, ident)
                || fields
                    .iter()
                    .any(|(_, value)| expr_mentions_identifier(value, ident))
        }
        Expr::SeqLit(items) | Expr::SetLit(items) => items
            .iter()
            .any(|item| expr_mentions_identifier(item, ident)),
        Expr::MapLit(entries) => entries.iter().any(|(key, value)| {
            expr_mentions_identifier(key, ident) || expr_mentions_identifier(value, ident)
        }),
        Expr::Call { args, .. } => args.iter().any(|arg| expr_mentions_identifier(arg, ident)),
        Expr::MethodCall { receiver, args, .. } => {
            expr_mentions_identifier(receiver, ident)
                || args.iter().any(|arg| expr_mentions_identifier(arg, ident))
        }
        Expr::Literal(_)
        | Expr::SeqEmpty
        | Expr::SetEmpty
        | Expr::MapEmpty
        | Expr::ConstantValue(_) => false,
    }
}

fn expression_to_pinned_assignment(
    expr: &verus_transpiler::ast::Expr,
    state_param: &str,
    constants_param: Option<&str>,
) -> Option<PinnedStateFieldAssignment> {
    if let Some(value) = expr_to_static_runtime_value(expr) {
        return Some(PinnedStateFieldAssignment::Literal(value));
    }
    if let Some(constants_field) =
        constants_param.and_then(|param| match_constants_field_access(expr, param))
    {
        return Some(PinnedStateFieldAssignment::ConstantsField(constants_field));
    }
    if expr_mentions_identifier(expr, state_param) {
        return None;
    }
    let constants_param = constants_param?;
    if expr_mentions_identifier(expr, constants_param) {
        return Some(PinnedStateFieldAssignment::ConstantsExpr(expr.clone()));
    }
    None
}

fn push_pinned_state_assignment(
    assignments: &mut std::collections::HashMap<String, Vec<PinnedStateFieldConstraint>>,
    field_name: String,
    assignment: PinnedStateFieldAssignment,
    condition: Option<&verus_transpiler::ast::Expr>,
) {
    assignments
        .entry(field_name)
        .or_default()
        .push(PinnedStateFieldConstraint {
            condition: condition.cloned(),
            assignment,
        });
}

fn collect_state_field_assignments(
    expr: &verus_transpiler::ast::Expr,
    state_param: &str,
    constants_param: Option<&str>,
    field_types: &std::collections::HashMap<String, verus_transpiler::ast::Type>,
    condition: Option<&verus_transpiler::ast::Expr>,
    assignments: &mut std::collections::HashMap<String, Vec<PinnedStateFieldConstraint>>,
) -> bool {
    use verus_transpiler::ast::{Expr, Type};
    use verus_transpiler::modelcheck::value::RuntimeValue;

    match expr {
        Expr::Conjunction(parts) => parts.iter().all(|part| {
            collect_state_field_assignments(
                part,
                state_param,
                constants_param,
                field_types,
                condition,
                assignments,
            )
        }),
        Expr::Binary(lhs, op, rhs) if *op == verus_transpiler::ast::BinOp::And => {
            collect_state_field_assignments(
                lhs,
                state_param,
                constants_param,
                field_types,
                condition,
                assignments,
            ) && collect_state_field_assignments(
                rhs,
                state_param,
                constants_param,
                field_types,
                condition,
                assignments,
            )
        }
        Expr::Implies(antecedent, consequent) => {
            if expr_mentions_identifier(antecedent, state_param) {
                return false;
            }
            let combined_condition = if let Some(existing) = condition {
                Expr::Conjunction(vec![existing.clone(), antecedent.as_ref().clone()])
            } else {
                antecedent.as_ref().clone()
            };
            collect_state_field_assignments(
                consequent,
                state_param,
                constants_param,
                field_types,
                Some(&combined_condition),
                assignments,
            )
        }
        Expr::Eq(lhs, rhs) => {
            if let Some(field_name) = match_state_field_access(lhs, state_param) {
                if let Some(value) =
                    expression_to_pinned_assignment(rhs, state_param, constants_param)
                {
                    push_pinned_state_assignment(assignments, field_name, value, condition);
                    return true;
                }
                return false;
            }
            if let Some(field_name) = match_state_field_access(rhs, state_param) {
                if let Some(value) =
                    expression_to_pinned_assignment(lhs, state_param, constants_param)
                {
                    push_pinned_state_assignment(assignments, field_name, value, condition);
                    return true;
                }
                return false;
            }
            true
        }
        Expr::Is(base, variant) => {
            let Some(field_name) = match_state_field_access(base, state_param) else {
                return true;
            };
            let Some(field_ty) = field_types.get(&field_name) else {
                return false;
            };
            let enum_ty = match field_ty {
                Type::Named(path) => path.last().map(str::to_string),
                Type::Reference { ty, .. } => match ty.as_ref() {
                    Type::Named(path) => path.last().map(str::to_string),
                    _ => None,
                },
                _ => None,
            };
            let Some(enum_ty) = enum_ty else {
                return false;
            };
            let Ok(value) = RuntimeValue::enum_value(enum_ty, variant.clone(), Vec::new()) else {
                return false;
            };
            push_pinned_state_assignment(
                assignments,
                field_name,
                PinnedStateFieldAssignment::Literal(value),
                condition,
            );
            true
        }
        _ => !expr_mentions_identifier(expr, state_param),
    }
}

fn derive_fully_pinned_state_template_from_init(
    init_fn: &verus_transpiler::ast::SpecFunction,
    state_ty: &verus_transpiler::ast::Type,
    schema: &verus_transpiler::spec_analyzer::SpecSchema,
) -> Result<Option<PinnedStateTemplate>> {
    let Some(state_param) = infer_init_state_param_name(init_fn) else {
        return Ok(None);
    };
    let constants_param = infer_init_constants_param_name(init_fn);
    let Some(struct_def) = state_struct_definition_from_type(state_ty, schema) else {
        return Ok(None);
    };

    let mut assignments = std::collections::HashMap::new();
    let field_types: std::collections::HashMap<String, verus_transpiler::ast::Type> = struct_def
        .fields
        .iter()
        .map(|field| (field.name.clone(), field.ty.clone()))
        .collect();
    if !collect_state_field_assignments(
        &init_fn.body,
        state_param,
        constants_param,
        &field_types,
        None,
        &mut assignments,
    ) {
        return Ok(None);
    }
    if struct_def
        .fields
        .iter()
        .any(|field| !assignments.contains_key(&field.name))
    {
        return Ok(None);
    }

    let mut fields = Vec::with_capacity(struct_def.fields.len());
    for field in &struct_def.fields {
        let Some(value) = assignments.remove(&field.name) else {
            return Ok(None);
        };
        fields.push((field.name.clone(), value));
    }
    Ok(Some(PinnedStateTemplate {
        struct_name: struct_def.name.clone(),
        constants_param: constants_param.map(str::to_string),
        fields,
    }))
}

fn instantiate_pinned_state_candidate(
    template: &PinnedStateTemplate,
    constants: Option<&verus_transpiler::modelcheck::value::RuntimeValue>,
    bounds: verus_transpiler::modelcheck::value::RuntimeCollectionBounds,
) -> Result<Option<verus_transpiler::modelcheck::value::RuntimeValue>> {
    use verus_transpiler::modelcheck::evaluator::{eval_expr, EvalContext};
    use verus_transpiler::modelcheck::value::RuntimeValue;

    let evaluate_expr_with_constants =
        |expr: &verus_transpiler::ast::Expr| -> Result<RuntimeValue> {
            let mut ctx = EvalContext::new(bounds);
            if let Some(constants_param) = template.constants_param.as_deref() {
                let constants_value = constants.ok_or_else(|| {
                miette::miette!(
                    "Failed to build `LInit`-derived state candidate for `{}`: missing `LConstants` valuation while resolving constants-dependent expression.",
                    template.struct_name
                )
            })?;
                ctx = ctx.with_binding(constants_param.to_string(), constants_value.clone());
            }
            eval_expr(expr, &ctx).map_err(|err| {
            miette::miette!(
                "Failed to build `LInit`-derived state candidate for `{}`: could not evaluate constants-dependent expression in `LInit` ({:?}): {}",
                template.struct_name,
                expr,
                err
            )
        })
        };

    let mut fields = Vec::with_capacity(template.fields.len());
    for (field_name, constraints) in &template.fields {
        let mut resolved_value: Option<RuntimeValue> = None;
        for constraint in constraints {
            if let Some(condition) = &constraint.condition {
                let condition_value = evaluate_expr_with_constants(condition)?;
                let RuntimeValue::Bool(is_active) = condition_value else {
                    return Err(miette::miette!(
                        "Failed to build `LInit`-derived state candidate for `{}`: implication guard for field `{}` did not evaluate to bool.",
                        template.struct_name,
                        field_name
                    ));
                };
                if !is_active {
                    continue;
                }
            }

            let value = match &constraint.assignment {
                PinnedStateFieldAssignment::Literal(value) => value.clone(),
                PinnedStateFieldAssignment::ConstantsField(constants_field) => {
                    let constants = constants.ok_or_else(|| {
                        miette::miette!(
                            "Failed to build `LInit`-derived state candidate for `{}`: missing `LConstants` valuation while resolving `{}.{}`.",
                            template.struct_name,
                            field_name,
                            constants_field
                        )
                    })?;
                    constants.field(constants_field).cloned().ok_or_else(|| {
                        miette::miette!(
                            "Failed to build `LInit`-derived state candidate for `{}`: constants field `{}` not found.",
                            template.struct_name,
                            constants_field
                        )
                    })?
                }
                PinnedStateFieldAssignment::ConstantsExpr(expr) => {
                    evaluate_expr_with_constants(expr)?
                }
            };

            if let Some(existing_value) = &resolved_value {
                if existing_value != &value {
                    return Ok(None);
                }
            } else {
                resolved_value = Some(value);
            }
        }

        let Some(value) = resolved_value else {
            return Ok(None);
        };
        fields.push((field_name.clone(), value));
    }

    RuntimeValue::struct_value(template.struct_name.clone(), fields)
        .map(Some)
        .map_err(|err| {
            miette::miette!(
                "Failed to build `LInit`-derived state candidate for `{}`: {}",
                template.struct_name,
                err
            )
        })
}

fn value_matches_domain_spec(
    value: &verus_transpiler::modelcheck::value::RuntimeValue,
    domain: &verus_transpiler::modelcheck::config::DomainSpec,
    field_name: &str,
) -> Result<bool> {
    use verus_transpiler::modelcheck::config::DomainSpec;
    use verus_transpiler::modelcheck::config::ModelValue;
    use verus_transpiler::modelcheck::value::RuntimeValue;

    match domain {
        DomainSpec::Values { values } => Ok(values.iter().any(|candidate| {
            if value == &RuntimeValue::from(candidate) {
                return true;
            }
            // For structured constants (Set/Seq/Map/Struct), allow matching by canonical key.
            // Example: values = ["set:{int:0}"] for a Set<int> constant field.
            matches!(candidate, ModelValue::String(raw) if value.canonical_key() == *raw)
        })),
        DomainSpec::IntRange { min, max } => match value {
            RuntimeValue::Int(v) => Ok((*min as i128..=*max as i128).contains(v)),
            RuntimeValue::Nat(v) => Ok((*min as i128..=*max as i128).contains(&i128::from(*v))),
            other => Err(miette::miette!(
                "Invalid constants domain for field `{}`: int_range requires int/nat values, got `{}`.",
                field_name,
                other.canonical_key()
            )),
        },
        DomainSpec::NatRange { max } => match value {
            RuntimeValue::Nat(v) => Ok(*v <= *max),
            RuntimeValue::Int(v) => Ok(
                *v >= 0 && u64::try_from(*v).map(|converted| converted <= *max).unwrap_or(false),
            ),
            other => Err(miette::miette!(
                "Invalid constants domain for field `{}`: nat_range requires int/nat values, got `{}`.",
                field_name,
                other.canonical_key()
            )),
        },
        DomainSpec::EnumSubset { variants } => match value {
            RuntimeValue::Enum { variant, .. } => Ok(variants.iter().any(|v| v == variant)),
            other => Err(miette::miette!(
                "Invalid constants domain for field `{}`: enum_subset requires enum values, got `{}`.",
                field_name,
                other.canonical_key()
            )),
        },
    }
}

fn constants_candidate_matches_config(
    candidate: &verus_transpiler::modelcheck::value::RuntimeValue,
    model_config: &verus_transpiler::modelcheck::config::ModelConfig,
) -> Result<bool> {
    use verus_transpiler::modelcheck::value::RuntimeValue;

    for (field, assigned) in &model_config.constants.assignments {
        let candidate_field = candidate.field(field).ok_or_else(|| {
            miette::miette!(
                "Invalid constants assignment: field `{}` does not exist on candidate constants value `{}`.",
                field,
                candidate.canonical_key()
            )
        })?;
        let expected = RuntimeValue::from(assigned);
        if candidate_field != &expected {
            return Ok(false);
        }
    }

    for (field, domain) in &model_config.constants.domains {
        let candidate_field = candidate.field(field).ok_or_else(|| {
            miette::miette!(
                "Invalid constants domain: field `{}` does not exist on candidate constants value `{}`.",
                field,
                candidate.canonical_key()
            )
        })?;
        if !value_matches_domain_spec(candidate_field, domain, field)? {
            return Ok(false);
        }
    }

    Ok(true)
}

fn assignment_value_for_constant_field(
    assigned: &verus_transpiler::modelcheck::config::ModelValue,
    existing_field: &verus_transpiler::modelcheck::value::RuntimeValue,
    field_name: &str,
) -> Result<verus_transpiler::modelcheck::value::RuntimeValue> {
    use verus_transpiler::modelcheck::value::RuntimeValue;

    let converted = RuntimeValue::from(assigned);
    match (existing_field, converted) {
        (RuntimeValue::Nat(_), RuntimeValue::Int(v)) if v >= 0 => Ok(RuntimeValue::Nat(v as u64)),
        (RuntimeValue::Nat(_), RuntimeValue::Int(v)) => Err(miette::miette!(
            "Invalid constants assignment: field `{}` expects nat-compatible values, got `{}`.",
            field_name,
            v
        )),
        (_, value) => Ok(value),
    }
}

fn synthesize_constants_candidates_from_assignments(
    candidates: &[verus_transpiler::modelcheck::value::RuntimeValue],
    model_config: &verus_transpiler::modelcheck::config::ModelConfig,
) -> Result<Vec<verus_transpiler::modelcheck::value::RuntimeValue>> {
    use std::collections::BTreeSet;
    use verus_transpiler::modelcheck::value::RuntimeValue;

    if model_config.constants.assignments.is_empty() {
        return Ok(Vec::new());
    }

    let mut seen = BTreeSet::new();
    let mut synthesized = Vec::new();
    for candidate in candidates {
        let RuntimeValue::Struct { ty, fields, .. } = candidate else {
            continue;
        };
        let mut rewritten_fields = fields.clone();
        for (field, assigned) in &model_config.constants.assignments {
            let sym = verus_transpiler::modelcheck::symbol::Symbol::intern(field);
            let existing_field = rewritten_fields.get(&sym).ok_or_else(|| {
                miette::miette!(
                    "Invalid constants assignment: field `{}` does not exist on candidate constants value `{}`.",
                    field,
                    candidate.canonical_key()
                )
            })?;
            let replacement = assignment_value_for_constant_field(assigned, existing_field, field)?;
            rewritten_fields.insert(sym, replacement);
        }

        let candidate = RuntimeValue::struct_value_sym(ty.clone(), rewritten_fields);
        if constants_candidate_matches_config(&candidate, model_config)? {
            let key = candidate.canonical_key();
            if seen.insert(key) {
                synthesized.push(candidate);
            }
        }
    }

    Ok(synthesized)
}

fn resolve_constants_values(
    candidates: Vec<verus_transpiler::modelcheck::value::RuntimeValue>,
    model_config: &verus_transpiler::modelcheck::config::ModelConfig,
) -> Result<Vec<verus_transpiler::modelcheck::value::RuntimeValue>> {
    use std::collections::BTreeSet;

    let mut unique_candidates = Vec::new();
    let mut seen = BTreeSet::new();
    for candidate in candidates {
        let key = candidate.canonical_key();
        if !seen.insert(key) {
            continue;
        }
        unique_candidates.push(candidate);
    }

    let mut filtered = Vec::new();
    for candidate in &unique_candidates {
        if constants_candidate_matches_config(candidate, model_config)? {
            filtered.push(candidate.clone());
        }
    }

    if filtered.is_empty() {
        filtered = synthesize_constants_candidates_from_assignments(
            unique_candidates.as_slice(),
            model_config,
        )?;
    }

    if filtered.is_empty() {
        return Err(miette::miette!(
            "Model-check constants resolution produced zero matching `LConstants` valuations. \
             Add/adjust `[constants.assignments]`, `[constants.domains]`, and quantifier domains."
        ));
    }

    if filtered.len() > model_config.search.max_states {
        return Err(miette::miette!(
            "Model-check constants resolution produced {} `LConstants` valuations, \
             exceeding configured search.max_states ({}). Narrow constants assignments/domains \
             or increase max_states.",
            filtered.len(),
            model_config.search.max_states
        ));
    }

    Ok(filtered)
}

// normalize_call_path, expand_quantifier_domain_for_binding,
// resolve_called_spec_function, eval_spec_function_call_recursive
// extracted to verus_transpiler::modelcheck::helpers (Phase 38.8.2.c)
fn expand_quantifier_domain_for_binding(
    binding: &verus_transpiler::ast::Binding,
    schema: &verus_transpiler::spec_analyzer::SpecSchema,
    model_config: &verus_transpiler::modelcheck::config::ModelConfig,
) -> verus_transpiler::error::TranspileResult<Vec<verus_transpiler::modelcheck::value::RuntimeValue>>
{
    verus_transpiler::modelcheck::helpers::expand_quantifier_domain_for_binding(
        binding,
        schema,
        model_config,
    )
}

fn eval_spec_function_call_recursive(
    functions: &[verus_transpiler::ast::SpecFunction],
    schema: &verus_transpiler::spec_analyzer::SpecSchema,
    model_config: &verus_transpiler::modelcheck::config::ModelConfig,
    func_path: &verus_transpiler::ast::Path,
    args: &[verus_transpiler::modelcheck::value::RuntimeValue],
    bounds: verus_transpiler::modelcheck::value::RuntimeCollectionBounds,
    depth: usize,
) -> verus_transpiler::error::TranspileResult<verus_transpiler::modelcheck::value::RuntimeValue> {
    verus_transpiler::modelcheck::helpers::eval_spec_function_call_recursive(
        functions,
        schema,
        model_config,
        func_path,
        args,
        bounds,
        depth,
    )
}

#[allow(clippy::too_many_arguments)]
fn try_solve_predicate_only_helper_branch(
    transition: &verus_transpiler::modelcheck::ir::TransitionIr,
    branch: &verus_transpiler::modelcheck::ir::TransitionBranchIr,
    current_state: &verus_transpiler::modelcheck::value::RuntimeValue,
    constants: Option<&verus_transpiler::modelcheck::value::RuntimeValue>,
    existential_assignments: &[verus_transpiler::modelcheck::domain::ExistentialAssignment],
    bundle: &verus_transpiler::spec_analyzer::ProtocolSourceBundle,
    model_config: &verus_transpiler::modelcheck::config::ModelConfig,
    bounds: verus_transpiler::modelcheck::value::RuntimeCollectionBounds,
    allow_partial_helper_solve: bool,
) -> verus_transpiler::error::TranspileResult<
    Option<Vec<verus_transpiler::modelcheck::value::RuntimeValue>>,
> {
    use verus_transpiler::ast::Expr;
    use verus_transpiler::error::TranspileError;
    use verus_transpiler::modelcheck::domain::expand_branch_existentials;
    use verus_transpiler::modelcheck::domain::ExistentialAssignment;
    use verus_transpiler::modelcheck::ir::BranchConstraintIr;
    use verus_transpiler::modelcheck::solver::{
        solve_branch_successors_with_candidates_and_telemetry, SolverHooks,
    };

    fn assignment_key(assignment: &ExistentialAssignment) -> String {
        assignment
            .iter()
            .map(|(name, value)| format!("{}={}", name, value.canonical_key()))
            .collect::<Vec<_>>()
            .join("|")
    }

    fn helper_expr_mentions_identifier(expr: &Expr, ident: &str) -> bool {
        match expr {
            Expr::Conjunction(items) | Expr::Disjunction(items) => items
                .iter()
                .any(|item| helper_expr_mentions_identifier(item, ident)),
            Expr::Implies(lhs, rhs)
            | Expr::Iff(lhs, rhs)
            | Expr::Eq(lhs, rhs)
            | Expr::Ne(lhs, rhs)
            | Expr::Lt(lhs, rhs)
            | Expr::Le(lhs, rhs)
            | Expr::Gt(lhs, rhs)
            | Expr::Ge(lhs, rhs)
            | Expr::Index(lhs, rhs)
            | Expr::Binary(lhs, _, rhs) => {
                helper_expr_mentions_identifier(lhs, ident)
                    || helper_expr_mentions_identifier(rhs, ident)
            }
            Expr::Not(inner)
            | Expr::View(inner)
            | Expr::Cast(inner, _)
            | Expr::Unary(_, inner)
            | Expr::Is(inner, _)
            | Expr::Field(inner, _)
            | Expr::Arrow(inner, _) => helper_expr_mentions_identifier(inner, ident),
            Expr::Forall { body, triggers, .. } => {
                helper_expr_mentions_identifier(body, ident)
                    || triggers
                        .iter()
                        .flat_map(|trigger| trigger.exprs.iter())
                        .any(|trigger_expr| helper_expr_mentions_identifier(trigger_expr, ident))
            }
            Expr::Exists { body, .. } | Expr::Closure { body, .. } | Expr::Choose { body, .. } => {
                helper_expr_mentions_identifier(body, ident)
            }
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                helper_expr_mentions_identifier(cond, ident)
                    || helper_expr_mentions_identifier(then_branch, ident)
                    || else_branch
                        .as_ref()
                        .map(|branch| helper_expr_mentions_identifier(branch, ident))
                        .unwrap_or(false)
            }
            Expr::Match { scrutinee, arms } => {
                helper_expr_mentions_identifier(scrutinee, ident)
                    || arms.iter().any(|arm| {
                        arm.guard
                            .as_ref()
                            .map(|guard| helper_expr_mentions_identifier(guard, ident))
                            .unwrap_or(false)
                            || helper_expr_mentions_identifier(&arm.body, ident)
                    })
            }
            Expr::Let { value, body, .. } => {
                helper_expr_mentions_identifier(value, ident)
                    || helper_expr_mentions_identifier(body, ident)
            }
            Expr::Struct { fields, .. } => fields
                .iter()
                .any(|(_, field_expr)| helper_expr_mentions_identifier(field_expr, ident)),
            Expr::StructUpdate { base, fields, .. } => {
                helper_expr_mentions_identifier(base, ident)
                    || fields
                        .iter()
                        .any(|(_, field_expr)| helper_expr_mentions_identifier(field_expr, ident))
            }
            Expr::SeqLit(items) | Expr::SetLit(items) => items
                .iter()
                .any(|item| helper_expr_mentions_identifier(item, ident)),
            Expr::MapLit(items) => items.iter().any(|(key, value)| {
                helper_expr_mentions_identifier(key, ident)
                    || helper_expr_mentions_identifier(value, ident)
            }),
            Expr::Call { args, .. } => args
                .iter()
                .any(|arg| helper_expr_mentions_identifier(arg, ident)),
            Expr::MethodCall { receiver, args, .. } => {
                helper_expr_mentions_identifier(receiver, ident)
                    || args
                        .iter()
                        .any(|arg| helper_expr_mentions_identifier(arg, ident))
            }
            Expr::Ident(name) => name == ident,
            Expr::SeqEmpty
            | Expr::SetEmpty
            | Expr::MapEmpty
            | Expr::Literal(_)
            | Expr::ConstantValue(_) => false,
        }
    }

    fn helper_constraint_depends_on_next_state(
        constraint: &BranchConstraintIr,
        next_state_param: &str,
    ) -> bool {
        match constraint {
            BranchConstraintIr::Eq { target, value } => {
                matches!(
                    target.root,
                    verus_transpiler::modelcheck::ir::ConstraintRoot::NextState
                ) || helper_expr_mentions_identifier(value, next_state_param)
            }
            BranchConstraintIr::Predicate { expr } => {
                helper_expr_mentions_identifier(expr, next_state_param)
            }
        }
    }

    if branch.constraints.len() != 1 {
        return Ok(None);
    }
    let BranchConstraintIr::Predicate { expr } = &branch.constraints[0] else {
        return Ok(None);
    };
    let Expr::Call { func, args } = expr else {
        return Ok(None);
    };

    let transition_param_arity = if transition.constants_param.is_some() {
        3
    } else {
        2
    };
    if args.len() < transition_param_arity {
        return Ok(None);
    }
    if !matches!(&args[0], Expr::Ident(name) if name == &transition.current_state_param) {
        return Ok(None);
    }
    if !matches!(&args[1], Expr::Ident(name) if name == &transition.next_state_param) {
        return Ok(None);
    }
    if let Some(constants_param_name) = transition.constants_param.as_ref() {
        if !matches!(&args[2], Expr::Ident(name) if name == constants_param_name) {
            return Ok(None);
        }
        if constants.is_none() {
            return Ok(None);
        }
    }

    let helper_fn = match verus_transpiler::modelcheck::helpers::resolve_called_spec_function(
        &bundle.spec_functions,
        func,
    ) {
        Ok(function) => function,
        Err(_) => return Ok(None),
    };
    if helper_fn.params.len() != args.len() {
        return Ok(None);
    }

    let helper_transition = match verus_transpiler::modelcheck::ir::build_transition_ir(helper_fn) {
        Ok(transition) => transition,
        Err(_) => return Ok(None),
    };

    let call_evaluator =
        |func_path: &verus_transpiler::ast::Path,
         args: &[verus_transpiler::modelcheck::value::RuntimeValue]| {
            eval_spec_function_call_recursive(
                &bundle.spec_functions,
                &bundle.schema,
                model_config,
                func_path,
                args,
                bounds,
                0,
            )
        };

    let quantifier_domain_evaluator = |binding: &verus_transpiler::ast::Binding| {
        expand_quantifier_domain_for_binding(binding, &bundle.schema, model_config)
    };

    let source_assignments: Vec<ExistentialAssignment> = if existential_assignments.is_empty() {
        vec![std::collections::BTreeMap::new()]
    } else {
        existential_assignments.to_vec()
    };

    let mut call_site_assignments = Vec::<ExistentialAssignment>::new();
    let extra_params = helper_fn.params.iter().skip(transition_param_arity);
    let extra_args = args.iter().skip(transition_param_arity);
    for source_assignment in &source_assignments {
        let mut call_assignment = std::collections::BTreeMap::<
            String,
            verus_transpiler::modelcheck::value::RuntimeValue,
        >::new();
        let mut unsupported = false;
        for (helper_param, arg_expr) in extra_params.clone().zip(extra_args.clone()) {
            match arg_expr {
                Expr::Ident(name) => {
                    let Some(value) = source_assignment.get(name).cloned() else {
                        unsupported = true;
                        break;
                    };
                    call_assignment.insert(helper_param.name.clone(), value);
                }
                _ => {
                    unsupported = true;
                    break;
                }
            }
        }
        if !unsupported {
            call_site_assignments.push(call_assignment);
        }
    }
    if call_site_assignments.is_empty() {
        return Ok(None);
    }
    let mut seen_call_assignments = std::collections::BTreeSet::new();
    call_site_assignments
        .retain(|assignment| seen_call_assignments.insert(assignment_key(assignment)));

    let mut successors = Vec::new();
    for helper_branch in &helper_transition.branches {
        let helper_assignments =
            expand_branch_existentials(helper_branch, &bundle.schema, model_config)?;
        let helper_assignments: Vec<ExistentialAssignment> = if helper_assignments.is_empty() {
            vec![std::collections::BTreeMap::new()]
        } else {
            helper_assignments
        };

        let mut merged_assignments = Vec::<ExistentialAssignment>::new();
        for call_assignment in &call_site_assignments {
            for helper_assignment in &helper_assignments {
                let mut merged = call_assignment.clone();
                let mut conflict = false;
                for (name, value) in helper_assignment {
                    if let Some(existing) = merged.get(name) {
                        if existing != value {
                            conflict = true;
                            break;
                        }
                    } else {
                        merged.insert(name.clone(), value.clone());
                    }
                }
                if !conflict {
                    merged_assignments.push(merged);
                }
            }
        }
        if merged_assignments.is_empty() {
            continue;
        }
        let mut seen_merged = std::collections::BTreeSet::new();
        merged_assignments.retain(|assignment| seen_merged.insert(assignment_key(assignment)));

        let helper_branch_depends_on_next_state =
            helper_branch.constraints.iter().any(|constraint| {
                helper_constraint_depends_on_next_state(
                    constraint,
                    helper_transition.next_state_param.as_str(),
                )
            });

        let solved = match solve_branch_successors_with_candidates_and_telemetry(
            &helper_transition,
            helper_branch,
            current_state,
            constants,
            &merged_assignments,
            None,
            None,
            bounds,
            SolverHooks {
                call_evaluator: Some(&call_evaluator),
                method_evaluator: None,
                quantifier_domain_evaluator: Some(&quantifier_domain_evaluator),
                predicate_only_branch_solver: None,
                bytecode_cache: None,
                native_cache: None,
            },
            None,
        ) {
            Ok(solved) => solved,
            Err(TranspileError::UnsupportedPattern { .. }) => {
                // If an unsupported helper sub-branch is provably disabled for
                // every merged assignment *and* does not depend on s_, we can
                // safely skip it without forcing full predicate fallback.
                let unsupported_branch_is_disabled = if helper_branch_depends_on_next_state {
                    false
                } else {
                    let mut satisfiable = false;
                    for merged_assignment in &merged_assignments {
                        let probe = solve_branch_successors_with_candidates_and_telemetry(
                            &helper_transition,
                            helper_branch,
                            current_state,
                            constants,
                            std::slice::from_ref(merged_assignment),
                            Some(std::slice::from_ref(current_state)),
                            None,
                            bounds,
                            SolverHooks {
                                call_evaluator: Some(&call_evaluator),
                                method_evaluator: None,
                                quantifier_domain_evaluator: Some(&quantifier_domain_evaluator),
                                predicate_only_branch_solver: None,
                                bytecode_cache: None,
                                native_cache: None,
                            },
                            None,
                        )?;
                        if !probe.successors.is_empty() {
                            satisfiable = true;
                            break;
                        }
                    }
                    !satisfiable
                };

                if unsupported_branch_is_disabled || allow_partial_helper_solve {
                    continue;
                }
                return Ok(None);
            }
            Err(err) => return Err(err),
        };
        successors.extend(solved.successors);
    }

    Ok(Some(
        verus_transpiler::modelcheck::solver::deduplicate_successors(successors),
    ))
}

/// Phase 38.18.10: invoke the relocated DPOR sleep-set explorer
/// (`crate::modelcheck::dpor::explore_dpor`) on the same bundle and
/// model config that the BFS path uses, then synthesize a minimal
/// `ExplorationResult` so the existing JSON-report code path can
/// consume it without changes.
///
/// Drops a few BFS-specific things (the per-state successor traces
/// used by the leads_to/liveness checker) — DPOR doesn't store
/// every reached state's RuntimeValue, only their canonical-key
/// strings. For DPOR runs, `exploration.explored` is empty and the
/// downstream leads_to check is skipped accordingly.
fn run_dpor_explorer_as_main_path(
    bundle: &verus_transpiler::spec_analyzer::ProtocolSourceBundle,
    model_config: &verus_transpiler::modelcheck::config::ModelConfig,
    bounds: verus_transpiler::modelcheck::value::RuntimeCollectionBounds,
    constants_value: &verus_transpiler::modelcheck::value::RuntimeValue,
    invariants: &[verus_transpiler::ast::SpecFunction],
    limits: verus_transpiler::modelcheck::explorer::ExplorationLimits,
    native_rlib_paths: Option<(PathBuf, PathBuf)>,
    conflict_profile: bool,
    num_workers: usize,
) -> std::result::Result<verus_transpiler::modelcheck::explorer::ExplorationResult, String> {
    use verus_transpiler::modelcheck::dpor::enabled::SpecContext;
    use verus_transpiler::modelcheck::dpor::{explore_dpor, explore_dpor_parallel, DporConfig};
    use verus_transpiler::modelcheck::explorer::{
        ExplorationResult, ExplorationStats, ExplorationStopReason,
    };

    let constants_opt = if matches!(
        constants_value,
        verus_transpiler::modelcheck::value::RuntimeValue::Unit
    ) {
        None
    } else {
        Some(constants_value.clone())
    };
    let field_schema =
        verus_transpiler::modelcheck::field_schema::FieldSchemaRegistry::from_spec_schema(
            &bundle.schema,
        );
    let ctx = SpecContext {
        bundle: bundle.clone(),
        model_config: model_config.clone(),
        bounds,
        constants: constants_opt,
        cached_transition_ir: std::sync::OnceLock::new(),
        cached_branch_assignments: std::sync::OnceLock::new(),
        field_schema,
        bytecode_cache: verus_transpiler::modelcheck::bytecode::BytecodeCache::new(),
        native_cache: native_rlib_paths.map(|(rlib, deps)| {
            verus_transpiler::modelcheck::native_compile::NativeCache::new(rlib, deps)
        }),
    };
    let invariant_names: Vec<String> = invariants.iter().map(|f| f.name.clone()).collect();
    let dpor_config = DporConfig {
        max_depth: limits.max_depth,
        max_states: limits.max_states,
        use_independence: true,
        use_sleep_sets: true,
        invariants: invariant_names,
        check_deadlock: model_config.properties.check_deadlock,
        runtime_overrides: None,
        ..Default::default()
    };
    let result = if num_workers > 1 {
        explore_dpor_parallel(&ctx, &dpor_config, num_workers)
    } else {
        explore_dpor(&ctx, &dpor_config)
    };

    if conflict_profile {
        let report = verus_transpiler::modelcheck::dpor::explore::format_conflict_profile(
            &result.sleep_independence_blockers,
            &result.runtime_conflict_stats,
        );
        eprintln!("{}", report);
    }

    let stop_reason = if result.violation.is_some() {
        ExplorationStopReason::InvariantViolated
    } else {
        ExplorationStopReason::FrontierExhausted
    };
    let stats = ExplorationStats {
        initial_states: 1,
        explored_states: result.distinct_states.len(),
        visited_states: result.distinct_states.len(),
        max_frontier_size: 0,
        frontier_size_at_stop: 0,
        successors_considered: result.transitions_fired,
        successors_enqueued: result.transitions_fired,
        duplicate_successors: 0,
        hash_compaction_collisions: 0,
        symmetry_collapses: 0,
    };
    Ok(ExplorationResult {
        explored: Vec::new(),
        stop_reason,
        stats,
        invariant_violation: None,
        deadlock: None,
        counterexample: None,
    })
}

fn execute_model_check(
    bundle: &verus_transpiler::spec_analyzer::ProtocolSourceBundle,
    model_config: &verus_transpiler::modelcheck::config::ModelConfig,
    selected_search: CliSearchMode,
    selected_invariants: &[&verus_transpiler::ast::SpecFunction],
    export_parity_debug: Option<&Path>,
    use_bytecode: bool,
    use_native_codegen: bool,
    workers: usize,
    conflict_profile: bool,
) -> Result<ModelCheckExecution> {
    use std::borrow::Cow;
    use std::collections::{BTreeMap, BTreeSet};
    use std::time::Instant;
    use verus_transpiler::modelcheck::config::PorHeuristic;
    use verus_transpiler::modelcheck::domain::expand_branch_existentials;
    use verus_transpiler::modelcheck::explorer::{
        explore_bfs_parallel, explore_state_space_with_traces_dedup_and_debug, ExplorationLimits,
        ExplorationStopReason, TracedSuccessor,
    };
    use verus_transpiler::modelcheck::graph::build_explored_graph_index;
    use verus_transpiler::modelcheck::init::{construct_initial_states, InitHooks};
    use verus_transpiler::modelcheck::invariant::{first_invariant_violation, InvariantHooks};
    use verus_transpiler::modelcheck::ir::build_transition_ir;
    use verus_transpiler::modelcheck::liveness::{
        check_leads_to_violations, resolve_leads_to_obligations, LivenessHooks,
    };
    use verus_transpiler::modelcheck::parity::ParityDebugExporter;
    use verus_transpiler::modelcheck::por::infer_invisible_branch_pruning;
    use verus_transpiler::modelcheck::solver::{
        solve_branch_successors_with_candidates_and_telemetry, SolverHooks,
    };
    use verus_transpiler::modelcheck::value::RuntimeCollectionBounds;

    let native_cache = if use_native_codegen {
        // Find the transpiler-runtime crate directory relative to the binary
        let runtime_crate_dir = std::env::current_exe()
            .ok()
            .and_then(|p| {
                // Walk up to find the workspace root containing transpiler/runtime/
                let mut dir = p.parent()?.to_path_buf();
                for _ in 0..5 {
                    let candidate = dir.join("transpiler").join("runtime");
                    if candidate.join("Cargo.toml").exists() {
                        return Some(candidate);
                    }
                    dir = dir.parent()?.to_path_buf();
                }
                None
            })
            .unwrap_or_else(|| {
                // Fallback: assume CWD-relative
                std::path::PathBuf::from("transpiler/runtime")
            });
        match verus_transpiler::modelcheck::native_compile::NativeCache::try_new(&runtime_crate_dir)
        {
            Ok(cache) => {
                eprintln!(
                    "[native-codegen] Runtime rlib built from {}",
                    runtime_crate_dir.display()
                );
                Some(cache)
            }
            Err(e) => {
                eprintln!(
                    "[native-codegen] WARNING: Failed to build runtime rlib: {}. \
                     Falling back to bytecode/AST.",
                    e
                );
                None
            }
        }
    } else {
        None
    };

    let bytecode_cache = if use_bytecode {
        Some(verus_transpiler::modelcheck::bytecode::BytecodeCache::new())
    } else {
        None
    };

    let candidate_eval_guardrail = model_config.search.candidate_eval_guardrail;

    let started = Instant::now();
    let mut timing_summary = ModelCheckPhaseTimingSummary::default();

    let mut transition =
        build_transition_ir(&bundle.entrypoints.lnext).map_err(|e| miette::miette!("{}", e))?;

    // Phase 38.17.2: Inline action predicate calls in branch constraints.
    // When LNext decomposes into branches like `LSend1a(s, s_, 1)`, the IR
    // creates a single Predicate { Call("LSend1a", ...) } constraint. The
    // solver can't extract s_.field assignments from this opaque call,
    // forcing the 500x-slower candidate-enumeration fallback.
    // Use the shared inliner from the library (Phase 38.17.4).
    verus_transpiler::modelcheck::ir::inline_action_calls(&mut transition, &bundle.spec_functions);
    // Phase 38.18.2: also inline zero-argument helper calls
    // (e.g. `LAcceptors()` → `set![1, 2, 3]`) so the runtime evaluator
    // never has to re-evaluate them. Eliminates both the
    // `eval_spec_function_call_recursive` invocation and the
    // Phase 38.18.5 cache lookup. Must run after `inline_action_calls`
    // so it sees the inlined branch bodies, not the opaque calls.
    verus_transpiler::modelcheck::ir::inline_zero_arg_helper_calls(
        &mut transition,
        &bundle.spec_functions,
    );
    verus_transpiler::modelcheck::ir::constant_fold_transition_ir(&mut transition);

    let transition_branch_labels = transition
        .branches
        .iter()
        .map(|branch| branch.label.clone())
        .collect::<BTreeSet<_>>();
    validate_fairness_labels_against_lnext_branches(
        &model_config.properties.fairness,
        &transition_branch_labels,
    )?;
    let owned_invariants: Vec<verus_transpiler::ast::SpecFunction> = selected_invariants
        .iter()
        .map(|invariant_fn| (*invariant_fn).clone())
        .collect();
    let por_pruned_branch_labels: BTreeSet<String> = match model_config.search.por_heuristic {
        PorHeuristic::None => BTreeSet::new(),
        PorHeuristic::InvisibleBranch => {
            infer_invisible_branch_pruning(&transition, &owned_invariants)
        }
    };
    let bounds = RuntimeCollectionBounds::from(&model_config.collections);
    let quantifier_domain_evaluator = |binding: &verus_transpiler::ast::Binding| {
        expand_quantifier_domain_for_binding(binding, &bundle.schema, model_config)
    };
    let search_mode = cli_search_to_explorer_mode(selected_search);
    let limits = ExplorationLimits::from(&model_config.search);
    let empty_successor_semantics =
        successor_semantics_to_solver_semantics(model_config.properties.successor_semantics);
    let mut enumeration_summary = ModelCheckEnumerationSummary {
        direct_assignment_branch_solves: 0,
        enumeration_fallback_branch_solves: 0,
        enumeration_candidate_evaluations: 0,
        guard_pruned_candidate_evaluations: 0,
        candidate_evaluation_guardrail_per_state_branch: candidate_eval_guardrail,
        successor_cache_hits: 0,
        successor_cache_misses: 0,
    };
    let mut branch_telemetry_summary = BTreeMap::<String, ModelCheckBranchTelemetrySummary>::new();

    let state_ty = bundle
        .entrypoints
        .lnext
        .params
        .first()
        .ok_or_else(|| miette::miette!("Missing current-state parameter in next entrypoint."))?
        .ty
        .clone();
    // LConstants is optional: standalone translated TLA+ specs may have
    // LInit(state) without a constants parameter. In that case, use a
    // dummy unit constants type with a single empty valuation.
    let constants_ty = bundle
        .entrypoints
        .linit
        .params
        .iter()
        .find(|param| {
            matches!(
                &param.ty,
                verus_transpiler::ast::Type::Named(path) if path.last() == Some("LConstants")
            )
        })
        .map(|p| p.ty.clone())
        .unwrap_or_else(|| {
            // No LConstants parameter — use a dummy unit type
            verus_transpiler::ast::Type::Named(verus_transpiler::ast::Path::single(
                "Unit".to_string(),
            ))
        });

    enum StateCandidatesSource {
        Expanded(Vec<verus_transpiler::modelcheck::value::RuntimeValue>),
        PinnedTemplate(PinnedStateTemplate),
    }

    let state_candidates_started = Instant::now();
    let state_candidates_source = match expand_type_domain_candidates(
        "candidate_states",
        "candidate_state",
        &state_ty,
        &bundle.schema,
        model_config,
    ) {
        Ok(candidates) => StateCandidatesSource::Expanded(candidates),
        Err(err)
            if err
                .to_string()
                .contains("Model-check candidate expansion for struct")
                && err.to_string().contains("exceeded limit") =>
        {
            match derive_fully_pinned_state_template_from_init(
                &bundle.entrypoints.linit,
                &state_ty,
                &bundle.schema,
            )? {
                Some(template) => StateCandidatesSource::PinnedTemplate(template),
                None => return Err(err),
            }
        }
        Err(err) => return Err(err),
    };
    timing_summary.candidate_generation_evaluation_ms = timing_summary
        .candidate_generation_evaluation_ms
        .saturating_add(state_candidates_started.elapsed().as_millis());

    let constants_candidates_started = Instant::now();
    let is_unit_constants = matches!(&constants_ty, verus_transpiler::ast::Type::Named(path) if path.last() == Some("Unit"));
    let constants_values = if is_unit_constants {
        // No LConstants in the spec — use a single dummy unit valuation
        vec![verus_transpiler::modelcheck::value::RuntimeValue::Unit]
    } else {
        let constants_candidates = expand_type_domain_candidates(
            "candidate_constants",
            "candidate_constants",
            &constants_ty,
            &bundle.schema,
            model_config,
        )?;
        resolve_constants_values(constants_candidates, model_config)?
    };
    timing_summary.candidate_generation_evaluation_ms = timing_summary
        .candidate_generation_evaluation_ms
        .saturating_add(constants_candidates_started.elapsed().as_millis());
    let constants_valuations_total = constants_values.len();

    // Expand extra LNext params (beyond state/state_/constants) as transition-level existentials
    let extra_param_assignments = verus_transpiler::modelcheck::domain::expand_extra_params(
        &transition.extra_params,
        &bundle.schema,
        model_config,
    )
    .map_err(|e| miette::miette!("{}", e))?;

    let mut assignments_by_branch = BTreeMap::new();
    for branch in &transition.branches {
        let assignments_started = Instant::now();
        let branch_assignments = expand_branch_existentials(branch, &bundle.schema, model_config)
            .map_err(|e| miette::miette!("{}", e))?;
        // Cross-product branch existentials with extra param assignments
        let assignments = if extra_param_assignments.len() <= 1 {
            // No extra params or single valuation — merge directly
            let extra = extra_param_assignments.first().cloned().unwrap_or_default();
            branch_assignments
                .into_iter()
                .map(|mut a| {
                    a.extend(extra.clone());
                    a
                })
                .collect()
        } else {
            let mut merged = Vec::new();
            for ba in &branch_assignments {
                for ea in &extra_param_assignments {
                    let mut combined = ba.clone();
                    combined.extend(ea.clone());
                    merged.push(combined);
                }
            }
            if merged.is_empty() {
                extra_param_assignments.clone()
            } else {
                merged
            }
        };
        timing_summary.candidate_generation_evaluation_ms = timing_summary
            .candidate_generation_evaluation_ms
            .saturating_add(assignments_started.elapsed().as_millis());
        assignments_by_branch.insert(branch.label.clone(), assignments);
    }
    let por_pruned_branches: Vec<String> = por_pruned_branch_labels.iter().cloned().collect();
    let mut aggregated_states = 0usize;
    let mut aggregated_transitions = 0usize;
    let mut aggregated_depth = 0usize;
    let mut constants_valuations_explored = 0usize;
    let mut first_ok_execution: Option<ModelCheckExecution> = None;
    let mut first_incomplete_execution: Option<ModelCheckExecution> = None;
    let mut first_violation_execution: Option<ModelCheckExecution> = None;

    for constants_value in &constants_values {
        constants_valuations_explored = constants_valuations_explored.saturating_add(1);
        let mut run_enumeration_summary = ModelCheckEnumerationSummary {
            direct_assignment_branch_solves: 0,
            enumeration_fallback_branch_solves: 0,
            enumeration_candidate_evaluations: 0,
            guard_pruned_candidate_evaluations: 0,
            candidate_evaluation_guardrail_per_state_branch: candidate_eval_guardrail,
            successor_cache_hits: 0,
            successor_cache_misses: 0,
        };
        let mut run_branch_telemetry = BTreeMap::<String, ModelCheckBranchTelemetrySummary>::new();
        let run_started = Instant::now();
        let mut run_initial_state_construction_ms = 0u128;
        let mut run_successor_solving_total_ms = 0u128;
        let mut run_candidate_generation_ms = 0u128;
        let mut run_candidate_evaluation_ms = 0u128;
        let mut run_invariant_evaluation_ms = 0u128;

        let run_state_candidates = match &state_candidates_source {
            StateCandidatesSource::Expanded(candidates) => Cow::Borrowed(candidates.as_slice()),
            StateCandidatesSource::PinnedTemplate(template) => {
                let instantiate_started = Instant::now();
                let instantiated =
                    instantiate_pinned_state_candidate(template, Some(constants_value), bounds)?;
                run_candidate_generation_ms = run_candidate_generation_ms
                    .saturating_add(instantiate_started.elapsed().as_millis());
                Cow::Owned(instantiated.into_iter().collect())
            }
        };
        let solver_candidate_states = match &state_candidates_source {
            StateCandidatesSource::Expanded(_) => Some(run_state_candidates.as_ref()),
            // Fully pinned init fallback is only for seeding initial states.
            // Do not filter transition solving to those pinned seeds.
            StateCandidatesSource::PinnedTemplate(_) => None,
        };
        let solver_candidate_state_count = solver_candidate_states.map_or(0, |c| c.len());
        let allow_partial_helper_solve = solver_candidate_states.is_none();

        let initial_states_started = Instant::now();
        let initial_states = construct_initial_states(
            &bundle.entrypoints.linit,
            run_state_candidates.as_ref(),
            Some(constants_value),
            bounds,
            InitHooks {
                call_evaluator: Some(&|func_path, args| {
                    eval_spec_function_call_recursive(
                        &bundle.spec_functions,
                        &bundle.schema,
                        model_config,
                        func_path,
                        args,
                        bounds,
                        0,
                    )
                }),
                method_evaluator: None,
                quantifier_domain_evaluator: Some(&quantifier_domain_evaluator),
            },
        )
        .map_err(|e| miette::miette!("{}", e))?;
        run_initial_state_construction_ms = run_initial_state_construction_ms
            .saturating_add(initial_states_started.elapsed().as_millis());

        let mut successor_cache = BTreeMap::<String, Vec<TracedSuccessor>>::new();
        let cooperative_timeout_hit = std::cell::Cell::new(false);
        let mut solve_traced_successors_for_state =
            |state: &verus_transpiler::modelcheck::value::RuntimeValue,
             update_enumeration_telemetry: bool|
             -> verus_transpiler::error::TranspileResult<Vec<TracedSuccessor>> {
                let state_key = state.canonical_key();
                if let Some(cached) = successor_cache.get(&state_key) {
                    run_enumeration_summary.successor_cache_hits = run_enumeration_summary
                        .successor_cache_hits
                        .saturating_add(1);
                    return Ok(cached.clone());
                }

                run_enumeration_summary.successor_cache_misses = run_enumeration_summary
                    .successor_cache_misses
                    .saturating_add(1);
                let mut traced_successors = Vec::new();
                let solve_timeout_reached = || {
                    let hit = run_started.elapsed().as_millis() >= u128::from(limits.timeout_ms);
                    if hit {
                        cooperative_timeout_hit.set(true);
                    }
                    hit
                };
                for branch in &transition.branches {
                    if solve_timeout_reached() {
                        break;
                    }
                    if por_pruned_branch_labels.contains(&branch.label) {
                        continue;
                    }
                    let branch_assignments = assignments_by_branch
                        .get(&branch.label)
                        .map(Vec::as_slice)
                        .unwrap_or(&[]);
                    let call_evaluator =
                        |func_path: &verus_transpiler::ast::Path,
                         args: &[verus_transpiler::modelcheck::value::RuntimeValue]| {
                            eval_spec_function_call_recursive(
                                &bundle.spec_functions,
                                &bundle.schema,
                                model_config,
                                func_path,
                                args,
                                bounds,
                                0,
                            )
                        };
                    let predicate_only_branch_solver =
                        |transition_ir: &verus_transpiler::modelcheck::ir::TransitionIr,
                         branch_ir: &verus_transpiler::modelcheck::ir::TransitionBranchIr,
                         current_state: &verus_transpiler::modelcheck::value::RuntimeValue,
                         constants: Option<&verus_transpiler::modelcheck::value::RuntimeValue>,
                         existential_assignments:
                             &[verus_transpiler::modelcheck::domain::ExistentialAssignment],
                         bounds: verus_transpiler::modelcheck::value::RuntimeCollectionBounds| {
                            try_solve_predicate_only_helper_branch(
                                transition_ir,
                                branch_ir,
                                current_state,
                                constants,
                                existential_assignments,
                                bundle,
                                model_config,
                                bounds,
                                allow_partial_helper_solve,
                            )
                        };
                    let branch_solve_started = Instant::now();
                    let solved = solve_branch_successors_with_candidates_and_telemetry(
                        &transition,
                        branch,
                        state,
                        Some(constants_value),
                        branch_assignments,
                        solver_candidate_states,
                        Some(candidate_eval_guardrail),
                        bounds,
                        SolverHooks {
                            call_evaluator: Some(&call_evaluator),
                            method_evaluator: None,
                            quantifier_domain_evaluator: Some(&quantifier_domain_evaluator),
                            predicate_only_branch_solver: Some(&predicate_only_branch_solver),
                            bytecode_cache: bytecode_cache.as_ref(),
                            native_cache: native_cache.as_ref(),
                        },
                        Some(&solve_timeout_reached),
                    )?;
                    let branch_solve_elapsed_ms = branch_solve_started.elapsed().as_millis();
                    let successful_successors = solved.successors.len();
                    if update_enumeration_telemetry {
                        run_successor_solving_total_ms =
                            run_successor_solving_total_ms.saturating_add(branch_solve_elapsed_ms);
                        run_candidate_evaluation_ms = run_candidate_evaluation_ms.saturating_add(
                            solved.telemetry.enumeration_candidate_evaluation_elapsed_ms,
                        );
                    }

                    if update_enumeration_telemetry {
                        run_enumeration_summary.direct_assignment_branch_solves +=
                            solved.telemetry.direct_assignment_branch_solves;
                        run_enumeration_summary.enumeration_fallback_branch_solves +=
                            solved.telemetry.enumeration_fallback_branch_solves;
                        run_enumeration_summary.enumeration_candidate_evaluations +=
                            solved.telemetry.enumeration_candidate_evaluations;
                        run_enumeration_summary.guard_pruned_candidate_evaluations +=
                            solved.telemetry.guard_pruned_candidate_evaluations;

                        let entry = run_branch_telemetry
                            .entry(branch.label.clone())
                            .or_insert_with(|| ModelCheckBranchTelemetrySummary {
                                branch_label: branch.label.clone(),
                                invocations: 0,
                                existential_assignment_count: branch_assignments.len().max(1),
                                candidate_state_count: solver_candidate_state_count,
                                direct_solver_hits: 0,
                                enumeration_fallback_hits: 0,
                                guard_pruned_candidate_evaluations: 0,
                                successful_successors: 0,
                                cumulative_solve_elapsed_ms: 0,
                                direct_assigned_fields: 0,
                                deferred_constraint_evaluations: 0,
                                evaluator_calls: 0,
                                guard_pruned_assignments: 0,
                                eq_constraints: 0,
                                predicate_constraints: 0,
                                fallback_reason: 0,
                            });
                        entry.invocations = entry.invocations.saturating_add(1);
                        entry.existential_assignment_count = entry
                            .existential_assignment_count
                            .max(branch_assignments.len().max(1));
                        entry.candidate_state_count = entry
                            .candidate_state_count
                            .max(solver_candidate_state_count);
                        entry.direct_solver_hits = entry
                            .direct_solver_hits
                            .saturating_add(solved.telemetry.direct_assignment_branch_solves);
                        entry.enumeration_fallback_hits = entry
                            .enumeration_fallback_hits
                            .saturating_add(solved.telemetry.enumeration_fallback_branch_solves);
                        entry.guard_pruned_candidate_evaluations = entry
                            .guard_pruned_candidate_evaluations
                            .saturating_add(solved.telemetry.guard_pruned_candidate_evaluations);
                        entry.successful_successors = entry
                            .successful_successors
                            .saturating_add(successful_successors);
                        entry.cumulative_solve_elapsed_ms = entry
                            .cumulative_solve_elapsed_ms
                            .saturating_add(branch_solve_elapsed_ms);
                        entry.direct_assigned_fields = entry
                            .direct_assigned_fields
                            .max(solved.telemetry.direct_assigned_fields);
                        entry.deferred_constraint_evaluations = entry
                            .deferred_constraint_evaluations
                            .max(solved.telemetry.deferred_constraint_evaluations);
                        entry.evaluator_calls = entry
                            .evaluator_calls
                            .saturating_add(solved.telemetry.evaluator_calls);
                        entry.guard_pruned_assignments = entry
                            .guard_pruned_assignments
                            .saturating_add(solved.telemetry.guard_pruned_assignments);
                        entry.eq_constraints =
                            entry.eq_constraints.max(solved.telemetry.eq_constraints);
                        entry.predicate_constraints = entry
                            .predicate_constraints
                            .max(solved.telemetry.predicate_constraints);
                        // Keep the first non-zero fallback reason seen
                        if entry.fallback_reason == 0 {
                            entry.fallback_reason = solved.telemetry.fallback_reason;
                        }
                    }

                    for successor in solved.successors {
                        traced_successors.push(TracedSuccessor {
                            action_branch: branch.label.clone(),
                            state: successor,
                        });
                    }
                }

                if traced_successors.is_empty()
                    && matches!(
                        empty_successor_semantics,
                        verus_transpiler::modelcheck::solver::EmptySuccessorSemantics::Stuttering
                    )
                {
                    traced_successors.push(TracedSuccessor {
                        action_branch: "stutter".to_string(),
                        state: state.clone(),
                    });
                }

                successor_cache.insert(state_key, traced_successors.clone());
                Ok(traced_successors)
            };

        let exploration_started = Instant::now();
        let mut debug_exporter = export_parity_debug.map(|dir| {
            ParityDebugExporter::new(dir)
                .unwrap_or_else(|e| panic!("Failed to create parity debug exporter: {e}"))
        });
        // Phase 38.18.10: when --search dpor is selected, route through
        // the relocated DPOR sleep-set explorer (in
        // `transpiler/src/modelcheck/dpor/`) instead of plain BFS/DFS.
        // The DPOR result is adapted into the same ExplorationResult
        // shape so the existing JSON-report code path keeps working.
        let mut exploration = if matches!(selected_search, CliSearchMode::Dpor) {
            run_dpor_explorer_as_main_path(
                bundle,
                model_config,
                bounds,
                constants_value,
                &owned_invariants,
                limits,
                native_cache.as_ref().map(|nc| nc.rlib_paths()),
                conflict_profile,
                workers,
            )
            .map_err(|e| miette::miette!("{}", e))?
        } else if workers > 1 && matches!(selected_search, CliSearchMode::Bfs) {
            // Phase 38.21.B: parallel BFS with rayon.
            // Uses fresh closures without mutable captures (no successor
            // cache or telemetry counters) so they are Fn + Sync + Send.
            //
            // Safety: bundle, transition, assignments_by_branch, and related
            // data are borrowed immutably for the duration of exploration.
            // The types are not Sync only because they contain proc_macro2::Span
            // and Rc<()> internally, but no mutation occurs.
            struct SyncRef<T>(T);
            unsafe impl<T> Sync for SyncRef<T> {}
            unsafe impl<T> Send for SyncRef<T> {}
            impl<T> std::ops::Deref for SyncRef<T> {
                type Target = T;
                fn deref(&self) -> &T {
                    &self.0
                }
            }
            let sync_bundle = SyncRef(bundle);
            let sync_transition = SyncRef(&transition);
            let sync_assignments = SyncRef(&assignments_by_branch);
            let sync_por = SyncRef(&por_pruned_branch_labels);
            let sync_invariants = SyncRef(&owned_invariants);
            let sync_qde = SyncRef(&quantifier_domain_evaluator);
            let par_successor_fn = |state: &verus_transpiler::modelcheck::value::RuntimeValue| -> verus_transpiler::error::TranspileResult<
                Vec<TracedSuccessor>,
            > {
                let bundle = &*sync_bundle;
                let transition = &**sync_transition;
                let assignments_by_branch = &**sync_assignments;
                let por_pruned = &**sync_por;
                let qde = &**sync_qde;
                let mut traced_successors = Vec::new();
                for branch in &transition.branches {
                    if por_pruned.contains(&branch.label) {
                        continue;
                    }
                    let branch_assignments = assignments_by_branch
                        .get(&branch.label)
                        .map(Vec::as_slice)
                        .unwrap_or(&[]);
                    let call_evaluator =
                        |func_path: &verus_transpiler::ast::Path,
                         args: &[verus_transpiler::modelcheck::value::RuntimeValue]| {
                            eval_spec_function_call_recursive(
                                &bundle.spec_functions,
                                &bundle.schema,
                                model_config,
                                func_path,
                                args,
                                bounds,
                                0,
                            )
                        };
                    let predicate_only_branch_solver =
                        |transition_ir: &verus_transpiler::modelcheck::ir::TransitionIr,
                         branch_ir: &verus_transpiler::modelcheck::ir::TransitionBranchIr,
                         current_state: &verus_transpiler::modelcheck::value::RuntimeValue,
                         constants: Option<&verus_transpiler::modelcheck::value::RuntimeValue>,
                         existential_assignments:
                             &[verus_transpiler::modelcheck::domain::ExistentialAssignment],
                         bounds: verus_transpiler::modelcheck::value::RuntimeCollectionBounds| {
                            try_solve_predicate_only_helper_branch(
                                transition_ir,
                                branch_ir,
                                current_state,
                                constants,
                                existential_assignments,
                                bundle,
                                model_config,
                                bounds,
                                solver_candidate_states.is_none(),
                            )
                        };
                    let solved = solve_branch_successors_with_candidates_and_telemetry(
                        transition,
                        branch,
                        state,
                        Some(constants_value),
                        branch_assignments,
                        solver_candidate_states,
                        Some(candidate_eval_guardrail),
                        bounds,
                        SolverHooks {
                            call_evaluator: Some(&call_evaluator),
                            method_evaluator: None,
                            quantifier_domain_evaluator: Some(qde),
                            predicate_only_branch_solver: Some(&predicate_only_branch_solver),
                            bytecode_cache: bytecode_cache.as_ref(),
                            native_cache: native_cache.as_ref(),
                        },
                        None, // no cooperative timeout for parallel workers
                    )?;
                    for successor in solved.successors {
                        traced_successors.push(TracedSuccessor {
                            action_branch: branch.label.clone(),
                            state: successor,
                        });
                    }
                }
                if traced_successors.is_empty()
                    && matches!(
                        empty_successor_semantics,
                        verus_transpiler::modelcheck::solver::EmptySuccessorSemantics::Stuttering
                    )
                {
                    traced_successors.push(TracedSuccessor {
                        action_branch: "stutter".to_string(),
                        state: state.clone(),
                    });
                }
                Ok(traced_successors)
            };
            explore_bfs_parallel(
                &initial_states,
                limits,
                model_config.properties.check_deadlock,
                par_successor_fn,
                |state, _depth| {
                    let bundle = &*sync_bundle;
                    let invariants = &**sync_invariants;
                    let qde = &**sync_qde;
                    first_invariant_violation(
                        invariants,
                        state,
                        Some(constants_value),
                        bounds,
                        InvariantHooks {
                            call_evaluator: Some(&|func_path, args| {
                                eval_spec_function_call_recursive(
                                    &bundle.spec_functions,
                                    &bundle.schema,
                                    model_config,
                                    func_path,
                                    args,
                                    bounds,
                                    0,
                                )
                            }),
                            method_evaluator: None,
                            quantifier_domain_evaluator: Some(qde),
                        },
                    )
                },
                workers,
            )
            .map_err(|e| miette::miette!("{}", e))?
        } else {
            explore_state_space_with_traces_dedup_and_debug(
                &initial_states,
                search_mode,
                limits,
                model_config.search.state_dedup,
                &model_config.search.symmetry_fields,
                model_config.properties.check_deadlock,
                |state| solve_traced_successors_for_state(state, true),
                |state, _depth| {
                    let invariant_started = Instant::now();
                    let result = first_invariant_violation(
                        &owned_invariants,
                        state,
                        Some(constants_value),
                        bounds,
                        InvariantHooks {
                            call_evaluator: Some(&|func_path, args| {
                                eval_spec_function_call_recursive(
                                    &bundle.spec_functions,
                                    &bundle.schema,
                                    model_config,
                                    func_path,
                                    args,
                                    bounds,
                                    0,
                                )
                            }),
                            method_evaluator: None,
                            quantifier_domain_evaluator: Some(&quantifier_domain_evaluator),
                        },
                    );
                    run_invariant_evaluation_ms = run_invariant_evaluation_ms
                        .saturating_add(invariant_started.elapsed().as_millis());
                    result
                },
                debug_exporter.as_mut(),
            )
            .map_err(|e| miette::miette!("{}", e))?
        };
        let exploration_elapsed_ms = exploration_started.elapsed().as_millis();
        if cooperative_timeout_hit.get()
            && matches!(
                exploration.stop_reason,
                ExplorationStopReason::FrontierExhausted
            )
        {
            exploration.stop_reason = ExplorationStopReason::TimeoutReached;
        }

        let mut leads_to_violation = None;
        if !model_config.properties.leads_to.is_empty()
            && matches!(
                exploration.stop_reason,
                ExplorationStopReason::FrontierExhausted
            )
        {
            let explored_graph = build_explored_graph_index(&exploration.explored, |state| {
                solve_traced_successors_for_state(state, false)
            })
            .map_err(|e| miette::miette!("{}", e))?;

            let resolved_leads_to = resolve_leads_to_obligations(
                &bundle.spec_functions,
                &model_config.properties.leads_to,
            )
            .map_err(|e| miette::miette!("{}", e))?;
            leads_to_violation = check_leads_to_violations(
                &explored_graph,
                &resolved_leads_to,
                &model_config.properties.fairness,
                Some(constants_value),
                bounds,
                LivenessHooks {
                    call_evaluator: Some(&|func_path, args| {
                        eval_spec_function_call_recursive(
                            &bundle.spec_functions,
                            &bundle.schema,
                            model_config,
                            func_path,
                            args,
                            bounds,
                            0,
                        )
                    }),
                    method_evaluator: None,
                    quantifier_domain_evaluator: Some(&quantifier_domain_evaluator),
                },
            )
            .map_err(|e| miette::miette!("{}", e))?;
        }

        let result = if leads_to_violation.is_some() {
            "leads_to_violated".to_string()
        } else {
            model_check_result_label(exploration.stop_reason).to_string()
        };

        let liveness_summary = if !model_config.properties.leads_to.is_empty()
            || !model_config.properties.fairness.weak.is_empty()
            || !model_config.properties.fairness.strong.is_empty()
        {
            let checked = !model_config.properties.leads_to.is_empty()
                && matches!(
                    exploration.stop_reason,
                    ExplorationStopReason::FrontierExhausted
                );
            let skipped_reason = if checked {
                None
            } else if model_config.properties.leads_to.is_empty() {
                Some("no_leads_to_obligations".to_string())
            } else {
                Some("incomplete_exploration".to_string())
            };

            Some(ModelCheckLivenessSummary {
                obligations: model_config.properties.leads_to.len(),
                fairness_weak: model_config.properties.fairness.weak.len(),
                fairness_strong: model_config.properties.fairness.strong.len(),
                checked,
                violation_found: leads_to_violation.is_some(),
                skipped_reason,
            })
        } else {
            None
        };

        let run_successor_solving_ms =
            run_successor_solving_total_ms.saturating_sub(run_candidate_evaluation_ms);
        let run_dedup_hashing_normalization_ms = exploration_elapsed_ms
            .saturating_sub(run_initial_state_construction_ms)
            .saturating_sub(run_successor_solving_total_ms)
            .saturating_sub(run_invariant_evaluation_ms);
        let run_timing = ModelCheckPhaseTimingSummary {
            source_ingestion_parsing_ms: 0,
            model_config_resolution_ms: 0,
            initial_state_construction_ms: run_initial_state_construction_ms,
            successor_solving_ms: run_successor_solving_ms,
            candidate_generation_evaluation_ms: run_candidate_generation_ms
                .saturating_add(run_candidate_evaluation_ms),
            dedup_hashing_normalization_ms: run_dedup_hashing_normalization_ms,
            invariant_evaluation_ms: run_invariant_evaluation_ms,
            report_serialization_output_ms: 0,
        };

        let run_summary = ModelCheckExecutionSummary {
            result,
            states: exploration.stats.visited_states,
            transitions: exploration.stats.successors_considered,
            depth: exploration
                .explored
                .iter()
                .map(|s| s.depth)
                .max()
                .unwrap_or(0),
            elapsed_ms: run_started.elapsed().as_millis(),
            constants_valuations_total,
            constants_valuations_explored,
            timing: run_timing,
            enumeration: run_enumeration_summary,
            branch_telemetry: run_branch_telemetry.values().cloned().collect(),
            liveness: liveness_summary,
        };

        timing_summary.initial_state_construction_ms = timing_summary
            .initial_state_construction_ms
            .saturating_add(run_timing.initial_state_construction_ms);
        timing_summary.successor_solving_ms = timing_summary
            .successor_solving_ms
            .saturating_add(run_timing.successor_solving_ms);
        timing_summary.candidate_generation_evaluation_ms = timing_summary
            .candidate_generation_evaluation_ms
            .saturating_add(run_timing.candidate_generation_evaluation_ms);
        timing_summary.invariant_evaluation_ms = timing_summary
            .invariant_evaluation_ms
            .saturating_add(run_timing.invariant_evaluation_ms);
        timing_summary.dedup_hashing_normalization_ms = timing_summary
            .dedup_hashing_normalization_ms
            .saturating_add(run_timing.dedup_hashing_normalization_ms);
        for entry in &run_summary.branch_telemetry {
            let aggregate = branch_telemetry_summary
                .entry(entry.branch_label.clone())
                .or_insert_with(|| ModelCheckBranchTelemetrySummary {
                    branch_label: entry.branch_label.clone(),
                    invocations: 0,
                    existential_assignment_count: 0,
                    candidate_state_count: 0,
                    direct_solver_hits: 0,
                    enumeration_fallback_hits: 0,
                    guard_pruned_candidate_evaluations: 0,
                    successful_successors: 0,
                    cumulative_solve_elapsed_ms: 0,
                    direct_assigned_fields: 0,
                    deferred_constraint_evaluations: 0,
                    evaluator_calls: 0,
                    guard_pruned_assignments: 0,
                    eq_constraints: 0,
                    predicate_constraints: 0,
                    fallback_reason: 0,
                });
            aggregate.invocations = aggregate.invocations.saturating_add(entry.invocations);
            aggregate.existential_assignment_count = aggregate
                .existential_assignment_count
                .max(entry.existential_assignment_count);
            aggregate.candidate_state_count = aggregate
                .candidate_state_count
                .max(entry.candidate_state_count);
            aggregate.direct_solver_hits = aggregate
                .direct_solver_hits
                .saturating_add(entry.direct_solver_hits);
            aggregate.enumeration_fallback_hits = aggregate
                .enumeration_fallback_hits
                .saturating_add(entry.enumeration_fallback_hits);
            aggregate.guard_pruned_candidate_evaluations = aggregate
                .guard_pruned_candidate_evaluations
                .saturating_add(entry.guard_pruned_candidate_evaluations);
            aggregate.successful_successors = aggregate
                .successful_successors
                .saturating_add(entry.successful_successors);
            aggregate.cumulative_solve_elapsed_ms = aggregate
                .cumulative_solve_elapsed_ms
                .saturating_add(entry.cumulative_solve_elapsed_ms);
            aggregate.direct_assigned_fields = aggregate
                .direct_assigned_fields
                .max(entry.direct_assigned_fields);
            aggregate.deferred_constraint_evaluations = aggregate
                .deferred_constraint_evaluations
                .max(entry.deferred_constraint_evaluations);
            aggregate.evaluator_calls = aggregate
                .evaluator_calls
                .saturating_add(entry.evaluator_calls);
            aggregate.guard_pruned_assignments = aggregate
                .guard_pruned_assignments
                .saturating_add(entry.guard_pruned_assignments);
            aggregate.eq_constraints = aggregate.eq_constraints.max(entry.eq_constraints);
            aggregate.predicate_constraints = aggregate
                .predicate_constraints
                .max(entry.predicate_constraints);
            if aggregate.fallback_reason == 0 {
                aggregate.fallback_reason = entry.fallback_reason;
            }
        }

        aggregated_states = aggregated_states.saturating_add(run_summary.states);
        aggregated_transitions = aggregated_transitions.saturating_add(run_summary.transitions);
        aggregated_depth = aggregated_depth.max(run_summary.depth);
        enumeration_summary.direct_assignment_branch_solves = enumeration_summary
            .direct_assignment_branch_solves
            .saturating_add(run_summary.enumeration.direct_assignment_branch_solves);
        enumeration_summary.enumeration_fallback_branch_solves = enumeration_summary
            .enumeration_fallback_branch_solves
            .saturating_add(run_summary.enumeration.enumeration_fallback_branch_solves);
        enumeration_summary.enumeration_candidate_evaluations = enumeration_summary
            .enumeration_candidate_evaluations
            .saturating_add(run_summary.enumeration.enumeration_candidate_evaluations);
        enumeration_summary.guard_pruned_candidate_evaluations = enumeration_summary
            .guard_pruned_candidate_evaluations
            .saturating_add(run_summary.enumeration.guard_pruned_candidate_evaluations);
        enumeration_summary.successor_cache_hits = enumeration_summary
            .successor_cache_hits
            .saturating_add(run_summary.enumeration.successor_cache_hits);
        enumeration_summary.successor_cache_misses = enumeration_summary
            .successor_cache_misses
            .saturating_add(run_summary.enumeration.successor_cache_misses);

        let run_execution = ModelCheckExecution {
            summary: run_summary,
            exploration,
            por_pruned_branches: por_pruned_branches.clone(),
            leads_to_violation,
        };
        if run_execution.leads_to_violation.is_some()
            || matches!(
                run_execution.exploration.stop_reason,
                ExplorationStopReason::InvariantViolated | ExplorationStopReason::DeadlockDetected
            )
        {
            first_violation_execution = Some(run_execution);
            break;
        }
        if !matches!(
            run_execution.exploration.stop_reason,
            ExplorationStopReason::FrontierExhausted
        ) {
            if first_incomplete_execution.is_none() {
                first_incomplete_execution = Some(run_execution);
            }
            continue;
        }
        if first_ok_execution.is_none() {
            first_ok_execution = Some(run_execution);
        }
    }

    let mut execution = first_violation_execution
        .or(first_incomplete_execution)
        .or(first_ok_execution)
        .ok_or_else(|| {
            miette::miette!(
                "Model-check constants resolution produced no runnable `LConstants` valuations."
            )
        })?;

    execution.summary.states = aggregated_states;
    execution.summary.transitions = aggregated_transitions;
    execution.summary.depth = aggregated_depth;
    execution.summary.elapsed_ms = started.elapsed().as_millis();
    execution.summary.constants_valuations_total = constants_valuations_total;
    execution.summary.constants_valuations_explored = constants_valuations_explored;
    execution.summary.enumeration = enumeration_summary;
    execution.summary.branch_telemetry = branch_telemetry_summary.values().cloned().collect();
    let total_core_ms = execution.summary.elapsed_ms;
    timing_summary.dedup_hashing_normalization_ms = total_core_ms
        .saturating_sub(timing_summary.initial_state_construction_ms)
        .saturating_sub(timing_summary.successor_solving_ms)
        .saturating_sub(timing_summary.candidate_generation_evaluation_ms)
        .saturating_sub(timing_summary.invariant_evaluation_ms);
    execution.summary.timing = timing_summary;

    Ok(execution)
}

#[allow(clippy::too_many_arguments)]
fn run_model_check_command(
    input: &Path,
    types: Option<&Path>,
    init: &str,
    next: &str,
    invariant_overrides: &[String],
    search: Option<CliSearchMode>,
    max_depth: Option<usize>,
    max_states: Option<usize>,
    timeout_ms: Option<u64>,
    model: &Path,
    export_parity_debug: Option<&Path>,
    use_bytecode: bool,
    use_native_codegen: bool,
    workers: usize,
    conflict_profile: bool,
) -> Result<ModelCheckCommandExecution> {
    use std::time::Instant;
    use verus_transpiler::modelcheck::config::{
        apply_model_config_overrides, parse_model_config_file, ModelConfigOverrides,
    };
    use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
    use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

    let source_ingestion_started = Instant::now();
    let bundle = ingest_protocol_sources_with_types_and_entrypoints(input, types, init, next)
        .map_err(|e| miette::miette!("{}", e))?;
    let source_ingestion_parsing_ms = source_ingestion_started.elapsed().as_millis();

    let model_resolution_started = Instant::now();
    let mut model_config = parse_model_config_file(model).map_err(|e| miette::miette!("{}", e))?;
    let overrides = ModelConfigOverrides {
        max_depth,
        max_states,
        timeout_ms,
        ..ModelConfigOverrides::default()
    };
    apply_model_config_overrides(&mut model_config, &overrides)
        .map_err(|e| miette::miette!("{}", e))?;

    if !invariant_overrides.is_empty() {
        let mut normalized = Vec::with_capacity(invariant_overrides.len());
        let mut seen = HashSet::new();
        for name in invariant_overrides {
            let trimmed = name.trim();
            if trimmed.is_empty() {
                return Err(miette::miette!(
                    "Invalid --invariant override: names cannot be empty."
                ));
            }
            let owned = trimmed.to_string();
            if !seen.insert(owned.clone()) {
                return Err(miette::miette!(
                    "Invalid --invariant override: duplicate invariant `{}`.",
                    owned
                ));
            }
            normalized.push(owned);
        }
        model_config.properties.invariants = normalized;
    }

    let selected_search = search.unwrap_or(CliSearchMode::Bfs);
    let selected_invariants =
        resolve_selected_invariants(&bundle.spec_functions, &model_config.properties.invariants)
            .map_err(|e| miette::miette!("{}", e))?;
    let model_config_resolution_ms = model_resolution_started.elapsed().as_millis();
    let resolved_invariant_names = selected_invariants
        .iter()
        .map(|invariant_fn| invariant_fn.name.clone())
        .collect::<Vec<_>>();
    let mut execution = execute_model_check(
        &bundle,
        &model_config,
        selected_search,
        &selected_invariants,
        export_parity_debug,
        use_bytecode,
        use_native_codegen,
        workers,
        conflict_profile,
    )?;
    execution.summary.timing.source_ingestion_parsing_ms = source_ingestion_parsing_ms;
    execution.summary.timing.model_config_resolution_ms = model_config_resolution_ms;

    Ok(ModelCheckCommandExecution {
        bundle,
        model_config,
        selected_search,
        resolved_invariant_names,
        execution,
    })
}

/// Handle subcommands
fn handle_command(command: &Commands, cli: &Cli) -> Result<()> {
    match command {
        Commands::ListTemplates => {
            println!("Supported quantifier templates:");
            println!("  - SeqComprehension: forall |i: int| 0 <= i < len ==> seq[i] == f(i)");
            println!("  - MapComprehension: forall |k| k in domain ==> map[k] == f(k)");
            println!("  - SetComprehension: forall |x| x in set <==> predicate(x)");
            println!("  - StructConstruction: s_.field1 == v1 &&& s_.field2 == v2");
            Ok(())
        }
        Commands::Check { annotations } => {
            use verus_transpiler::AnnotationParser;
            if cli.verbose {
                eprintln!("Checking: {}", annotations.display());
            }
            let content = std::fs::read_to_string(annotations)
                .map_err(|e| miette::miette!("Failed to read annotation file: {}", e))?;
            let parser = AnnotationParser::new(content);
            match parser.parse() {
                Ok(modules) => {
                    println!("OK: {} module(s) parsed successfully", modules.len());
                    for module in &modules {
                        println!(
                            "  - {} ({} functions)",
                            module.module_path,
                            module.functions.len()
                        );
                    }
                }
                Err(e) => {
                    return Err(miette::miette!("Parse error: {}", e));
                }
            }
            Ok(())
        }
        Commands::ModelConfig {
            model,
            max_depth,
            max_states,
            timeout_ms,
            max_seq_len,
            max_set_len,
            max_map_len,
            int_range,
            nat_max,
            candidate_eval_guardrail,
        } => {
            use verus_transpiler::modelcheck::config::{
                apply_model_config_overrides, parse_int_range_override, parse_model_config_file,
                ModelConfigOverrides,
            };

            if cli.verbose {
                eprintln!("Loading model config: {}", model.display());
            }

            let mut config =
                parse_model_config_file(model).map_err(|e| miette::miette!("{}", e))?;
            let parsed_int_range = if let Some(raw) = int_range {
                Some(parse_int_range_override(raw).map_err(|e| miette::miette!("{}", e))?)
            } else {
                None
            };

            let overrides = ModelConfigOverrides {
                max_depth: *max_depth,
                max_states: *max_states,
                timeout_ms: *timeout_ms,
                max_seq_len: *max_seq_len,
                max_set_len: *max_set_len,
                max_map_len: *max_map_len,
                int_range: parsed_int_range,
                nat_max: *nat_max,
                candidate_eval_guardrail: *candidate_eval_guardrail,
            };
            apply_model_config_overrides(&mut config, &overrides)
                .map_err(|e| miette::miette!("{}", e))?;

            let rendered = toml::to_string_pretty(&config)
                .map_err(|e| miette::miette!("Failed to serialize resolved model config: {}", e))?;
            println!("{}", rendered);
            Ok(())
        }
        Commands::ModelCheck {
            input,
            types,
            init,
            next,
            invariant,
            search,
            max_depth,
            max_states,
            timeout_ms,
            json_report,
            export_parity,
            export_parity_debug,
            model,
            no_bytecode,
            native_codegen,
            workers,
            conflict_profile,
        } => {
            if cli.verbose {
                eprintln!("Loading protocol spec: {}", input.display());
                if let Some(types_file) = types {
                    eprintln!("Loading explicit types spec: {}", types_file.display());
                }
                eprintln!("Entrypoints: init=`{}`, next=`{}`", init, next);
                eprintln!("Loading model config: {}", model.display());
            }

            let ModelCheckCommandExecution {
                bundle,
                model_config,
                selected_search,
                resolved_invariant_names,
                mut execution,
            } = run_model_check_command(
                input.as_path(),
                types.as_deref(),
                init,
                next,
                invariant,
                *search,
                *max_depth,
                *max_states,
                *timeout_ms,
                model.as_path(),
                export_parity_debug.as_deref(),
                !*no_bytecode,
                *native_codegen,
                *workers,
                *conflict_profile,
            )?;
            let search_evidence_mode = classify_search_evidence_mode(&model_config.search);

            // Parity export (Phase 36.1.3)
            if let Some(parity_dir) = export_parity {
                std::fs::create_dir_all(parity_dir).map_err(|e| {
                    miette::miette!("Failed to create parity export directory: {}", e)
                })?;

                // Identify initial states (depth 0 in explored set)
                let initial_keys: std::collections::BTreeSet<String> = execution
                    .exploration
                    .explored
                    .iter()
                    .filter(|s| s.depth == 0)
                    .map(|s| s.state.canonical_key())
                    .collect();

                // Deduplicate explored states by canonical key (keep shallowest depth)
                let mut deduped: std::collections::BTreeMap<
                    String,
                    &verus_transpiler::modelcheck::explorer::ExploredState,
                > = std::collections::BTreeMap::new();
                for es in &execution.exploration.explored {
                    let key = es.state.canonical_key();
                    let entry = deduped.entry(key);
                    use std::collections::btree_map::Entry;
                    match entry {
                        Entry::Vacant(e) => {
                            e.insert(es);
                        }
                        Entry::Occupied(mut e) => {
                            if es.depth < e.get().depth {
                                e.insert(es);
                            }
                        }
                    }
                }

                let states_path = parity_dir.join("states.jsonl");
                let mut states_file =
                    std::io::BufWriter::new(std::fs::File::create(&states_path).map_err(|e| {
                        miette::miette!("Failed to create {}: {}", states_path.display(), e)
                    })?);

                // Export states sorted by canonical key (BTreeMap order)
                for (key, es) in &deduped {
                    let line = serde_json::json!({
                        "id": key,
                        "state": es.state.to_canonical_json(),
                        "initial": initial_keys.contains(key),
                        "depth": es.depth,
                    });
                    use std::io::Write;
                    writeln!(states_file, "{}", serde_json::to_string(&line).unwrap())
                        .map_err(|e| miette::miette!("Write error: {}", e))?;
                }
                drop(states_file);

                eprintln!(
                    "Parity export: {} distinct states written to {}",
                    deduped.len(),
                    states_path.display()
                );
            }

            if *json_report {
                let mut report = serde_json::json!({
                    "result": execution.summary.result,
                    "protocol": bundle.protocol_file.display().to_string(),
                    "types": bundle.types_file.display().to_string(),
                    "entrypoints": {
                        "init": bundle.entrypoints.linit.name,
                        "next": bundle.entrypoints.lnext.name,
                    },
                    "invariants": {
                        "configured_count": model_config.properties.invariants.len(),
                        "resolved_count": resolved_invariant_names.len(),
                        "configured": model_config.properties.invariants,
                        "resolved": resolved_invariant_names,
                    },
                    "search": {
                        "strategy": selected_search.as_str(),
                        "successor_semantics": model_config.properties.successor_semantics,
                        "state_dedup": model_config.search.state_dedup,
                        "symmetry_fields": model_config.search.symmetry_fields,
                        "por_heuristic": model_config.search.por_heuristic,
                        "por_pruned_branches": execution.por_pruned_branches,
                        "max_depth": model_config.search.max_depth,
                        "max_states": model_config.search.max_states,
                        "timeout_ms": model_config.search.timeout_ms,
                        "evidence_mode": {
                            "class": search_evidence_mode.class,
                            "proof_strength": search_evidence_mode.proof_strength,
                            "lossy_reasons": search_evidence_mode.lossy_reasons,
                            "guidance": search_evidence_mode.guidance,
                        },
                    },
                    "summary": {
                        "states": execution.summary.states,
                        "transitions": execution.summary.transitions,
                        "depth": execution.summary.depth,
                        "elapsed_ms": execution.summary.elapsed_ms,
                        "constants_valuations_total": execution.summary.constants_valuations_total,
                        "constants_valuations_explored": execution.summary.constants_valuations_explored,
                        "pruned_by_por": execution.por_pruned_branches.len(),
                        "hash_compaction_collisions": execution.exploration.stats.hash_compaction_collisions,
                        "symmetry_collapses": execution.exploration.stats.symmetry_collapses,
                        "direct_assignment_branch_solves": execution.summary.enumeration.direct_assignment_branch_solves,
                        "enumeration_fallback_branch_solves": execution.summary.enumeration.enumeration_fallback_branch_solves,
                        "enumeration_candidate_evaluations": execution.summary.enumeration.enumeration_candidate_evaluations,
                        "guard_pruned_candidate_evaluations": execution.summary.enumeration.guard_pruned_candidate_evaluations,
                        "candidate_evaluation_guardrail_per_state_branch": execution.summary.enumeration.candidate_evaluation_guardrail_per_state_branch,
                        "successor_cache_hits": execution.summary.enumeration.successor_cache_hits,
                        "successor_cache_misses": execution.summary.enumeration.successor_cache_misses,
                        "branch_telemetry": execution.summary.branch_telemetry.iter().map(|branch| serde_json::json!({
                            "branch_label": branch.branch_label,
                            "invocations": branch.invocations,
                            "existential_assignment_count": branch.existential_assignment_count,
                            "candidate_state_count": branch.candidate_state_count,
                            "direct_solver_hits": branch.direct_solver_hits,
                            "enumeration_fallback_hits": branch.enumeration_fallback_hits,
                            "guard_pruned_candidate_evaluations": branch.guard_pruned_candidate_evaluations,
                            "successful_successors": branch.successful_successors,
                            "cumulative_solve_elapsed_ms": branch.cumulative_solve_elapsed_ms,
                            "direct_assigned_fields": branch.direct_assigned_fields,
                            "deferred_constraint_evaluations": branch.deferred_constraint_evaluations,
                            "evaluator_calls": branch.evaluator_calls,
                            "guard_pruned_assignments": branch.guard_pruned_assignments,
                            "eq_constraints": branch.eq_constraints,
                            "predicate_constraints": branch.predicate_constraints,
                            "fallback_reason": match branch.fallback_reason {
                                0 => "direct",
                                1 => "no_next_state_assignment",
                                2 => "not_all_fields_assigned",
                                _ => "unknown",
                            },
                        })).collect::<Vec<_>>(),
                        "timing": {
                            "source_ingestion_parsing_ms": execution.summary.timing.source_ingestion_parsing_ms,
                            "model_config_resolution_ms": execution.summary.timing.model_config_resolution_ms,
                            "initial_state_construction_ms": execution.summary.timing.initial_state_construction_ms,
                            "successor_solving_ms": execution.summary.timing.successor_solving_ms,
                            "candidate_generation_evaluation_ms": execution.summary.timing.candidate_generation_evaluation_ms,
                            "dedup_hashing_normalization_ms": execution.summary.timing.dedup_hashing_normalization_ms,
                            "invariant_evaluation_ms": execution.summary.timing.invariant_evaluation_ms,
                            "report_serialization_output_ms": execution.summary.timing.report_serialization_output_ms,
                        },
                    },
                    "liveness": execution.summary.liveness.as_ref().map(|liveness| serde_json::json!({
                        "obligations": liveness.obligations,
                        "checked": liveness.checked,
                        "violation_found": liveness.violation_found,
                        "skipped_reason": liveness.skipped_reason,
                        "fairness": {
                            "weak_count": liveness.fairness_weak,
                            "strong_count": liveness.fairness_strong,
                            "weak": model_config.properties.fairness.weak,
                            "strong": model_config.properties.fairness.strong,
                        },
                    })),
                    "stop_reason": format!("{:?}", execution.exploration.stop_reason),
                    "invariant_violation": execution.exploration.invariant_violation.as_ref().map(|violation| serde_json::json!({
                        "invariant": violation.invariant,
                        "depth": violation.depth,
                        "state": violation.state.canonical_key(),
                    })),
                    "deadlock": execution.exploration.deadlock.as_ref().map(|deadlock| serde_json::json!({
                        "depth": deadlock.depth,
                        "state": deadlock.state.canonical_key(),
                    })),
                    "leads_to_violation": execution.leads_to_violation.as_ref().map(|violation| serde_json::json!({
                        "obligation": violation.obligation_name,
                        "from": violation.from_name,
                        "to": violation.to_name,
                        "component_size": violation.violating_component.len(),
                        "cycle_edge": {
                            "from": violation.representative_cycle_edge.from_key,
                            "to": violation.representative_cycle_edge.to_key,
                        },
                        "counterexample": {
                            "initial_state": violation.counterexample.initial_state.canonical_key(),
                            "steps": violation.counterexample.steps.iter().map(|step| serde_json::json!({
                                "action_branch": step.action_branch,
                                "state": step.state.canonical_key(),
                                "diffs": step.diffs.iter().map(|diff| serde_json::json!({
                                    "path": diff.path,
                                    "before": diff.before,
                                    "after": diff.after,
                                })).collect::<Vec<_>>(),
                            })).collect::<Vec<_>>(),
                        },
                    })),
                });
                let report_serialization_started = std::time::Instant::now();
                let _ = serde_json::to_string_pretty(&report).map_err(|e| {
                    miette::miette!("Failed to serialize model-check JSON report: {}", e)
                })?;
                let report_serialization_output_ms =
                    report_serialization_started.elapsed().as_millis();
                execution.summary.timing.report_serialization_output_ms =
                    report_serialization_output_ms;
                if let Some(summary) = report.get_mut("summary").and_then(|v| v.as_object_mut()) {
                    if let Some(timing) = summary.get_mut("timing").and_then(|v| v.as_object_mut())
                    {
                        timing.insert(
                            "report_serialization_output_ms".to_string(),
                            serde_json::json!(report_serialization_output_ms),
                        );
                    }
                    // Phase 36.1.8: pre-dedup counters for TLC parity mapping
                    let stats = &execution.exploration.stats;
                    summary.insert(
                        "generated_states".to_string(),
                        serde_json::json!(stats.initial_states + stats.successors_considered),
                    );
                    summary.insert(
                        "distinct_states".to_string(),
                        serde_json::json!(stats.visited_states),
                    );
                    summary.insert(
                        "duplicate_states".to_string(),
                        serde_json::json!(stats.duplicate_successors),
                    );
                    summary.insert(
                        "initial_states".to_string(),
                        serde_json::json!(stats.initial_states),
                    );
                    summary.insert(
                        "explored_states".to_string(),
                        serde_json::json!(stats.explored_states),
                    );
                }
                let rendered = serde_json::to_string_pretty(&report).map_err(|e| {
                    miette::miette!("Failed to serialize model-check JSON report: {}", e)
                })?;
                println!("{}", rendered);
                // Phase 38.22.1.a: dump eval_expr profile to stderr
                // when TLARS_EVAL_PROFILE=1.
                verus_transpiler::modelcheck::evaluator::dump_eval_expr_profile();
                // Phase 38.21.A.b: dump eval dispatch profile (native/bytecode/AST).
                verus_transpiler::modelcheck::solver::dump_eval_dispatch_profile();
                return Ok(());
            }

            println!("Model-check run complete");
            println!("  protocol: {}", bundle.protocol_file.display());
            println!("  types: {}", bundle.types_file.display());
            println!(
                "  entrypoints: init=`{}`, next=`{}`",
                bundle.entrypoints.linit.name, bundle.entrypoints.lnext.name
            );
            println!(
                "  invariants: configured={}, resolved={}",
                model_config.properties.invariants.len(),
                resolved_invariant_names.len()
            );
            println!(
                "  search: strategy={}, mode_semantics={:?}, state_dedup={:?}, symmetry_fields={:?}, por_heuristic={:?}, por_pruned_branches={}, max_depth={}, max_states={}, timeout_ms={}",
                selected_search.as_str(),
                model_config.properties.successor_semantics,
                model_config.search.state_dedup,
                model_config.search.symmetry_fields,
                model_config.search.por_heuristic,
                execution.por_pruned_branches.len(),
                model_config.search.max_depth,
                model_config.search.max_states,
                model_config.search.timeout_ms
            );
            println!(
                "  search_evidence: class={}, proof_strength={}, lossy_reasons={}",
                search_evidence_mode.class,
                search_evidence_mode.proof_strength,
                search_evidence_mode.lossy_reasons.join(",")
            );
            if !search_evidence_mode.proof_strength {
                println!("  search_evidence_note: {}", search_evidence_mode.guidance);
            }
            if !execution.por_pruned_branches.is_empty() {
                println!("  por_pruned_branches: {:?}", execution.por_pruned_branches);
            }
            println!("  result: {}", execution.summary.result);
            println!(
                "  summary: states={}, transitions={}, depth={}, elapsed_ms={}, constants_valuations_total={}, constants_valuations_explored={}, pruned_by_por={}, hash_compaction_collisions={}, symmetry_collapses={}",
                execution.summary.states,
                execution.summary.transitions,
                execution.summary.depth,
                execution.summary.elapsed_ms,
                execution.summary.constants_valuations_total,
                execution.summary.constants_valuations_explored,
                execution.por_pruned_branches.len(),
                execution.exploration.stats.hash_compaction_collisions,
                execution.exploration.stats.symmetry_collapses,
            );
            println!(
                "  solver_enumeration: direct_assignment_branch_solves={}, enumeration_fallback_branch_solves={}, enumeration_candidate_evaluations={}, guard_pruned_candidate_evaluations={}, candidate_eval_guardrail_per_state_branch={}, successor_cache_hits={}, successor_cache_misses={}",
                execution.summary.enumeration.direct_assignment_branch_solves,
                execution.summary.enumeration.enumeration_fallback_branch_solves,
                execution.summary.enumeration.enumeration_candidate_evaluations,
                execution.summary.enumeration.guard_pruned_candidate_evaluations,
                execution.summary.enumeration.candidate_evaluation_guardrail_per_state_branch,
                execution.summary.enumeration.successor_cache_hits,
                execution.summary.enumeration.successor_cache_misses,
            );
            println!(
                "  timing_ms: source_ingestion_parsing={}, model_config_resolution={}, initial_state_construction={}, successor_solving={}, candidate_generation_evaluation={}, dedup_hashing_normalization={}, invariant_evaluation={}, report_serialization_output={}",
                execution.summary.timing.source_ingestion_parsing_ms,
                execution.summary.timing.model_config_resolution_ms,
                execution.summary.timing.initial_state_construction_ms,
                execution.summary.timing.successor_solving_ms,
                execution.summary.timing.candidate_generation_evaluation_ms,
                execution.summary.timing.dedup_hashing_normalization_ms,
                execution.summary.timing.invariant_evaluation_ms,
                execution.summary.timing.report_serialization_output_ms,
            );
            if let Some(liveness) = &execution.summary.liveness {
                println!(
                    "  liveness: obligations={}, fairness_weak={}, fairness_strong={}, checked={}, violation_found={}, skipped_reason={}",
                    liveness.obligations,
                    liveness.fairness_weak,
                    liveness.fairness_strong,
                    liveness.checked,
                    liveness.violation_found,
                    liveness.skipped_reason.as_deref().unwrap_or("<none>")
                );
            }
            if let Some(violation) = &execution.exploration.invariant_violation {
                println!(
                    "  invariant_violation: invariant=`{}`, depth={}",
                    violation.invariant, violation.depth
                );
            }
            if let Some(deadlock) = &execution.exploration.deadlock {
                println!("  deadlock: depth={}", deadlock.depth);
            }
            if let Some(violation) = &execution.leads_to_violation {
                println!(
                    "  leads_to_violation: obligation=`{}` ({} ~> {}), component_size={}",
                    violation.obligation_name,
                    violation.from_name,
                    violation.to_name,
                    violation.violating_component.len()
                );
            }

            // Phase 38.21.A.e: dump eval profiles to stderr (non-JSON path).
            verus_transpiler::modelcheck::evaluator::dump_eval_expr_profile();
            verus_transpiler::modelcheck::solver::dump_eval_dispatch_profile();

            Ok(())
        }
        Commands::ReportAssumes { input_dir, output } => {
            if cli.verbose {
                eprintln!("Collecting assume report from {}", input_dir.display());
            }

            let report = collect_assume_report(input_dir.as_path())?;
            let rendered = serde_json::to_string_pretty(&report)
                .map_err(|e| miette::miette!("Failed to serialize assume report: {}", e))?;

            if let Some(output_path) = output {
                if let Some(parent) = output_path.parent() {
                    if !parent.as_os_str().is_empty() {
                        std::fs::create_dir_all(parent).map_err(|e| {
                            miette::miette!(
                                "Failed to create report output directory `{}`: {}",
                                parent.display(),
                                e
                            )
                        })?;
                    }
                }
                std::fs::write(output_path, rendered).map_err(|e| {
                    miette::miette!(
                        "Failed to write assume report `{}`: {}",
                        output_path.display(),
                        e
                    )
                })?;
                if cli.verbose {
                    eprintln!("Wrote assume report to {}", output_path.display());
                }
            } else {
                println!("{}", rendered);
            }

            Ok(())
        }
        Commands::GenerateMcWrapper {
            input,
            output,
            cfg_output,
            init,
            next,
            module_suffix,
            packet_mode,
            packet_var,
            invariant,
        } => {
            use verus_transpiler::tla::{generate_relational_mc_wrapper, McWrapperOptions};

            if cli.verbose {
                eprintln!("Generating model-check wrapper from {}", input.display());
                eprintln!("  output: {}", output.display());
                eprintln!("  init/next: {}/{}", init, next);
            }

            let source = std::fs::read_to_string(input)
                .map_err(|e| miette::miette!("Failed to read input module: {}", e))?;
            let options = McWrapperOptions {
                init_operator: init.clone(),
                next_operator: next.clone(),
                wrapper_suffix: module_suffix.clone(),
                packet_projection: packet_mode.as_internal(),
                packet_var: packet_var.clone(),
                invariants: invariant.clone(),
            };
            let artifacts = generate_relational_mc_wrapper(&source, &options)
                .map_err(|e| miette::miette!("{}", e))?;

            if let Some(parent) = output.parent() {
                if !parent.as_os_str().is_empty() {
                    std::fs::create_dir_all(parent).map_err(|e| {
                        miette::miette!(
                            "Failed to create output directory `{}`: {}",
                            parent.display(),
                            e
                        )
                    })?;
                }
            }
            std::fs::write(output, artifacts.wrapper_tla)
                .map_err(|e| miette::miette!("Failed to write wrapper output: {}", e))?;

            let cfg_path = cfg_output
                .clone()
                .unwrap_or_else(|| output.with_extension("cfg"));
            if let Some(parent) = cfg_path.parent() {
                if !parent.as_os_str().is_empty() {
                    std::fs::create_dir_all(parent).map_err(|e| {
                        miette::miette!(
                            "Failed to create cfg output directory `{}`: {}",
                            parent.display(),
                            e
                        )
                    })?;
                }
            }
            std::fs::write(&cfg_path, artifacts.cfg)
                .map_err(|e| miette::miette!("Failed to write cfg output: {}", e))?;

            println!(
                "Generated wrapper module `{}` at {}",
                artifacts.wrapper_module_name,
                output.display()
            );
            println!("Generated cfg at {}", cfg_path.display());
            Ok(())
        }
        Commands::GenerateTypes {
            input,
            output,
            config,
        } => {
            use verus_transpiler::types::TypeDef;
            use verus_transpiler::{TypeParser, TypeRegistry};

            if input.is_empty() {
                return Err(miette::miette!("At least one --input file is required"));
            }

            if cli.verbose {
                for f in input {
                    eprintln!("Input file: {}", f.display());
                }
            }

            // Load config for remappings, naming, imports, and type extensions if provided
            let mut file_config = if let Some(config_path) = config {
                if cli.verbose {
                    eprintln!("Loading config from: {}", config_path.display());
                }
                FileConfig::from_file(config_path)
                    .map_err(|e| miette::miette!("Failed to load config: {}", e))?
            } else {
                FileConfig::default()
            };

            // Auto-infer config from input spec files (clone_strategy, etc.)
            {
                let spec_paths: Vec<&Path> = input.iter().map(|p| p.as_path()).collect();
                let analysis_result = if spec_paths.len() > 1 {
                    analyze_spec_files(&spec_paths)
                } else {
                    analyze_spec_file(spec_paths[0])
                };
                match analysis_result {
                    Ok(schema) => {
                        let function_path_hints = infer_function_paths_from_spec_paths(
                            &spec_paths,
                            &schema,
                            &file_config.naming,
                        );
                        let method_call_hints = infer_method_calls_from_spec_paths(
                            &spec_paths,
                            &schema,
                            &file_config.naming,
                        );
                        let eq_function_field_hints = infer_eq_function_fields_from_spec_paths(
                            &spec_paths,
                            &schema,
                            &file_config.naming,
                        );
                        let type_view_expr_hints = infer_type_view_exprs_from_spec_paths(
                            &spec_paths,
                            &schema,
                            &file_config.naming,
                        );
                        let inferer = ConfigInferer::new(&schema, &file_config.naming)
                            .with_function_path_hints(function_path_hints)
                            .with_method_call_hints(method_call_hints)
                            .with_eq_function_field_hints(eq_function_field_hints)
                            .with_type_view_expr_hints(type_view_expr_hints);
                        let inferred = inferer.infer();
                        merge_configs(&mut file_config, &inferred);
                        if cli.verbose {
                            eprintln!(
                                "Auto-inferred config from {} file(s): {} structs, {} enums",
                                spec_paths.len(),
                                schema.structs.len(),
                                schema.enums.len()
                            );
                        }
                    }
                    Err(e) => {
                        if cli.verbose {
                            eprintln!("Note: spec analysis skipped ({})", e);
                        }
                    }
                }
            }

            let naming_config = file_config.naming.clone();
            let remapping = file_config.remapping.clone();
            let custom_imports = file_config.output.custom_imports.clone();
            let validity_predicate_name = file_config.output.validity_predicate_name.clone();
            let view_overrides = file_config.view_overrides.clone();
            let extra_fields = file_config.extra_fields.clone();
            let clone_strategy = file_config.clone_strategy.clone();
            let skip_types = file_config.skip_types.clone();
            let re_exports = file_config.re_exports.clone();
            let extra_type_aliases = file_config.extra_type_aliases.clone();
            let custom_derives = file_config.custom_derives.clone();
            let skip_fields = file_config.skip_fields.clone();
            let skip_validity_types = file_config.skip_validity_types.clone();
            let skip_view_types = file_config.skip_view_types.clone();
            let generate_clone_up_to_view_simple =
                file_config.output.generate_clone_up_to_view_simple;
            let generate_unreachable_value_helper =
                file_config.output.generate_unreachable_value_helper;
            // Note: manual_code is NOT injected during generate-types.
            // It is a function-generation concern (injected into *_gen.rs, not types_gen.rs).
            // Protocols that share a single TOML config for both types and functions
            // (e.g., Raft) would incorrectly inject function-level manual code into types.

            let mut registry = TypeRegistry::new();

            // Parse all input files in order (user provides dependency order)
            for input_file in input {
                if cli.verbose {
                    eprintln!("Parsing: {}", input_file.display());
                }
                let content = std::fs::read_to_string(input_file).map_err(|e| {
                    miette::miette!("Failed to read {}: {}", input_file.display(), e)
                })?;

                let mut parser = TypeParser::new(&content);
                let type_defs = parser.parse_types().map_err(|e| {
                    miette::miette!("Failed to parse {}: {}", input_file.display(), e)
                })?;

                for type_def in type_defs {
                    match type_def {
                        TypeDef::Struct(struct_def) => {
                            if cli.verbose {
                                eprintln!("  Found struct: {}", struct_def.name);
                            }
                            registry.register_struct(struct_def);
                        }
                        TypeDef::Enum(enum_def) => {
                            if cli.verbose {
                                eprintln!("  Found enum: {}", enum_def.name);
                            }
                            registry.register_enum(enum_def);
                        }
                        TypeDef::Alias(alias) => {
                            if cli.verbose {
                                eprintln!("  Found type alias: {}", alias.name);
                            }
                            registry.register_alias(alias);
                        }
                        TypeDef::Function(func) => {
                            if cli.verbose {
                                eprintln!("  Found spec function: {}", func.name);
                            }
                            registry.register_function(func);
                        }
                    }
                }
            }

            if registry.structs.is_empty()
                && registry.enums.is_empty()
                && registry.aliases.is_empty()
            {
                return Err(miette::miette!("No spec types found in input file(s)"));
            }

            // Generate exec types using the registry function
            let generated = verus_transpiler::codegen::generate_all_types_full(
                &verus_transpiler::codegen::TypeGenConfig {
                    registry: &registry,
                    naming: &naming_config,
                    remapping: &remapping,
                    custom_imports: &custom_imports,
                    validity_predicate_name: &validity_predicate_name,
                    view_overrides: &view_overrides,
                    extra_fields: &extra_fields,
                    clone_strategy: &clone_strategy,
                    skip_types: &skip_types,
                    re_exports: &re_exports,
                    extra_type_aliases: &extra_type_aliases,
                    custom_derives: &custom_derives,
                    skip_fields: &skip_fields,
                    skip_validity_types: &skip_validity_types,
                    skip_view_types: &skip_view_types,
                    generate_clone_up_to_view_simple,
                    generate_unreachable_value_helper,
                    manual_code: None,
                    arc_wrap_types: &file_config.arc_wrap_types,
                    arc_wrap_fields: &file_config.arc_wrap_fields,
                },
            );

            // Print any warnings
            for warning in &generated.warnings {
                eprintln!("Warning: {}", warning);
            }

            let all_code = generated.code;

            // Output
            if let Some(output_path) = output {
                std::fs::write(output_path, &all_code)
                    .map_err(|e| miette::miette!("Failed to write output: {}", e))?;
                println!(
                    "Generated {} structs, {} enums, {} aliases -> {}",
                    registry.structs.len(),
                    registry.enums.len(),
                    registry.aliases.len(),
                    output_path.display()
                );
            } else {
                println!("{}", all_code);
            }

            Ok(())
        }

        Commands::Verus2Tla {
            input,
            output,
            spec_prefix,
            include_recommends,
            generate_types,
            batch,
        } => {
            use verus_transpiler::verus2tla::{
                converter::{ConverterConfig, Verus2TlaConverter},
                printer::TlaPrinter,
            };

            // Configure converter
            let config = ConverterConfig {
                spec_prefix: spec_prefix.clone(),
                include_recommends: *include_recommends,
                generate_type_defs: *generate_types,
                ..ConverterConfig::default()
            };

            if *batch {
                // Batch mode: process all .rs files in input directory
                if !input.is_dir() {
                    return Err(miette::miette!(
                        "In batch mode, --input must be a directory, got: {}",
                        input.display()
                    ));
                }

                let output_dir = output.as_ref().ok_or_else(|| {
                    miette::miette!("In batch mode, --output must be specified as output directory")
                })?;

                // Create output directory if needed
                std::fs::create_dir_all(output_dir)
                    .map_err(|e| miette::miette!("Failed to create output directory: {}", e))?;

                if cli.verbose {
                    eprintln!("=== Verus to TLA+ Batch Conversion ===");
                    eprintln!("Input directory: {}", input.display());
                    eprintln!("Output directory: {}", output_dir.display());
                }

                // Find all .rs files (excluding mod.rs)
                let mut files: Vec<_> = std::fs::read_dir(input)
                    .map_err(|e| miette::miette!("Failed to read input directory: {}", e))?
                    .filter_map(|entry| entry.ok())
                    .filter(|entry| {
                        let path = entry.path();
                        path.is_file()
                            && path.extension().map(|e| e == "rs").unwrap_or(false)
                            && path.file_name().map(|n| n != "mod.rs").unwrap_or(true)
                    })
                    .collect();

                files.sort_by_key(|e| e.path());

                let printer = TlaPrinter::new();
                let mut converted_count = 0;

                for entry in files {
                    let input_path = entry.path();
                    let file_stem = input_path
                        .file_stem()
                        .and_then(|s| s.to_str())
                        .unwrap_or("module");

                    // Convert filename to TLA+ naming convention (capitalize first letter)
                    let tla_name = {
                        let mut chars = file_stem.chars();
                        match chars.next() {
                            None => file_stem.to_string(),
                            Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
                        }
                    };
                    let output_path = output_dir.join(format!("{}.tla", tla_name));

                    // Convert
                    let mut converter = Verus2TlaConverter::with_config(config.clone());
                    match converter.convert_file(&input_path) {
                        Ok(tla_module) => {
                            let tla_code = printer.print_module(&tla_module);
                            if let Err(e) = std::fs::write(&output_path, &tla_code) {
                                eprintln!(
                                    "Warning: Failed to write {}: {}",
                                    output_path.display(),
                                    e
                                );
                            } else {
                                if cli.verbose {
                                    eprintln!(
                                        "  {} -> {}",
                                        input_path.display(),
                                        output_path.display()
                                    );
                                }
                                converted_count += 1;
                            }
                        }
                        Err(e) => {
                            eprintln!("Warning: Failed to convert {}: {}", input_path.display(), e);
                        }
                    }
                }

                println!(
                    "Batch conversion complete: {} files converted to {}",
                    converted_count,
                    output_dir.display()
                );
            } else {
                // Single file mode
                if cli.verbose {
                    eprintln!("=== Verus to TLA+ Conversion ===");
                    eprintln!("Input: {}", input.display());
                }

                // Create converter and convert
                let mut converter = Verus2TlaConverter::with_config(config);
                let tla_module = converter
                    .convert_file(input)
                    .map_err(|e| miette::miette!("Failed to convert Verus to TLA+: {}", e))?;

                if cli.verbose {
                    eprintln!("  Module: {}", tla_module.name);
                    eprintln!(
                        "  Operators: {:?}",
                        tla_module
                            .operators
                            .iter()
                            .map(|o| &o.name)
                            .collect::<Vec<_>>()
                    );
                }

                // Print TLA+ output
                let printer = TlaPrinter::new();
                let tla_code = printer.print_module(&tla_module);

                // Output
                if let Some(output_path) = output {
                    std::fs::write(output_path, &tla_code)
                        .map_err(|e| miette::miette!("Failed to write output: {}", e))?;
                    println!("Converted {} -> {}", input.display(), output_path.display());
                } else {
                    println!("{}", tla_code);
                }
            }

            Ok(())
        }

        Commands::TranslateTla {
            input,
            output,
            types,
            gen_modes,
            spec_prefix,
            state_name,
        } => {
            use verus_transpiler::tla::{
                generate_mode_annotations, parse_module, ModuleConfig, ModuleTranslator,
                TypeAnnotations, TypeInference,
            };

            if cli.verbose {
                eprintln!("Translating TLA+ file: {}", input.display());
            }

            // Read TLA+ source
            let source = std::fs::read_to_string(input)
                .map_err(|e| miette::miette!("Failed to read TLA+ file: {}", e))?;

            // Parse TLA+ module
            let module = parse_module(&source)
                .map_err(|e| miette::miette!("Failed to parse TLA+ file: {}", e))?;

            if cli.verbose {
                eprintln!("  Module: {}", module.name);
                eprintln!("  Variables: {:?}", module.variables);
                eprintln!(
                    "  Constants: {:?}",
                    module.constants.iter().map(|c| &c.name).collect::<Vec<_>>()
                );
                eprintln!(
                    "  Operators: {:?}",
                    module.operators.iter().map(|o| &o.name).collect::<Vec<_>>()
                );
            }

            // Configure module translation
            let config = ModuleConfig {
                spec_prefix: spec_prefix.clone(),
                state_name: state_name.clone(),
                ..ModuleConfig::default()
            };

            // Build type environment
            let type_env = if let Some(types_path) = types {
                if cli.verbose {
                    eprintln!("  Loading type annotations from: {}", types_path.display());
                }
                let types_content = std::fs::read_to_string(types_path)
                    .map_err(|e| miette::miette!("Failed to read type annotations file: {}", e))?;
                let annotations = TypeAnnotations::parse(&types_content)?;

                // Start with inferred types, then override with annotations
                let mut inference = TypeInference::new();
                let mut env = inference.infer_types(&module);

                // Apply type annotations to the environment
                for (var_name, tla_type) in &annotations.variables {
                    env.variables.insert(var_name.clone(), tla_type.clone());
                }
                for (const_name, tla_type) in &annotations.constants {
                    env.constants.insert(const_name.clone(), tla_type.clone());
                }
                for (op_name, tla_type) in &annotations.operators {
                    env.operators.insert(op_name.clone(), tla_type.clone());
                }

                // Resolve any remaining type variables to concrete types
                inference.resolve_with_fallback(&env)
            } else {
                // Use automatic type inference only
                let mut inference = TypeInference::new();
                let env = inference.infer_types(&module);
                // Resolve any remaining type variables to concrete types
                inference.resolve_with_fallback(&env)
            };

            // Translate module with type information
            let mut translator = ModuleTranslator::with_config(config).with_types(type_env);
            let verus_code = translator.translate(&module);

            // Output Verus code
            if let Some(output_path) = output {
                std::fs::write(output_path, &verus_code)
                    .map_err(|e| miette::miette!("Failed to write output: {}", e))?;

                if cli.verbose {
                    eprintln!("  Written Verus code to: {}", output_path.display());
                }

                // Generate mode annotations if requested
                if *gen_modes {
                    let mode_path = output_path.with_extension("automan");
                    let mode_annotations = generate_mode_annotations(&module);
                    std::fs::write(&mode_path, &mode_annotations)
                        .map_err(|e| miette::miette!("Failed to write mode annotations: {}", e))?;

                    if cli.verbose {
                        eprintln!("  Written mode annotations to: {}", mode_path.display());
                    }
                }

                println!(
                    "Translated {} -> {}",
                    input.display(),
                    output_path.display()
                );
            } else if cli.stdout {
                println!("{}", verus_code);

                // Print mode annotations to stderr if requested
                if *gen_modes {
                    let mode_annotations = generate_mode_annotations(&module);
                    eprintln!("\n--- Mode Annotations ---\n{}", mode_annotations);
                }
            } else {
                println!("{}", verus_code);
            }

            Ok(())
        }

        Commands::Pipeline {
            tla_input,
            exec_output,
            types,
            keep_intermediate,
            spec_output,
            spec_prefix,
            exec_prefix,
            state_name,
            config,
        } => {
            use verus_transpiler::tla::{
                generate_mode_annotations, parse_module, ModuleConfig, ModuleTranslator,
                TypeAnnotations, TypeInference,
            };

            if cli.verbose {
                eprintln!("=== TLA+ to Verus Exec Pipeline ===");
                eprintln!("Input TLA+: {}", tla_input.display());
                eprintln!("Output exec: {}", exec_output.display());
            }

            // Step 1: Parse TLA+ module
            if cli.verbose {
                eprintln!("\n[Step 1] Parsing TLA+ module...");
            }
            let tla_source = std::fs::read_to_string(tla_input)
                .map_err(|e| miette::miette!("Failed to read TLA+ file: {}", e))?;
            let tla_module = parse_module(&tla_source)
                .map_err(|e| miette::miette!("Failed to parse TLA+ file: {}", e))?;

            if cli.verbose {
                eprintln!("  Module: {}", tla_module.name);
                eprintln!("  Variables: {:?}", tla_module.variables);
                eprintln!(
                    "  Operators: {:?}",
                    tla_module
                        .operators
                        .iter()
                        .map(|o| &o.name)
                        .collect::<Vec<_>>()
                );
            }

            // Step 2: Build type environment
            if cli.verbose {
                eprintln!("\n[Step 2] Inferring types...");
            }
            let type_env = if let Some(types_path) = types {
                if cli.verbose {
                    eprintln!("  Loading type annotations from: {}", types_path.display());
                }
                let types_content = std::fs::read_to_string(types_path)
                    .map_err(|e| miette::miette!("Failed to read type annotations file: {}", e))?;
                let annotations = TypeAnnotations::parse(&types_content)?;

                let mut inference = TypeInference::new();
                let mut env = inference.infer_types(&tla_module);

                for (var_name, tla_type) in &annotations.variables {
                    env.variables.insert(var_name.clone(), tla_type.clone());
                }
                for (const_name, tla_type) in &annotations.constants {
                    env.constants.insert(const_name.clone(), tla_type.clone());
                }
                for (op_name, tla_type) in &annotations.operators {
                    env.operators.insert(op_name.clone(), tla_type.clone());
                }
                env
            } else {
                let mut inference = TypeInference::new();
                inference.infer_types(&tla_module)
            };

            // Step 3: Translate TLA+ to Verus spec
            if cli.verbose {
                eprintln!("\n[Step 3] Translating TLA+ to Verus spec...");
            }
            let module_config = ModuleConfig {
                spec_prefix: spec_prefix.clone(),
                exec_prefix: exec_prefix.clone(),
                state_name: state_name.clone(),
                ..ModuleConfig::default()
            };
            let mut tla_translator =
                ModuleTranslator::with_config(module_config.clone()).with_types(type_env);
            let verus_spec_code = tla_translator.translate(&tla_module);

            // Generate mode annotations
            let mode_annotations = generate_mode_annotations(&tla_module);

            // Determine intermediate file paths
            let spec_path = spec_output.clone().unwrap_or_else(|| {
                let mut p = exec_output.clone();
                p.set_extension("spec.rs");
                p
            });
            let automan_path = spec_path.with_extension("automan");

            // Write intermediate files
            if cli.verbose {
                eprintln!("  Writing spec to: {}", spec_path.display());
                eprintln!("  Writing annotations to: {}", automan_path.display());
            }
            std::fs::write(&spec_path, &verus_spec_code)
                .map_err(|e| miette::miette!("Failed to write spec file: {}", e))?;
            std::fs::write(&automan_path, &mode_annotations)
                .map_err(|e| miette::miette!("Failed to write annotation file: {}", e))?;

            // Step 4: Transpile Verus spec to exec
            if cli.verbose {
                eprintln!("\n[Step 4] Transpiling Verus spec to exec...");
            }

            // Load transpiler config if provided
            let transpiler_config = if let Some(config_path) = config {
                load_config(config_path)?
            } else {
                // Create default config with appropriate prefixes
                TranspilerConfig {
                    translator: TranslatorConfig {
                        spec_prefix: spec_prefix.clone(),
                        exec_prefix: exec_prefix.clone(),
                        assume_postconditions: true,
                        ..TranslatorConfig::default()
                    },
                    generate_inline_types: true,
                    custom_imports: vec![
                        "use vstd::prelude::*;".to_string(),
                        "use std::collections::HashSet;".to_string(),
                    ],
                    ..TranspilerConfig::default()
                }
            };

            let transpiler = Transpiler::new(transpiler_config);
            let exec_code = transpiler
                .transpile_file(&spec_path, &automan_path)
                .map_err(|e| miette::miette!("Failed to transpile spec to exec: {}", e))?;

            // Build self-contained output: spec definitions + exec code
            // The exec code references spec types (LState, LConstants) and spec functions,
            // so we embed the spec code before the exec code for standalone compilation.
            let mut full_output = String::new();
            full_output.push_str(&verus_spec_code);
            full_output.push('\n');
            full_output.push_str(&exec_code);

            // Write exec output
            std::fs::write(exec_output, &full_output)
                .map_err(|e| miette::miette!("Failed to write exec output: {}", e))?;

            if cli.verbose {
                eprintln!("\n[Step 5] Cleaning up...");
            }

            // Clean up intermediate files unless requested to keep
            if !*keep_intermediate {
                if cli.verbose {
                    eprintln!("  Removing intermediate files...");
                }
                let _ = std::fs::remove_file(&spec_path);
                let _ = std::fs::remove_file(&automan_path);
            } else if cli.verbose {
                eprintln!("  Keeping intermediate files.");
            }

            println!(
                "Pipeline complete: {} -> {}",
                tla_input.display(),
                exec_output.display()
            );

            Ok(())
        }

        Commands::GenerateMessages { config, output } => {
            let file_config = FileConfig::from_file(config)
                .map_err(|e| miette::miette!("Failed to load config: {}", e))?;

            let msg_config = file_config
                .messages
                .ok_or_else(|| miette::miette!("Config file has no [messages] section"))?;

            if msg_config.enum_name.is_empty() {
                return Err(miette::miette!("[messages] enum_name is required"));
            }
            if msg_config.variants.is_empty() {
                return Err(miette::miette!("[messages] must have at least one variant"));
            }

            let code = verus_transpiler::generate_message_code(&msg_config);

            if let Some(output_path) = output {
                std::fs::write(output_path, &code)
                    .map_err(|e| miette::miette!("Failed to write output: {}", e))?;
                println!(
                    "Generated {} message with {} variants -> {}",
                    msg_config.enum_name,
                    msg_config.variants.len(),
                    output_path.display()
                );
            } else {
                println!("{}", code);
            }

            Ok(())
        }

        Commands::GenerateMarshalable { config, output } => {
            let file_config = FileConfig::from_file(config)
                .map_err(|e| miette::miette!("Failed to load config: {}", e))?;

            let marsh_config = file_config
                .marshalable
                .ok_or_else(|| miette::miette!("Config file has no [marshalable] section"))?;

            if marsh_config.types.is_empty() && marsh_config.enums.is_empty() {
                return Err(miette::miette!(
                    "[marshalable] must have at least one type or enum"
                ));
            }

            let code = verus_transpiler::generate_marshalable_impls(&marsh_config);

            if let Some(output_path) = output {
                std::fs::write(output_path, &code)
                    .map_err(|e| miette::miette!("Failed to write output: {}", e))?;
                let total = marsh_config.types.len() + marsh_config.enums.len();
                println!(
                    "Generated Marshalable impls for {} types ({} struct, {} enum) -> {}",
                    total,
                    marsh_config.types.len(),
                    marsh_config.enums.len(),
                    output_path.display()
                );
            } else {
                println!("{}", code);
            }

            Ok(())
        }

        Commands::AnalyzeLnext {
            input,
            config: config_path,
            next_fn,
            spec_prefix,
            exec_prefix,
            output,
        } => {
            let spec_fns = verus_transpiler::parse_file(input)
                .map_err(|e| miette::miette!("Failed to parse spec file: {}", e))?;

            let mut sched_config = verus_transpiler::find_and_analyze_lnext(
                &spec_fns,
                next_fn,
                spec_prefix,
                exec_prefix,
            )
            .ok_or_else(|| {
                miette::miette!(
                    "Function '{}' not found or body is not a disjunction",
                    next_fn
                )
            })?;

            // Load message variants and classification overrides from TOML config
            let (message_variants, classification_overrides) = if let Some(cfg_path) = config_path {
                let file_config = FileConfig::from_file(cfg_path)
                    .map_err(|e| miette::miette!("Failed to load config: {}", e))?;
                let variants = file_config
                    .messages
                    .map(|m| m.variants.iter().map(|v| v.name.clone()).collect())
                    .unwrap_or_default();
                let overrides = file_config
                    .scheduler
                    .map(|s| verus_transpiler::ActionClassificationOverrides {
                        message_response_overrides: s.message_response_overrides,
                        role_prefixes: s.role_prefixes,
                        timer_overrides: s.timer_overrides,
                    })
                    .unwrap_or_default();
                (variants, overrides)
            } else {
                (
                    vec![],
                    verus_transpiler::ActionClassificationOverrides::default(),
                )
            };

            // Classify actions as message_driven or timer_driven
            verus_transpiler::classify_actions(
                &mut sched_config,
                &message_variants,
                &classification_overrides,
            );

            let msg_count = sched_config
                .actions
                .iter()
                .filter(|a| a.kind == verus_transpiler::ActionKind::MessageDriven)
                .count();
            let timer_count = sched_config.actions.len() - msg_count;

            let toml = verus_transpiler::scheduler_config_to_toml(&sched_config);

            if let Some(output_path) = output {
                std::fs::write(output_path, &toml)
                    .map_err(|e| miette::miette!("Failed to write output: {}", e))?;
                println!(
                    "Extracted {} actions ({} message_driven, {} timer_driven) from {} -> {}",
                    sched_config.actions.len(),
                    msg_count,
                    timer_count,
                    sched_config.next_fn_name,
                    output_path.display()
                );
            } else {
                println!("{}", toml);
            }

            Ok(())
        }

        Commands::GenerateHost {
            config,
            protocol,
            gen_module,
            output,
        } => {
            let file_config = FileConfig::from_file(config)
                .map_err(|e| miette::miette!("Failed to load config: {}", e))?;

            let msg_config = file_config
                .messages
                .ok_or_else(|| miette::miette!("Config file has no [messages] section"))?;

            let sched_config = file_config
                .scheduler
                .ok_or_else(|| miette::miette!("Config file has no [scheduler] section"))?;

            // Derive module name from protocol name
            let module_name = protocol.to_lowercase();
            let gen_mod = gen_module
                .clone()
                .unwrap_or_else(|| format!("{}_gen", module_name));

            let params = verus_transpiler::codegen::scheduler::HostScaffoldParams {
                protocol_name: protocol.clone(),
                module_name: module_name.clone(),
                gen_module: gen_mod,
                message_enum: msg_config.enum_name.clone(),
                message_variants: msg_config.variants,
                actions: sched_config.actions,
                role_dispatch: sched_config.role_dispatch,
            };

            let code = verus_transpiler::generate_host_scaffold(&params);

            if let Some(output_path) = output {
                std::fs::write(output_path, &code)
                    .map_err(|e| miette::miette!("Failed to write output: {}", e))?;
                println!(
                    "Generated {} host scaffold ({} actions) -> {}",
                    protocol,
                    params.actions.len(),
                    output_path.display()
                );
            } else {
                println!("{}", code);
            }

            Ok(())
        }
    }
}

/// Load configuration from a TOML file
fn load_config(path: &Path) -> Result<TranspilerConfig> {
    let file_config =
        FileConfig::from_file(path).map_err(|e| miette::miette!("Failed to load config: {}", e))?;
    convert_file_config(file_config, path)
}

/// Convert a FileConfig to internal TranspilerConfig.
/// `config_path` is used for resolving relative paths (e.g., manual_code).
fn convert_file_config(file_config: FileConfig, config_path: &Path) -> Result<TranspilerConfig> {
    Ok(TranspilerConfig {
        translator: TranslatorConfig {
            validity_predicate_name: file_config.output.validity_predicate_name,
            generate_loops_for_verification: file_config.output.generate_loops_for_verification,
            generate_proofs: file_config.output.generate_proofs,
            type_remapping: file_config.remapping.clone(),
            function_paths: file_config.function_paths.clone(),
            spec_only_functions: file_config.spec_only_functions.into_iter().collect(),
            method_calls: file_config.method_calls.clone(),
            primitive_types: file_config.primitive_types.into_iter().collect(),
            skip_valid_types: file_config.skip_valid_types.into_iter().collect(),
            int_type: file_config.naming.int_type.clone(),
            nat_type: file_config.naming.nat_type.clone(),
            variant_remapping: file_config.variant_remapping.clone(),
            collection_fields: file_config.collection_fields.into_iter().collect(),
            vec_fields: file_config.vec_fields.into_iter().collect(),
            clone_fields: file_config.clone_fields.into_iter().collect(),
            clone_field_types: file_config.clone_field_types.clone(),
            struct_vec_fields: file_config
                .struct_vec_fields
                .iter()
                .map(|(k, v)| {
                    let exec_type = v.first().cloned().unwrap_or_default();
                    let spec_type = v.get(1).cloned().unwrap_or_default();
                    (k.clone(), (exec_type, spec_type))
                })
                .collect(),
            map_fields: file_config
                .map_fields
                .iter()
                .map(|(k, v)| {
                    let exec_map_type = v.first().cloned().unwrap_or_default();
                    let abstractify_prefix = v.get(1).cloned().unwrap_or_default();
                    let exec_value_type = v.get(2).cloned().unwrap_or_default();
                    (
                        k.clone(),
                        (exec_map_type, abstractify_prefix, exec_value_type),
                    )
                })
                .collect(),
            verified_clone_fns: file_config.verified_clone_fns.clone(),
            hashmap_index_fields: file_config.hashmap_index_fields.iter().cloned().collect(),
            type_view_exprs: file_config.type_view_exprs.clone(),
            extra_requires: file_config.extra_requires.clone(),
            inline_expansions: file_config.inline_expansions.clone(),
            eq_function_fields: file_config.eq_function_fields.clone(),
            arrow_variants: file_config.arrow_variants.clone(),
            clone_method: file_config.output.clone_method.clone(),
            clone_up_to_view_types: file_config.clone_up_to_view_types.iter().cloned().collect(),
            vec_element_ensures: file_config.vec_element_ensures.clone(),
            set_fields: file_config.set_fields.iter().cloned().collect(),
            assume_postconditions: file_config.output.assume_postconditions,
            proven_functions: file_config
                .output
                .proven_functions
                .iter()
                .cloned()
                .collect(),
            use_verified_hashset_clone: file_config
                .clone_strategy
                .values()
                .any(|v| v == "verified"),
            has_msg_vec_type: file_config.msg_vec_type.is_some(),
            spec_prefix: file_config.naming.spec_prefix.clone(),
            exec_prefix: file_config.naming.exec_prefix.clone(),
            generate_abstraction_fns: false,
            generate_validity_predicates: false,
            arc_wrap_fields: file_config
                .arc_wrap_fields
                .iter()
                .map(|(k, v)| (k.clone(), v.iter().cloned().collect()))
                .collect(),
            mut_self_types: file_config.mut_self_types.iter().cloned().collect(),
        },
        custom_imports: file_config.output.custom_imports,
        generate_inline_types: file_config.output.generate_inline_types,
        type_remapping: file_config.remapping,
        generate_wrapper_methods: file_config.output.generate_wrapper_methods,
        wrapper_impl_type: file_config.output.wrapper_impl_type,
        skip_functions: file_config.skip_functions,
        no_stub_functions: file_config.no_stub_functions,
        manual_code: file_config.output.manual_code.and_then(|rel_path| {
            let base_dir = config_path.parent().unwrap_or(Path::new("."));
            let manual_path = base_dir.join(&rel_path);
            std::fs::read_to_string(&manual_path).ok()
        }),
        auto_skip: false,
        proof_fallback: false,
        msg_vec_type: file_config.msg_vec_type.as_ref().map(|v| {
            let exec_type = v.first().cloned().unwrap_or_default();
            let spec_type = v.get(1).cloned().unwrap_or_default();
            (exec_type, spec_type)
        }),
        printer: verus_transpiler::PrinterConfig {
            extra_fields: file_config.extra_fields,
            ..Default::default()
        },
        arc_wrap_types: file_config.arc_wrap_types,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cli_parsing() {
        // Just verify the CLI struct can be created
        let cli = Cli::parse_from([
            "verus-transpile",
            "--input",
            "test.rs",
            "--annotations",
            "test.automan",
        ]);
        assert_eq!(cli.input, Some(PathBuf::from("test.rs")));
        assert_eq!(cli.annotations, Some(PathBuf::from("test.automan")));
    }

    #[test]
    fn test_translate_tla_cli_parsing() {
        // Test parsing of translate-tla subcommand
        let cli = Cli::parse_from([
            "verus-transpile",
            "translate-tla",
            "--input",
            "spec.tla",
            "--output",
            "spec.rs",
        ]);

        match cli.command {
            Some(Commands::TranslateTla {
                input,
                output,
                types,
                gen_modes,
                spec_prefix,
                state_name,
            }) => {
                assert_eq!(input, PathBuf::from("spec.tla"));
                assert_eq!(output, Some(PathBuf::from("spec.rs")));
                assert!(types.is_none());
                assert!(!gen_modes);
                assert_eq!(spec_prefix, "L");
                assert_eq!(state_name, "State");
            }
            _ => panic!("Expected TranslateTla command"),
        }
    }

    #[test]
    fn test_translate_tla_cli_with_options() {
        // Test parsing with all options
        let cli = Cli::parse_from([
            "verus-transpile",
            "translate-tla",
            "--input",
            "spec.tla",
            "--output",
            "spec.rs",
            "--types",
            "spec.tla-types",
            "--gen-modes",
            "--spec-prefix",
            "Spec",
            "--state-name",
            "MyState",
        ]);

        match cli.command {
            Some(Commands::TranslateTla {
                input,
                output,
                types,
                gen_modes,
                spec_prefix,
                state_name,
            }) => {
                assert_eq!(input, PathBuf::from("spec.tla"));
                assert_eq!(output, Some(PathBuf::from("spec.rs")));
                assert_eq!(types, Some(PathBuf::from("spec.tla-types")));
                assert!(gen_modes);
                assert_eq!(spec_prefix, "Spec");
                assert_eq!(state_name, "MyState");
            }
            _ => panic!("Expected TranslateTla command"),
        }
    }

    #[test]
    fn test_translate_tla_integration() {
        // Integration test: parse and translate a simple TLA+ spec
        use verus_transpiler::tla::{
            generate_mode_annotations, parse_module, ModuleConfig, ModuleTranslator, TypeInference,
        };

        let tla_source = r#"
---- MODULE SimpleSpec ----
VARIABLE x

Init == x = 0

Next == x' = x + 1

====
"#;

        // Parse module
        let module = parse_module(tla_source).expect("Failed to parse TLA+ module");
        assert_eq!(module.name, "SimpleSpec");
        assert_eq!(module.variables, vec!["x"]);
        assert_eq!(module.operators.len(), 2);

        // Translate with type inference
        let config = ModuleConfig {
            spec_prefix: "L".to_string(),
            state_name: "State".to_string(),
            ..ModuleConfig::default()
        };
        let mut inference = TypeInference::new();
        let type_env = inference.infer_types(&module);
        let mut translator = ModuleTranslator::with_config(config).with_types(type_env);
        let verus_code = translator.translate(&module);

        // Verify output contains expected elements
        assert!(
            verus_code.contains("pub struct LState"),
            "Should contain LState struct"
        );
        assert!(
            verus_code.contains("pub open spec fn LInit"),
            "Should contain LInit function"
        );
        assert!(
            verus_code.contains("pub open spec fn LNext"),
            "Should contain LNext function"
        );

        // Test mode annotation generation
        let mode_annotations = generate_mode_annotations(&module);
        assert!(
            mode_annotations.contains("module SimpleSpec"),
            "Should contain module name"
        );
        assert!(
            mode_annotations.contains("LInit"),
            "Should contain Init operator"
        );
        assert!(
            mode_annotations.contains("LNext"),
            "Should contain Next operator"
        );
    }

    #[test]
    fn test_translate_tla_with_constants() {
        use verus_transpiler::tla::{parse_module, ModuleConfig, ModuleTranslator, TypeInference};

        let tla_source = r#"
---- MODULE WithConstants ----
CONSTANT N

VARIABLE count

Init == count = 0

Next == count' = count + N

====
"#;

        let module = parse_module(tla_source).expect("Failed to parse TLA+ module");
        assert_eq!(module.name, "WithConstants");
        assert_eq!(module.variables, vec!["count"]);
        assert_eq!(module.constants.len(), 1);
        assert_eq!(module.constants[0].name, "N");

        // Translate
        let config = ModuleConfig::default();
        let mut inference = TypeInference::new();
        let type_env = inference.infer_types(&module);
        let mut translator = ModuleTranslator::with_config(config).with_types(type_env);
        let verus_code = translator.translate(&module);

        // Should contain constants struct
        assert!(
            verus_code.contains("LConstants"),
            "Should contain LConstants struct"
        );
        assert!(verus_code.contains("pub N:"), "Should contain N constant");
    }

    #[test]
    fn test_pipeline_cli_parsing() {
        // Test parsing of pipeline subcommand
        let cli = Cli::parse_from([
            "verus-transpile",
            "pipeline",
            "--tla-input",
            "spec.tla",
            "--exec-output",
            "impl.rs",
        ]);

        match cli.command {
            Some(Commands::Pipeline {
                tla_input,
                exec_output,
                types,
                keep_intermediate,
                spec_output,
                spec_prefix,
                exec_prefix,
                state_name,
                config,
            }) => {
                assert_eq!(tla_input, PathBuf::from("spec.tla"));
                assert_eq!(exec_output, PathBuf::from("impl.rs"));
                assert!(types.is_none());
                assert!(!keep_intermediate);
                assert!(spec_output.is_none());
                assert_eq!(spec_prefix, "L");
                assert_eq!(exec_prefix, "C");
                assert_eq!(state_name, "State");
                assert!(config.is_none());
            }
            _ => panic!("Expected Pipeline command"),
        }
    }

    #[test]
    fn test_pipeline_cli_with_options() {
        // Test parsing with all options
        let cli = Cli::parse_from([
            "verus-transpile",
            "pipeline",
            "--tla-input",
            "spec.tla",
            "--exec-output",
            "impl.rs",
            "--types",
            "spec.tla-types",
            "--keep-intermediate",
            "--spec-output",
            "spec.rs",
            "--spec-prefix",
            "Spec",
            "--exec-prefix",
            "Exec",
            "--state-name",
            "MyState",
            "--config",
            "config.toml",
        ]);

        match cli.command {
            Some(Commands::Pipeline {
                tla_input,
                exec_output,
                types,
                keep_intermediate,
                spec_output,
                spec_prefix,
                exec_prefix,
                state_name,
                config,
            }) => {
                assert_eq!(tla_input, PathBuf::from("spec.tla"));
                assert_eq!(exec_output, PathBuf::from("impl.rs"));
                assert_eq!(types, Some(PathBuf::from("spec.tla-types")));
                assert!(keep_intermediate);
                assert_eq!(spec_output, Some(PathBuf::from("spec.rs")));
                assert_eq!(spec_prefix, "Spec");
                assert_eq!(exec_prefix, "Exec");
                assert_eq!(state_name, "MyState");
                assert_eq!(config, Some(PathBuf::from("config.toml")));
            }
            _ => panic!("Expected Pipeline command"),
        }
    }

    #[test]
    fn test_generate_mc_wrapper_cli_parsing() {
        let cli = Cli::parse_from([
            "verus-transpile",
            "generate-mc-wrapper",
            "--input",
            "Demo.tla",
            "--output",
            "Demo_MC.tla",
            "--cfg-output",
            "Demo_MC.cfg",
            "--init",
            "InitCustom",
            "--next",
            "NextCustom",
            "--module-suffix",
            "_WRAP",
            "--packet-mode",
            "append-seq",
            "--packet-var",
            "packets",
            "--invariant",
            "TypeOK",
            "--invariant",
            "Safety",
        ]);

        match cli.command {
            Some(Commands::GenerateMcWrapper {
                input,
                output,
                cfg_output,
                init,
                next,
                module_suffix,
                packet_mode,
                packet_var,
                invariant,
            }) => {
                assert_eq!(input, PathBuf::from("Demo.tla"));
                assert_eq!(output, PathBuf::from("Demo_MC.tla"));
                assert_eq!(cfg_output, Some(PathBuf::from("Demo_MC.cfg")));
                assert_eq!(init, "InitCustom");
                assert_eq!(next, "NextCustom");
                assert_eq!(module_suffix, "_WRAP");
                assert_eq!(packet_mode, CliPacketProjectionMode::AppendSeq);
                assert_eq!(packet_var, "packets");
                assert_eq!(invariant, vec!["TypeOK".to_string(), "Safety".to_string()]);
            }
            _ => panic!("Expected GenerateMcWrapper command"),
        }
    }

    #[test]
    fn test_generate_mc_wrapper_command_writes_wrapper_and_cfg() {
        let dir = tempfile::tempdir().unwrap();
        let input_path = dir.path().join("Demo.tla");
        let output_path = dir.path().join("Demo_MC.tla");
        let cfg_path = dir.path().join("Demo_MC.cfg");

        std::fs::write(
            &input_path,
            r#"
---- MODULE Demo ----
EXTENDS Integers

CONSTANTS Constants, State

Init(s, c) == s \in State /\ c \in Constants
Next(s, s_, c) == s_ = s

====
"#,
        )
        .unwrap();

        let command = Commands::GenerateMcWrapper {
            input: input_path,
            output: output_path.clone(),
            cfg_output: Some(cfg_path.clone()),
            init: "Init".to_string(),
            next: "Next".to_string(),
            module_suffix: "_MC".to_string(),
            packet_mode: CliPacketProjectionMode::None,
            packet_var: "sent_packets".to_string(),
            invariant: vec!["TypeOK".to_string()],
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        handle_command(&command, &cli).unwrap();

        let generated_wrapper = std::fs::read_to_string(&output_path).unwrap();
        assert!(generated_wrapper.contains("---- MODULE Demo_MC ----"));
        assert!(generated_wrapper.contains("EXTENDS Demo"));
        assert!(generated_wrapper.contains("Init(state, constants)"));
        assert!(generated_wrapper.contains("Next(state, state_, constants)"));

        let generated_cfg = std::fs::read_to_string(&cfg_path).unwrap();
        assert!(generated_cfg.contains("SPECIFICATION Spec"));
        assert!(generated_cfg.contains("CHECK_DEADLOCK FALSE"));
        assert!(generated_cfg.contains("INVARIANTS"));
        assert!(generated_cfg.contains("TypeOK"));
    }

    #[test]
    fn test_generate_mc_wrapper_command_with_packet_projection_mode() {
        let dir = tempfile::tempdir().unwrap();
        let input_path = dir.path().join("Demo.tla");
        let output_path = dir.path().join("Demo_MC.tla");

        std::fs::write(
            &input_path,
            r#"
---- MODULE Demo ----
EXTENDS Integers, Sequences
CONSTANTS Constants, Msg
Init(s, c) == TRUE
Step(s, s_, c, sent_packets) == sent_packets = <<>>
Next(s, s_, c) ==
    \E sent_packets \in Seq(Msg) : Step(s, s_, c, sent_packets)
====
"#,
        )
        .unwrap();

        let command = Commands::GenerateMcWrapper {
            input: input_path,
            output: output_path.clone(),
            cfg_output: None,
            init: "Init".to_string(),
            next: "Next".to_string(),
            module_suffix: "_MC".to_string(),
            packet_mode: CliPacketProjectionMode::AppendSeq,
            packet_var: "sent_packets".to_string(),
            invariant: vec![],
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        handle_command(&command, &cli).unwrap();
        let generated = std::fs::read_to_string(&output_path).unwrap();
        assert!(generated.contains("VARIABLE state, constants, msgs"));
        assert!(generated.contains("msgs' = msgs \\o sent_packets"));
        assert!(generated.contains("vars == <<state, constants, msgs>>"));
    }

    #[test]
    fn test_model_config_cli_parsing() {
        let cli = Cli::parse_from([
            "verus-transpile",
            "model-config",
            "--model",
            "model.toml",
            "--max-depth",
            "40",
            "--max-states",
            "20000",
            "--timeout-ms",
            "5000",
            "--max-seq-len",
            "8",
            "--max-set-len",
            "6",
            "--max-map-len",
            "10",
            "--int-range",
            "-2..5",
            "--nat-max",
            "12",
        ]);

        match cli.command {
            Some(Commands::ModelConfig {
                model,
                max_depth,
                max_states,
                timeout_ms,
                max_seq_len,
                max_set_len,
                max_map_len,
                int_range,
                nat_max,
                candidate_eval_guardrail,
            }) => {
                assert_eq!(model, PathBuf::from("model.toml"));
                assert_eq!(max_depth, Some(40));
                assert_eq!(max_states, Some(20000));
                assert_eq!(timeout_ms, Some(5000));
                assert_eq!(max_seq_len, Some(8));
                assert_eq!(max_set_len, Some(6));
                assert_eq!(max_map_len, Some(10));
                assert_eq!(int_range, Some("-2..5".to_string()));
                assert_eq!(candidate_eval_guardrail, None);
                assert_eq!(nat_max, Some(12));
            }
            _ => panic!("Expected ModelConfig command"),
        }
    }

    #[test]
    fn test_model_config_command_rejects_invalid_int_range() {
        let dir = tempfile::tempdir().unwrap();
        let model_path = dir.path().join("model.toml");
        std::fs::write(&model_path, "[properties]\ninvariants=[]\n").unwrap();

        let command = Commands::ModelConfig {
            model: model_path,
            max_depth: None,
            max_states: None,
            timeout_ms: None,
            max_seq_len: None,
            max_set_len: None,
            max_map_len: None,
            int_range: Some("oops".to_string()),
            nat_max: None,
            candidate_eval_guardrail: None,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        let err = handle_command(&command, &cli).unwrap_err();
        assert!(
            err.to_string().contains("Invalid int range override"),
            "unexpected error: {}",
            err
        );
    }

    #[test]
    fn test_model_check_cli_parsing() {
        let cli = Cli::parse_from([
            "verus-transpile",
            "model-check",
            "--input",
            "src/protocol/TwoPhase/twophase.rs",
            "--types",
            "src/protocol/TwoPhase/types.rs",
            "--init",
            "InitOverride",
            "--next",
            "NextOverride",
            "--invariant",
            "LTypeOK",
            "--invariant",
            "LSafety",
            "--search",
            "dfs",
            "--max-depth",
            "64",
            "--max-states",
            "4096",
            "--timeout",
            "2500",
            "--json-report",
            "--model",
            "model.toml",
        ]);

        match cli.command {
            Some(Commands::ModelCheck {
                input,
                types,
                init,
                next,
                invariant,
                search,
                max_depth,
                max_states,
                timeout_ms,
                json_report,
                export_parity: _,
                export_parity_debug: _,
                model,
                no_bytecode: _,
                native_codegen: _,
                workers: _,
                conflict_profile: _,
            }) => {
                assert_eq!(input, PathBuf::from("src/protocol/TwoPhase/twophase.rs"));
                assert_eq!(types, Some(PathBuf::from("src/protocol/TwoPhase/types.rs")));
                assert_eq!(init, "InitOverride");
                assert_eq!(next, "NextOverride");
                assert_eq!(
                    invariant,
                    vec!["LTypeOK".to_string(), "LSafety".to_string()]
                );
                assert_eq!(search, Some(CliSearchMode::Dfs));
                assert_eq!(max_depth, Some(64));
                assert_eq!(max_states, Some(4096));
                assert_eq!(timeout_ms, Some(2500));
                assert!(json_report);
                assert_eq!(model, PathBuf::from("model.toml"));
            }
            _ => panic!("Expected ModelCheck command"),
        }
    }

    #[test]
    fn test_model_check_cli_native_codegen_flag() {
        // Default: native_codegen is false
        let cli = Cli::parse_from([
            "verus-transpile",
            "model-check",
            "--input",
            "demo.rs",
            "--model",
            "model.toml",
        ]);
        match cli.command {
            Some(Commands::ModelCheck {
                native_codegen,
                no_bytecode,
                ..
            }) => {
                assert!(!native_codegen, "native_codegen should default to false");
                assert!(!no_bytecode, "no_bytecode should default to false");
            }
            _ => panic!("Expected ModelCheck command"),
        }

        // With --native-codegen flag
        let cli = Cli::parse_from([
            "verus-transpile",
            "model-check",
            "--input",
            "demo.rs",
            "--model",
            "model.toml",
            "--native-codegen",
        ]);
        match cli.command {
            Some(Commands::ModelCheck {
                native_codegen, ..
            }) => {
                assert!(native_codegen, "native_codegen should be true with --native-codegen");
            }
            _ => panic!("Expected ModelCheck command"),
        }
    }

    #[test]
    fn test_model_check_cli_conflict_profile_flag() {
        // Default: conflict_profile is false
        let cli = Cli::parse_from([
            "verus-transpile",
            "model-check",
            "--input",
            "demo.rs",
            "--model",
            "model.toml",
        ]);
        match cli.command {
            Some(Commands::ModelCheck {
                conflict_profile, ..
            }) => {
                assert!(!conflict_profile, "conflict_profile should default to false");
            }
            _ => panic!("Expected ModelCheck command"),
        }

        // With --conflict-profile flag
        let cli = Cli::parse_from([
            "verus-transpile",
            "model-check",
            "--input",
            "demo.rs",
            "--model",
            "model.toml",
            "--conflict-profile",
        ]);
        match cli.command {
            Some(Commands::ModelCheck {
                conflict_profile, ..
            }) => {
                assert!(
                    conflict_profile,
                    "conflict_profile should be true with --conflict-profile"
                );
            }
            _ => panic!("Expected ModelCheck command"),
        }
    }

    #[test]
    fn test_model_check_cli_rejects_invalid_search_mode() {
        let err = Cli::try_parse_from([
            "verus-transpile",
            "model-check",
            "--input",
            "src/protocol/TwoPhase/twophase.rs",
            "--search",
            "beam",
            "--model",
            "model.toml",
        ])
        .unwrap_err();
        assert!(err.to_string().contains("possible values: bfs, dfs"));
    }

    #[test]
    fn test_model_check_cli_json_report_defaults_false() {
        let cli = Cli::parse_from([
            "verus-transpile",
            "model-check",
            "--input",
            "src/protocol/TwoPhase/twophase.rs",
            "--model",
            "model.toml",
        ]);

        match cli.command {
            Some(Commands::ModelCheck { json_report, .. }) => {
                assert!(!json_report);
            }
            _ => panic!("Expected ModelCheck command"),
        }
    }

    #[test]
    fn test_report_assumes_cli_parsing() {
        let cli = Cli::parse_from([
            "verus-transpile",
            "report-assumes",
            "--input-dir",
            "src/generated/RSL",
            "--output",
            "report.json",
        ]);

        match cli.command {
            Some(Commands::ReportAssumes { input_dir, output }) => {
                assert_eq!(input_dir, PathBuf::from("src/generated/RSL"));
                assert_eq!(output, Some(PathBuf::from("report.json")));
            }
            _ => panic!("Expected ReportAssumes command"),
        }
    }

    #[test]
    fn test_collect_assume_report_for_file_tracks_function_and_line() {
        let source = r#"
pub exec fn COne() {
    assume(false);
}

pub exec fn CTwo() {
    // assume(false);
    assume(x > 0);
}
"#;

        let report = collect_assume_report_for_file("demo_gen.rs", source);
        assert_eq!(report.assume_count, 2);
        assert_eq!(report.assume_false_count, 1);
        assert_eq!(report.assume_sites[0].function.as_deref(), Some("COne"));
        assert_eq!(report.assume_sites[0].line, 3);
        assert!(report.assume_sites[0].assume_false);
        assert_eq!(report.assume_sites[1].function.as_deref(), Some("CTwo"));
        assert_eq!(report.assume_sites[1].line, 8);
        assert!(!report.assume_sites[1].assume_false);
    }

    #[test]
    fn test_collect_assume_report_directory_summary() {
        let dir = tempfile::tempdir().unwrap();
        let generated_dir = dir.path().join("generated");
        std::fs::create_dir_all(&generated_dir).unwrap();

        std::fs::write(
            generated_dir.join("alpha_gen.rs"),
            "pub exec fn CAlpha() {\n    assume(false);\n}\n",
        )
        .unwrap();
        std::fs::write(
            generated_dir.join("beta_gen.rs"),
            "pub exec fn CBeta() { }\n",
        )
        .unwrap();
        std::fs::write(generated_dir.join("notes.txt"), "assume(false);\n").unwrap();

        let report = collect_assume_report(generated_dir.as_path()).unwrap();
        assert_eq!(report.summary.files_scanned, 2);
        assert_eq!(report.summary.files_with_assumes, 1);
        assert_eq!(report.summary.assume_count, 1);
        assert_eq!(report.summary.assume_false_count, 1);
        assert_eq!(report.summary.non_fallback_assume_count, 0);
        assert_eq!(report.files.len(), 2);
        assert_eq!(report.files[0].module, "alpha_gen.rs");
        assert_eq!(report.files[1].module, "beta_gen.rs");
    }

    #[test]
    fn test_model_check_command_preflight_success() {
        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }

    pub open spec fn LInv(s: LState, c: LConstants) -> bool {
        s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1

[properties]
invariants = ["LInv"]
"#,
        )
        .unwrap();

        let command = Commands::ModelCheck {
            input: proto_path,
            types: None,
            init: "LInit".to_string(),
            next: "LNext".to_string(),
            invariant: vec![],
            search: None,
            max_depth: None,
            max_states: None,
            timeout_ms: None,
            json_report: false,
            export_parity: None,
            export_parity_debug: None,
            model: model_path,
            no_bytecode: false,
            native_codegen: false,
            workers: 1,
            conflict_profile: false,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        handle_command(&command, &cli).unwrap();
    }

    #[test]
    fn test_model_check_command_accepts_fairness_configuration() {
        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }

    pub open spec fn LInv(s: LState, c: LConstants) -> bool {
        s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1

[properties]
invariants = ["LInv"]
fairness = { weak = ["branch_0"] }
"#,
        )
        .unwrap();

        let command = Commands::ModelCheck {
            input: proto_path,
            types: None,
            init: "LInit".to_string(),
            next: "LNext".to_string(),
            invariant: vec![],
            search: None,
            max_depth: None,
            max_states: None,
            timeout_ms: None,
            json_report: false,
            export_parity: None,
            export_parity_debug: None,
            model: model_path,
            no_bytecode: false,
            native_codegen: false,
            workers: 1,
            conflict_profile: false,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        handle_command(&command, &cli).unwrap();
    }

    #[test]
    fn test_model_check_command_rejects_unknown_fairness_branch_labels() {
        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }

    pub open spec fn LInv(s: LState, c: LConstants) -> bool {
        s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1

[properties]
invariants = ["LInv"]
fairness = { weak = ["branch_typo"], strong = ["branch_missing"] }
"#,
        )
        .unwrap();

        let command = Commands::ModelCheck {
            input: proto_path,
            types: None,
            init: "LInit".to_string(),
            next: "LNext".to_string(),
            invariant: vec![],
            search: None,
            max_depth: None,
            max_states: None,
            timeout_ms: None,
            json_report: false,
            export_parity: None,
            export_parity_debug: None,
            model: model_path,
            no_bytecode: false,
            native_codegen: false,
            workers: 1,
            conflict_profile: false,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        let err = handle_command(&command, &cli).unwrap_err();
        let message = err.to_string();
        assert!(message.contains("unknown fairness branch label"));
        assert!(message.contains("properties.fairness.weak"));
        assert!(message.contains("properties.fairness.strong"));
        assert!(message.contains("branch_typo"));
        assert!(message.contains("branch_missing"));
        assert!(message.contains("Available LNext branch labels"));
        assert!(message.contains("branch_0"));
    }

    #[test]
    fn test_model_check_command_accepts_search_override() {
        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1

[search]
max_states = 1
"#,
        )
        .unwrap();

        let command = Commands::ModelCheck {
            input: proto_path,
            types: None,
            init: "LInit".to_string(),
            next: "LNext".to_string(),
            invariant: vec![],
            search: Some(CliSearchMode::Dfs),
            max_depth: Some(55),
            max_states: Some(2048),
            timeout_ms: Some(7777),
            json_report: false,
            export_parity: None,
            export_parity_debug: None,
            model: model_path,
            no_bytecode: false,
            native_codegen: false,
            workers: 1,
            conflict_profile: false,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        handle_command(&command, &cli).unwrap();
    }

    #[test]
    fn test_model_check_command_timeout_override_changes_execution_behavior() {
        use verus_transpiler::modelcheck::explorer::ExplorationStopReason;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 2000 }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s.value < c.limit && s_.value == s.value + 1
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 2000

[quantifiers.int]
min = 0
max = 2000

[search]
max_depth = 2000
max_states = 3000
timeout_ms = 60000
"#,
        )
        .unwrap();

        let baseline = run_model_check_command(
            proto_path.as_path(),
            None,
            "LInit",
            "LNext",
            &[],
            None,
            None,
            None,
            None,
            model_path.as_path(),
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();
        assert_eq!(baseline.execution.summary.result, "ok");

        let cli_with_timeout = Cli::parse_from([
            "verus-transpile",
            "model-check",
            "--input",
            "demo.rs",
            "--model",
            "model.toml",
            "--timeout",
            "1",
        ]);
        let timeout_override = match cli_with_timeout.command {
            Some(Commands::ModelCheck { timeout_ms, .. }) => timeout_ms,
            _ => panic!("Expected ModelCheck command"),
        };
        let timeout_run = run_model_check_command(
            proto_path.as_path(),
            None,
            "LInit",
            "LNext",
            &[],
            None,
            None,
            None,
            timeout_override,
            model_path.as_path(),
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();
        assert_eq!(timeout_run.execution.summary.result, "timeout_reached");
        assert_eq!(
            timeout_run.execution.exploration.stop_reason,
            ExplorationStopReason::TimeoutReached
        );

        let cli_with_timeout_alias = Cli::parse_from([
            "verus-transpile",
            "model-check",
            "--input",
            "demo.rs",
            "--model",
            "model.toml",
            "--timeout-ms",
            "1",
        ]);
        let timeout_alias_override = match cli_with_timeout_alias.command {
            Some(Commands::ModelCheck { timeout_ms, .. }) => timeout_ms,
            _ => panic!("Expected ModelCheck command"),
        };
        let timeout_alias_run = run_model_check_command(
            proto_path.as_path(),
            None,
            "LInit",
            "LNext",
            &[],
            None,
            None,
            None,
            timeout_alias_override,
            model_path.as_path(),
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();
        assert_eq!(
            timeout_alias_run.execution.summary.result,
            "timeout_reached"
        );
        assert_eq!(
            timeout_alias_run.execution.exploration.stop_reason,
            ExplorationStopReason::TimeoutReached
        );
    }

    #[test]
    fn test_model_check_command_rejects_invalid_limit_overrides() {
        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1
"#,
        )
        .unwrap();

        let command = Commands::ModelCheck {
            input: proto_path,
            types: None,
            init: "LInit".to_string(),
            next: "LNext".to_string(),
            invariant: vec![],
            search: None,
            max_depth: Some(0),
            max_states: None,
            timeout_ms: None,
            json_report: false,
            export_parity: None,
            export_parity_debug: None,
            model: model_path,
            no_bytecode: false,
            native_codegen: false,
            workers: 1,
            conflict_profile: false,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        let err = handle_command(&command, &cli).unwrap_err();
        assert!(err.to_string().contains("search limits must be > 0"));
    }

    #[test]
    fn test_model_check_command_accepts_json_report() {
        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1
"#,
        )
        .unwrap();

        let command = Commands::ModelCheck {
            input: proto_path,
            types: None,
            init: "LInit".to_string(),
            next: "LNext".to_string(),
            invariant: vec![],
            search: None,
            max_depth: None,
            max_states: None,
            timeout_ms: None,
            json_report: true,
            export_parity: None,
            export_parity_debug: None,
            model: model_path,
            no_bytecode: false,
            native_codegen: false,
            workers: 1,
            conflict_profile: false,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        handle_command(&command, &cli).unwrap();
    }

    #[test]
    fn test_execute_model_check_reports_invariant_violation_summary() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }

    pub open spec fn LInvBad(s: LState, c: LConstants) -> bool {
        s.value < 0 && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1

[properties]
invariants = ["LInvBad"]
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "invariant_violated");
        assert_eq!(
            execution
                .exploration
                .invariant_violation
                .as_ref()
                .map(|v| v.invariant.as_str()),
            Some("LInvBad")
        );
        assert_eq!(execution.summary.states, 2);
    }

    #[test]
    fn test_execute_model_check_explores_multiple_constants_valuations() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.domains.limit]
kind = "int_range"
min = 1
max = 2

[quantifiers.int]
min = 0
max = 2
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert_eq!(execution.summary.constants_valuations_total, 2);
        assert_eq!(execution.summary.constants_valuations_explored, 2);
        assert_eq!(execution.summary.states, 2);
        assert_eq!(execution.summary.transitions, 2);
    }

    #[test]
    fn test_execute_model_check_uses_fully_pinned_linit_state_fallback_on_expansion_limit() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState {
        pub a: int,
        pub b: int,
        pub c: int,
        pub d: int,
        pub e: int,
        pub f: int,
        pub g: int,
        pub h: int,
    }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.a == 0
        &&& s.b == 0
        &&& s.c == 0
        &&& s.d == 0
        &&& s.e == 0
        &&& s.f == 0
        &&& s.g == 0
        &&& s.h == 0
        &&& c.limit >= 0
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        &&& s_.a == s.a
        &&& s_.b == s.b
        &&& s_.c == s.c
        &&& s_.d == s.d
        &&& s_.e == s.e
        &&& s_.f == s.f
        &&& s_.g == s.g
        &&& s_.h == s.h
        &&& s.a <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 0

[quantifiers.int]
min = 0
max = 1

[search]
max_depth = 1
max_states = 50
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert_eq!(execution.summary.states, 1);
        assert_eq!(execution.summary.transitions, 1);
    }

    #[test]
    fn test_execute_model_check_linit_fallback_supports_binary_and_and_unfiltered_successors() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState {
        pub a: int,
        pub b: int,
        pub c: int,
        pub d: int,
        pub e: int,
        pub f: int,
        pub g: int,
        pub h: int,
        pub tags: Set<int>,
    }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        (s.a == 0)
            && (s.b == 0)
            && (s.c == 0)
            && (s.d == 0)
            && (s.e == 0)
            && (s.f == 0)
            && (s.g == 0)
            && (s.h == 0)
            && (s.tags == Set::<int>::empty())
            && (c.limit >= 0)
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        (s_.a == s.a + 1)
            && (s_.b == s.b)
            && (s_.c == s.c)
            && (s_.d == s.d)
            && (s_.e == s.e)
            && (s_.f == s.f)
            && (s_.g == s.g)
            && (s_.h == s.h)
            && (s_.tags == s.tags)
            && (s.a < c.limit)
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1

[collections]
max_set_len = 1
max_seq_len = 1
max_map_len = 1

[search]
max_depth = 3
max_states = 50
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert_eq!(execution.summary.states, 2);
        assert_eq!(execution.summary.transitions, 1);
    }

    #[test]
    fn test_execute_model_check_linit_fallback_supports_enum_variant_is_constraints() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub enum LPhase { Empty, Busy }

    pub struct LState {
        pub a: int,
        pub b: int,
        pub c: int,
        pub d: int,
        pub e: int,
        pub f: int,
        pub g: int,
        pub h: int,
        pub phase: LPhase,
    }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.a == 0
        &&& s.b == 0
        &&& s.c == 0
        &&& s.d == 0
        &&& s.e == 0
        &&& s.f == 0
        &&& s.g == 0
        &&& s.h == 0
        &&& s.phase is Empty
        &&& c.limit >= 0
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        &&& s_.a == s.a
        &&& s_.b == s.b
        &&& s_.c == s.c
        &&& s_.d == s.d
        &&& s_.e == s.e
        &&& s_.f == s.f
        &&& s_.g == s.g
        &&& s_.h == s.h
        &&& s_.phase == s.phase
        &&& s.a <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 0

[quantifiers.int]
min = 0
max = 1

[search]
max_depth = 1
max_states = 50
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert_eq!(execution.summary.states, 1);
        assert_eq!(execution.summary.transitions, 1);
    }

    #[test]
    fn test_execute_model_check_linit_fallback_supports_constants_field_equalities() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState {
        pub a: int,
        pub b: int,
        pub c: int,
        pub d: int,
        pub e: int,
        pub f: int,
        pub g: int,
        pub h: int,
    }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.a == 0
        &&& s.b == 0
        &&& s.c == 0
        &&& s.d == 0
        &&& s.e == 0
        &&& s.f == 0
        &&& s.g == 0
        &&& s.h == c.limit
        &&& c.limit >= 0
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        &&& s_.a == s.a
        &&& s_.b == s.b
        &&& s_.c == s.c
        &&& s_.d == s.d
        &&& s_.e == s.e
        &&& s_.f == s.f
        &&& s_.g == s.g
        &&& s_.h == s.h
        &&& s.h <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.domains.limit]
kind = "int_range"
min = 1
max = 2

[quantifiers.int]
min = 0
max = 2

[search]
max_depth = 1
max_states = 50
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert_eq!(execution.summary.constants_valuations_total, 2);
        assert_eq!(execution.summary.constants_valuations_explored, 2);
        assert_eq!(execution.summary.states, 2);
        assert_eq!(execution.summary.transitions, 2);
    }

    #[test]
    fn test_execute_model_check_linit_fallback_supports_implication_and_if_constants_expressions() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub enum LRole { Head, Tail }

    pub struct LState {
        pub a: int,
        pub b: int,
        pub c: int,
        pub d: int,
        pub e: int,
        pub f: int,
        pub g: int,
        pub h: int,
        pub role: LRole,
        pub has_predecessor: bool,
        pub predecessor: int,
        pub alive: bool,
    }
    pub struct LConstants { pub node_id: int, pub chain_len: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.a == 0
        &&& s.b == 0
        &&& s.c == 0
        &&& s.d == 0
        &&& s.e == 0
        &&& s.f == 0
        &&& s.g == 0
        &&& s.h == 0
        &&& (c.node_id == 0 ==> s.role is Head)
        &&& (c.node_id == c.chain_len - 1 ==> s.role is Tail)
        &&& s.has_predecessor == (c.node_id > 0)
        &&& s.predecessor == (if c.node_id > 0 { c.node_id - 1 } else { 0int })
        &&& s.alive == true
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        &&& s_.a == s.a
        &&& s_.b == s.b
        &&& s_.c == s.c
        &&& s_.d == s.d
        &&& s_.e == s.e
        &&& s_.f == s.f
        &&& s_.g == s.g
        &&& s_.h == s.h
        &&& s_.role == s.role
        &&& s_.has_predecessor == s.has_predecessor
        &&& s_.predecessor == s.predecessor
        &&& s_.alive == s.alive
        &&& s.predecessor <= c.chain_len
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
node_id = 0
chain_len = 2

[quantifiers.int]
min = 0
max = 2

[search]
max_depth = 1
max_states = 50
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert_eq!(execution.summary.states, 1);
        assert_eq!(execution.summary.transitions, 1);
    }

    #[test]
    fn test_execute_model_check_constants_resolution_still_rejects_zero_matches() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.domains.limit]
kind = "int_range"
min = 5
max = 6

[quantifiers.int]
min = 0
max = 2
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let err = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap_err();
        assert!(
            err.to_string().contains(
                "Model-check constants resolution produced zero matching `LConstants` valuations"
            ),
            "expected zero-match constants resolution error, got: {}",
            err
        );
    }

    #[test]
    fn test_execute_model_check_constants_assignments_can_synthesize_out_of_domain_values() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 3 }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        (s.value == 0 && s_.value == 1 && c.limit == 3)
        || (s.value == 1 && s_.value == 1 && c.limit == 3)
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 3

[quantifiers.int]
min = 0
max = 1

[search]
max_depth = 3
max_states = 50

[properties]
check_deadlock = true
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert_eq!(execution.summary.constants_valuations_total, 1);
        assert_eq!(execution.summary.constants_valuations_explored, 1);
        assert!(execution.summary.states >= 2);
        assert!(execution.summary.transitions >= 1);
    }

    #[test]
    fn test_execute_model_check_reports_leads_to_violation_on_avoidable_cycle() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 1 }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        (s.value == 0 && s_.value == 0)
        || (s.value == 0 && s_.value == 1 && s_.value <= c.limit)
        || (s.value == 1 && s_.value == 1 && s_.value <= c.limit)
    }

    pub open spec fn LFrom(s: LState, c: LConstants) -> bool { s.value == 0 && 0 <= c.limit }
    pub open spec fn LTo(s: LState, c: LConstants) -> bool { s.value == 1 && 0 <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1

[properties]
leads_to = [{ name = "eventual_one", from = "LFrom", to = "LTo" }]
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "leads_to_violated");
        let violation = execution
            .leads_to_violation
            .as_ref()
            .expect("expected leads-to violation");
        assert_eq!(violation.obligation_name, "eventual_one");
        assert_eq!(violation.from_name, "LFrom");
        assert_eq!(violation.to_name, "LTo");
        assert!(!violation.counterexample.steps.is_empty());
        let liveness = execution
            .summary
            .liveness
            .as_ref()
            .expect("expected liveness summary");
        assert!(liveness.checked);
        assert!(liveness.violation_found);
        assert_eq!(liveness.obligations, 1);
        assert_eq!(liveness.fairness_weak, 0);
        assert_eq!(liveness.fairness_strong, 0);
        assert!(liveness.skipped_reason.is_none());
        assert!(execution.summary.enumeration.successor_cache_hits > 0);
        assert!(execution.summary.enumeration.successor_cache_misses > 0);
    }

    #[test]
    fn test_execute_model_check_accepts_leads_to_when_destination_is_eventually_forced() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 1 }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        (s.value == 0 && s_.value == 1 && s_.value <= c.limit)
        || (s.value == 1 && s_.value == 1 && s_.value <= c.limit)
    }

    pub open spec fn LFrom(s: LState, c: LConstants) -> bool { s.value == 0 && 0 <= c.limit }
    pub open spec fn LTo(s: LState, c: LConstants) -> bool { s.value == 1 && 0 <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1

[properties]
leads_to = [{ from = "LFrom", to = "LTo" }]
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert!(execution.leads_to_violation.is_none());
        let liveness = execution
            .summary
            .liveness
            .as_ref()
            .expect("expected liveness summary");
        assert!(liveness.checked);
        assert!(!liveness.violation_found);
        assert_eq!(liveness.obligations, 1);
        assert!(liveness.skipped_reason.is_none());
        assert!(execution.summary.enumeration.successor_cache_hits > 0);
        assert!(execution.summary.enumeration.successor_cache_misses > 0);
    }

    #[test]
    fn test_execute_model_check_reports_enumeration_fallback_telemetry() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 1 }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert_eq!(
            execution
                .summary
                .enumeration
                .direct_assignment_branch_solves,
            0
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .enumeration_fallback_branch_solves,
            2
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .enumeration_candidate_evaluations,
            4
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .guard_pruned_candidate_evaluations,
            0
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .candidate_evaluation_guardrail_per_state_branch,
            10_000
        );
        assert_eq!(execution.summary.enumeration.successor_cache_hits, 0);
        assert!(execution.summary.enumeration.successor_cache_misses > 0);
    }

    #[test]
    fn test_execute_model_check_uses_direct_helper_branch_solving_when_possible() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 1 }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LStep(s: LState, s_: LState, c: LConstants) -> bool {
        (s.value == 0 && s_.value == 1 && s_.value <= c.limit)
        || (s.value == 1 && s_.value == 1 && s_.value <= c.limit)
    }

    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        LStep(s, s_, c)
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert_eq!(
            execution
                .summary
                .enumeration
                .direct_assignment_branch_solves,
            2
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .enumeration_fallback_branch_solves,
            0
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .enumeration_candidate_evaluations,
            0
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .guard_pruned_candidate_evaluations,
            0
        );

        let branch_telemetry = &execution.summary.branch_telemetry;
        assert_eq!(branch_telemetry.len(), 1);
        let branch = &branch_telemetry[0];
        assert_eq!(branch.branch_label, "branch_0");
        assert!(branch.invocations > 0);
        assert_eq!(branch.existential_assignment_count, 1);
        assert_eq!(branch.candidate_state_count, 2);
        assert_eq!(branch.direct_solver_hits, 2);
        assert_eq!(branch.enumeration_fallback_hits, 0);
        assert_eq!(branch.guard_pruned_candidate_evaluations, 0);
        assert!(branch.successful_successors > 0);
        assert!(branch.cumulative_solve_elapsed_ms <= execution.summary.elapsed_ms);
    }

    #[test]
    fn test_execute_model_check_uses_direct_helper_branch_solving_with_call_site_existentials() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 1 }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LStep(s: LState, s_: LState, c: LConstants, i: int) -> bool {
        &&& i == 1
        &&& s_.value == i
        &&& s_.value <= c.limit
    }

    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        exists |i: int| LStep(s, s_, c, i)
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert!(
            execution
                .summary
                .enumeration
                .direct_assignment_branch_solves
                > 0
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .enumeration_fallback_branch_solves,
            0
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .enumeration_candidate_evaluations,
            0
        );
        let branch = execution
            .summary
            .branch_telemetry
            .iter()
            .find(|entry| entry.branch_label == "branch_0")
            .expect("branch_0 telemetry should be present");
        assert!(branch.direct_solver_hits > 0);
        assert_eq!(branch.enumeration_fallback_hits, 0);
    }

    #[test]
    fn test_execute_model_check_helper_solver_skips_unsupported_subbranches() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 1 }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LStep(s: LState, s_: LState, c: LConstants) -> bool {
        (s.value == 0)
            || ((s_.value == s.value + 1) && (s_.value <= c.limit))
    }

    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        LStep(s, s_, c)
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert!(execution.summary.states >= 1);
    }

    #[test]
    fn test_execute_model_check_helper_solver_skips_statically_disabled_unsupported_subbranches_without_fallback(
    ) {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 1 }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LStep(s: LState, s_: LState, c: LConstants) -> bool {
        (s.value == 2) || ((s_.value == s.value + 1) && (s_.value <= c.limit))
    }

    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        LStep(s, s_, c)
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert!(
            execution
                .summary
                .enumeration
                .direct_assignment_branch_solves
                > 0
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .enumeration_fallback_branch_solves,
            0
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .enumeration_candidate_evaluations,
            0
        );
        let branch = execution
            .summary
            .branch_telemetry
            .iter()
            .find(|entry| entry.branch_label == "branch_0")
            .expect("branch_0 telemetry should be present");
        assert!(branch.direct_solver_hits > 0);
        assert_eq!(branch.enumeration_fallback_hits, 0);
    }

    #[test]
    fn test_case19_epaxos_propose_helper_is_satisfiable_from_init_with_record_packets() {
        use std::path::PathBuf;
        use std::sync::Arc;
        use verus_transpiler::ast::Path;
        use verus_transpiler::modelcheck::config::parse_model_config_str;
        use verus_transpiler::modelcheck::value::{RuntimeCollectionBounds, RuntimeValue, SetRepr};
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let protocol_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("DPOR_based_model_tla_rs_checker/tests/tla-rs/19_epaxos_small/Epaxos.rs");
        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            protocol_path.as_path(),
            None,
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_str(
            r#"
[quantifiers.int]
min = 0
max = 1
"#,
        )
        .unwrap();
        let bounds = RuntimeCollectionBounds::from(&model_config.collections);

        let empty_set = || RuntimeValue::Set(Arc::new(SetRepr::new()));
        let singleton_set =
            |v: i128| RuntimeValue::Set(Arc::new(SetRepr::from_values(vec![RuntimeValue::Int(v)])));

        let init_state = RuntimeValue::struct_value(
            "LState",
            vec![
                ("accept_senders".to_string(), empty_set()),
                ("ballot".to_string(), RuntimeValue::Int(0)),
                ("cmd".to_string(), RuntimeValue::Int(0)),
                ("committed_count".to_string(), RuntimeValue::Int(0)),
                ("dep_count".to_string(), RuntimeValue::Int(0)),
                ("executed_count".to_string(), RuntimeValue::Int(0)),
                ("has_conflict".to_string(), RuntimeValue::Bool(false)),
                ("is_leader".to_string(), RuntimeValue::Bool(false)),
                ("max_resp_seq".to_string(), RuntimeValue::Int(0)),
                ("phase".to_string(), RuntimeValue::Int(0)),
                ("preaccept_senders".to_string(), empty_set()),
                ("seq".to_string(), RuntimeValue::Int(0)),
            ],
        )
        .unwrap();

        let init_result = eval_spec_function_call_recursive(
            &bundle.spec_functions,
            &bundle.schema,
            &model_config,
            &Path::single("LInit".to_string()),
            std::slice::from_ref(&init_state),
            bounds,
            0,
        )
        .unwrap();
        assert_eq!(init_result, RuntimeValue::Bool(true));

        let next_state = RuntimeValue::struct_value(
            "LState",
            vec![
                ("accept_senders".to_string(), empty_set()),
                ("ballot".to_string(), RuntimeValue::Int(0)),
                ("cmd".to_string(), RuntimeValue::Int(1)),
                ("committed_count".to_string(), RuntimeValue::Int(0)),
                ("dep_count".to_string(), RuntimeValue::Int(0)),
                ("executed_count".to_string(), RuntimeValue::Int(0)),
                ("has_conflict".to_string(), RuntimeValue::Bool(false)),
                ("is_leader".to_string(), RuntimeValue::Bool(true)),
                ("max_resp_seq".to_string(), RuntimeValue::Int(0)),
                ("phase".to_string(), RuntimeValue::Int(1)),
                ("preaccept_senders".to_string(), singleton_set(0)),
                ("seq".to_string(), RuntimeValue::Int(1)),
            ],
        )
        .unwrap();

        let propose_result = eval_spec_function_call_recursive(
            &bundle.spec_functions,
            &bundle.schema,
            &model_config,
            &Path::single("LPropose".to_string()),
            &[init_state, next_state, RuntimeValue::Int(1)],
            bounds,
            0,
        )
        .unwrap();
        assert_eq!(propose_result, RuntimeValue::Bool(true));
    }

    #[test]
    fn test_execute_model_check_helper_direct_solver_supports_next_state_is_constraints() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub enum LPhase {
        Idle,
        Phase1,
    }
    pub struct LState {
        pub phase: LPhase,
        pub value: int,
    }
    pub struct LConstants {
        pub limit: int,
    }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        &&& s.phase is Idle
        &&& s.value == 0
        &&& c.limit == 1
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LStep(s: LState, s_: LState, c: LConstants, i: int) -> bool {
        &&& i == 1
        &&& s.phase is Idle
        &&& s_.phase is Phase1
        &&& s_.value == i
        &&& s_.value <= c.limit
    }

    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        exists |i: int| LStep(s, s_, c, i)
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert!(
            execution
                .summary
                .enumeration
                .direct_assignment_branch_solves
                > 0
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .enumeration_fallback_branch_solves,
            0
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .enumeration_candidate_evaluations,
            0
        );
        let branch = execution
            .summary
            .branch_telemetry
            .iter()
            .find(|entry| entry.branch_label == "branch_0")
            .expect("branch_0 telemetry should be present");
        assert!(branch.direct_solver_hits > 0);
        assert_eq!(branch.enumeration_fallback_hits, 0);
    }

    #[test]
    fn test_execute_model_check_reports_guard_pruned_enumeration_telemetry() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 1 }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LStep(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value <= c.limit
    }

    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s.value == 1 && LStep(s, s_, c)
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[properties]
check_deadlock = false

[quantifiers.int]
min = 0
max = 1
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert_eq!(
            execution
                .summary
                .enumeration
                .direct_assignment_branch_solves,
            0
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .enumeration_fallback_branch_solves,
            1
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .enumeration_candidate_evaluations,
            0
        );
        assert_eq!(
            execution
                .summary
                .enumeration
                .guard_pruned_candidate_evaluations,
            2
        );

        let branch_telemetry = &execution.summary.branch_telemetry;
        assert_eq!(branch_telemetry.len(), 1);
        let branch = &branch_telemetry[0];
        assert_eq!(branch.branch_label, "branch_0");
        assert_eq!(branch.existential_assignment_count, 1);
        assert_eq!(branch.candidate_state_count, 2);
        assert_eq!(branch.direct_solver_hits, 0);
        assert_eq!(branch.enumeration_fallback_hits, 1);
        assert_eq!(branch.guard_pruned_candidate_evaluations, 2);
        assert_eq!(branch.successful_successors, 0);
    }

    #[test]
    fn test_execute_model_check_candidate_enumeration_guardrail_triggers_clean_error() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 10001 }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 10001

[quantifiers.int]
min = 0
max = 10001
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let err = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap_err();

        let message = err.to_string();
        assert!(message.contains("candidate-enumeration guardrail exceeded"));
        assert!(message.contains("branch `branch_0`"));
        assert!(message.contains("limit = 10000"));
    }

    #[test]
    fn test_execute_model_check_filters_leads_to_violation_with_strong_fairness() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 2 }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        (s.value == 0 && s_.value == 1 && s_.value <= c.limit)
        || (s.value == 1 && s_.value == 0 && s_.value <= c.limit)
        || (s.value == 0 && s_.value == 2 && s_.value <= c.limit)
        || (s.value == 1 && s_.value == 2 && s_.value <= c.limit)
        || (s.value == 2 && s_.value == 2 && s_.value <= c.limit)
    }

    pub open spec fn LFrom(s: LState, c: LConstants) -> bool { s.value == 0 && 0 <= c.limit }
    pub open spec fn LTo(s: LState, c: LConstants) -> bool { s.value == 2 && 0 <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 2

[quantifiers.int]
min = 0
max = 2

[properties]
leads_to = [{ from = "LFrom", to = "LTo" }]
fairness = { strong = ["branch_2", "branch_3"] }
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "ok");
        assert!(execution.leads_to_violation.is_none());
        let liveness = execution
            .summary
            .liveness
            .as_ref()
            .expect("expected liveness summary");
        assert!(liveness.checked);
        assert!(!liveness.violation_found);
        assert_eq!(liveness.obligations, 1);
        assert_eq!(liveness.fairness_weak, 0);
        assert_eq!(liveness.fairness_strong, 2);
        assert!(liveness.skipped_reason.is_none());
    }

    #[test]
    fn test_execute_model_check_marks_liveness_skipped_when_exploration_is_incomplete() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 1 }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        (s.value == 0 && s_.value == 1 && s_.value <= c.limit)
        || (s.value == 1 && s_.value == 1 && s_.value <= c.limit)
    }

    pub open spec fn LFrom(s: LState, c: LConstants) -> bool { s.value == 0 && 0 <= c.limit }
    pub open spec fn LTo(s: LState, c: LConstants) -> bool { s.value == 1 && 0 <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1

[search]
max_states = 2

[properties]
leads_to = [{ from = "LFrom", to = "LTo" }]
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "max_states_reached");
        assert!(execution.leads_to_violation.is_none());
        let liveness = execution
            .summary
            .liveness
            .as_ref()
            .expect("expected liveness summary");
        assert!(!liveness.checked);
        assert!(!liveness.violation_found);
        assert_eq!(
            liveness.skipped_reason.as_deref(),
            Some("incomplete_exploration")
        );
        assert_eq!(execution.summary.enumeration.successor_cache_hits, 0);
    }

    #[test]
    fn test_execute_model_check_marks_liveness_skipped_on_timeout() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 2000 }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s.value < c.limit && s_.value == s.value + 1
    }

    pub open spec fn LFrom(s: LState, c: LConstants) -> bool { s.value == 0 && c.limit == 2000 }
    pub open spec fn LTo(s: LState, c: LConstants) -> bool { s.value == c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 2000

[quantifiers.int]
min = 0
max = 2000

[search]
max_depth = 2000
max_states = 4000
timeout_ms = 1

[properties]
leads_to = [{ from = "LFrom", to = "LTo" }]
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(execution.summary.result, "timeout_reached");
        let liveness = execution
            .summary
            .liveness
            .as_ref()
            .expect("expected liveness summary");
        assert!(!liveness.checked);
        assert!(!liveness.violation_found);
        assert_eq!(
            liveness.skipped_reason.as_deref(),
            Some("incomplete_exploration")
        );
        assert_eq!(execution.summary.enumeration.successor_cache_hits, 0);
    }

    #[test]
    fn test_execute_model_check_respects_hash_compaction_dedup_mode() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        (s.value < c.limit && s_.value == s.value + 1) || (s_.value == s.value)
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1

[search]
state_dedup = "hash_compaction64"
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(
            model_config.search.state_dedup,
            verus_transpiler::modelcheck::config::StateDedupMode::HashCompaction64
        );
        assert_eq!(execution.summary.result, "ok");
        assert!(execution.summary.states >= 1);
        assert_eq!(execution.exploration.stats.hash_compaction_collisions, 0);
    }

    #[test]
    fn test_classify_search_evidence_mode_marks_canonical_as_exact_proof_strength() {
        use verus_transpiler::modelcheck::config::SearchLimits;

        let search = SearchLimits::default();
        let evidence = classify_search_evidence_mode(&search);

        assert_eq!(evidence.class, "exact_proof_strength");
        assert!(evidence.proof_strength);
        assert!(evidence.lossy_reasons.is_empty());
        assert!(evidence.guidance.contains("proof-strength"));
    }

    #[test]
    fn test_classify_search_evidence_mode_marks_hash_compaction_as_lossy_bug_finding() {
        use verus_transpiler::modelcheck::config::{SearchLimits, StateDedupMode};

        let search = SearchLimits {
            state_dedup: StateDedupMode::HashCompaction64,
            ..Default::default()
        };
        let evidence = classify_search_evidence_mode(&search);

        assert_eq!(evidence.class, "lossy_bug_finding_accelerator");
        assert!(!evidence.proof_strength);
        assert_eq!(
            evidence.lossy_reasons,
            vec!["hash_compaction64_collision_risk"]
        );
        assert!(evidence.guidance.contains("bug-finding"));
    }

    #[test]
    fn test_classify_search_evidence_mode_marks_symmetry_merging_as_lossy_bug_finding() {
        use verus_transpiler::modelcheck::config::SearchLimits;

        let search = SearchLimits {
            symmetry_fields: vec!["node_a".to_string()],
            ..Default::default()
        };
        let evidence = classify_search_evidence_mode(&search);

        assert_eq!(evidence.class, "lossy_bug_finding_accelerator");
        assert!(!evidence.proof_strength);
        assert_eq!(
            evidence.lossy_reasons,
            vec!["symmetry_fields_state_merging"]
        );
    }

    #[test]
    fn test_execute_model_check_respects_symmetry_field_dedup() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1

[search]
state_dedup = "canonical"
symmetry_fields = ["value"]
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(
            model_config.search.symmetry_fields,
            vec!["value".to_string()]
        );
        assert_eq!(execution.summary.result, "ok");
        assert_eq!(execution.summary.states, 1);
        assert_eq!(execution.exploration.stats.symmetry_collapses, 1);
    }

    #[test]
    fn test_execute_model_check_applies_invisible_branch_por_heuristic() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub visible: int, pub hidden: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        s.visible == 0 && s.hidden == 0 && 0 <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        (s_.hidden == s.hidden + 1)
        || (s_.visible == s.visible + 1 && s_.visible <= c.limit)
    }

    pub open spec fn LVisibleBound(s: LState, c: LConstants) -> bool {
        s.visible <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1

[search]
por_heuristic = "invisible_branch"

[properties]
invariants = ["LVisibleBound"]
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();
        let execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        assert_eq!(
            model_config.search.por_heuristic,
            verus_transpiler::modelcheck::config::PorHeuristic::InvisibleBranch
        );
        assert_eq!(execution.por_pruned_branches, vec!["branch_0".to_string()]);
        assert_eq!(execution.summary.result, "ok");
        assert_eq!(execution.summary.states, 3);
        assert_eq!(execution.por_pruned_branches.len(), 1);
    }

    #[test]
    fn test_parallel_bfs_produces_same_state_count_as_sequential() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        // A protocol with multiple branches and enough state space to exercise
        // parallel frontier expansion: a 2-counter system with wrap-around.
        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub x: int, pub y: int }
    pub struct LConstants { pub bound: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        s.x == 0 && s.y == 0 && c.bound > 0
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        ||| {
            &&& s_.x == (s.x + 1) % c.bound
            &&& s_.y == s.y
        }
        ||| {
            &&& s_.x == s.x
            &&& s_.y == (s.y + 1) % c.bound
        }
    }
    pub open spec fn LTypeOK(s: LState, c: LConstants) -> bool {
        0 <= s.x < c.bound && 0 <= s.y < c.bound
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
bound = 3

[quantifiers.int]
min = 0
max = 3

[properties]
invariants = ["LTypeOK"]
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();

        // Sequential (workers=1)
        let seq_execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        // Parallel (workers=2)
        let par_execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            2,
            false,
        )
        .unwrap();

        assert_eq!(seq_execution.summary.result, "ok");
        assert_eq!(par_execution.summary.result, "ok");
        // Both must explore exactly the same number of states
        assert_eq!(
            seq_execution.summary.states, par_execution.summary.states,
            "parallel BFS state count ({}) should match sequential ({})",
            par_execution.summary.states, seq_execution.summary.states
        );
        // 3×3 = 9 states expected
        assert_eq!(seq_execution.summary.states, 9);
    }

    #[test]
    fn test_parallel_bfs_detects_invariant_violation() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        s.value == 0 && c.limit > 0
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value + 1 && s.value < c.limit
    }
    pub open spec fn LInvBad(s: LState, c: LConstants) -> bool {
        s.value < 2
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 3

[quantifiers.int]
min = 0
max = 4

[properties]
invariants = ["LInvBad"]
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();

        // Sequential (workers=1)
        let seq_execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        // Parallel (workers=2)
        let par_execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            2,
            false,
        )
        .unwrap();

        // Both should detect the invariant violation
        assert_eq!(seq_execution.summary.result, "invariant_violated");
        assert_eq!(par_execution.summary.result, "invariant_violated");
    }

    #[test]
    fn test_parallel_bfs_multi_constants_valuations_parity() {
        use verus_transpiler::modelcheck::config::parse_model_config_file;
        use verus_transpiler::modelcheck::invariant::resolve_selected_invariants;
        use verus_transpiler::spec_analyzer::ingest_protocol_sources_with_types_and_entrypoints;

        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool {
        s.value == c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.domains.limit]
kind = "int_range"
min = 1
max = 3

[quantifiers.int]
min = 0
max = 3
"#,
        )
        .unwrap();

        let bundle = ingest_protocol_sources_with_types_and_entrypoints(
            proto_path.as_path(),
            Some(types_path.as_path()),
            "LInit",
            "LNext",
        )
        .unwrap();
        let model_config = parse_model_config_file(&model_path).unwrap();
        let selected_invariants = resolve_selected_invariants(
            &bundle.spec_functions,
            &model_config.properties.invariants,
        )
        .unwrap();

        let seq_execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            1,
            false,
        )
        .unwrap();

        let par_execution = execute_model_check(
            &bundle,
            &model_config,
            CliSearchMode::Bfs,
            &selected_invariants,
            None,
            false,
            false,
            2,
            false,
        )
        .unwrap();

        assert_eq!(seq_execution.summary.result, "ok");
        assert_eq!(par_execution.summary.result, "ok");
        // Multiple constants valuations: each should explore independently
        assert_eq!(seq_execution.summary.constants_valuations_total, 3);
        assert_eq!(par_execution.summary.constants_valuations_total, 3);
        assert_eq!(
            seq_execution.summary.states, par_execution.summary.states,
            "parallel BFS state count ({}) should match sequential ({}) across multiple constants valuations",
            par_execution.summary.states, seq_execution.summary.states
        );
    }

    #[test]
    fn test_model_check_command_with_explicit_types_override() {
        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("custom_types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1
"#,
        )
        .unwrap();

        let command = Commands::ModelCheck {
            input: proto_path,
            types: Some(types_path),
            init: "LInit".to_string(),
            next: "LNext".to_string(),
            invariant: vec![],
            search: None,
            max_depth: None,
            max_states: None,
            timeout_ms: None,
            json_report: false,
            export_parity: None,
            export_parity_debug: None,
            model: model_path,
            no_bytecode: false,
            native_codegen: false,
            workers: 1,
            conflict_profile: false,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        handle_command(&command, &cli).unwrap();
    }

    #[test]
    fn test_model_check_command_with_custom_entrypoint_names() {
        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn InitCustom(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn NextCustom(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1
"#,
        )
        .unwrap();

        let command = Commands::ModelCheck {
            input: proto_path,
            types: None,
            init: "InitCustom".to_string(),
            next: "NextCustom".to_string(),
            invariant: vec![],
            search: None,
            max_depth: None,
            max_states: None,
            timeout_ms: None,
            json_report: false,
            export_parity: None,
            export_parity_debug: None,
            model: model_path,
            no_bytecode: false,
            native_codegen: false,
            workers: 1,
            conflict_profile: false,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        handle_command(&command, &cli).unwrap();
    }

    #[test]
    fn test_value_domain_values_accepts_structured_canonical_key() {
        use verus_transpiler::modelcheck::config::{DomainSpec, ModelValue};
        use verus_transpiler::modelcheck::value::{RuntimeCollectionBounds, RuntimeValue};

        let bounds = RuntimeCollectionBounds {
            max_seq_len: 1,
            max_set_len: 1,
            max_map_len: 1,
        };
        let value = RuntimeValue::set_bounded([RuntimeValue::Int(0)], &bounds)
            .expect("set runtime value should construct");
        let domain = DomainSpec::Values {
            values: vec![ModelValue::String("set:{int:0}".to_string())],
        };

        assert!(
            value_matches_domain_spec(&value, &domain, "rm")
                .expect("canonical-key matching should evaluate"),
            "values-domain canonical key should match structured runtime constants"
        );
    }

    #[test]
    fn test_model_check_command_rejects_missing_custom_next_entrypoint() {
        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn InitCustom(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn NextOther(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(&model_path, "").unwrap();

        let command = Commands::ModelCheck {
            input: proto_path,
            types: None,
            init: "InitCustom".to_string(),
            next: "NextCustom".to_string(),
            invariant: vec![],
            search: None,
            max_depth: None,
            max_states: None,
            timeout_ms: None,
            json_report: false,
            export_parity: None,
            export_parity_debug: None,
            model: model_path,
            no_bytecode: false,
            native_codegen: false,
            workers: 1,
            conflict_profile: false,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        let err = handle_command(&command, &cli).unwrap_err();
        assert!(err
            .to_string()
            .contains("Missing required entrypoint `NextCustom"));
    }

    #[test]
    fn test_model_check_command_rejects_missing_explicit_types_path() {
        let dir = tempfile::tempdir().unwrap();
        let proto_path = dir.path().join("demo.rs");
        let missing_types_path = dir.path().join("missing_types.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(&model_path, "").unwrap();

        let command = Commands::ModelCheck {
            input: proto_path,
            types: Some(missing_types_path),
            init: "LInit".to_string(),
            next: "LNext".to_string(),
            invariant: vec![],
            search: None,
            max_depth: None,
            max_states: None,
            timeout_ms: None,
            json_report: false,
            export_parity: None,
            export_parity_debug: None,
            model: model_path,
            no_bytecode: false,
            native_codegen: false,
            workers: 1,
            conflict_profile: false,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        let err = handle_command(&command, &cli).unwrap_err();
        assert!(err
            .to_string()
            .contains("Explicit types source file not found"));
    }

    #[test]
    fn test_model_check_command_rejects_unknown_invariant() {
        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1

[properties]
invariants = ["LMissing"]
"#,
        )
        .unwrap();

        let command = Commands::ModelCheck {
            input: proto_path,
            types: None,
            init: "LInit".to_string(),
            next: "LNext".to_string(),
            invariant: vec![],
            search: None,
            max_depth: None,
            max_states: None,
            timeout_ms: None,
            json_report: false,
            export_parity: None,
            export_parity_debug: None,
            model: model_path,
            no_bytecode: false,
            native_codegen: false,
            workers: 1,
            conflict_profile: false,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        let err = handle_command(&command, &cli).unwrap_err();
        assert!(err.to_string().contains("Invariant `LMissing`"));
    }

    #[test]
    fn test_model_check_command_cli_invariant_override_takes_precedence() {
        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }

    pub open spec fn LInv(s: LState, c: LConstants) -> bool {
        s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &model_path,
            r#"
[constants.assignments]
limit = 1

[quantifiers.int]
min = 0
max = 1

[properties]
invariants = ["LMissing"]
"#,
        )
        .unwrap();

        let command = Commands::ModelCheck {
            input: proto_path,
            types: None,
            init: "LInit".to_string(),
            next: "LNext".to_string(),
            invariant: vec!["LInv".to_string()],
            search: None,
            max_depth: None,
            max_states: None,
            timeout_ms: None,
            json_report: false,
            export_parity: None,
            export_parity_debug: None,
            model: model_path,
            no_bytecode: false,
            native_codegen: false,
            workers: 1,
            conflict_profile: false,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        handle_command(&command, &cli).unwrap();
    }

    #[test]
    fn test_model_check_command_rejects_duplicate_cli_invariants() {
        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }

    pub open spec fn LInv(s: LState, c: LConstants) -> bool {
        s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(&model_path, "").unwrap();

        let command = Commands::ModelCheck {
            input: proto_path,
            types: None,
            init: "LInit".to_string(),
            next: "LNext".to_string(),
            invariant: vec!["LInv".to_string(), "LInv".to_string()],
            search: None,
            max_depth: None,
            max_states: None,
            timeout_ms: None,
            json_report: false,
            export_parity: None,
            export_parity_debug: None,
            model: model_path,
            no_bytecode: false,
            native_codegen: false,
            workers: 1,
            conflict_profile: false,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        let err = handle_command(&command, &cli).unwrap_err();
        assert!(err.to_string().contains("duplicate invariant `LInv`"));
    }

    #[test]
    fn test_model_check_command_rejects_empty_cli_invariant_name() {
        let dir = tempfile::tempdir().unwrap();
        let types_path = dir.path().join("types.rs");
        let proto_path = dir.path().join("demo.rs");
        let model_path = dir.path().join("model.toml");

        std::fs::write(
            &types_path,
            r#"
verus! {
    pub struct LState { pub value: int }
    pub struct LConstants { pub limit: int }
    pub open spec fn LInit(s: LState, c: LConstants) -> bool { s.value <= c.limit }
}
"#,
        )
        .unwrap();
        std::fs::write(
            &proto_path,
            r#"
verus! {
    pub open spec fn LNext(s: LState, s_: LState, c: LConstants) -> bool {
        s_.value == s.value && s.value <= c.limit
    }
}
"#,
        )
        .unwrap();
        std::fs::write(&model_path, "").unwrap();

        let command = Commands::ModelCheck {
            input: proto_path,
            types: None,
            init: "LInit".to_string(),
            next: "LNext".to_string(),
            invariant: vec!["   ".to_string()],
            search: None,
            max_depth: None,
            max_states: None,
            timeout_ms: None,
            json_report: false,
            export_parity: None,
            export_parity_debug: None,
            model: model_path,
            no_bytecode: false,
            native_codegen: false,
            workers: 1,
            conflict_profile: false,
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        let err = handle_command(&command, &cli).unwrap_err();
        assert!(err.to_string().contains("names cannot be empty"));
    }

    #[test]
    fn test_generate_types_does_not_inject_manual_code() {
        use std::io::Write;

        let dir = tempfile::tempdir().unwrap();
        let input_path = dir.path().join("types.rs");
        let config_path = dir.path().join("types.toml");
        let manual_path = dir.path().join("manual_helpers.rs");
        let output_path = dir.path().join("types_gen.rs");

        std::fs::write(
            &input_path,
            r#"
use vstd::prelude::*;

verus! {
pub struct LState {
    pub counter: int,
}
}
"#,
        )
        .unwrap();
        std::fs::write(
            &manual_path,
            "pub open spec fn ManualTypesHelper() -> bool { true }",
        )
        .unwrap();

        let mut config_file = std::fs::File::create(&config_path).unwrap();
        writeln!(
            config_file,
            r#"
[output]
manual_code = "manual_helpers.rs"
"#
        )
        .unwrap();

        let command = Commands::GenerateTypes {
            input: vec![input_path.clone()],
            output: Some(output_path.clone()),
            config: Some(config_path.clone()),
        };
        let cli = Cli {
            command: None,
            input: None,
            annotations: None,
            output: None,
            config: None,
            project: None,
            output_dir: None,
            stdout: false,
            verbose: false,
            dry_run: false,
            auto_skip: false,
            proof_fallback: false,
            dump_config: false,
        };

        handle_command(&command, &cli).unwrap();

        let generated = std::fs::read_to_string(&output_path).unwrap();
        // manual_code should NOT be injected in generate-types mode;
        // it is a function-generation concern (belongs in *_gen.rs, not types_gen.rs).
        assert!(
            !generated.contains("ManualTypesHelper"),
            "manual_code must not be injected during generate-types"
        );
    }

    #[test]
    fn test_rsl_types_config_has_no_manual_helpers() {
        let config_path = PathBuf::from("../src/protocol/RSL/types_transpile.toml");
        let config = load_config(&config_path).expect("RSL type config should load");
        assert!(
            config.manual_code.is_none(),
            "RSL type config should not load output.manual_code"
        );

        let file_config = FileConfig::from_file(&config_path).expect("RSL file config should load");
        assert!(
            file_config.output.manual_code.is_none(),
            "RSL file config output.manual_code should be removed"
        );
        assert!(
            file_config.output.generate_clone_up_to_view_simple,
            "RSL file config should enable output.generate_clone_up_to_view_simple"
        );
        assert!(
            file_config.output.generate_unreachable_value_helper,
            "RSL file config should enable output.generate_unreachable_value_helper"
        );
        assert_eq!(
            file_config.extra_type_aliases.get("CRslIo"),
            Some(&"LIoOp<EndPoint, CMessage>".to_string()),
            "RSL file config should define CRslIo in extra_type_aliases"
        );
        let required_skips = [
            "Ballot",
            "Request",
            "Reply",
            "Vote",
            "LAcceptor",
            "LProposer",
            "LReplica",
            "LScheduler",
            "LearnerTuple",
        ];
        for name in required_skips {
            assert!(
                file_config.skip_types.iter().any(|n| n == name),
                "skip_types should include {}",
                name
            );
        }
        assert!(
            !file_config.skip_types.iter().any(|n| n == "LParameters"),
            "skip_types should no longer include LParameters"
        );
        assert!(
            file_config
                .skip_validity_types
                .iter()
                .any(|n| n == "CParameters"),
            "skip_validity_types should include CParameters"
        );
        assert!(
            file_config
                .skip_view_types
                .iter()
                .any(|n| n == "CParameters"),
            "skip_view_types should include CParameters"
        );
        assert!(
            file_config
                .re_exports
                .iter()
                .any(|r: &String| r.contains("types_i::")),
            "re_exports should include types_i re-export"
        );
    }

    #[test]
    fn test_load_config_generate_proofs() {
        use std::io::Write;
        let dir = tempfile::tempdir().unwrap();
        let config_path = dir.path().join("test.toml");
        let mut f = std::fs::File::create(&config_path).unwrap();
        writeln!(
            f,
            r#"
[naming]
spec_prefix = "L"
exec_prefix = "C"
int_type = "u64"

[output]
generate_loops_for_verification = true
generate_proofs = true
validity_predicate_name = "valid"
"#
        )
        .unwrap();

        let config = load_config(&config_path).unwrap();
        assert!(config.translator.generate_proofs);
        assert!(config.translator.generate_loops_for_verification);
    }

    #[test]
    fn test_load_config_generate_proofs_default() {
        use std::io::Write;
        let dir = tempfile::tempdir().unwrap();
        let config_path = dir.path().join("test.toml");
        let mut f = std::fs::File::create(&config_path).unwrap();
        writeln!(
            f,
            r#"
[naming]
spec_prefix = "L"
exec_prefix = "C"

[output]
validity_predicate_name = "valid"
"#
        )
        .unwrap();

        let config = load_config(&config_path).unwrap();
        assert!(!config.translator.generate_proofs);
    }

    #[test]
    fn test_auto_skip_cli_flag() {
        let cli = Cli::parse_from([
            "verus-transpile",
            "--input",
            "test.rs",
            "--annotations",
            "test.automan",
            "--auto-skip",
        ]);
        assert!(cli.auto_skip, "auto_skip flag should be set");
    }

    #[test]
    fn test_auto_skip_default_off() {
        let cli = Cli::parse_from([
            "verus-transpile",
            "--input",
            "test.rs",
            "--annotations",
            "test.automan",
        ]);
        assert!(!cli.auto_skip, "auto_skip should default to false");
    }

    #[test]
    fn test_load_config_auto_skip_defaults_false() {
        let dir = tempfile::tempdir().unwrap();
        let config_path = dir.path().join("test.toml");
        std::fs::write(
            &config_path,
            r#"
[naming]
spec_prefix = "L"
exec_prefix = "C"

[output]
generate_proofs = false
validity_predicate_name = "valid"
"#,
        )
        .unwrap();

        let config = load_config(&config_path).unwrap();
        assert!(
            !config.auto_skip,
            "auto_skip should default to false from TOML"
        );
    }

    #[test]
    fn test_dump_config_cli_flag() {
        let cli = Cli::parse_from([
            "verus-transpile",
            "--input",
            "test.rs",
            "--annotations",
            "test.automan",
            "--dump-config",
        ]);
        assert!(cli.dump_config, "dump_config flag should be set");
    }

    #[test]
    fn test_dump_config_default_off() {
        let cli = Cli::parse_from([
            "verus-transpile",
            "--input",
            "test.rs",
            "--annotations",
            "test.automan",
        ]);
        assert!(!cli.dump_config, "dump_config should default to false");
    }

    #[test]
    fn test_convert_file_config_uses_naming_prefixes() {
        let file_config = FileConfig {
            naming: verus_transpiler::config::NamingConfig {
                spec_prefix: "Spec".to_string(),
                exec_prefix: "Exec".to_string(),
                ..Default::default()
            },
            ..Default::default()
        };
        let config = convert_file_config(file_config, Path::new(".")).unwrap();
        assert_eq!(config.translator.spec_prefix, "Spec");
        assert_eq!(config.translator.exec_prefix, "Exec");
    }

    #[test]
    fn test_convert_file_config_default_prefixes() {
        let file_config = FileConfig::default();
        let config = convert_file_config(file_config, Path::new(".")).unwrap();
        assert_eq!(config.translator.spec_prefix, "L");
        assert_eq!(config.translator.exec_prefix, "C");
    }

    /// Strip Tier 1 auto-derivable fields from a FileConfig, keeping only
    /// fields that require manual specification (Tier 3 overrides).
    fn strip_auto_derivable(config: &FileConfig) -> FileConfig {
        let mut minimal = config.clone();
        // Clear Tier 1 auto-derivable fields
        minimal.remapping.clear();
        minimal.variant_remapping.clear();
        minimal.collection_fields.clear();
        minimal.vec_fields.clear();
        minimal.clone_fields.clear();
        minimal.clone_field_types.clear();
        minimal.clone_strategy.clear();
        minimal.arrow_variants.clear();
        minimal.struct_vec_fields.clear();
        minimal.hashmap_index_fields.clear();
        minimal
    }

    /// Helper: run the transpiler on a spec file with a given FileConfig,
    /// including auto-inference from sibling types.rs.
    fn transpile_with_auto_inference(
        input: &Path,
        annotations: &Path,
        file_config: FileConfig,
        config_path: &Path,
    ) -> String {
        let mut fc = file_config;

        // Auto-infer from spec + sibling types.rs (mirrors main() flow)
        let mut spec_paths: Vec<&Path> = Vec::new();
        let types_path = input.parent().map(|dir| dir.join("types.rs"));
        let tp_ref; // to extend lifetime
        if let Some(ref tp) = types_path {
            if tp.exists() && tp != input {
                tp_ref = tp.clone();
                spec_paths.push(&tp_ref);
            }
        }
        spec_paths.push(input);

        let analysis_result = if spec_paths.len() > 1 {
            analyze_spec_files(&spec_paths)
        } else {
            analyze_spec_file(input)
        };

        if let Ok(schema) = analysis_result {
            let annotation_modules = parse_annotation_file(annotations).ok();
            let function_path_hints =
                infer_function_paths_from_spec_paths(&spec_paths, &schema, &fc.naming);
            let method_call_hints =
                infer_method_calls_from_spec_paths(&spec_paths, &schema, &fc.naming);
            let eq_function_field_hints =
                infer_eq_function_fields_from_spec_paths(&spec_paths, &schema, &fc.naming);
            let type_view_expr_hints =
                infer_type_view_exprs_from_spec_paths(&spec_paths, &schema, &fc.naming);
            let inferer = if let Some(modules) = annotation_modules.as_ref() {
                ConfigInferer::with_annotations(&schema, &fc.naming, modules)
            } else {
                ConfigInferer::new(&schema, &fc.naming)
            }
            .with_function_path_hints(function_path_hints)
            .with_method_call_hints(method_call_hints)
            .with_eq_function_field_hints(eq_function_field_hints)
            .with_type_view_expr_hints(type_view_expr_hints);
            let inferred = inferer.infer();
            merge_configs(&mut fc, &inferred);
        }

        let config = convert_file_config(fc, config_path).unwrap();
        let transpiler = Transpiler::new(config);
        transpiler
            .transpile_file(input, annotations)
            .unwrap_or_else(|e| panic!("transpilation failed: {}", e))
    }

    #[test]
    fn test_infer_function_paths_from_generated_symbols_prefers_generated_module() {
        let dir = tempfile::tempdir().unwrap();
        let spec_path = dir.path().join("src/protocol/RSL/acceptor.rs");
        let generated_path = dir.path().join("src/generated/RSL/broadcast_gen.rs");

        std::fs::create_dir_all(spec_path.parent().unwrap()).unwrap();
        std::fs::create_dir_all(generated_path.parent().unwrap()).unwrap();

        std::fs::write(
            &spec_path,
            r#"
verus! {
    pub open spec fn LAcceptorStep() -> bool {
        LBroadcastToEveryone()
    }
}
"#,
        )
        .unwrap();

        std::fs::write(
            &generated_path,
            r#"
verus! {
    pub exec fn CBroadcastToEveryone() -> bool {
        true
    }
}
"#,
        )
        .unwrap();

        let schema = analyze_spec_file(&spec_path).unwrap();
        let naming = verus_transpiler::NamingConfig::default();
        let inferred = infer_function_paths_from_generated_symbols(&spec_path, &schema, &naming);

        assert_eq!(
            inferred.get("BroadcastToEveryone"),
            Some(&"crate::generated::RSL::broadcast_gen::CBroadcastToEveryone".to_string())
        );
    }

    #[test]
    fn test_infer_function_paths_from_generated_symbols_falls_back_to_impl_symbol() {
        let dir = tempfile::tempdir().unwrap();
        let spec_path = dir.path().join("src/protocol/RSL/proposer.rs");
        let implementation_path = dir.path().join("src/implementation/RSL/ProposerImpl.rs");

        std::fs::create_dir_all(spec_path.parent().unwrap()).unwrap();
        std::fs::create_dir_all(implementation_path.parent().unwrap()).unwrap();

        std::fs::write(
            &spec_path,
            r#"
verus! {
    pub open spec fn LProposerStep() -> bool {
        LSetOfMessage1bAboutBallot()
    }
}
"#,
        )
        .unwrap();

        std::fs::write(
            &implementation_path,
            r#"
verus! {
    impl CProposer {
        pub exec fn CSetOfMessage1bAboutBallot() -> bool {
            true
        }
    }
}
"#,
        )
        .unwrap();

        let schema = analyze_spec_file(&spec_path).unwrap();
        let naming = verus_transpiler::NamingConfig::default();
        let inferred = infer_function_paths_from_generated_symbols(&spec_path, &schema, &naming);

        assert_eq!(
            inferred.get("SetOfMessage1bAboutBallot"),
            Some(&"CProposer::CSetOfMessage1bAboutBallot".to_string())
        );
    }

    #[test]
    fn test_infer_method_calls_from_spec_paths_infers_receiver_and_destructure() {
        let dir = tempfile::tempdir().unwrap();
        let spec_path = dir.path().join("src/protocol/RSL/election.rs");
        let implementation_path = dir.path().join("src/implementation/RSL/cconfiguration.rs");

        std::fs::create_dir_all(spec_path.parent().unwrap()).unwrap();
        std::fs::create_dir_all(implementation_path.parent().unwrap()).unwrap();

        std::fs::write(
            &spec_path,
            r#"
verus! {
    pub struct LConfiguration {}

    pub open spec fn LMinQuorumSize(config: LConfiguration) -> nat {
        0
    }

    pub open spec fn GetReplicaIndex(id: int, config: LConfiguration) -> int {
        0
    }

    pub open spec fn LEntry(config: LConfiguration, id: int) -> bool {
        LMinQuorumSize(config) >= 0 && GetReplicaIndex(id, config) >= 0
    }
}
"#,
        )
        .unwrap();

        std::fs::write(
            &implementation_path,
            r#"
verus! {
    impl CConfiguration {
        pub fn CMinQuorumSize(&self) -> (q:usize) {
            0
        }

        pub fn CGetReplicaIndex(&self, id:&u64) -> (rc:(bool, usize)) {
            (true, 0)
        }
    }
}
"#,
        )
        .unwrap();

        let schema = analyze_spec_file(&spec_path).unwrap();
        let naming = verus_transpiler::NamingConfig::default();
        let spec_paths = vec![spec_path.as_path()];
        let inferred = infer_method_calls_from_spec_paths(&spec_paths, &schema, &naming);

        let min_quorum = inferred
            .get("LMinQuorumSize")
            .expect("LMinQuorumSize should be inferred as method call");
        assert_eq!(min_quorum.method_name, "CMinQuorumSize");
        assert_eq!(min_quorum.receiver_arg_index, 0);
        assert_eq!(min_quorum.destructure_index, None);

        let get_replica = inferred
            .get("GetReplicaIndex")
            .expect("GetReplicaIndex should be inferred as method call");
        assert_eq!(get_replica.method_name, "CGetReplicaIndex");
        assert_eq!(get_replica.receiver_arg_index, 1);
        assert_eq!(get_replica.destructure_index, Some(1));
    }

    #[test]
    fn test_infer_method_calls_from_spec_paths_skips_ambiguous_receivers() {
        let dir = tempfile::tempdir().unwrap();
        let spec_path = dir.path().join("src/protocol/RSL/replica.rs");
        let implementation_path = dir.path().join("src/implementation/RSL/cconfiguration.rs");

        std::fs::create_dir_all(spec_path.parent().unwrap()).unwrap();
        std::fs::create_dir_all(implementation_path.parent().unwrap()).unwrap();

        std::fs::write(
            &spec_path,
            r#"
verus! {
    pub struct LConfiguration {}

    pub open spec fn LAmbiguous(a: LConfiguration, b: LConfiguration) -> bool {
        true
    }

    pub open spec fn LEntry(a: LConfiguration, b: LConfiguration) -> bool {
        LAmbiguous(a, b)
    }
}
"#,
        )
        .unwrap();

        std::fs::write(
            &implementation_path,
            r#"
verus! {
    impl CConfiguration {
        pub fn CAmbiguous(&self, other:&CConfiguration) -> (res:bool) {
            true
        }
    }
}
"#,
        )
        .unwrap();

        let schema = analyze_spec_file(&spec_path).unwrap();
        let naming = verus_transpiler::NamingConfig::default();
        let spec_paths = vec![spec_path.as_path()];
        let inferred = infer_method_calls_from_spec_paths(&spec_paths, &schema, &naming);

        assert!(
            !inferred.contains_key("LAmbiguous"),
            "ambiguous receiver candidates should not be auto-inferred"
        );
    }

    #[test]
    fn test_infer_eq_function_fields_from_spec_paths_maps_struct_and_variant_fields() {
        let dir = tempfile::tempdir().unwrap();
        let spec_path = dir.path().join("src/protocol/RSL/election.rs");
        let implementation_path = dir.path().join("src/implementation/RSL/types_i.rs");

        std::fs::create_dir_all(spec_path.parent().unwrap()).unwrap();
        std::fs::create_dir_all(implementation_path.parent().unwrap()).unwrap();

        std::fs::write(
            &spec_path,
            r#"
verus! {
    pub struct Ballot {
        pub seqno: int,
    }

    pub struct LElectionState {
        pub current_view: Ballot,
    }

    pub enum RslMessage {
        RslMessage1b { bal_1b: Ballot },
    }
}
"#,
        )
        .unwrap();

        std::fs::write(
            &implementation_path,
            r#"
verus! {
    pub fn CBalEq(ba:&CBallot, bb:&CBallot) -> (r:bool) {
        true
    }
}
"#,
        )
        .unwrap();

        let schema = analyze_spec_file(&spec_path).unwrap();
        let naming = verus_transpiler::NamingConfig::default();
        let spec_paths = vec![spec_path.as_path()];
        let inferred = infer_eq_function_fields_from_spec_paths(&spec_paths, &schema, &naming);

        assert_eq!(inferred.get("current_view"), Some(&"CBalEq".to_string()));
        assert_eq!(inferred.get("bal_1b"), Some(&"CBalEq".to_string()));
    }

    #[test]
    fn test_infer_eq_function_fields_from_spec_paths_skips_ambiguous_helpers() {
        let dir = tempfile::tempdir().unwrap();
        let spec_path = dir.path().join("src/protocol/RSL/election.rs");
        let implementation_path = dir.path().join("src/implementation/RSL/types_i.rs");

        std::fs::create_dir_all(spec_path.parent().unwrap()).unwrap();
        std::fs::create_dir_all(implementation_path.parent().unwrap()).unwrap();

        std::fs::write(
            &spec_path,
            r#"
verus! {
    pub struct Ballot {
        pub seqno: int,
    }

    pub struct LElectionState {
        pub current_view: Ballot,
    }
}
"#,
        )
        .unwrap();

        std::fs::write(
            &implementation_path,
            r#"
verus! {
    pub fn CBalEq(ba:&CBallot, bb:&CBallot) -> (r:bool) {
        true
    }

    pub fn CBallotEq(a:&CBallot, b:&CBallot) -> (r:bool) {
        true
    }
}
"#,
        )
        .unwrap();

        let schema = analyze_spec_file(&spec_path).unwrap();
        let naming = verus_transpiler::NamingConfig::default();
        let spec_paths = vec![spec_path.as_path()];
        let inferred = infer_eq_function_fields_from_spec_paths(&spec_paths, &schema, &naming);

        assert!(
            !inferred.contains_key("current_view"),
            "ambiguous helper matches for the same type should be skipped"
        );
    }

    #[test]
    fn test_infer_type_view_exprs_from_spec_paths_maps_helpers() {
        let dir = tempfile::tempdir().unwrap();
        let spec_path = dir.path().join("src/protocol/RSL/types.rs");
        let implementation_path = dir.path().join("src/implementation/RSL/types_i.rs");

        std::fs::create_dir_all(spec_path.parent().unwrap()).unwrap();
        std::fs::create_dir_all(implementation_path.parent().unwrap()).unwrap();

        std::fs::write(
            &spec_path,
            r#"
verus! {
    pub type RequestBatch = Seq<int>;
    pub type ReplyCache = Map<int, int>;
    pub type Votes = Set<int>;
}
"#,
        )
        .unwrap();

        std::fs::write(
            &implementation_path,
            r#"
verus! {
    pub fn abstractify_crequestbatch(s:&CRequestBatch) -> RequestBatch {
        RequestBatch::empty()
    }

    pub fn abstractify_creplycache(m:&CReplyCache) -> ReplyCache {
        ReplyCache::empty()
    }

    pub fn abstractify_cvotes(v:&CVotes) -> Votes {
        Votes::empty()
    }
}
"#,
        )
        .unwrap();

        let schema = analyze_spec_file(&spec_path).unwrap();
        let naming = verus_transpiler::NamingConfig::default();
        let spec_paths = vec![spec_path.as_path()];
        let inferred = infer_type_view_exprs_from_spec_paths(&spec_paths, &schema, &naming);

        assert_eq!(
            inferred.get("RequestBatch"),
            Some(&"abstractify_crequestbatch({param})".to_string())
        );
        assert_eq!(
            inferred.get("ReplyCache"),
            Some(&"abstractify_creplycache({param})".to_string())
        );
        assert_eq!(
            inferred.get("Votes"),
            Some(&"abstractify_cvotes({param})".to_string())
        );
    }

    #[test]
    fn test_infer_type_view_exprs_from_spec_paths_skips_ambiguous_or_mismatched_helpers() {
        let dir = tempfile::tempdir().unwrap();
        let spec_path = dir.path().join("src/protocol/RSL/types.rs");
        let implementation_path = dir.path().join("src/implementation/RSL/types_i.rs");

        std::fs::create_dir_all(spec_path.parent().unwrap()).unwrap();
        std::fs::create_dir_all(implementation_path.parent().unwrap()).unwrap();

        std::fs::write(
            &spec_path,
            r#"
verus! {
    pub type Votes = Set<int>;
    pub type Foo = Set<int>;
}
"#,
        )
        .unwrap();

        std::fs::write(
            &implementation_path,
            r#"
verus! {
    pub fn abstractify_cvotes(v:CVotes) -> Votes {
        Votes::empty()
    }

    pub fn abstractify_cfoo_wrong(v:&CBar) -> Foo {
        Foo::empty()
    }

    pub fn abstractify_cfoo_a(v:&CFoo) -> Foo {
        Foo::empty()
    }

    pub fn abstractify_cfoo_b(v:&CFoo) -> Foo {
        Foo::empty()
    }
}
"#,
        )
        .unwrap();

        let schema = analyze_spec_file(&spec_path).unwrap();
        let naming = verus_transpiler::NamingConfig::default();
        let spec_paths = vec![spec_path.as_path()];
        let inferred = infer_type_view_exprs_from_spec_paths(&spec_paths, &schema, &naming);

        assert!(
            !inferred.contains_key("Votes"),
            "by-value helpers should not be auto-inferred as view expressions"
        );
        assert!(
            !inferred.contains_key("Foo"),
            "ambiguous or mismatched helper matches should be skipped"
        );
    }

    #[test]
    fn test_minimal_toml_produces_identical_output() {
        let protocols: Vec<(&str, &str, &str)> = vec![
            ("TwoPhase", "twophase", "twophase_transpile"),
            ("Paxos", "paxos", "paxos_transpile"),
            ("LeaderElection", "election", "election_transpile"),
            ("Raft", "raft", "raft_transpile"),
            ("ChainReplication", "chain", "chain_transpile"),
            ("PrimaryBackup", "primarybackup", "primarybackup_transpile"),
            ("PBFT", "pbft", "pbft_transpile"),
            ("VerticalPaxos", "vpaxos", "vpaxos_transpile"),
            ("EPaxos", "epaxos", "epaxos_transpile"),
        ];

        let mut passed = 0;
        let mut skipped = 0;
        let mut failed = Vec::new();

        for (name, spec_name, toml_name) in &protocols {
            let base = format!("../src/protocol/{}", name);
            let input = PathBuf::from(format!("{}/{}.rs", base, spec_name));
            let annot = PathBuf::from(format!("{}/{}.automan", base, spec_name));
            let toml_path = PathBuf::from(format!("{}/{}.toml", base, toml_name));

            if !input.exists() || !annot.exists() || !toml_path.exists() {
                continue;
            }

            // Load full TOML config
            let full_config = FileConfig::from_file(&toml_path)
                .unwrap_or_else(|e| panic!("{}: failed to load TOML: {}", name, e));

            // Generate with full TOML + auto-inference (skip if transpilation
            // fails due to unsupported patterns like complex existentials)
            let input_c = input.clone();
            let annot_c = annot.clone();
            let toml_c = toml_path.clone();
            let fc = full_config.clone();
            let full_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                transpile_with_auto_inference(&input_c, &annot_c, fc, &toml_c)
            }));
            let full_output = match full_result {
                Ok(output) => output,
                Err(_) => {
                    skipped += 1;
                    continue;
                }
            };

            // Create minimal TOML (strip Tier 1 fields)
            let minimal_config = strip_auto_derivable(&full_config);

            // Generate with minimal TOML + auto-inference
            let input_c = input.clone();
            let annot_c = annot.clone();
            let toml_c = toml_path.clone();
            let minimal_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                transpile_with_auto_inference(&input_c, &annot_c, minimal_config, &toml_c)
            }));
            let minimal_output = match minimal_result {
                Ok(output) => output,
                Err(_) => {
                    skipped += 1;
                    continue;
                }
            };

            if full_output == minimal_output {
                passed += 1;
            } else {
                // Find first difference for debugging
                let full_lines: Vec<&str> = full_output.lines().collect();
                let min_lines: Vec<&str> = minimal_output.lines().collect();
                let first_diff = full_lines
                    .iter()
                    .zip(min_lines.iter())
                    .enumerate()
                    .find(|(_, (a, b))| a != b)
                    .map(|(i, (a, b))| format!("line {}: full='{}' vs min='{}'", i + 1, a, b))
                    .unwrap_or_else(|| {
                        format!(
                            "length diff: full={} vs min={}",
                            full_lines.len(),
                            min_lines.len()
                        )
                    });
                failed.push(format!("{}: {}", name, first_diff));
            }
        }

        assert!(
            failed.is_empty(),
            "Minimal TOML should produce identical output for all protocols.\n\
             Passed: {}, Skipped: {}, Failed: {}\nFailures:\n{}",
            passed,
            skipped,
            failed.len(),
            failed.join("\n")
        );
        assert!(
            passed + skipped >= 9,
            "Should have tested at least 9 protocols, got {} passed + {} skipped",
            passed,
            skipped
        );
    }
}
