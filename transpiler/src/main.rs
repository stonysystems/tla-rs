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
use std::path::{Path, PathBuf};
use verus_transpiler::spec_analyzer::{analyze_spec_file, analyze_spec_files, ConfigInferer, merge_configs};
use verus_transpiler::{FileConfig, TranslatorConfig, Transpiler, TranspilerConfig};

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
                let inferer = ConfigInferer::new(&schema, &file_config.naming);
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
                if sf.reason.starts_with("transpilation error") || sf.reason.starts_with("annotation error") || sf.reason.starts_with("not functionalizable") {
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
            eprintln!(
                "Auto-skipped {} function(s):",
                skipped.len()
            );
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
                    analyze_spec_file(&spec_paths[0])
                };
                match analysis_result {
                    Ok(schema) => {
                        let inferer = ConfigInferer::new(&schema, &file_config.naming);
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
            let manual_code = config
                .as_ref()
                .and_then(|config_path| {
                    file_config
                        .output.manual_code.as_ref()
                        .map(|rel_path| (config_path, rel_path))
                })
                .and_then(|(config_path, rel_path)| {
                    let base_dir = config_path.parent().unwrap_or(Path::new("."));
                    std::fs::read_to_string(base_dir.join(rel_path)).ok()
                });

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
                    manual_code: manual_code.as_deref(),
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

            // Load message variants from TOML config if provided
            let message_variants: Vec<String> = if let Some(cfg_path) = config_path {
                let file_config = FileConfig::from_file(cfg_path)
                    .map_err(|e| miette::miette!("Failed to load config: {}", e))?;
                file_config
                    .messages
                    .map(|m| m.variants.iter().map(|v| v.name.clone()).collect())
                    .unwrap_or_default()
            } else {
                vec![]
            };

            // Classify actions as message_driven or timer_driven
            verus_transpiler::classify_actions(&mut sched_config, &message_variants);

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
            let gen_mod = gen_module.clone().unwrap_or_else(|| format!("{}_gen", module_name));

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
            hashmap_index_fields: file_config.hashmap_index_fields.iter().cloned().collect(),
            type_view_exprs: file_config.type_view_exprs.clone(),
            extra_requires: file_config.extra_requires.clone(),
            eq_function_fields: file_config.eq_function_fields.clone(),
            arrow_variants: file_config.arrow_variants.clone(),
            clone_method: file_config.output.clone_method.clone(),
            vec_element_ensures: file_config.vec_element_ensures.clone(),
            set_fields: std::collections::HashSet::new(),
            assume_postconditions: file_config.output.assume_postconditions,
            spec_prefix: file_config.naming.spec_prefix.clone(),
            exec_prefix: file_config.naming.exec_prefix.clone(),
            generate_abstraction_fns: false,
            generate_validity_predicates: false,
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
        printer: verus_transpiler::PrinterConfig {
            extra_fields: file_config.extra_fields,
            ..Default::default()
        },
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
    fn test_generate_types_injects_manual_code_from_config_file() {
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
        let manual_pos = generated
            .find("ManualTypesHelper")
            .expect("manual helper should be injected");
        let close_pos = generated
            .find("} // verus!")
            .expect("verus close marker missing");
        assert!(
            manual_pos < close_pos,
            "manual helper must be inside verus block"
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
        assert!(!config.auto_skip, "auto_skip should default to false from TOML");
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
            let inferer = ConfigInferer::new(&schema, &fc.naming);
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

            // Generate with full TOML + auto-inference
            let full_output = transpile_with_auto_inference(
                &input, &annot, full_config.clone(), &toml_path,
            );

            // Create minimal TOML (strip Tier 1 fields)
            let minimal_config = strip_auto_derivable(&full_config);

            // Generate with minimal TOML + auto-inference
            let minimal_output = transpile_with_auto_inference(
                &input, &annot, minimal_config, &toml_path,
            );

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
             Passed: {}, Failed: {}\nFailures:\n{}",
            passed,
            failed.len(),
            failed.join("\n")
        );
        assert!(
            passed >= 9,
            "Should have tested at least 9 protocols, got {}",
            passed
        );
    }
}
