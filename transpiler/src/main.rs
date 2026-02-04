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
        /// Input spec file
        #[arg(short, long)]
        input: PathBuf,

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

    // Load configuration if provided
    let config = if let Some(config_path) = &cli.config {
        load_config(config_path)?
    } else {
        TranspilerConfig::default()
    };

    // Create transpiler
    let transpiler = Transpiler::new(config);

    // Run transpilation
    let result = transpiler
        .transpile_file(input, annotations)
        .map_err(|e| miette::miette!("{}", e))?;

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
            use std::collections::HashMap;
            use verus_transpiler::config::NamingConfig;
            use verus_transpiler::types::TypeDef;
            use verus_transpiler::{TypeParser, TypeRegistry};

            if cli.verbose {
                eprintln!("Generating types from: {}", input.display());
            }

            // Load config for remappings and imports if provided
            let (remapping, custom_imports): (HashMap<String, String>, Vec<String>) =
                if let Some(config_path) = config {
                    if cli.verbose {
                        eprintln!("Loading config from: {}", config_path.display());
                    }
                    let file_config = FileConfig::from_file(config_path)
                        .map_err(|e| miette::miette!("Failed to load config: {}", e))?;
                    (
                        file_config.remapping.clone(),
                        file_config.output.custom_imports.clone(),
                    )
                } else {
                    (HashMap::new(), Vec::new())
                };

            let content = std::fs::read_to_string(input)
                .map_err(|e| miette::miette!("Failed to read input file: {}", e))?;

            let mut parser = TypeParser::new(&content);
            let mut registry = TypeRegistry::new();

            // Parse all type definitions from the source
            let type_defs = parser
                .parse_types()
                .map_err(|e| miette::miette!("Failed to parse types: {}", e))?;

            for type_def in type_defs {
                match type_def {
                    TypeDef::Struct(struct_def) => {
                        if cli.verbose {
                            eprintln!("  Found struct: {}", struct_def.name);
                        }
                        registry.structs.insert(struct_def.name.clone(), struct_def);
                    }
                    TypeDef::Enum(enum_def) => {
                        if cli.verbose {
                            eprintln!("  Found enum: {}", enum_def.name);
                        }
                        registry.enums.insert(enum_def.name.clone(), enum_def);
                    }
                    TypeDef::Alias(_) => {
                        // Type aliases are not directly generated
                    }
                }
            }

            if registry.structs.is_empty() && registry.enums.is_empty() {
                return Err(miette::miette!("No spec types found in input file"));
            }

            // Generate exec types using the registry function
            let naming_config = NamingConfig::default();
            let generated = verus_transpiler::codegen::generate_all_types_with_options(
                &registry,
                &naming_config,
                &remapping,
                &custom_imports,
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
                    "Generated {} structs, {} enums -> {}",
                    registry.structs.len(),
                    registry.enums.len(),
                    output_path.display()
                );
            } else {
                println!("{}", all_code);
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
                    module
                        .constants
                        .iter()
                        .map(|c| &c.name)
                        .collect::<Vec<_>>()
                );
                eprintln!(
                    "  Operators: {:?}",
                    module
                        .operators
                        .iter()
                        .map(|o| &o.name)
                        .collect::<Vec<_>>()
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
                let annotations = TypeAnnotations::parse(&types_content)
                    .map_err(|e| miette::miette!("Failed to parse type annotations: {}", e))?;

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

                env
            } else {
                // Use automatic type inference only
                let mut inference = TypeInference::new();
                inference.infer_types(&module)
            };

            // Translate module with type information
            let translator = ModuleTranslator::with_config(config).with_types(type_env);
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

                println!("Translated {} -> {}", input.display(), output_path.display());
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
                let annotations = TypeAnnotations::parse(&types_content)
                    .map_err(|e| miette::miette!("Failed to parse type annotations: {}", e))?;

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
            let tla_translator =
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
                        ..TranslatorConfig::default()
                    },
                    generate_inline_types: true,
                    ..TranspilerConfig::default()
                }
            };

            let transpiler = Transpiler::new(transpiler_config);
            let exec_code = transpiler
                .transpile_file(&spec_path, &automan_path)
                .map_err(|e| miette::miette!("Failed to transpile spec to exec: {}", e))?;

            // Write exec output
            std::fs::write(exec_output, &exec_code)
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
    }
}

/// Load configuration from a TOML file
fn load_config(path: &Path) -> Result<TranspilerConfig> {
    let file_config =
        FileConfig::from_file(path).map_err(|e| miette::miette!("Failed to load config: {}", e))?;

    // Convert FileConfig to internal TranspilerConfig
    Ok(TranspilerConfig {
        translator: TranslatorConfig {
            validity_predicate_name: file_config.output.validity_predicate_name,
            generate_loops_for_verification: file_config.output.generate_loops_for_verification,
            type_remapping: file_config.remapping.clone(),
            function_paths: file_config.function_paths.clone(),
            spec_only_functions: file_config.spec_only_functions.into_iter().collect(),
            method_calls: file_config.method_calls.clone(),
            primitive_types: file_config.primitive_types.into_iter().collect(),
            int_type: file_config.naming.int_type.clone(),
            nat_type: file_config.naming.nat_type.clone(),
            ..TranslatorConfig::default()
        },
        custom_imports: file_config.output.custom_imports,
        generate_inline_types: file_config.output.generate_inline_types,
        type_remapping: file_config.remapping,
        generate_wrapper_methods: file_config.output.generate_wrapper_methods,
        wrapper_impl_type: file_config.output.wrapper_impl_type,
        skip_functions: file_config.skip_functions,
        ..TranspilerConfig::default()
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
        let translator = ModuleTranslator::with_config(config).with_types(type_env);
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
        let translator = ModuleTranslator::with_config(config).with_types(type_env);
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
}
