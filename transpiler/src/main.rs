//! CLI entry point for the Verus transpiler.
//!
//! Usage:
//! ```bash
//! # Single file mode
//! verus-transpile \
//!     --input src/protocol/RSL/acceptor.rs \
//!     --annotations src/protocol/RSL/acceptor.automan \
//!     --config transpile.toml \
//!     --output src/implementation/RSL/acceptor_gen.rs
//!
//! # Batch mode
//! verus-transpile --project . --output-dir src/generated/
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
        Commands::GenerateTypes { input, output } => {
            use verus_transpiler::config::NamingConfig;
            use verus_transpiler::types::TypeDef;
            use verus_transpiler::{TypeGenerator, TypeParser, TypeRegistry};

            if cli.verbose {
                eprintln!("Generating types from: {}", input.display());
            }

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

            // Generate exec types
            let config = NamingConfig::default();
            let generator = TypeGenerator::new(config);
            let mut all_code = String::new();
            all_code.push_str("// Auto-generated exec types\n");
            all_code.push_str("// DO NOT EDIT MANUALLY\n\n");
            all_code.push_str("use crate::runtime::{View, ExecType};\n\n");

            for struct_def in registry.structs.values() {
                let generated = generator.generate_struct(struct_def);
                all_code.push_str(&generated.code);
                all_code.push_str("\n\n");
                for warning in &generated.warnings {
                    eprintln!("Warning: {}", warning);
                }
            }

            for enum_def in registry.enums.values() {
                let generated = generator.generate_enum(enum_def);
                all_code.push_str(&generated.code);
                all_code.push_str("\n\n");
                for warning in &generated.warnings {
                    eprintln!("Warning: {}", warning);
                }
            }

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
            ..TranslatorConfig::default()
        },
        custom_imports: file_config.output.custom_imports,
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
}
