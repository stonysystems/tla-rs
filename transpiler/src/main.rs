//! CLI entry point for the Verus transpiler.
//!
//! Usage:
//! ```bash
//! verus-transpile \
//!     --input src/protocol/RSL/acceptor.rs \
//!     --annotations src/protocol/RSL/acceptor.automan \
//!     --config transpile.toml \
//!     --output src/implementation/RSL/acceptor_gen.rs
//! ```

use clap::Parser;
use miette::Result;
use std::path::PathBuf;
use verus_transpiler::{Transpiler, TranspilerConfig};

/// Verus Spec-to-Implementation Transpiler
///
/// Transforms Verus spec functions into verified exec implementations
/// with proof linkage to the original specifications.
#[derive(Parser, Debug)]
#[command(name = "verus-transpile")]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Input Verus spec file (.rs)
    #[arg(short, long)]
    input: PathBuf,

    /// Annotation file (.automan) with mode specifications
    #[arg(short, long)]
    annotations: PathBuf,

    /// Output file for generated exec code
    #[arg(short, long)]
    output: Option<PathBuf>,

    /// Configuration file (TOML)
    #[arg(short, long)]
    config: Option<PathBuf>,

    /// Print output to stdout instead of file
    #[arg(long)]
    stdout: bool,

    /// Verbose output
    #[arg(short, long)]
    verbose: bool,
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    if cli.verbose {
        eprintln!("Input: {}", cli.input.display());
        eprintln!("Annotations: {}", cli.annotations.display());
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
        .transpile_file(&cli.input, &cli.annotations)
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

/// Load configuration from a TOML file
fn load_config(path: &PathBuf) -> Result<TranspilerConfig> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| miette::miette!("Failed to read config file: {}", e))?;

    // For now, just return default config
    // TODO: Parse TOML configuration
    let _ = content;
    Ok(TranspilerConfig::default())
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
        assert_eq!(cli.input, PathBuf::from("test.rs"));
    }
}
