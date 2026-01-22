//! Build integration support for the transpiler.
//!
//! This module provides functions that can be called from build.rs or scons
//! to automatically transpile spec files when they change.

use crate::error::TranspileResult;
use crate::{Transpiler, TranspilerConfig};
use std::path::{Path, PathBuf};

/// Configuration for build-time transpilation
#[derive(Debug, Clone)]
pub struct BuildConfig {
    /// Input directory containing spec files
    pub input_dir: PathBuf,
    /// Output directory for generated files
    pub output_dir: PathBuf,
    /// Transpiler configuration
    pub transpiler_config: TranspilerConfig,
    /// Whether to fail the build on transpilation errors
    pub fail_on_error: bool,
    /// File extension for spec files (default: "rs")
    pub spec_extension: String,
    /// File extension for annotation files (default: "automan")
    pub annotation_extension: String,
}

impl Default for BuildConfig {
    fn default() -> Self {
        Self {
            input_dir: PathBuf::from("src/protocol"),
            output_dir: PathBuf::from("src/generated"),
            transpiler_config: TranspilerConfig::default(),
            fail_on_error: true,
            spec_extension: "rs".to_string(),
            annotation_extension: "automan".to_string(),
        }
    }
}

impl BuildConfig {
    /// Create a new build configuration
    pub fn new(input_dir: impl Into<PathBuf>, output_dir: impl Into<PathBuf>) -> Self {
        Self {
            input_dir: input_dir.into(),
            output_dir: output_dir.into(),
            ..Default::default()
        }
    }

    /// Set the transpiler configuration
    pub fn with_transpiler_config(mut self, config: TranspilerConfig) -> Self {
        self.transpiler_config = config;
        self
    }

    /// Set whether to fail on errors
    pub fn fail_on_error(mut self, fail: bool) -> Self {
        self.fail_on_error = fail;
        self
    }
}

/// Result of build-time transpilation
#[derive(Debug)]
pub struct BuildResult {
    /// Number of files successfully transpiled
    pub success_count: usize,
    /// Number of files that failed
    pub error_count: usize,
    /// List of generated file paths
    pub generated_files: Vec<PathBuf>,
    /// List of errors encountered
    pub errors: Vec<(PathBuf, String)>,
}

/// Run transpilation as part of the build process.
///
/// This function is designed to be called from a build.rs file:
///
/// ```ignore
/// // build.rs
/// fn main() {
///     let config = verus_transpiler::build_integration::BuildConfig::new(
///         "src/protocol",
///         "src/generated"
///     );
///
///     let result = verus_transpiler::build_integration::run_build(&config)
///         .expect("Transpilation failed");
///
///     println!("cargo:rerun-if-changed=src/protocol");
///     for file in result.generated_files {
///         println!("Generated: {}", file.display());
///     }
/// }
/// ```
pub fn run_build(config: &BuildConfig) -> TranspileResult<BuildResult> {
    let transpiler = Transpiler::new(config.transpiler_config.clone());

    let mut result = BuildResult {
        success_count: 0,
        error_count: 0,
        generated_files: Vec::new(),
        errors: Vec::new(),
    };

    // Find all annotation files
    let annotation_files = find_files(&config.input_dir, &config.annotation_extension)?;

    for annotation_path in annotation_files {
        // Find corresponding spec file
        let spec_path = annotation_path.with_extension(&config.spec_extension);

        if !spec_path.exists() {
            continue;
        }

        // Calculate output path
        let relative = annotation_path
            .strip_prefix(&config.input_dir)
            .unwrap_or(&annotation_path);
        let output_path = config.output_dir.join(relative).with_extension("gen.rs");

        // Create output directory if needed
        if let Some(parent) = output_path.parent() {
            std::fs::create_dir_all(parent)?;
        }

        // Transpile
        match transpiler.transpile_file(&spec_path, &annotation_path) {
            Ok(generated) => {
                std::fs::write(&output_path, &generated)?;
                result.success_count += 1;
                result.generated_files.push(output_path);
            }
            Err(e) => {
                result.error_count += 1;
                result.errors.push((spec_path.clone(), e.to_string()));

                if config.fail_on_error {
                    return Err(e);
                }
            }
        }
    }

    Ok(result)
}

/// Print cargo instructions for rerun-if-changed
pub fn print_rerun_instructions(input_dir: &Path) {
    println!("cargo:rerun-if-changed={}", input_dir.display());
}

/// Find all files with a given extension in a directory tree
fn find_files(dir: &Path, extension: &str) -> TranspileResult<Vec<PathBuf>> {
    let mut files = Vec::new();
    find_files_recursive(dir, extension, &mut files)?;
    Ok(files)
}

fn find_files_recursive(
    dir: &Path,
    extension: &str,
    files: &mut Vec<PathBuf>,
) -> TranspileResult<()> {
    if !dir.is_dir() {
        return Ok(());
    }

    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();

        if path.is_dir() {
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
            // Skip hidden directories and common non-source directories
            if !name.starts_with('.') && name != "target" && name != "node_modules" {
                find_files_recursive(&path, extension, files)?;
            }
        } else if path.extension().and_then(|e| e.to_str()) == Some(extension) {
            files.push(path);
        }
    }

    Ok(())
}

/// Generate a build.rs template for a project
pub fn generate_build_rs_template() -> String {
    r#"//! Build script for transpiling Verus spec files
//!
//! This build script automatically transpiles spec files when they change.

fn main() {
    // Configure transpilation
    let config = verus_transpiler::build_integration::BuildConfig::new(
        "src/protocol",  // Input directory with spec files
        "src/generated", // Output directory for generated code
    );

    // Run transpilation
    match verus_transpiler::build_integration::run_build(&config) {
        Ok(result) => {
            println!("Transpiled {} files successfully", result.success_count);

            // Tell cargo when to re-run this script
            verus_transpiler::build_integration::print_rerun_instructions(&config.input_dir);

            // Also watch individual generated files
            for file in &result.generated_files {
                println!("cargo:rerun-if-changed={}", file.display());
            }
        }
        Err(e) => {
            eprintln!("Transpilation failed: {}", e);
            std::process::exit(1);
        }
    }
}
"#
    .to_string()
}

/// Generate an scons helper script
pub fn generate_scons_helper() -> String {
    r#"# SCons helper for verus-transpiler
# Add this to your SConstruct file

import subprocess
import os

def transpile_action(target, source, env):
    """Run the verus-transpiler on spec files."""
    input_dir = str(source[0])
    output_dir = str(target[0])

    cmd = [
        'cargo', 'run', '--package', 'verus-transpiler', '--',
        '--project', input_dir,
        '--output-dir', output_dir,
    ]

    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        print(f"Transpilation failed:\n{result.stderr}")
        return 1
    print(result.stdout)
    return 0

def transpile_emitter(target, source, env):
    """Emit dependencies for the transpiler."""
    import glob

    input_dir = str(source[0])
    automan_files = glob.glob(os.path.join(input_dir, '**/*.automan'), recursive=True)
    rs_files = glob.glob(os.path.join(input_dir, '**/*.rs'), recursive=True)

    # Add all spec files as dependencies
    for f in automan_files + rs_files:
        env.Depends(target, f)

    return target, source

# Create the builder
transpile_builder = Builder(
    action=transpile_action,
    emitter=transpile_emitter,
)

# Usage in SConstruct:
# env = Environment()
# env.Append(BUILDERS={'Transpile': transpile_builder})
# env.Transpile('src/generated', 'src/protocol')
"#
    .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = BuildConfig::default();
        assert_eq!(config.input_dir, PathBuf::from("src/protocol"));
        assert_eq!(config.output_dir, PathBuf::from("src/generated"));
        assert!(config.fail_on_error);
    }

    #[test]
    fn test_config_builder() {
        let config = BuildConfig::new("input", "output").fail_on_error(false);

        assert_eq!(config.input_dir, PathBuf::from("input"));
        assert_eq!(config.output_dir, PathBuf::from("output"));
        assert!(!config.fail_on_error);
    }

    #[test]
    fn test_build_rs_template() {
        let template = generate_build_rs_template();
        assert!(template.contains("BuildConfig::new"));
        assert!(template.contains("run_build"));
        assert!(template.contains("cargo:rerun-if-changed"));
    }

    #[test]
    fn test_scons_helper() {
        let helper = generate_scons_helper();
        assert!(helper.contains("transpile_action"));
        assert!(helper.contains("Builder"));
    }
}
