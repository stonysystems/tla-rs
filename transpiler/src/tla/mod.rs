//! TLA+ parsing and translation module.
//!
//! This module provides functionality to parse TLA+ specifications and translate
//! them to Verus/TLA-rs code.

pub mod ast;
pub mod mc_wrapper;
pub mod parser;
pub mod tokenizer;
pub mod translator;
pub mod types;

pub use ast::{
    TlaBinOp, TlaConstantDecl, TlaExceptPath, TlaExceptUpdate, TlaExpr, TlaInstance, TlaModule,
    TlaNumber, TlaOperator, TlaParam, TlaQuantBound, TlaTheorem, TlaUnaryOp,
};
pub use mc_wrapper::{
    generate_relational_mc_wrapper, McWrapperArtifacts, McWrapperOptions, PacketProjectionMode,
};
pub use parser::{parse_module, ParseResult, TlaParseError, TlaParser};
pub use tokenizer::{TlaToken, TlaTokenKind, TlaTokenizer, TlaTokenizerError};
pub use translator::{
    generate_mode_annotations, translate_expr, translate_expr_with_config, translate_module,
    translate_module_with_types, ExprTranslator, ModeAnnotationGenerator, ModuleConfig,
    ModuleTranslator, OperatorModes, ParameterMode, TranslatorConfig,
};
pub use types::{
    ConstraintCollector, DiagnosticSeverity, RecordType, StandardLibrary, TlaType, TypeAnnotations,
    TypeConstraint, TypeDiagnostic, TypeEnv, TypeInference, TypeSubstitution, TypeUnifier,
    UnifyResult,
};
