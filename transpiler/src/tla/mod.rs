//! TLA+ parsing and translation module.
//!
//! This module provides functionality to parse TLA+ specifications and translate
//! them to Verus/TLA-rs code.

pub mod ast;
pub mod parser;
pub mod tokenizer;

pub use ast::{
    TlaBinOp, TlaConstantDecl, TlaExceptPath, TlaExceptUpdate, TlaExpr, TlaInstance, TlaModule,
    TlaNumber, TlaOperator, TlaParam, TlaQuantBound, TlaTheorem, TlaUnaryOp,
};
pub use parser::{parse_module, ParseResult, TlaParseError, TlaParser};
pub use tokenizer::{TlaToken, TlaTokenKind, TlaTokenizer, TlaTokenizerError};
