//! Spec Analyzer: extracts structured schema from protocol spec files.
//!
//! This module parses spec `.rs` files (types + protocol logic) and builds a
//! `SpecSchema` containing all struct/enum definitions, type aliases, and
//! function signatures. This is the foundation for Phase 20 auto-inference
//! of TOML configuration.
//!
//! # Usage
//!
//! ```ignore
//! use verus_transpiler::spec_analyzer::{analyze_spec_file, analyze_spec_files, SpecSchema};
//!
//! // Analyze a single file
//! let schema = analyze_spec_file("src/protocol/Paxos/paxos.rs")?;
//!
//! // Analyze types + protocol files together
//! let schema = analyze_spec_files(&[
//!     "src/protocol/Paxos/types.rs",
//!     "src/protocol/Paxos/paxos.rs",
//! ])?;
//!
//! assert!(schema.structs.contains_key("LState"));
//! assert!(schema.functions.contains_key("LInit"));
//! ```

use crate::error::TranspileResult;
use crate::types::{
    build_registry, parse_types_from_file, EnumDef, FieldDef, FunctionSig, StructDef, TypeAlias,
    TypeRegistry, VariantDef, VariantFields,
};
use std::collections::HashMap;
use std::path::Path;

/// A structured schema extracted from protocol spec files.
///
/// Contains all type definitions (structs, enums, aliases) and function
/// signatures found in the spec. This is the input for auto-deriving
/// TOML configuration in later phases.
#[derive(Debug, Default)]
pub struct SpecSchema {
    /// All struct definitions, keyed by name (e.g., "LState", "LConstants")
    pub structs: HashMap<String, StructDef>,
    /// All enum definitions, keyed by name (e.g., "LMessage")
    pub enums: HashMap<String, EnumDef>,
    /// All type aliases, keyed by name (e.g., "Votes", "RequestBatch")
    pub aliases: HashMap<String, TypeAlias>,
    /// All spec function signatures, keyed by name (e.g., "LInit", "LSend1a")
    pub functions: HashMap<String, FunctionSig>,
    /// Insertion order for structs (deterministic iteration)
    pub struct_order: Vec<String>,
    /// Insertion order for enums (deterministic iteration)
    pub enum_order: Vec<String>,
    /// Insertion order for aliases (deterministic iteration)
    pub alias_order: Vec<String>,
    /// Source files that were analyzed
    pub source_files: Vec<String>,
}

impl SpecSchema {
    /// Create a new empty schema
    pub fn new() -> Self {
        Self::default()
    }

    /// Build from a TypeRegistry
    pub fn from_registry(registry: TypeRegistry) -> Self {
        Self {
            structs: registry.structs,
            enums: registry.enums,
            aliases: registry.aliases,
            functions: registry.functions,
            struct_order: registry.struct_order,
            enum_order: registry.enum_order,
            alias_order: registry.alias_order,
            source_files: Vec::new(),
        }
    }

    /// Merge another schema into this one (for combining types.rs + protocol.rs)
    pub fn merge(&mut self, other: SpecSchema) {
        for name in &other.struct_order {
            if let Some(s) = other.structs.get(name) {
                if !self.structs.contains_key(name) {
                    self.struct_order.push(name.clone());
                }
                self.structs.insert(name.clone(), s.clone());
            }
        }
        for name in &other.enum_order {
            if let Some(e) = other.enums.get(name) {
                if !self.enums.contains_key(name) {
                    self.enum_order.push(name.clone());
                }
                self.enums.insert(name.clone(), e.clone());
            }
        }
        for name in &other.alias_order {
            if let Some(a) = other.aliases.get(name) {
                if !self.aliases.contains_key(name) {
                    self.alias_order.push(name.clone());
                }
                self.aliases.insert(name.clone(), a.clone());
            }
        }
        for (name, f) in other.functions {
            self.functions.insert(name, f);
        }
        self.source_files.extend(other.source_files);
    }

    /// Get all struct field names for a given struct
    pub fn get_struct_fields(&self, name: &str) -> Option<&[FieldDef]> {
        self.structs.get(name).map(|s| s.fields.as_slice())
    }

    /// Get all enum variant names for a given enum
    pub fn get_enum_variants(&self, name: &str) -> Option<&[VariantDef]> {
        self.enums.get(name).map(|e| e.variants.as_slice())
    }

    /// Find which enum variant contains a given field name.
    /// Returns (enum_name, variant_name) if found.
    pub fn find_variant_with_field(&self, field_name: &str) -> Option<(String, String)> {
        for (enum_name, enum_def) in &self.enums {
            for variant in &enum_def.variants {
                match &variant.fields {
                    VariantFields::Struct(fields) => {
                        if fields.iter().any(|f| f.name == field_name) {
                            return Some((enum_name.clone(), variant.name.clone()));
                        }
                    }
                    _ => {}
                }
            }
        }
        None
    }

    /// Get all function names
    pub fn function_names(&self) -> Vec<&str> {
        self.functions.keys().map(|s| s.as_str()).collect()
    }

    /// Get the number of each type of definition
    pub fn summary(&self) -> SchemaSummary {
        SchemaSummary {
            num_structs: self.structs.len(),
            num_enums: self.enums.len(),
            num_aliases: self.aliases.len(),
            num_functions: self.functions.len(),
        }
    }
}

/// Summary statistics for a SpecSchema
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchemaSummary {
    pub num_structs: usize,
    pub num_enums: usize,
    pub num_aliases: usize,
    pub num_functions: usize,
}

/// Analyze a single spec file and return a SpecSchema.
pub fn analyze_spec_file<P: AsRef<Path>>(path: P) -> TranspileResult<SpecSchema> {
    let path = path.as_ref();
    let type_defs = parse_types_from_file(path)?;
    let registry = build_registry(type_defs);
    let mut schema = SpecSchema::from_registry(registry);
    schema.source_files.push(path.display().to_string());
    Ok(schema)
}

/// Analyze multiple spec files and return a merged SpecSchema.
/// Typically used to combine types.rs + protocol.rs for a single protocol.
pub fn analyze_spec_files<P: AsRef<Path>>(paths: &[P]) -> TranspileResult<SpecSchema> {
    let mut schema = SpecSchema::new();
    for path in paths {
        let file_schema = analyze_spec_file(path)?;
        schema.merge(file_schema);
    }
    Ok(schema)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Generics, Path as AstPath, Type};
    use crate::types::{ParamSig, TypeParser};

    #[test]
    fn test_empty_schema() {
        let schema = SpecSchema::new();
        assert_eq!(schema.structs.len(), 0);
        assert_eq!(schema.enums.len(), 0);
        assert_eq!(schema.aliases.len(), 0);
        assert_eq!(schema.functions.len(), 0);
    }

    #[test]
    fn test_schema_from_registry() {
        let mut registry = TypeRegistry::new();
        registry.register_struct(StructDef {
            name: "LState".to_string(),
            generics: Generics::default(),
            fields: vec![],
            is_spec: true,
        });
        registry.register_function(FunctionSig {
            name: "LInit".to_string(),
            generics: Generics::default(),
            params: vec![],
            return_type: Type::Bool,
            is_spec: true,
        });

        let schema = SpecSchema::from_registry(registry);
        assert_eq!(schema.structs.len(), 1);
        assert!(schema.structs.contains_key("LState"));
        assert_eq!(schema.functions.len(), 1);
        assert!(schema.functions.contains_key("LInit"));
    }

    #[test]
    fn test_schema_merge() {
        let mut schema1 = SpecSchema::new();
        schema1.structs.insert(
            "LState".to_string(),
            StructDef {
                name: "LState".to_string(),
                generics: Generics::default(),
                fields: vec![],
                is_spec: true,
            },
        );
        schema1.struct_order.push("LState".to_string());

        let mut schema2 = SpecSchema::new();
        schema2.functions.insert(
            "LInit".to_string(),
            FunctionSig {
                name: "LInit".to_string(),
                generics: Generics::default(),
                params: vec![],
                return_type: Type::Bool,
                is_spec: true,
            },
        );
        schema2.structs.insert(
            "LConstants".to_string(),
            StructDef {
                name: "LConstants".to_string(),
                generics: Generics::default(),
                fields: vec![],
                is_spec: true,
            },
        );
        schema2.struct_order.push("LConstants".to_string());

        schema1.merge(schema2);
        assert_eq!(schema1.structs.len(), 2);
        assert_eq!(schema1.functions.len(), 1);
        assert_eq!(schema1.struct_order, vec!["LState", "LConstants"]);
    }

    #[test]
    fn test_find_variant_with_field() {
        let mut schema = SpecSchema::new();
        schema.enums.insert(
            "LMessage".to_string(),
            EnumDef {
                name: "LMessage".to_string(),
                generics: Generics::default(),
                variants: vec![
                    VariantDef {
                        name: "Msg1a".to_string(),
                        fields: VariantFields::Struct(vec![FieldDef {
                            name: "bal_1a".to_string(),
                            ty: Type::Named(AstPath::single("Ballot".to_string())),
                            is_public: true,
                        }]),
                    },
                    VariantDef {
                        name: "Msg2a".to_string(),
                        fields: VariantFields::Struct(vec![
                            FieldDef {
                                name: "bal_2a".to_string(),
                                ty: Type::Named(AstPath::single("Ballot".to_string())),
                                is_public: true,
                            },
                            FieldDef {
                                name: "val_2a".to_string(),
                                ty: Type::Named(AstPath::single("RequestBatch".to_string())),
                                is_public: true,
                            },
                        ]),
                    },
                ],
                is_spec: true,
            },
        );

        assert_eq!(
            schema.find_variant_with_field("bal_1a"),
            Some(("LMessage".to_string(), "Msg1a".to_string()))
        );
        assert_eq!(
            schema.find_variant_with_field("val_2a"),
            Some(("LMessage".to_string(), "Msg2a".to_string()))
        );
        assert_eq!(schema.find_variant_with_field("nonexistent"), None);
    }

    #[test]
    fn test_parse_spec_fn_from_source() {
        let source = r#"
verus! {
    pub struct LState {
        pub value: int,
    }

    pub open spec fn LInit(s: LState, c: LConstants) -> bool
    {
        s.value == 0
    }

    pub open spec fn LStep(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LMessage>) -> bool
    {
        &&& s_.value == s.value + 1
        &&& sent_packets == Seq::empty()
    }
}
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        // Should parse: 1 struct + 2 functions
        let structs: Vec<_> = types
            .iter()
            .filter(|t| matches!(t, crate::types::TypeDef::Struct(_)))
            .collect();
        let functions: Vec<_> = types
            .iter()
            .filter(|t| matches!(t, crate::types::TypeDef::Function(_)))
            .collect();

        assert_eq!(structs.len(), 1);
        assert_eq!(functions.len(), 2);

        // Check first function
        match &functions[0] {
            crate::types::TypeDef::Function(f) => {
                assert_eq!(f.name, "LInit");
                assert_eq!(f.params.len(), 2);
                assert_eq!(f.params[0].name, "s");
                assert_eq!(f.params[1].name, "c");
                assert!(matches!(f.return_type, Type::Bool));
                assert!(f.is_spec);
            }
            _ => unreachable!(),
        }

        // Check second function
        match &functions[1] {
            crate::types::TypeDef::Function(f) => {
                assert_eq!(f.name, "LStep");
                assert_eq!(f.params.len(), 4);
                assert_eq!(f.params[0].name, "s");
                assert_eq!(f.params[1].name, "s_");
                assert_eq!(f.params[2].name, "c");
                assert_eq!(f.params[3].name, "sent_packets");
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_parse_spec_fn_with_recommends() {
        let source = r#"
verus! {
    pub open spec fn helper(x: int, y: int) -> bool
        recommends x > 0
    {
        x + y > 0
    }
}
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        let functions: Vec<_> = types
            .iter()
            .filter(|t| matches!(t, crate::types::TypeDef::Function(_)))
            .collect();

        assert_eq!(functions.len(), 1);
        match &functions[0] {
            crate::types::TypeDef::Function(f) => {
                assert_eq!(f.name, "helper");
                assert_eq!(f.params.len(), 2);
                assert!(matches!(f.return_type, Type::Bool));
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_parse_spec_fn_no_return_type() {
        // Some spec functions don't have explicit -> bool
        let source = r#"
verus! {
    pub open spec fn u64_inc(x: u64) -> u64
    {
        if x < u64::MAX { (x + 1) as u64 } else { x }
    }
}
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        let functions: Vec<_> = types
            .iter()
            .filter(|t| matches!(t, crate::types::TypeDef::Function(_)))
            .collect();

        assert_eq!(functions.len(), 1);
        match &functions[0] {
            crate::types::TypeDef::Function(f) => {
                assert_eq!(f.name, "u64_inc");
                assert_eq!(f.params.len(), 1);
                // Return type should be u64 (Named type)
                match &f.return_type {
                    Type::Named(path) => assert_eq!(path.segments[0], "u64"),
                    _ => panic!("Expected Named type u64, got {:?}", f.return_type),
                }
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_parse_mixed_types_and_functions() {
        let source = r#"
verus! {
    pub struct LState {
        pub tm_state: LTMState,
        pub rm_states: Map<int, LRMState>,
    }

    pub enum LTMState {
        Init,
        Committed,
        Aborted,
    }

    pub type RequestBatch = Seq<Request>;

    pub open spec fn LInit(s: LState, c: LConstants) -> bool
    {
        &&& s.tm_state is Init
        &&& forall |rm: int| 0 <= rm < c.num_rms ==> s.rm_states[rm] is Working
    }

    pub open spec fn LTMSendPrepare(s: LState, s_: LState, c: LConstants, sent_packets: Seq<LTPCMessage>) -> bool
    {
        &&& s.tm_state is Init
        &&& s_ == s
        &&& sent_packets.len() == c.num_rms
    }
}
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        let registry = build_registry(types);
        let schema = SpecSchema::from_registry(registry);

        assert_eq!(schema.structs.len(), 1);
        assert!(schema.structs.contains_key("LState"));
        assert_eq!(schema.enums.len(), 1);
        assert!(schema.enums.contains_key("LTMState"));
        assert_eq!(schema.aliases.len(), 1);
        assert!(schema.aliases.contains_key("RequestBatch"));
        assert_eq!(schema.functions.len(), 2);
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.contains_key("LTMSendPrepare"));

        let summary = schema.summary();
        assert_eq!(
            summary,
            SchemaSummary {
                num_structs: 1,
                num_enums: 1,
                num_aliases: 1,
                num_functions: 2,
            }
        );
    }

    // --- Real protocol spec file tests ---

    #[test]
    fn test_analyze_twophase_types() {
        let path = std::path::Path::new("../src/protocol/TwoPhase/types.rs");
        if !path.exists() {
            return; // Skip if not in workspace
        }
        let schema = analyze_spec_file(path).unwrap();
        // TwoPhase types.rs should have structs and enums
        assert!(
            schema.structs.len() + schema.enums.len() > 0,
            "TwoPhase types.rs should have type definitions"
        );
    }

    #[test]
    fn test_analyze_twophase_protocol() {
        let types_path = std::path::Path::new("../src/protocol/TwoPhase/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/TwoPhase/twophase.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();

        // Must have LState, LConstants
        assert!(
            schema.structs.contains_key("LState"),
            "TwoPhase should have LState struct"
        );
        assert!(
            schema.structs.contains_key("LConstants"),
            "TwoPhase should have LConstants struct"
        );

        // Must have LInit function
        assert!(
            schema.functions.contains_key("LInit"),
            "TwoPhase should have LInit function"
        );

        // Should have multiple transition functions
        assert!(
            schema.functions.len() >= 3,
            "TwoPhase should have at least 3 functions, got {}",
            schema.functions.len()
        );

        let summary = schema.summary();
        assert!(summary.num_structs >= 2);
        assert!(summary.num_functions >= 3);
    }

    #[test]
    fn test_analyze_paxos_protocol() {
        let types_path = std::path::Path::new("../src/protocol/Paxos/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/Paxos/paxos.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 3);
    }

    #[test]
    fn test_analyze_leaderelection_protocol() {
        let types_path = std::path::Path::new("../src/protocol/LeaderElection/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/LeaderElection/election.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 3);
    }

    #[test]
    fn test_analyze_raft_protocol() {
        let types_path = std::path::Path::new("../src/protocol/Raft/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/Raft/raft.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 5);
    }

    #[test]
    fn test_analyze_chainreplication_protocol() {
        let types_path = std::path::Path::new("../src/protocol/ChainReplication/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/ChainReplication/chain.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 3);
    }

    #[test]
    fn test_analyze_primarybackup_protocol() {
        let types_path = std::path::Path::new("../src/protocol/PrimaryBackup/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/PrimaryBackup/primarybackup.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 3);
    }

    #[test]
    fn test_analyze_pbft_protocol() {
        let types_path = std::path::Path::new("../src/protocol/PBFT/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/PBFT/pbft.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 3);
    }

    #[test]
    fn test_analyze_verticalpaxos_protocol() {
        let types_path = std::path::Path::new("../src/protocol/VerticalPaxos/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/VerticalPaxos/vpaxos.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 3);
    }

    #[test]
    fn test_analyze_epaxos_protocol() {
        let types_path = std::path::Path::new("../src/protocol/EPaxos/types.rs");
        let proto_path = std::path::Path::new("../src/protocol/EPaxos/epaxos.rs");
        if !types_path.exists() || !proto_path.exists() {
            return;
        }
        let schema = analyze_spec_files(&[types_path, proto_path]).unwrap();
        assert!(schema.structs.contains_key("LState"));
        assert!(schema.structs.contains_key("LConstants"));
        assert!(schema.functions.contains_key("LInit"));
        assert!(schema.functions.len() >= 3);
    }

    #[test]
    fn test_analyze_all_protocols_summary() {
        // Test that all 10 protocols can be analyzed and print summary
        let protocols = vec![
            ("TwoPhase", "types.rs", "twophase.rs"),
            ("Paxos", "types.rs", "paxos.rs"),
            ("LeaderElection", "types.rs", "election.rs"),
            ("Raft", "types.rs", "raft.rs"),
            ("ChainReplication", "types.rs", "chain.rs"),
            ("PrimaryBackup", "types.rs", "primarybackup.rs"),
            ("PBFT", "types.rs", "pbft.rs"),
            ("VerticalPaxos", "types.rs", "vpaxos.rs"),
            ("EPaxos", "types.rs", "epaxos.rs"),
        ];

        let mut all_ok = true;
        for (name, types_file, proto_file) in &protocols {
            let types_path =
                std::path::PathBuf::from(format!("../src/protocol/{}/{}", name, types_file));
            let proto_path =
                std::path::PathBuf::from(format!("../src/protocol/{}/{}", name, proto_file));

            if !types_path.exists() || !proto_path.exists() {
                continue;
            }

            match analyze_spec_files(&[types_path.as_path(), proto_path.as_path()]) {
                Ok(schema) => {
                    let summary = schema.summary();
                    // Every protocol should have at least: LState, LConstants, LInit
                    assert!(
                        summary.num_structs >= 2,
                        "{}: expected >= 2 structs, got {}",
                        name,
                        summary.num_structs
                    );
                    assert!(
                        summary.num_functions >= 2,
                        "{}: expected >= 2 functions, got {}",
                        name,
                        summary.num_functions
                    );
                }
                Err(e) => {
                    panic!("{}: failed to analyze: {}", name, e);
                }
            }
        }
    }
}
