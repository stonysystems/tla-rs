//! Type table builder for tracking struct, enum, and function types.
//!
//! This module provides a type registry that collects and stores information about:
//! - Struct definitions with their fields and types
//! - Enum definitions with their variants
//! - Function/predicate signatures
//! - Generic type parameters and bounds
//!
//! The type table is used during code generation to:
//! - Generate concrete type implementations from spec types
//! - Create View trait implementations
//! - Verify type consistency across translations

use crate::ast::{GenericParam, Generics, Path, SpecFunction, Type};
use crate::error::{TranspileError, TranspileResult};
use std::collections::HashMap;

/// Registry of all types found in the codebase
#[derive(Debug, Default)]
pub struct TypeRegistry {
    /// Struct definitions indexed by full path
    pub structs: HashMap<String, StructDef>,
    /// Enum definitions indexed by full path
    pub enums: HashMap<String, EnumDef>,
    /// Function signatures indexed by full path
    pub functions: HashMap<String, FunctionSig>,
    /// Type aliases indexed by full path
    pub aliases: HashMap<String, TypeAlias>,
}

/// A struct definition
#[derive(Debug, Clone)]
pub struct StructDef {
    /// Full path name (e.g., "RSL::Acceptor::LAcceptor")
    pub name: String,
    /// Generic type parameters
    pub generics: Generics,
    /// Fields in declaration order
    pub fields: Vec<FieldDef>,
    /// Whether this is a spec type (L prefix) or exec type (C prefix)
    pub is_spec: bool,
}

/// A struct field definition
#[derive(Debug, Clone)]
pub struct FieldDef {
    /// Field name
    pub name: String,
    /// Field type
    pub ty: Type,
    /// Whether the field is public
    pub is_public: bool,
}

/// An enum definition
#[derive(Debug, Clone)]
pub struct EnumDef {
    /// Full path name
    pub name: String,
    /// Generic type parameters
    pub generics: Generics,
    /// Variants
    pub variants: Vec<VariantDef>,
    /// Whether this is a spec type
    pub is_spec: bool,
}

/// An enum variant definition
#[derive(Debug, Clone)]
pub struct VariantDef {
    /// Variant name
    pub name: String,
    /// Variant fields (empty for unit variants)
    pub fields: VariantFields,
}

/// Enum variant field structure
#[derive(Debug, Clone)]
pub enum VariantFields {
    /// Unit variant (no fields)
    Unit,
    /// Tuple variant (unnamed fields)
    Tuple(Vec<Type>),
    /// Struct variant (named fields)
    Struct(Vec<FieldDef>),
}

/// A function/predicate signature
#[derive(Debug, Clone)]
pub struct FunctionSig {
    /// Full path name
    pub name: String,
    /// Generic type parameters
    pub generics: Generics,
    /// Parameter types in order
    pub params: Vec<ParamSig>,
    /// Return type
    pub return_type: Type,
    /// Whether this is a spec function
    pub is_spec: bool,
}

/// A function parameter signature
#[derive(Debug, Clone)]
pub struct ParamSig {
    /// Parameter name
    pub name: String,
    /// Parameter type
    pub ty: Type,
}

/// A type alias
#[derive(Debug, Clone)]
pub struct TypeAlias {
    /// Alias name
    pub name: String,
    /// Generic type parameters
    pub generics: Generics,
    /// The aliased type
    pub ty: Type,
}

impl TypeRegistry {
    /// Create a new empty type registry
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a struct definition
    pub fn register_struct(&mut self, def: StructDef) {
        self.structs.insert(def.name.clone(), def);
    }

    /// Register an enum definition
    pub fn register_enum(&mut self, def: EnumDef) {
        self.enums.insert(def.name.clone(), def);
    }

    /// Register a function signature
    pub fn register_function(&mut self, sig: FunctionSig) {
        self.functions.insert(sig.name.clone(), sig);
    }

    /// Register a spec function from parsed AST
    pub fn register_spec_function(&mut self, spec_fn: &SpecFunction) {
        let sig = FunctionSig {
            name: spec_fn.name.clone(),
            generics: spec_fn.generics.clone(),
            params: spec_fn
                .params
                .iter()
                .map(|p| ParamSig {
                    name: p.name.clone(),
                    ty: p.ty.clone(),
                })
                .collect(),
            return_type: spec_fn.return_type.clone(),
            is_spec: true,
        };
        self.register_function(sig);
    }

    /// Register a type alias
    pub fn register_alias(&mut self, alias: TypeAlias) {
        self.aliases.insert(alias.name.clone(), alias);
    }

    /// Look up a struct definition by name
    pub fn get_struct(&self, name: &str) -> Option<&StructDef> {
        self.structs.get(name)
    }

    /// Look up an enum definition by name
    pub fn get_enum(&self, name: &str) -> Option<&EnumDef> {
        self.enums.get(name)
    }

    /// Look up a function signature by name
    pub fn get_function(&self, name: &str) -> Option<&FunctionSig> {
        self.functions.get(name)
    }

    /// Look up a type alias by name
    pub fn get_alias(&self, name: &str) -> Option<&TypeAlias> {
        self.aliases.get(name)
    }

    /// Check if a type name refers to a struct
    pub fn is_struct(&self, name: &str) -> bool {
        self.structs.contains_key(name)
    }

    /// Check if a type name refers to an enum
    pub fn is_enum(&self, name: &str) -> bool {
        self.enums.contains_key(name)
    }

    /// Get all fields for a struct type
    pub fn get_struct_fields(&self, name: &str) -> Option<&[FieldDef]> {
        self.structs.get(name).map(|s| s.fields.as_slice())
    }

    /// Get all variants for an enum type
    pub fn get_enum_variants(&self, name: &str) -> Option<&[VariantDef]> {
        self.enums.get(name).map(|e| e.variants.as_slice())
    }

    /// Get the corresponding exec type name for a spec type
    /// Applies naming conventions: L* -> C*, or uses remapping if configured
    pub fn get_exec_type_name(
        &self,
        spec_name: &str,
        config: &crate::config::NamingConfig,
    ) -> String {
        // Try prefix replacement
        if spec_name.starts_with(&config.spec_prefix) {
            let base = &spec_name[config.spec_prefix.len()..];
            return format!("{}{}", config.exec_prefix, base);
        }

        // Default: prepend exec prefix
        format!("{}{}", config.exec_prefix, spec_name)
    }

    /// Resolve a type path to its fully qualified name
    pub fn resolve_type_path(&self, path: &Path) -> String {
        path.segments.join("::")
    }
}

/// Parser for struct and enum definitions from Verus source
pub struct TypeParser<'a> {
    content: &'a str,
    pos: usize,
}

impl<'a> TypeParser<'a> {
    /// Create a new type parser
    pub fn new(content: &'a str) -> Self {
        Self { content, pos: 0 }
    }

    /// Parse all type definitions from the content
    pub fn parse_types(&mut self) -> TranspileResult<Vec<TypeDef>> {
        let mut types = Vec::new();

        while self.pos < self.content.len() {
            self.skip_whitespace_and_comments();

            if self.pos >= self.content.len() {
                break;
            }

            // Try to enter a verus! block
            if self.try_enter_verus_block()? {
                // Parse types inside the verus! block
                types.extend(self.parse_verus_block_types()?);
                continue;
            }

            // Try to parse a struct
            if let Some(s) = self.try_parse_struct()? {
                types.push(TypeDef::Struct(s));
                continue;
            }

            // Try to parse an enum
            if let Some(e) = self.try_parse_enum()? {
                types.push(TypeDef::Enum(e));
                continue;
            }

            // Try to parse a type alias
            if let Some(a) = self.try_parse_type_alias()? {
                types.push(TypeDef::Alias(a));
                continue;
            }

            // Skip other items
            self.skip_item();
        }

        Ok(types)
    }

    /// Try to detect and enter a verus! { ... } block
    fn try_enter_verus_block(&mut self) -> TranspileResult<bool> {
        let start_pos = self.pos;

        // Look for "verus!" pattern
        if !self.try_consume("verus") {
            return Ok(false);
        }
        self.skip_whitespace();

        if !self.try_consume("!") {
            self.pos = start_pos;
            return Ok(false);
        }
        self.skip_whitespace();

        // Expect opening brace
        if self.peek() != Some('{') {
            self.pos = start_pos;
            return Ok(false);
        }
        self.advance(); // consume '{'

        Ok(true)
    }

    /// Parse type definitions inside a verus! block
    fn parse_verus_block_types(&mut self) -> TranspileResult<Vec<TypeDef>> {
        let mut types = Vec::new();
        let mut brace_depth = 1;

        while brace_depth > 0 && self.pos < self.content.len() {
            self.skip_whitespace_and_comments();

            if self.pos >= self.content.len() {
                break;
            }

            // Check for closing brace
            if self.peek() == Some('}') {
                brace_depth -= 1;
                self.advance();
                if brace_depth == 0 {
                    break;
                }
                continue;
            }

            // Try to parse a struct
            if let Some(s) = self.try_parse_struct()? {
                types.push(TypeDef::Struct(s));
                continue;
            }

            // Try to parse an enum
            if let Some(e) = self.try_parse_enum()? {
                types.push(TypeDef::Enum(e));
                continue;
            }

            // Try to parse a type alias
            if let Some(a) = self.try_parse_type_alias()? {
                types.push(TypeDef::Alias(a));
                continue;
            }

            // Skip other items (functions, etc.) while tracking braces
            self.skip_verus_item(&mut brace_depth);
        }

        Ok(types)
    }

    /// Skip a verus item while tracking brace depth
    fn skip_verus_item(&mut self, brace_depth: &mut i32) {
        loop {
            match self.peek() {
                Some('{') => {
                    *brace_depth += 1;
                    self.advance();
                }
                Some('}') => {
                    // Don't consume the closing brace here - let the caller handle it
                    break;
                }
                Some(_) => {
                    self.advance();
                    // Check if we've reached the end of an item
                    // (semicolon at depth 1 or closing brace)
                    if self.pos > 0 {
                        let prev = self.content[..self.pos].chars().last();
                        if prev == Some(';') || prev == Some('}') {
                            break;
                        }
                    }
                }
                None => break,
            }
        }
    }

    /// Try to parse a struct definition
    fn try_parse_struct(&mut self) -> TranspileResult<Option<StructDef>> {
        let start_pos = self.pos;

        // Skip visibility
        if self.try_consume("pub") {
            self.skip_whitespace();
        }

        // Check for struct keyword
        if !self.try_consume("struct") {
            self.pos = start_pos;
            return Ok(None);
        }
        self.skip_whitespace();

        // Parse name
        let name = self.parse_identifier()?;
        self.skip_whitespace();

        // Parse generics (optional)
        let generics = if self.peek() == Some('<') {
            self.parse_generics()?
        } else {
            Generics::default()
        };
        self.skip_whitespace();

        // Check if it's a spec type (starts with L) or exec type (starts with C)
        let is_spec = name.starts_with('L');

        // Parse fields
        if self.peek() != Some('{') {
            // Tuple struct or unit struct
            self.pos = start_pos;
            return Ok(None);
        }
        self.advance();

        let mut fields = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek() == Some('}') {
                break;
            }

            let is_public = self.try_consume("pub");
            if is_public {
                self.skip_whitespace();
            }

            let field_name = self.parse_identifier()?;
            self.skip_whitespace();
            self.expect(':')?;
            self.skip_whitespace();
            let field_ty = self.parse_type()?;
            self.skip_whitespace();

            fields.push(FieldDef {
                name: field_name,
                ty: field_ty,
                is_public,
            });

            self.try_consume(",");
        }
        self.expect('}')?;

        Ok(Some(StructDef {
            name,
            generics,
            fields,
            is_spec,
        }))
    }

    /// Try to parse an enum definition
    fn try_parse_enum(&mut self) -> TranspileResult<Option<EnumDef>> {
        let start_pos = self.pos;

        // Skip visibility
        if self.try_consume("pub") {
            self.skip_whitespace();
        }

        // Check for enum keyword
        if !self.try_consume("enum") {
            self.pos = start_pos;
            return Ok(None);
        }
        self.skip_whitespace();

        // Parse name
        let name = self.parse_identifier()?;
        self.skip_whitespace();

        // Parse generics (optional)
        let generics = if self.peek() == Some('<') {
            self.parse_generics()?
        } else {
            Generics::default()
        };
        self.skip_whitespace();

        let is_spec = name.starts_with('L');

        // Parse variants
        self.expect('{')?;
        let mut variants = Vec::new();

        loop {
            self.skip_whitespace_and_comments();
            if self.peek() == Some('}') {
                break;
            }

            let variant_name = self.parse_identifier()?;
            self.skip_whitespace();

            // Parse variant fields
            let fields = if self.peek() == Some('(') {
                // Tuple variant
                self.advance();
                let mut tys = Vec::new();
                loop {
                    self.skip_whitespace();
                    if self.peek() == Some(')') {
                        break;
                    }
                    tys.push(self.parse_type()?);
                    self.skip_whitespace();
                    self.try_consume(",");
                }
                self.expect(')')?;
                VariantFields::Tuple(tys)
            } else if self.peek() == Some('{') {
                // Struct variant
                self.advance();
                let mut flds = Vec::new();
                loop {
                    self.skip_whitespace();
                    if self.peek() == Some('}') {
                        break;
                    }
                    let is_pub = self.try_consume("pub");
                    if is_pub {
                        self.skip_whitespace();
                    }
                    let fld_name = self.parse_identifier()?;
                    self.skip_whitespace();
                    self.expect(':')?;
                    self.skip_whitespace();
                    let fld_ty = self.parse_type()?;
                    self.skip_whitespace();
                    flds.push(FieldDef {
                        name: fld_name,
                        ty: fld_ty,
                        is_public: is_pub,
                    });
                    self.try_consume(",");
                }
                self.expect('}')?;
                VariantFields::Struct(flds)
            } else {
                VariantFields::Unit
            };

            variants.push(VariantDef {
                name: variant_name,
                fields,
            });

            self.skip_whitespace();
            self.try_consume(",");
        }
        self.expect('}')?;

        Ok(Some(EnumDef {
            name,
            generics,
            variants,
            is_spec,
        }))
    }

    /// Try to parse a type alias
    fn try_parse_type_alias(&mut self) -> TranspileResult<Option<TypeAlias>> {
        let start_pos = self.pos;

        // Skip visibility
        if self.try_consume("pub") {
            self.skip_whitespace();
        }

        // Check for type keyword
        if !self.try_consume("type") {
            self.pos = start_pos;
            return Ok(None);
        }
        self.skip_whitespace();

        // Parse name
        let name = self.parse_identifier()?;
        self.skip_whitespace();

        // Parse generics (optional)
        let generics = if self.peek() == Some('<') {
            self.parse_generics()?
        } else {
            Generics::default()
        };
        self.skip_whitespace();

        // Expect =
        if !self.try_consume("=") {
            self.pos = start_pos;
            return Ok(None);
        }
        self.skip_whitespace();

        // Parse the aliased type
        let ty = self.parse_type()?;
        self.skip_whitespace();
        self.try_consume(";");

        Ok(Some(TypeAlias { name, generics, ty }))
    }

    // Helper methods (similar to parser/mod.rs but for type parsing)

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            self.skip_whitespace();
            if self.peek_str(2) == Some("//") {
                self.skip_until_pattern("\n");
                continue;
            }
            if self.peek_str(2) == Some("/*") {
                self.advance();
                self.advance();
                let mut depth = 1;
                while depth > 0 && self.pos < self.content.len() {
                    if self.peek_str(2) == Some("/*") {
                        depth += 1;
                        self.advance();
                    } else if self.peek_str(2) == Some("*/") {
                        depth -= 1;
                        self.advance();
                    }
                    self.advance();
                }
                continue;
            }
            break;
        }
    }

    fn skip_until_pattern(&mut self, pattern: &str) {
        while self.pos + pattern.len() <= self.content.len() {
            if &self.content[self.pos..self.pos + pattern.len()] == pattern {
                return;
            }
            self.advance();
        }
    }

    fn skip_item(&mut self) {
        // Skip leading whitespace
        self.skip_whitespace_and_comments();

        // Handle items that end with semicolon (use, type alias, etc.)
        // vs items that end with braces (fn, struct, enum, impl, etc.)
        let mut depth = 0;
        let mut found_brace = false;

        loop {
            match self.peek() {
                Some('{') => {
                    found_brace = true;
                    depth += 1;
                    self.advance();
                }
                Some('}') => {
                    depth -= 1;
                    self.advance();
                    if depth == 0 && found_brace {
                        break;
                    }
                }
                Some(';') => {
                    self.advance();
                    // If we haven't entered a brace block, semicolon ends the item
                    if depth == 0 && !found_brace {
                        break;
                    }
                }
                Some(_) => {
                    self.advance();
                }
                None => break,
            }
        }
    }

    fn peek(&self) -> Option<char> {
        self.content[self.pos..].chars().next()
    }

    fn peek_str(&self, n: usize) -> Option<&str> {
        if self.pos + n <= self.content.len() {
            Some(&self.content[self.pos..self.pos + n])
        } else {
            None
        }
    }

    fn advance(&mut self) {
        if let Some(c) = self.peek() {
            self.pos += c.len_utf8();
        }
    }

    fn try_consume(&mut self, s: &str) -> bool {
        if self.pos + s.len() <= self.content.len()
            && &self.content[self.pos..self.pos + s.len()] == s
        {
            // Check it's not part of a longer identifier
            if s.chars()
                .last()
                .is_some_and(|c| c.is_alphanumeric() || c == '_')
            {
                let next_char = self.content[self.pos + s.len()..].chars().next();
                if next_char.is_some_and(|c| c.is_alphanumeric() || c == '_') {
                    return false;
                }
            }
            self.pos += s.len();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, c: char) -> TranspileResult<()> {
        self.skip_whitespace();
        if self.peek() == Some(c) {
            self.advance();
            Ok(())
        } else {
            Err(TranspileError::Parse {
                message: format!("Expected '{}', found '{:?}'", c, self.peek()),
                span: None,
            })
        }
    }

    fn parse_identifier(&mut self) -> TranspileResult<String> {
        self.skip_whitespace();
        let start = self.pos;

        if let Some(c) = self.peek() {
            if !c.is_alphabetic() && c != '_' {
                return Err(TranspileError::Parse {
                    message: format!("Expected identifier, found '{}'", c),
                    span: None,
                });
            }
        } else {
            return Err(TranspileError::Parse {
                message: "Unexpected end of input".to_string(),
                span: None,
            });
        }

        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                self.advance();
            } else {
                break;
            }
        }

        Ok(self.content[start..self.pos].to_string())
    }

    fn parse_generics(&mut self) -> TranspileResult<Generics> {
        self.expect('<')?;
        let mut params = Vec::new();

        loop {
            self.skip_whitespace();
            if self.peek() == Some('>') {
                break;
            }

            let name = self.parse_identifier()?;
            self.skip_whitespace();

            let mut bounds = Vec::new();
            if self.try_consume(":") {
                self.skip_whitespace();
                while self.peek() != Some(',') && self.peek() != Some('>') {
                    let bound_name = self.parse_identifier()?;
                    bounds.push(crate::ast::TypeBound {
                        path: Path::single(bound_name),
                    });
                    self.skip_whitespace();
                    if !self.try_consume("+") {
                        break;
                    }
                    self.skip_whitespace();
                }
            }

            params.push(GenericParam::Type { name, bounds });

            self.skip_whitespace();
            if !self.try_consume(",") {
                break;
            }
        }

        self.expect('>')?;

        Ok(Generics {
            params,
            where_clause: None,
        })
    }

    fn parse_type(&mut self) -> TranspileResult<Type> {
        self.skip_whitespace();

        // Check for reference
        if self.try_consume("&") {
            let mutable = self.try_consume("mut");
            self.skip_whitespace();
            let inner = self.parse_type()?;
            return Ok(Type::Reference {
                ty: Box::new(inner),
                mutable,
            });
        }

        // Check for tuple
        if self.peek() == Some('(') {
            self.advance();
            let mut types = Vec::new();
            loop {
                self.skip_whitespace();
                if self.peek() == Some(')') {
                    break;
                }
                types.push(self.parse_type()?);
                self.skip_whitespace();
                if !self.try_consume(",") {
                    break;
                }
            }
            self.expect(')')?;
            if types.is_empty() {
                return Ok(Type::Unit);
            }
            return Ok(Type::Tuple(types));
        }

        // Parse named type
        let name = self.parse_identifier()?;
        self.skip_whitespace();

        match name.as_str() {
            "bool" => return Ok(Type::Bool),
            "int" => return Ok(Type::Int),
            "nat" => return Ok(Type::Nat),
            "Seq" => {
                self.expect('<')?;
                let inner = self.parse_type()?;
                self.expect('>')?;
                return Ok(Type::Seq(Box::new(inner)));
            }
            "Set" => {
                self.expect('<')?;
                let inner = self.parse_type()?;
                self.expect('>')?;
                return Ok(Type::Set(Box::new(inner)));
            }
            "Map" => {
                self.expect('<')?;
                let key = self.parse_type()?;
                self.skip_whitespace();
                self.expect(',')?;
                let value = self.parse_type()?;
                self.expect('>')?;
                return Ok(Type::Map(Box::new(key), Box::new(value)));
            }
            _ => {}
        }

        // Check for generic parameters
        if self.peek() == Some('<') {
            self.advance();
            let mut type_args = Vec::new();
            loop {
                self.skip_whitespace();
                if self.peek() == Some('>') {
                    break;
                }
                type_args.push(self.parse_type()?);
                self.skip_whitespace();
                if !self.try_consume(",") {
                    break;
                }
            }
            self.expect('>')?;
            return Ok(Type::Generic(Path::single(name), type_args));
        }

        Ok(Type::Named(Path::single(name)))
    }
}

/// A parsed type definition
#[derive(Debug)]
pub enum TypeDef {
    Struct(StructDef),
    Enum(EnumDef),
    Alias(TypeAlias),
}

/// Parse types from a file
pub fn parse_types_from_file(path: &std::path::Path) -> TranspileResult<Vec<TypeDef>> {
    let source = std::fs::read_to_string(path)?;
    let mut parser = TypeParser::new(&source);
    parser.parse_types()
}

/// Build a type registry from parsed types
pub fn build_registry(types: Vec<TypeDef>) -> TypeRegistry {
    let mut registry = TypeRegistry::new();

    for type_def in types {
        match type_def {
            TypeDef::Struct(s) => registry.register_struct(s),
            TypeDef::Enum(e) => registry.register_enum(e),
            TypeDef::Alias(a) => registry.register_alias(a),
        }
    }

    registry
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_registry_creation() {
        let registry = TypeRegistry::new();
        assert!(registry.structs.is_empty());
        assert!(registry.enums.is_empty());
        assert!(registry.functions.is_empty());
    }

    #[test]
    fn test_register_struct() {
        let mut registry = TypeRegistry::new();

        let struct_def = StructDef {
            name: "LAcceptor".to_string(),
            generics: Generics::default(),
            fields: vec![
                FieldDef {
                    name: "max_bal".to_string(),
                    ty: Type::Named(Path::single("Ballot".to_string())),
                    is_public: true,
                },
                FieldDef {
                    name: "votes".to_string(),
                    ty: Type::Named(Path::single("Votes".to_string())),
                    is_public: true,
                },
            ],
            is_spec: true,
        };

        registry.register_struct(struct_def);

        assert!(registry.is_struct("LAcceptor"));
        let def = registry.get_struct("LAcceptor").unwrap();
        assert_eq!(def.fields.len(), 2);
        assert!(def.is_spec);
    }

    #[test]
    fn test_register_enum() {
        let mut registry = TypeRegistry::new();

        let enum_def = EnumDef {
            name: "LMessage".to_string(),
            generics: Generics::default(),
            variants: vec![
                VariantDef {
                    name: "Msg1a".to_string(),
                    fields: VariantFields::Struct(vec![FieldDef {
                        name: "bal".to_string(),
                        ty: Type::Named(Path::single("Ballot".to_string())),
                        is_public: true,
                    }]),
                },
                VariantDef {
                    name: "Msg1b".to_string(),
                    fields: VariantFields::Tuple(vec![
                        Type::Named(Path::single("Ballot".to_string())),
                        Type::Named(Path::single("Votes".to_string())),
                    ]),
                },
                VariantDef {
                    name: "Empty".to_string(),
                    fields: VariantFields::Unit,
                },
            ],
            is_spec: true,
        };

        registry.register_enum(enum_def);

        assert!(registry.is_enum("LMessage"));
        let def = registry.get_enum("LMessage").unwrap();
        assert_eq!(def.variants.len(), 3);
    }

    #[test]
    fn test_parse_simple_struct() {
        let source = r#"
            pub struct LAcceptor {
                pub max_bal: Ballot,
                pub votes: Votes,
            }
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        assert_eq!(types.len(), 1);
        match &types[0] {
            TypeDef::Struct(s) => {
                assert_eq!(s.name, "LAcceptor");
                assert_eq!(s.fields.len(), 2);
                assert!(s.is_spec);
            }
            _ => panic!("Expected struct"),
        }
    }

    #[test]
    fn test_parse_generic_struct() {
        let source = r#"
            pub struct Container<T> {
                pub items: Seq<T>,
            }
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        assert_eq!(types.len(), 1);
        match &types[0] {
            TypeDef::Struct(s) => {
                assert_eq!(s.name, "Container");
                assert_eq!(s.generics.params.len(), 1);
            }
            _ => panic!("Expected struct"),
        }
    }

    #[test]
    fn test_parse_enum() {
        let source = r#"
            pub enum LMessage {
                Msg1a { bal: Ballot },
                Msg1b(Ballot, Votes),
                Empty,
            }
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        assert_eq!(types.len(), 1);
        match &types[0] {
            TypeDef::Enum(e) => {
                assert_eq!(e.name, "LMessage");
                assert_eq!(e.variants.len(), 3);
                assert!(matches!(e.variants[0].fields, VariantFields::Struct(_)));
                assert!(matches!(e.variants[1].fields, VariantFields::Tuple(_)));
                assert!(matches!(e.variants[2].fields, VariantFields::Unit));
            }
            _ => panic!("Expected enum"),
        }
    }

    #[test]
    fn test_parse_type_alias() {
        let source = r#"
            pub type Votes = Map<Ballot, Vote>;
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        assert_eq!(types.len(), 1);
        match &types[0] {
            TypeDef::Alias(a) => {
                assert_eq!(a.name, "Votes");
                assert!(matches!(a.ty, Type::Map(_, _)));
            }
            _ => panic!("Expected type alias"),
        }
    }

    #[test]
    fn test_exec_type_name() {
        let config = crate::config::NamingConfig::default();
        let registry = TypeRegistry::new();

        assert_eq!(
            registry.get_exec_type_name("LAcceptor", &config),
            "CAcceptor"
        );
        assert_eq!(registry.get_exec_type_name("LState", &config), "CState");
        assert_eq!(registry.get_exec_type_name("Ballot", &config), "CBallot");
    }

    #[test]
    fn test_parse_verus_block_struct() {
        let source = r#"
            verus! {
                pub struct LAcceptor {
                    pub constants: LReplicaConstants,
                    pub max_bal: Ballot,
                    pub votes: Votes,
                    pub last_checkpointed_operation: Seq<OperationNumber>,
                    pub log_truncation_point: OperationNumber,
                }

                pub open spec fn LAcceptorInit(s: LAcceptor) -> bool {
                    s.max_bal == Ballot::default()
                }
            }
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        // Should parse the struct from inside the verus! block
        assert_eq!(types.len(), 1);
        match &types[0] {
            TypeDef::Struct(s) => {
                assert_eq!(s.name, "LAcceptor");
                assert_eq!(s.fields.len(), 5);
                assert!(s.is_spec);
                assert_eq!(s.fields[0].name, "constants");
                assert_eq!(s.fields[1].name, "max_bal");
                assert_eq!(s.fields[2].name, "votes");
                assert_eq!(s.fields[3].name, "last_checkpointed_operation");
                assert_eq!(s.fields[4].name, "log_truncation_point");
            }
            _ => panic!("Expected struct"),
        }
    }

    #[test]
    fn test_parse_verus_block_multiple_types() {
        let source = r#"
            verus! {
                pub struct LAcceptor {
                    pub max_bal: Ballot,
                }

                pub type Votes = Map<OperationNumber, Vote>;

                pub enum LMessage {
                    Msg1a { bal: Ballot },
                    Msg2a,
                }

                pub open spec fn some_pred(x: int) -> bool {
                    x > 0
                }
            }
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        // Should parse struct, type alias, and enum from inside verus! block
        assert_eq!(types.len(), 3);

        // Check struct
        match &types[0] {
            TypeDef::Struct(s) => {
                assert_eq!(s.name, "LAcceptor");
            }
            _ => panic!("Expected struct at index 0"),
        }

        // Check type alias
        match &types[1] {
            TypeDef::Alias(a) => {
                assert_eq!(a.name, "Votes");
            }
            _ => panic!("Expected type alias at index 1"),
        }

        // Check enum
        match &types[2] {
            TypeDef::Enum(e) => {
                assert_eq!(e.name, "LMessage");
                assert_eq!(e.variants.len(), 2);
            }
            _ => panic!("Expected enum at index 2"),
        }
    }

    #[test]
    fn test_parse_verus_block_with_complex_functions() {
        // Test that we correctly skip complex spec functions without breaking
        let source = r#"
            verus! {
                pub struct LState {
                    pub value: int,
                }

                pub open spec fn complex_pred(s: LState, s_: LState) -> bool {
                    if s.value > 0 {
                        &&& s_.value == s.value + 1
                        &&& some_other_condition()
                    } else {
                        s_ == s
                    }
                }

                pub open spec fn another_fn(x: int, y: int) -> bool
                    recommends x > 0
                {
                    x + y > 0
                }
            }
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        // Should only parse the struct, skipping the functions
        assert_eq!(types.len(), 1);
        match &types[0] {
            TypeDef::Struct(s) => {
                assert_eq!(s.name, "LState");
                assert_eq!(s.fields.len(), 1);
            }
            _ => panic!("Expected struct"),
        }
    }

    #[test]
    fn test_parse_real_acceptor_format() {
        // Test parsing real RSL acceptor format (no spaces after colons)
        let source = r#"
verus! {
    pub struct LAcceptor {
        pub constants:LReplicaConstants,
        pub max_bal:Ballot,
        pub votes:Votes,
        pub last_checkpointed_operation:Seq<OperationNumber>,
        pub log_truncation_point:OperationNumber,
    }

    pub open spec fn IsLogTruncationPointValid(log_truncation_point:OperationNumber, last_checkpointed_operation:Seq<OperationNumber>,
                                              config:LConfiguration) -> bool
    {
        true
    }

    pub open spec fn RemoveVotesBeforeLogTruncationPoint(votes:Votes, votes_:Votes, log_truncation_point:OperationNumber) -> bool
    {
        &&& (forall |opn:OperationNumber| votes_.contains_key(opn) ==> votes.contains_key(opn) && votes_[opn] == votes[opn])
        &&& (forall |opn:OperationNumber| opn < log_truncation_point ==> !votes_.contains_key(opn))
    }
}
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        assert_eq!(types.len(), 1);
        match &types[0] {
            TypeDef::Struct(s) => {
                assert_eq!(s.name, "LAcceptor");
                assert_eq!(s.fields.len(), 5);
                assert!(s.is_spec);

                // Check field names
                assert_eq!(s.fields[0].name, "constants");
                assert_eq!(s.fields[1].name, "max_bal");
                assert_eq!(s.fields[2].name, "votes");
                assert_eq!(s.fields[3].name, "last_checkpointed_operation");
                assert_eq!(s.fields[4].name, "log_truncation_point");

                // Check field types
                match &s.fields[0].ty {
                    Type::Named(path) => assert_eq!(path.segments[0], "LReplicaConstants"),
                    _ => panic!("Expected Named type for constants"),
                }
                match &s.fields[3].ty {
                    Type::Seq(inner) => match inner.as_ref() {
                        Type::Named(path) => assert_eq!(path.segments[0], "OperationNumber"),
                        _ => panic!("Expected Named type inside Seq"),
                    },
                    _ => panic!("Expected Seq type for last_checkpointed_operation"),
                }
            }
            _ => panic!("Expected struct"),
        }
    }

    #[test]
    fn test_parse_with_use_statements_before_verus() {
        // Test that use statements before verus! block don't break parsing
        let source = r#"
use vstd::prelude::*;
use std::collections::*;
use crate::some::module::*;

verus! {
    pub struct Ballot {
        pub seqno: int,
        pub proposer_id: int,
    }

    pub struct Request {
        pub client: AbstractEndPoint,
        pub seqno: int,
    }
}
        "#;

        let mut parser = TypeParser::new(source);
        let types = parser.parse_types().unwrap();

        // Should parse both structs from inside verus! block
        assert_eq!(types.len(), 2);
        match &types[0] {
            TypeDef::Struct(s) => {
                assert_eq!(s.name, "Ballot");
                assert_eq!(s.fields.len(), 2);
            }
            _ => panic!("Expected struct Ballot"),
        }
        match &types[1] {
            TypeDef::Struct(s) => {
                assert_eq!(s.name, "Request");
                assert_eq!(s.fields.len(), 2);
            }
            _ => panic!("Expected struct Request"),
        }
    }
}
