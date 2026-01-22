//! Verus parser using `syn`.
//!
//! This module handles parsing of Verus spec functions from Rust source files.
//! It extracts `spec fn` declarations from `verus! { ... }` macro blocks and
//! converts them to our internal AST representation.

use crate::ast::{
    Binding, BinOp, Expr, Generics, GenericParam, Literal, MatchArm, Parameter, Path, Pattern,
    SpecFunction, Type, TypeBound,
};
use crate::error::{TranspileError, TranspileResult};

/// Parser for Verus source files
pub struct VerusParser {
    /// Source code being parsed
    source: String,
    /// File path for error reporting
    file_path: Option<String>,
}

impl VerusParser {
    /// Create a new parser for the given source code
    pub fn new(source: String) -> Self {
        Self {
            source,
            file_path: None,
        }
    }

    /// Set the file path for error reporting
    pub fn with_file_path(mut self, path: String) -> Self {
        self.file_path = Some(path);
        self
    }

    /// Parse all spec functions from the source
    pub fn parse_spec_functions(&self) -> TranspileResult<Vec<SpecFunction>> {
        let mut functions = Vec::new();

        // Find verus! macro blocks
        let verus_blocks = self.find_verus_blocks()?;

        for block_content in verus_blocks {
            let block_fns = self.parse_verus_block(&block_content)?;
            functions.extend(block_fns);
        }

        Ok(functions)
    }

    /// Find all verus! { ... } macro blocks in the source
    fn find_verus_blocks(&self) -> TranspileResult<Vec<String>> {
        let mut blocks = Vec::new();
        let source = &self.source;

        // Simple pattern matching for verus! { ... }
        // This is a simplified approach; a full implementation would use proper parsing
        let mut i = 0;
        let chars: Vec<char> = source.chars().collect();

        while i < chars.len() {
            // Look for "verus!" pattern
            if i + 6 <= chars.len() && &source[i..i + 6] == "verus!" {
                i += 6;
                // Skip whitespace
                while i < chars.len() && chars[i].is_whitespace() {
                    i += 1;
                }
                // Expect '{'
                if i < chars.len() && chars[i] == '{' {
                    let start = i + 1;
                    let mut depth = 1;
                    i += 1;

                    while i < chars.len() && depth > 0 {
                        match chars[i] {
                            '{' => depth += 1,
                            '}' => depth -= 1,
                            _ => {}
                        }
                        i += 1;
                    }

                    if depth == 0 {
                        let block_content = source[start..i - 1].to_string();
                        blocks.push(block_content);
                    }
                }
            } else {
                i += 1;
            }
        }

        Ok(blocks)
    }

    /// Parse spec functions from a verus block
    fn parse_verus_block(&self, content: &str) -> TranspileResult<Vec<SpecFunction>> {
        let mut functions = Vec::new();
        let mut parser = VerusBlockParser::new(content);

        while let Some(item) = parser.next_item()? {
            match item {
                VerusItem::SpecFn(func) => functions.push(*func),
                VerusItem::Other => {} // Skip non-spec-fn items
            }
        }

        Ok(functions)
    }

    /// Parse a single spec function from a string
    pub fn parse_single_spec_fn(&self, fn_source: &str) -> TranspileResult<SpecFunction> {
        let mut parser = VerusBlockParser::new(fn_source);

        match parser.next_item()? {
            Some(VerusItem::SpecFn(func)) => Ok(*func),
            _ => Err(TranspileError::Parse {
                message: "Expected spec function".to_string(),
                span: None,
            }),
        }
    }
}

/// Item parsed from verus block
enum VerusItem {
    SpecFn(Box<SpecFunction>),
    Other,
}

/// Parser for content inside a verus block
struct VerusBlockParser<'a> {
    content: &'a str,
    pos: usize,
}

impl<'a> VerusBlockParser<'a> {
    fn new(content: &'a str) -> Self {
        Self { content, pos: 0 }
    }

    /// Get the next item from the block
    fn next_item(&mut self) -> TranspileResult<Option<VerusItem>> {
        self.skip_whitespace_and_comments();

        if self.pos >= self.content.len() {
            return Ok(None);
        }

        // Try to parse a spec function
        if let Some(func) = self.try_parse_spec_fn()? {
            return Ok(Some(VerusItem::SpecFn(Box::new(func))));
        }

        // Skip other items (structs, enums, type aliases, etc.)
        self.skip_item();
        Ok(Some(VerusItem::Other))
    }

    /// Try to parse a spec function
    fn try_parse_spec_fn(&mut self) -> TranspileResult<Option<SpecFunction>> {
        let start_pos = self.pos;

        // Look for spec fn pattern: [pub] [open] spec [fn]
        // Could also be: pub open spec(checked) fn
        let is_pub = self.try_consume("pub");
        if is_pub {
            self.skip_whitespace();
        }

        let is_open = self.try_consume("open");
        if is_open {
            self.skip_whitespace();
        }

        if !self.try_consume("spec") {
            self.pos = start_pos;
            return Ok(None);
        }
        self.skip_whitespace();

        // Handle spec(checked)
        if self.try_consume("(checked)") {
            self.skip_whitespace();
        }

        if !self.try_consume("fn") {
            self.pos = start_pos;
            return Ok(None);
        }
        self.skip_whitespace();

        // Parse function name
        let name = self.parse_identifier()?;
        self.skip_whitespace();

        // Parse generics (optional)
        let generics = if self.peek() == Some('<') {
            self.parse_generics()?
        } else {
            Generics::default()
        };
        self.skip_whitespace();

        // Parse parameters
        self.expect('(')?;
        let params = self.parse_parameters()?;
        self.expect(')')?;
        self.skip_whitespace();

        // Parse return type (optional)
        let return_type = if self.try_consume("->") {
            self.skip_whitespace();
            self.parse_type()?
        } else {
            Type::Bool
        };
        self.skip_whitespace();

        // Parse recommends clause (optional)
        let recommends = if self.try_consume("recommends") {
            self.skip_whitespace();
            self.parse_expr_list_until_brace()?
        } else {
            Vec::new()
        };
        self.skip_whitespace();

        // Parse function body
        self.expect('{')?;
        let body = self.parse_block_body()?;
        self.expect('}')?;

        Ok(Some(SpecFunction {
            name,
            generics,
            params,
            return_type,
            recommends,
            body,
            span: None,
        }))
    }

    /// Parse an identifier
    fn parse_identifier(&mut self) -> TranspileResult<String> {
        self.skip_whitespace();
        let start = self.pos;

        // First char must be letter or underscore
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

        // Consume identifier chars
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                self.advance();
            } else {
                break;
            }
        }

        let ident = self.content[start..self.pos].to_string();
        Ok(ident)
    }

    /// Parse generic parameters
    fn parse_generics(&mut self) -> TranspileResult<Generics> {
        self.expect('<')?;
        let mut params = Vec::new();

        loop {
            self.skip_whitespace();
            if self.peek() == Some('>') {
                break;
            }

            // Parse generic parameter (simplified: just type params for now)
            let name = self.parse_identifier()?;
            self.skip_whitespace();

            // Check for bounds
            let mut bounds = Vec::new();
            if self.try_consume(":") {
                self.skip_whitespace();
                // Parse bound (simplified)
                while self.peek() != Some(',') && self.peek() != Some('>') {
                    let bound_name = self.parse_identifier()?;
                    bounds.push(TypeBound {
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

    /// Parse function parameters
    fn parse_parameters(&mut self) -> TranspileResult<Vec<Parameter>> {
        let mut params = Vec::new();

        loop {
            self.skip_whitespace();
            if self.peek() == Some(')') {
                break;
            }

            // Parse parameter name
            let name = self.parse_identifier()?;
            self.skip_whitespace();

            // Expect ':'
            self.expect(':')?;
            self.skip_whitespace();

            // Parse type
            let ty = self.parse_type()?;
            self.skip_whitespace();

            params.push(Parameter {
                name,
                ty,
                mode: None,
                span: None,
            });

            if !self.try_consume(",") {
                break;
            }
        }

        Ok(params)
    }

    /// Parse a type
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
            return self.parse_tuple_type();
        }

        // Parse named type
        let name = self.parse_identifier()?;
        self.skip_whitespace();

        // Check for special types
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
            "Option" => {
                self.expect('<')?;
                let inner = self.parse_type()?;
                self.expect('>')?;
                return Ok(Type::Generic(
                    Path::single("Option".to_string()),
                    vec![inner],
                ));
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

    /// Parse a tuple type
    fn parse_tuple_type(&mut self) -> TranspileResult<Type> {
        self.expect('(')?;
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
            Ok(Type::Unit)
        } else {
            Ok(Type::Tuple(types))
        }
    }

    /// Parse expressions until we hit an opening brace
    fn parse_expr_list_until_brace(&mut self) -> TranspileResult<Vec<Expr>> {
        let mut exprs = Vec::new();

        while self.peek() != Some('{') {
            exprs.push(self.parse_expression()?);
            self.skip_whitespace();
            if !self.try_consume(",") {
                break;
            }
            self.skip_whitespace();
        }

        Ok(exprs)
    }

    /// Parse a block body (expression inside braces)
    fn parse_block_body(&mut self) -> TranspileResult<Expr> {
        self.skip_whitespace();
        self.parse_expression()
    }

    /// Parse an expression
    fn parse_expression(&mut self) -> TranspileResult<Expr> {
        self.skip_whitespace();

        // Check for conjunction chain (&&&)
        // Look-ahead check since try_consume would consume
        if self.peek_str(3) == Some("&&&") {
            self.pos += 3; // Consume &&&
            return self.parse_conjunction_chain();
        }

        // Check for disjunction chain (|||)
        if self.peek_str(3) == Some("|||") {
            self.pos += 3; // Consume |||
            return self.parse_disjunction_chain();
        }

        // Parse primary expression and handle binary operators
        let expr = self.parse_primary_expr()?;
        self.skip_whitespace();

        // Handle comparison and logical operators
        self.parse_binary_continuation(expr)
    }

    /// Parse a conjunction chain (&&&)
    fn parse_conjunction_chain(&mut self) -> TranspileResult<Expr> {
        let mut exprs = Vec::new();

        loop {
            self.skip_whitespace();
            let expr = self.parse_primary_expr()?;
            exprs.push(self.parse_binary_continuation(expr)?);
            self.skip_whitespace();

            // Use peek to check for next &&&
            if self.peek_str(3) == Some("&&&") {
                self.pos += 3; // Consume &&&
            } else {
                break;
            }
        }

        Ok(Expr::Conjunction(exprs))
    }

    /// Parse a disjunction chain (|||)
    fn parse_disjunction_chain(&mut self) -> TranspileResult<Expr> {
        let mut exprs = Vec::new();

        loop {
            self.skip_whitespace();
            let expr = self.parse_primary_expr()?;
            exprs.push(self.parse_binary_continuation(expr)?);
            self.skip_whitespace();

            // Use peek to check for next |||
            if self.peek_str(3) == Some("|||") {
                self.pos += 3; // Consume |||
            } else {
                break;
            }
        }

        Ok(Expr::Disjunction(exprs))
    }

    /// Parse binary operators after a primary expression
    fn parse_binary_continuation(&mut self, left: Expr) -> TranspileResult<Expr> {
        self.skip_whitespace();

        // Check for implication FIRST (before == to avoid consuming prefix)
        if self.try_consume("==>") {
            self.skip_whitespace();
            let right = self.parse_expression()?;
            return Ok(Expr::Implies(Box::new(left), Box::new(right)));
        }

        // Check for comparison operators
        if self.try_consume("==") {
            self.skip_whitespace();
            let right = self.parse_primary_expr()?;
            return self.parse_binary_continuation(Expr::Eq(Box::new(left), Box::new(right)));
        }

        if self.try_consume("!=") {
            self.skip_whitespace();
            let right = self.parse_primary_expr()?;
            return self.parse_binary_continuation(Expr::Ne(Box::new(left), Box::new(right)));
        }

        if self.try_consume("<=") {
            self.skip_whitespace();
            let right = self.parse_primary_expr()?;
            return self.parse_binary_continuation(Expr::Le(Box::new(left), Box::new(right)));
        }

        if self.try_consume(">=") {
            self.skip_whitespace();
            let right = self.parse_primary_expr()?;
            return self.parse_binary_continuation(Expr::Ge(Box::new(left), Box::new(right)));
        }

        if self.try_consume("<") {
            self.skip_whitespace();
            let right = self.parse_primary_expr()?;
            return self.parse_binary_continuation(Expr::Lt(Box::new(left), Box::new(right)));
        }

        if self.try_consume(">") {
            self.skip_whitespace();
            let right = self.parse_primary_expr()?;
            return self.parse_binary_continuation(Expr::Gt(Box::new(left), Box::new(right)));
        }

        // Check for logical and/or
        // BUT: Don't consume && if it's actually &&& (conjunction chain)
        // AND: Don't consume || if it's actually ||| (disjunction chain)
        if self.peek_str(2) == Some("&&") && self.peek_str(3) != Some("&&&") {
            self.pos += 2; // Consume &&
            self.skip_whitespace();
            let right = self.parse_expression()?;
            return Ok(Expr::Binary(Box::new(left), BinOp::And, Box::new(right)));
        }

        if self.peek_str(2) == Some("||") && self.peek_str(3) != Some("|||") {
            self.pos += 2; // Consume ||
            self.skip_whitespace();
            let right = self.parse_expression()?;
            return Ok(Expr::Binary(Box::new(left), BinOp::Or, Box::new(right)));
        }

        // Check for arithmetic operators
        if self.try_consume("+") {
            self.skip_whitespace();
            let right = self.parse_primary_expr()?;
            return self.parse_binary_continuation(Expr::Binary(
                Box::new(left),
                BinOp::Add,
                Box::new(right),
            ));
        }

        if self.try_consume("-") && self.peek() != Some('>') {
            self.skip_whitespace();
            let right = self.parse_primary_expr()?;
            return self.parse_binary_continuation(Expr::Binary(
                Box::new(left),
                BinOp::Sub,
                Box::new(right),
            ));
        }

        if self.try_consume("*") {
            self.skip_whitespace();
            let right = self.parse_primary_expr()?;
            return self.parse_binary_continuation(Expr::Binary(
                Box::new(left),
                BinOp::Mul,
                Box::new(right),
            ));
        }

        if self.try_consume("/") {
            self.skip_whitespace();
            let right = self.parse_primary_expr()?;
            return self.parse_binary_continuation(Expr::Binary(
                Box::new(left),
                BinOp::Div,
                Box::new(right),
            ));
        }

        if self.try_consume("%") {
            self.skip_whitespace();
            let right = self.parse_primary_expr()?;
            return self.parse_binary_continuation(Expr::Binary(
                Box::new(left),
                BinOp::Mod,
                Box::new(right),
            ));
        }

        Ok(left)
    }

    /// Parse a primary expression
    fn parse_primary_expr(&mut self) -> TranspileResult<Expr> {
        self.skip_whitespace();

        // Check for nested conjunction/disjunction
        if self.peek() == Some('{') {
            return self.parse_block_expr();
        }

        // Check for if expression
        if self.try_consume("if") {
            return self.parse_if_expr();
        }

        // Check for let expression
        if self.try_consume("let") {
            return self.parse_let_expr();
        }

        // Check for forall quantifier
        if self.try_consume("forall") {
            return self.parse_forall_expr();
        }

        // Check for exists quantifier
        if self.try_consume("exists") {
            return self.parse_exists_expr();
        }

        // Check for match expression
        if self.try_consume("match") {
            return self.parse_match_expr();
        }

        // Check for negation
        if self.try_consume("!") {
            self.skip_whitespace();
            let inner = self.parse_primary_expr()?;
            return Ok(Expr::Not(Box::new(inner)));
        }

        // Check for parenthesized expression or tuple
        if self.peek() == Some('(') {
            return self.parse_paren_or_tuple_expr();
        }

        // Check for sequence literal
        if self.try_consume("seq!") || self.try_consume("Seq::empty") {
            return self.parse_seq_expr();
        }

        // Check for set literal
        if self.try_consume("set!") || self.try_consume("Set::empty") {
            return self.parse_set_expr();
        }

        // Check for map literal
        if self.try_consume("map!") || self.try_consume("Map::empty") {
            return self.parse_map_expr();
        }

        // Check for boolean literals
        if self.try_consume("true") {
            return Ok(Expr::Literal(Literal::Bool(true)));
        }
        if self.try_consume("false") {
            return Ok(Expr::Literal(Literal::Bool(false)));
        }

        // Check for numeric literals
        if let Some(c) = self.peek() {
            if c.is_ascii_digit() || c == '-' {
                return self.parse_number_literal();
            }
        }

        // Parse identifier or path, then handle postfix operations
        let ident = self.parse_identifier()?;
        let mut expr = Expr::Ident(ident);

        // Handle postfix operations
        expr = self.parse_postfix_ops(expr)?;

        Ok(expr)
    }

    /// Parse postfix operations (field access, method calls, index, etc.)
    fn parse_postfix_ops(&mut self, mut expr: Expr) -> TranspileResult<Expr> {
        loop {
            self.skip_whitespace();

            // Check for view operator (@)
            if self.try_consume("@") {
                expr = Expr::View(Box::new(expr));
                continue;
            }

            // Check for path continuation (::)
            if self.peek_str(2) == Some("::") {
                self.pos += 2; // Consume ::
                self.skip_whitespace();
                let segment = self.parse_identifier()?;
                self.skip_whitespace();

                // Check if it's a function call like LState::default()
                if self.peek() == Some('(') {
                    self.advance();
                    let args = self.parse_call_args()?;
                    self.expect(')')?;

                    // Build a path from the identifier + segment
                    if let Expr::Ident(name) = &expr {
                        let path_segments = vec![name.clone(), segment];
                        expr = Expr::Call {
                            func: Path { segments: path_segments },
                            args,
                        };
                        continue;
                    }
                }

                // Otherwise it's just a path expression
                if let Expr::Ident(name) = &expr {
                    expr = Expr::Ident(format!("{}::{}", name, segment));
                }
                continue;
            }

            // Check for arrow operator (->)
            if self.try_consume("->") {
                self.skip_whitespace();
                let field = self.parse_identifier()?;
                expr = Expr::Arrow(Box::new(expr), field);
                continue;
            }

            // Check for dot access
            if self.try_consume(".") {
                self.skip_whitespace();
                let field = self.parse_identifier()?;
                self.skip_whitespace();

                // Check if it's a method call
                if self.peek() == Some('(') {
                    self.advance();
                    let args = self.parse_call_args()?;
                    self.expect(')')?;
                    expr = Expr::MethodCall {
                        receiver: Box::new(expr),
                        method: field,
                        args,
                    };
                } else {
                    expr = Expr::Field(Box::new(expr), field);
                }
                continue;
            }

            // Check for index access
            if self.try_consume("[") {
                let index = self.parse_expression()?;
                self.expect(']')?;
                expr = Expr::Index(Box::new(expr), Box::new(index));
                continue;
            }

            // Check for function call
            if self.peek() == Some('(') {
                if let Expr::Ident(name) = &expr {
                    self.advance();
                    let args = self.parse_call_args()?;
                    self.expect(')')?;
                    expr = Expr::Call {
                        func: Path::single(name.clone()),
                        args,
                    };
                    continue;
                }
            }

            break;
        }

        Ok(expr)
    }

    /// Parse call arguments
    fn parse_call_args(&mut self) -> TranspileResult<Vec<Expr>> {
        let mut args = Vec::new();

        loop {
            self.skip_whitespace();
            if self.peek() == Some(')') {
                break;
            }

            args.push(self.parse_expression()?);
            self.skip_whitespace();

            if !self.try_consume(",") {
                break;
            }
        }

        Ok(args)
    }

    /// Parse a block expression
    fn parse_block_expr(&mut self) -> TranspileResult<Expr> {
        self.expect('{')?;
        self.skip_whitespace();

        // Check for conjunction or disjunction using peek
        if self.peek_str(3) == Some("&&&") {
            self.pos += 3; // Consume &&&
            let expr = self.parse_conjunction_chain()?;
            self.skip_whitespace();
            self.expect('}')?;
            return Ok(expr);
        }

        if self.peek_str(3) == Some("|||") {
            self.pos += 3; // Consume |||
            let expr = self.parse_disjunction_chain()?;
            self.skip_whitespace();
            self.expect('}')?;
            return Ok(expr);
        }

        // Otherwise parse as regular expression
        let expr = self.parse_expression()?;
        self.skip_whitespace();
        self.expect('}')?;
        Ok(expr)
    }

    /// Parse an if expression
    fn parse_if_expr(&mut self) -> TranspileResult<Expr> {
        self.skip_whitespace();

        // Parse condition
        let cond = self.parse_expression_until_brace()?;
        self.skip_whitespace();

        // Parse then branch
        self.expect('{')?;
        let then_branch = self.parse_block_body()?;
        self.expect('}')?;
        self.skip_whitespace();

        // Parse optional else branch
        let else_branch = if self.try_consume("else") {
            self.skip_whitespace();
            if self.try_consume("if") {
                // else if
                Some(Box::new(self.parse_if_expr()?))
            } else {
                self.expect('{')?;
                let else_expr = self.parse_block_body()?;
                self.expect('}')?;
                Some(Box::new(else_expr))
            }
        } else {
            None
        };

        Ok(Expr::If {
            cond: Box::new(cond),
            then_branch: Box::new(then_branch),
            else_branch,
        })
    }

    /// Parse expression until we hit a brace (for if conditions)
    fn parse_expression_until_brace(&mut self) -> TranspileResult<Expr> {
        let expr = self.parse_primary_expr()?;
        self.skip_whitespace();

        // Continue with binary operations, but stop at '{'
        if self.peek() == Some('{') {
            return Ok(expr);
        }

        self.parse_binary_continuation(expr)
    }

    /// Parse a let expression
    fn parse_let_expr(&mut self) -> TranspileResult<Expr> {
        self.skip_whitespace();

        let name = self.parse_identifier()?;
        self.skip_whitespace();

        // Optional type annotation
        let ty = if self.try_consume(":") {
            self.skip_whitespace();
            Some(self.parse_type()?)
        } else {
            None
        };
        self.skip_whitespace();

        self.expect('=')?;
        self.skip_whitespace();

        // Parse value, ending at ';' or at expression end
        let value = self.parse_expression_until_semicolon()?;

        // If we have a semicolon, parse the body
        let body = if self.try_consume(";") {
            self.skip_whitespace();
            self.parse_expression()?
        } else {
            // No body, just the let binding as an expression
            Expr::Ident(name.clone())
        };

        Ok(Expr::Let {
            binding: Binding { name, ty },
            value: Box::new(value),
            body: Box::new(body),
        })
    }

    /// Parse expression until semicolon
    fn parse_expression_until_semicolon(&mut self) -> TranspileResult<Expr> {
        let expr = self.parse_primary_expr()?;
        self.skip_whitespace();

        if self.peek() == Some(';') {
            return Ok(expr);
        }

        self.parse_binary_continuation(expr)
    }

    /// Parse forall expression
    fn parse_forall_expr(&mut self) -> TranspileResult<Expr> {
        self.skip_whitespace();

        // Parse |vars|
        self.expect('|')?;
        let vars = self.parse_binding_list()?;
        self.expect('|')?;
        self.skip_whitespace();

        // Parse optional trigger
        let triggers = if self.try_consume("#![auto]") || self.try_consume("#![trigger") {
            // Skip trigger specification for now
            self.skip_until_pattern("]");
            self.try_consume("]");
            Vec::new()
        } else {
            Vec::new()
        };
        self.skip_whitespace();

        // Parse body
        let body = self.parse_expression()?;

        Ok(Expr::Forall {
            vars,
            triggers,
            body: Box::new(body),
        })
    }

    /// Parse exists expression
    fn parse_exists_expr(&mut self) -> TranspileResult<Expr> {
        self.skip_whitespace();

        // Parse |vars|
        self.expect('|')?;
        let vars = self.parse_binding_list()?;
        self.expect('|')?;
        self.skip_whitespace();

        // Parse body
        let body = self.parse_expression()?;

        Ok(Expr::Exists {
            vars,
            body: Box::new(body),
        })
    }

    /// Parse binding list for quantifiers
    fn parse_binding_list(&mut self) -> TranspileResult<Vec<Binding>> {
        let mut bindings = Vec::new();

        loop {
            self.skip_whitespace();
            if self.peek() == Some('|') {
                break;
            }

            let name = self.parse_identifier()?;
            self.skip_whitespace();

            let ty = if self.try_consume(":") {
                self.skip_whitespace();
                Some(self.parse_type()?)
            } else {
                None
            };

            bindings.push(Binding { name, ty });

            self.skip_whitespace();
            if !self.try_consume(",") {
                break;
            }
        }

        Ok(bindings)
    }

    /// Parse match expression
    fn parse_match_expr(&mut self) -> TranspileResult<Expr> {
        self.skip_whitespace();

        // Parse scrutinee
        let scrutinee = self.parse_expression_until_brace()?;
        self.skip_whitespace();

        self.expect('{')?;
        let mut arms = Vec::new();

        loop {
            self.skip_whitespace();
            if self.peek() == Some('}') {
                break;
            }

            // Parse pattern
            let pattern = self.parse_pattern()?;
            self.skip_whitespace();

            // Parse optional guard
            let guard = if self.try_consume("if") {
                self.skip_whitespace();
                Some(self.parse_expression_until_arrow()?)
            } else {
                None
            };
            self.skip_whitespace();

            // Expect =>
            self.expect('=')?;
            self.expect('>')?;
            self.skip_whitespace();

            // Parse body
            let body = self.parse_expression()?;
            self.skip_whitespace();

            arms.push(MatchArm {
                pattern,
                guard,
                body,
            });

            // Optional comma
            self.try_consume(",");
        }

        self.expect('}')?;

        Ok(Expr::Match {
            scrutinee: Box::new(scrutinee),
            arms,
        })
    }

    /// Parse expression until =>
    fn parse_expression_until_arrow(&mut self) -> TranspileResult<Expr> {
        let expr = self.parse_primary_expr()?;
        self.skip_whitespace();

        // Don't parse past the arrow
        if self.peek_str(2) == Some("=>") {
            return Ok(expr);
        }

        self.parse_binary_continuation(expr)
    }

    /// Parse a pattern
    fn parse_pattern(&mut self) -> TranspileResult<Pattern> {
        self.skip_whitespace();

        if self.try_consume("_") {
            return Ok(Pattern::Wildcard);
        }

        // Check for literal patterns
        if self.try_consume("true") {
            return Ok(Pattern::Literal(Literal::Bool(true)));
        }
        if self.try_consume("false") {
            return Ok(Pattern::Literal(Literal::Bool(false)));
        }

        // Parse identifier or path pattern
        let name = self.parse_identifier()?;
        self.skip_whitespace();

        // Check for struct/variant pattern
        if self.peek() == Some('{') {
            self.advance();
            let mut fields = Vec::new();

            loop {
                self.skip_whitespace();
                if self.peek() == Some('}') {
                    break;
                }

                let field_name = self.parse_identifier()?;
                self.skip_whitespace();

                let field_pat = if self.try_consume(":") {
                    self.skip_whitespace();
                    self.parse_pattern()?
                } else {
                    Pattern::Ident(field_name.clone())
                };

                fields.push((field_name, field_pat));

                self.skip_whitespace();
                if !self.try_consume(",") {
                    break;
                }
            }

            self.expect('}')?;
            return Ok(Pattern::Struct {
                name: Path::single(name),
                fields,
            });
        }

        // Check for tuple variant pattern
        if self.peek() == Some('(') {
            self.advance();
            let mut pats = Vec::new();

            loop {
                self.skip_whitespace();
                if self.peek() == Some(')') {
                    break;
                }

                pats.push(self.parse_pattern()?);

                self.skip_whitespace();
                if !self.try_consume(",") {
                    break;
                }
            }

            self.expect(')')?;
            return Ok(Pattern::Variant {
                name: Path::single(name),
                fields: pats,
            });
        }

        Ok(Pattern::Ident(name))
    }

    /// Parse parenthesized expression or tuple
    fn parse_paren_or_tuple_expr(&mut self) -> TranspileResult<Expr> {
        self.expect('(')?;
        self.skip_whitespace();

        if self.peek() == Some(')') {
            self.advance();
            return Ok(Expr::Literal(Literal::Int(0))); // Unit
        }

        let first = self.parse_expression()?;
        self.skip_whitespace();

        // Check if it's a tuple
        if self.try_consume(",") {
            let mut elements = vec![first];
            loop {
                self.skip_whitespace();
                if self.peek() == Some(')') {
                    break;
                }
                elements.push(self.parse_expression()?);
                self.skip_whitespace();
                if !self.try_consume(",") {
                    break;
                }
            }
            self.expect(')')?;
            // Return as struct with unnamed fields (simplified)
            return Ok(Expr::Struct {
                name: Path::single("tuple".to_string()),
                fields: elements
                    .into_iter()
                    .enumerate()
                    .map(|(i, e)| (i.to_string(), e))
                    .collect(),
            });
        }

        self.expect(')')?;
        Ok(first)
    }

    /// Parse a sequence expression
    fn parse_seq_expr(&mut self) -> TranspileResult<Expr> {
        self.skip_whitespace();

        // Check for empty
        if self.try_consume("()") {
            return Ok(Expr::SeqEmpty);
        }

        // Check for bracket
        if self.try_consume("[") || self.peek() == Some('[') {
            if self.peek() == Some('[') {
                self.advance();
            }

            let mut elements = Vec::new();
            loop {
                self.skip_whitespace();
                if self.peek() == Some(']') {
                    break;
                }
                elements.push(self.parse_expression()?);
                self.skip_whitespace();
                if !self.try_consume(",") {
                    break;
                }
            }
            self.expect(']')?;
            return Ok(Expr::SeqLit(elements));
        }

        Ok(Expr::SeqEmpty)
    }

    /// Parse a set expression
    fn parse_set_expr(&mut self) -> TranspileResult<Expr> {
        self.skip_whitespace();

        if self.try_consume("()") || !self.try_consume("[") {
            return Ok(Expr::SetEmpty);
        }

        let mut elements = Vec::new();
        loop {
            self.skip_whitespace();
            if self.peek() == Some(']') {
                break;
            }
            elements.push(self.parse_expression()?);
            self.skip_whitespace();
            if !self.try_consume(",") {
                break;
            }
        }
        self.expect(']')?;
        Ok(Expr::SetLit(elements))
    }

    /// Parse a map expression
    fn parse_map_expr(&mut self) -> TranspileResult<Expr> {
        self.skip_whitespace();

        if self.try_consume("()") || !self.try_consume("[") {
            return Ok(Expr::MapEmpty);
        }

        let mut elements = Vec::new();
        loop {
            self.skip_whitespace();
            if self.peek() == Some(']') {
                break;
            }
            let key = self.parse_expression()?;
            self.skip_whitespace();
            self.expect('=')?;
            self.expect('>')?;
            self.skip_whitespace();
            let value = self.parse_expression()?;
            elements.push((key, value));
            self.skip_whitespace();
            if !self.try_consume(",") {
                break;
            }
        }
        self.expect(']')?;
        Ok(Expr::MapLit(elements))
    }

    /// Parse a number literal
    fn parse_number_literal(&mut self) -> TranspileResult<Expr> {
        let start = self.pos;

        if self.peek() == Some('-') {
            self.advance();
        }

        while let Some(c) = self.peek() {
            if c.is_ascii_digit() || c == '_' {
                self.advance();
            } else {
                break;
            }
        }

        // Skip type suffix if present (i32, nat, etc.)
        while let Some(c) = self.peek() {
            if c.is_alphabetic() || c == '_' {
                self.advance();
            } else {
                break;
            }
        }

        let num_str: String = self.content[start..self.pos]
            .chars()
            .filter(|c| c.is_ascii_digit() || *c == '-')
            .collect();

        let value: i128 = num_str.parse().unwrap_or(0);
        Ok(Expr::Literal(Literal::Int(value)))
    }

    // Helper methods

    /// Skip whitespace and comments
    fn skip_whitespace_and_comments(&mut self) {
        loop {
            self.skip_whitespace();

            // Skip line comments
            if self.peek_str(2) == Some("//") {
                self.skip_until_pattern("\n");
                continue;
            }

            // Skip block comments
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

    /// Skip whitespace
    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    /// Skip until a pattern is found
    fn skip_until_pattern(&mut self, pattern: &str) {
        while self.pos + pattern.len() <= self.content.len() {
            if &self.content[self.pos..self.pos + pattern.len()] == pattern {
                return;
            }
            self.advance();
        }
    }

    /// Skip a non-spec item
    fn skip_item(&mut self) {
        // Skip until we find a closing brace that matches
        let mut depth = 0;

        loop {
            match self.peek() {
                Some('{') => {
                    depth += 1;
                    self.advance();
                }
                Some('}') => {
                    if depth == 0 {
                        break;
                    }
                    depth -= 1;
                    self.advance();
                    if depth == 0 {
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

    /// Peek the current character
    fn peek(&self) -> Option<char> {
        self.content[self.pos..].chars().next()
    }

    /// Peek n characters as string
    fn peek_str(&self, n: usize) -> Option<&str> {
        if self.pos + n <= self.content.len() {
            Some(&self.content[self.pos..self.pos + n])
        } else {
            None
        }
    }

    /// Advance one character
    fn advance(&mut self) {
        if let Some(c) = self.peek() {
            self.pos += c.len_utf8();
        }
    }

    /// Try to consume a string, returning true if successful
    fn try_consume(&mut self, s: &str) -> bool {
        if self.pos + s.len() <= self.content.len()
            && &self.content[self.pos..self.pos + s.len()] == s
        {
            // Make sure it's not part of a longer identifier
            if s.chars().last().is_some_and(|c| c.is_alphanumeric() || c == '_') {
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

    /// Expect a specific character
    fn expect(&mut self, c: char) -> TranspileResult<()> {
        self.skip_whitespace();
        if self.peek() == Some(c) {
            self.advance();
            Ok(())
        } else {
            Err(TranspileError::Parse {
                message: format!(
                    "Expected '{}', found '{:?}'",
                    c,
                    self.peek()
                ),
                span: None,
            })
        }
    }
}

/// Parse Verus source from a file
pub fn parse_file(path: &std::path::Path) -> TranspileResult<Vec<SpecFunction>> {
    let source = std::fs::read_to_string(path)?;
    let parser = VerusParser::new(source).with_file_path(path.display().to_string());
    parser.parse_spec_functions()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parser_creation() {
        let parser = VerusParser::new("// test".to_string());
        let result = parser.parse_spec_functions();
        assert!(result.is_ok());
        assert!(result.unwrap().is_empty());
    }

    #[test]
    fn test_parse_simple_spec_fn() {
        let source = r#"
        verus! {
            pub open spec fn test_fn(x: bool) -> bool {
                x
            }
        }
        "#;

        let parser = VerusParser::new(source.to_string());
        let result = parser.parse_spec_functions();
        assert!(result.is_ok());

        let funcs = result.unwrap();
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "test_fn");
        assert_eq!(funcs[0].params.len(), 1);
        assert_eq!(funcs[0].params[0].name, "x");
    }

    #[test]
    fn test_parse_spec_fn_with_conjunction() {
        let source = r#"
        verus! {
            pub open spec fn NodeInit(s: State, config: Config) -> bool {
                &&& s.value == 0
                &&& s.config == config
            }
        }
        "#;

        let parser = VerusParser::new(source.to_string());
        let result = parser.parse_spec_functions();
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());

        let funcs = result.unwrap();
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "NodeInit");

        // Check that body is a conjunction
        match &funcs[0].body {
            Expr::Conjunction(exprs) => {
                assert_eq!(exprs.len(), 2);
            }
            _ => panic!("Expected conjunction"),
        }
    }

    #[test]
    fn test_parse_spec_fn_with_if() {
        let source = r#"
        verus! {
            pub open spec fn test_if(x: bool) -> bool {
                if x {
                    true
                } else {
                    false
                }
            }
        }
        "#;

        let parser = VerusParser::new(source.to_string());
        let result = parser.parse_spec_functions();
        assert!(result.is_ok());

        let funcs = result.unwrap();
        assert_eq!(funcs.len(), 1);

        match &funcs[0].body {
            Expr::If { cond: _, then_branch: _, else_branch } => {
                assert!(else_branch.is_some());
            }
            _ => panic!("Expected if expression"),
        }
    }

    #[test]
    fn test_parse_spec_fn_with_forall() {
        // Use a simpler forall without chained comparisons
        let source = r#"
        verus! {
            pub open spec fn test_forall(s: Seq<int>) -> bool {
                forall |i| i >= 0 ==> s[i] >= 0
            }
        }
        "#;

        let parser = VerusParser::new(source.to_string());
        let result = parser.parse_spec_functions();
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());

        let funcs = result.unwrap();
        assert_eq!(funcs.len(), 1);

        match &funcs[0].body {
            Expr::Forall { vars, .. } => {
                assert_eq!(vars.len(), 1);
                assert_eq!(vars[0].name, "i");
            }
            _ => panic!("Expected forall expression"),
        }
    }

    #[test]
    fn test_parse_view_operator() {
        let source = r#"
        verus! {
            pub open spec fn test_view(s: CState) -> bool {
                s@ == LState::default()
            }
        }
        "#;

        let parser = VerusParser::new(source.to_string());
        let result = parser.parse_spec_functions();
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());

        let funcs = result.unwrap();
        assert_eq!(funcs.len(), 1);

        // The body should be an equality with a View on the left side
        match &funcs[0].body {
            Expr::Eq(left, _) => {
                assert!(matches!(**left, Expr::View(_)));
            }
            _ => panic!("Expected equality expression"),
        }
    }

    #[test]
    fn test_parse_arrow_operator() {
        let source = r#"
        verus! {
            pub open spec fn test_arrow(msg: Message) -> bool {
                msg->field == 42
            }
        }
        "#;

        let parser = VerusParser::new(source.to_string());
        let result = parser.parse_spec_functions();
        assert!(result.is_ok());

        let funcs = result.unwrap();
        assert_eq!(funcs.len(), 1);

        match &funcs[0].body {
            Expr::Eq(left, _) => {
                assert!(matches!(**left, Expr::Arrow(_, _)));
            }
            _ => panic!("Expected equality with arrow expression"),
        }
    }
}
