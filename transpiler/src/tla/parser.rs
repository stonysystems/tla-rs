//! TLA+ parser implementation.
//!
//! This module parses tokenized TLA+ source into an AST representation.
//! It handles module structure including:
//! - Module headers (`---- MODULE Name ----`)
//! - EXTENDS declarations
//! - CONSTANT and VARIABLE declarations
//! - Operator definitions
//! - Module instances (INSTANCE)

use crate::tla::ast::*;
use crate::tla::tokenizer::{Span, TlaToken, TlaTokenKind, TlaTokenizer, TlaTokenizerError};
use std::fmt;

/// Parser error type
#[derive(Debug, Clone)]
pub struct TlaParseError {
    pub message: String,
    pub span: Option<Span>,
}

impl TlaParseError {
    pub fn new(message: impl Into<String>, span: Option<Span>) -> Self {
        Self {
            message: message.into(),
            span,
        }
    }

    pub fn at_token(message: impl Into<String>, token: &TlaToken) -> Self {
        Self {
            message: message.into(),
            span: Some(token.span),
        }
    }

    pub fn unexpected_token(expected: &str, found: &TlaToken) -> Self {
        Self::at_token(
            format!("Expected {}, found {:?}", expected, found.kind),
            found,
        )
    }

    pub fn unexpected_eof(expected: &str) -> Self {
        Self::new(
            format!("Unexpected end of file, expected {}", expected),
            None,
        )
    }
}

impl fmt::Display for TlaParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(span) = &self.span {
            write!(
                f,
                "Parse error at {}:{}: {}",
                span.start.line, span.start.column, self.message
            )
        } else {
            write!(f, "Parse error: {}", self.message)
        }
    }
}

impl std::error::Error for TlaParseError {}

impl From<TlaTokenizerError> for TlaParseError {
    fn from(err: TlaTokenizerError) -> Self {
        TlaParseError::new(err.message, None)
    }
}

/// Result type for parsing operations
pub type ParseResult<T> = Result<T, TlaParseError>;

/// TLA+ parser
pub struct TlaParser {
    tokens: Vec<TlaToken>,
    pos: usize,
}

impl TlaParser {
    /// Create a new parser from source code
    pub fn new(source: &str) -> ParseResult<Self> {
        let mut tokenizer = TlaTokenizer::new(source);
        let tokens = tokenizer.tokenize()?;
        Ok(Self { tokens, pos: 0 })
    }

    /// Create a parser from pre-tokenized input
    pub fn from_tokens(tokens: Vec<TlaToken>) -> Self {
        Self { tokens, pos: 0 }
    }

    /// Parse a complete TLA+ module
    pub fn parse_module(&mut self) -> ParseResult<TlaModule> {
        // Parse module header: ---- MODULE Name ----
        self.expect(TlaTokenKind::ModuleDashes)?;
        self.expect(TlaTokenKind::Module)?;

        let name = self.expect_ident()?;

        self.expect(TlaTokenKind::ModuleDashes)?;

        let mut module = TlaModule::new(name);

        // Parse module body until we hit the closing dashes or EOF
        while !self.is_at_end() && !self.check(TlaTokenKind::ModuleDashes) {
            self.parse_module_unit(&mut module)?;
        }

        // Consume optional closing dashes (==== or ----)
        if self.check(TlaTokenKind::ModuleDashes) {
            self.advance();
        }

        Ok(module)
    }

    /// Parse a single unit within a module (declaration or definition)
    fn parse_module_unit(&mut self, module: &mut TlaModule) -> ParseResult<()> {
        match self.peek_kind() {
            Some(TlaTokenKind::Extends) => {
                let extends = self.parse_extends()?;
                module.extends.extend(extends);
            }
            Some(TlaTokenKind::Constant) | Some(TlaTokenKind::Constants) => {
                let constants = self.parse_constants()?;
                module.constants.extend(constants);
            }
            Some(TlaTokenKind::Variable) | Some(TlaTokenKind::Variables) => {
                let variables = self.parse_variables()?;
                module.variables.extend(variables);
            }
            Some(TlaTokenKind::Assume) => {
                let assumption = self.parse_assume()?;
                module.assumptions.push(assumption);
            }
            Some(TlaTokenKind::Theorem) => {
                let theorem = self.parse_theorem()?;
                module.theorems.push(theorem);
            }
            Some(TlaTokenKind::Instance) => {
                let instance = self.parse_instance()?;
                module.instances.push(instance);
            }
            Some(TlaTokenKind::Local) => {
                // LOCAL can precede operator definitions or INSTANCE
                self.advance();
                if self.check(TlaTokenKind::Instance) {
                    let mut instance = self.parse_instance()?;
                    instance.is_local = true;
                    module.instances.push(instance);
                } else {
                    let mut op = self.parse_operator_def()?;
                    op.is_local = true;
                    module.operators.push(op);
                }
            }
            Some(TlaTokenKind::Recursive) => {
                // RECURSIVE declaration followed by operator definition
                self.advance();
                // Skip the recursive declaration for now, the actual operator comes later
                // Format: RECURSIVE Op(_, _)
                let _name = self.expect_ident()?;
                if self.check(TlaTokenKind::LParen) {
                    self.advance();
                    while !self.check(TlaTokenKind::RParen) && !self.is_at_end() {
                        self.advance();
                    }
                    self.expect(TlaTokenKind::RParen)?;
                }
            }
            Some(TlaTokenKind::Ident(_)) => {
                // Operator definition: Name == expr or Name(params) == expr
                let op = self.parse_operator_def()?;
                module.operators.push(op);
            }
            Some(TlaTokenKind::ModuleDashes) => {
                // End of module
                return Ok(());
            }
            Some(TlaTokenKind::Eof) => {
                return Ok(());
            }
            Some(other) => {
                return Err(TlaParseError::new(
                    format!("Unexpected token in module: {:?}", other),
                    self.current_span(),
                ));
            }
            None => {
                return Ok(());
            }
        }
        Ok(())
    }

    /// Parse EXTENDS declaration
    fn parse_extends(&mut self) -> ParseResult<Vec<String>> {
        self.expect(TlaTokenKind::Extends)?;

        let mut extends = Vec::new();
        extends.push(self.expect_ident()?);

        while self.check(TlaTokenKind::Comma) {
            self.advance();
            extends.push(self.expect_ident()?);
        }

        Ok(extends)
    }

    /// Parse CONSTANT or CONSTANTS declaration
    fn parse_constants(&mut self) -> ParseResult<Vec<TlaConstantDecl>> {
        // Consume CONSTANT or CONSTANTS
        self.advance();

        let mut constants = Vec::new();
        constants.push(TlaConstantDecl::new(self.expect_ident()?));

        while self.check(TlaTokenKind::Comma) {
            self.advance();
            constants.push(TlaConstantDecl::new(self.expect_ident()?));
        }

        Ok(constants)
    }

    /// Parse VARIABLE or VARIABLES declaration
    fn parse_variables(&mut self) -> ParseResult<Vec<String>> {
        // Consume VARIABLE or VARIABLES
        self.advance();

        let mut variables = Vec::new();
        variables.push(self.expect_ident()?);

        while self.check(TlaTokenKind::Comma) {
            self.advance();
            variables.push(self.expect_ident()?);
        }

        Ok(variables)
    }

    /// Parse ASSUME declaration
    fn parse_assume(&mut self) -> ParseResult<TlaExpr> {
        self.expect(TlaTokenKind::Assume)?;
        // A named assumption -- `ASSUME NAssump == N \in Nat` -- binds a name to
        // the assumed formula so proofs can cite it. The name carries no
        // semantic content for us, so it is consumed and the formula returned.
        if matches!(self.peek_kind(), Some(TlaTokenKind::Ident(_)))
            && matches!(self.peek_ahead_kind(1), Some(TlaTokenKind::DefEq))
        {
            self.advance();
            self.advance();
        }
        self.parse_expr()
    }

    /// Parse THEOREM declaration
    fn parse_theorem(&mut self) -> ParseResult<TlaTheorem> {
        let start_span = self.current_span();
        self.expect(TlaTokenKind::Theorem)?;

        // Optional theorem name
        let name = if self.check_ident() && self.peek_ahead_kind(1) == Some(TlaTokenKind::DefEq) {
            let n = self.expect_ident()?;
            self.expect(TlaTokenKind::DefEq)?;
            Some(n)
        } else {
            None
        };

        let body = self.parse_expr()?;

        Ok(TlaTheorem {
            name,
            body,
            span: start_span,
        })
    }

    /// Parse INSTANCE declaration
    fn parse_instance(&mut self) -> ParseResult<TlaInstance> {
        let start_span = self.current_span();
        self.expect(TlaTokenKind::Instance)?;

        let module_name = self.expect_ident()?;

        // Optional WITH substitutions
        let mut substitutions = Vec::new();
        if self.check_keyword("WITH") {
            self.advance();
            loop {
                let param = self.expect_ident()?;
                self.expect(TlaTokenKind::LeftArrow)?;
                let value = self.parse_expr()?;
                substitutions.push((param, value));

                if !self.check(TlaTokenKind::Comma) {
                    break;
                }
                self.advance();
            }
        }

        Ok(TlaInstance {
            local_name: None,
            module_name,
            substitutions,
            is_local: false,
            span: start_span,
        })
    }

    /// Parse an operator definition: Name == expr or Name(params) == expr
    fn parse_operator_def(&mut self) -> ParseResult<TlaOperator> {
        let start_span = self.current_span();
        let name = self.expect_ident()?;

        // Infix operator definition: `a \prec b == body`. The name parsed above
        // is the left operand, not the operator. Bakery defines `\prec` this
        // way for lexicographic ticket comparison.
        if let Some(TlaTokenKind::InfixOp(op)) = self.peek_kind() {
            self.advance();
            let rhs = self.expect_ident()?;
            self.expect(TlaTokenKind::DefEq)?;
            let body = self.parse_expr()?;
            return Ok(TlaOperator {
                name: format!("\\{}", op),
                params: vec![TlaParam::new(name), TlaParam::new(rhs)],
                body,
                is_recursive: false,
                is_local: false,
                span: start_span,
            });
        }

        // Parse optional parameters
        let params = if self.check(TlaTokenKind::LParen) {
            self.parse_params()?
        } else {
            Vec::new()
        };

        self.expect(TlaTokenKind::DefEq)?;

        let body = self.parse_expr()?;

        Ok(TlaOperator {
            name,
            params,
            body,
            is_recursive: false,
            is_local: false,
            span: start_span,
        })
    }

    /// Parse parameter list
    fn parse_params(&mut self) -> ParseResult<Vec<TlaParam>> {
        self.expect(TlaTokenKind::LParen)?;

        let mut params = Vec::new();

        if !self.check(TlaTokenKind::RParen) {
            params.push(self.parse_param()?);

            while self.check(TlaTokenKind::Comma) {
                self.advance();
                params.push(self.parse_param()?);
            }
        }

        self.expect(TlaTokenKind::RParen)?;
        Ok(params)
    }

    /// Parse a single parameter (may be higher-order)
    fn parse_param(&mut self) -> ParseResult<TlaParam> {
        // Handle underscore for unused params
        if self.check(TlaTokenKind::Underscore) {
            self.advance();
            return Ok(TlaParam::new("_"));
        }

        let name = self.expect_ident()?;

        // Check for higher-order parameter: Op(_, _)
        let arity = if self.check(TlaTokenKind::LParen) {
            self.advance();
            let mut arity = 0;
            if !self.check(TlaTokenKind::RParen) {
                self.expect(TlaTokenKind::Underscore)?;
                arity = 1;
                while self.check(TlaTokenKind::Comma) {
                    self.advance();
                    self.expect(TlaTokenKind::Underscore)?;
                    arity += 1;
                }
            }
            self.expect(TlaTokenKind::RParen)?;
            arity
        } else {
            0
        };

        Ok(if arity > 0 {
            TlaParam::higher_order(name, arity)
        } else {
            TlaParam::new(name)
        })
    }

    /// Parse an expression (simplified for now - will be expanded in T2.3)
    fn parse_expr(&mut self) -> ParseResult<TlaExpr> {
        self.parse_or_expr()
    }

    /// Parse OR expressions (lowest precedence)
    /// Handles both inline `a \/ b` and bullet-list style:
    /// ```tla
    /// \/ expr1
    /// \/ expr2
    /// ```
    fn parse_or_expr(&mut self) -> ParseResult<TlaExpr> {
        // Handle bullet-list disjunction: \/ expr1 \/ expr2 ...
        if self.check(TlaTokenKind::Or) {
            self.advance();
            let mut left = self.parse_and_expr()?;
            while self.check(TlaTokenKind::Or) {
                self.advance();
                let right = self.parse_and_expr()?;
                left = TlaExpr::binop(TlaBinOp::Or, left, right);
            }
            return Ok(left);
        }

        let mut left = self.parse_and_expr()?;

        while self.check(TlaTokenKind::Or) {
            self.advance();
            let right = self.parse_and_expr()?;
            left = TlaExpr::binop(TlaBinOp::Or, left, right);
        }

        Ok(left)
    }

    /// Parse AND expressions
    /// Handles both inline `a /\ b` and bullet-list style:
    /// ```tla
    /// /\ expr1
    /// /\ expr2
    /// ```
    fn parse_and_expr(&mut self) -> ParseResult<TlaExpr> {
        // Handle bullet-list conjunction: /\ expr1 /\ expr2 ...
        if self.check(TlaTokenKind::And) {
            self.advance();
            let mut left = self.parse_implies_expr()?;
            while self.check(TlaTokenKind::And) {
                self.advance();
                let right = self.parse_implies_expr()?;
                left = TlaExpr::binop(TlaBinOp::And, left, right);
            }
            return Ok(left);
        }

        let mut left = self.parse_implies_expr()?;

        while self.check(TlaTokenKind::And) {
            self.advance();
            let right = self.parse_implies_expr()?;
            left = TlaExpr::binop(TlaBinOp::And, left, right);
        }

        Ok(left)
    }

    /// Parse implication expressions (and leads-to)
    fn parse_implies_expr(&mut self) -> ParseResult<TlaExpr> {
        let mut left = self.parse_comparison_expr()?;

        while self.check(TlaTokenKind::Implies)
            || self.check(TlaTokenKind::Iff)
            || self.check(TlaTokenKind::LeadsTo)
        {
            if self.check(TlaTokenKind::LeadsTo) {
                self.advance();
                let right = self.parse_comparison_expr()?;
                left = TlaExpr::LeadsTo {
                    left: Box::new(left),
                    right: Box::new(right),
                };
            } else {
                let op = if self.check(TlaTokenKind::Implies) {
                    TlaBinOp::Implies
                } else {
                    TlaBinOp::Iff
                };
                self.advance();
                let right = self.parse_comparison_expr()?;
                left = TlaExpr::binop(op, left, right);
            }
        }

        Ok(left)
    }

    /// Parse comparison expressions
    fn parse_comparison_expr(&mut self) -> ParseResult<TlaExpr> {
        let mut left = self.parse_set_expr()?;

        loop {
            // Application of an infix operator with no dedicated token kind
            // (`a \prec b`, `s \o t`). It becomes an ordinary operator
            // application named `\prec` / `\o`, which is how the definition
            // side records it too.
            if let Some(TlaTokenKind::InfixOp(op)) = self.peek_kind() {
                self.advance();
                let right = self.parse_set_expr()?;
                left = TlaExpr::OpApply {
                    op: Box::new(TlaExpr::Ident(format!("\\{}", op))),
                    args: vec![left, right],
                };
                continue;
            }

            let op = match self.peek_kind() {
                Some(TlaTokenKind::Eq) => TlaBinOp::Eq,
                Some(TlaTokenKind::Neq) => TlaBinOp::Neq,
                Some(TlaTokenKind::Lt) => TlaBinOp::Lt,
                Some(TlaTokenKind::Gt) => TlaBinOp::Gt,
                Some(TlaTokenKind::Leq) => TlaBinOp::Leq,
                Some(TlaTokenKind::Geq) => TlaBinOp::Geq,
                Some(TlaTokenKind::SetIn) => TlaBinOp::In,
                Some(TlaTokenKind::NotIn) => TlaBinOp::NotIn,
                Some(TlaTokenKind::Subseteq) => TlaBinOp::Subseteq,
                _ => break,
            };
            self.advance();
            let right = self.parse_set_expr()?;
            left = TlaExpr::binop(op, left, right);
        }

        Ok(left)
    }

    /// Parse set operation expressions
    fn parse_set_expr(&mut self) -> ParseResult<TlaExpr> {
        let mut left = self.parse_additive_expr()?;

        loop {
            let op = match self.peek_kind() {
                Some(TlaTokenKind::Cup) => TlaBinOp::Cup,
                Some(TlaTokenKind::Cap) => TlaBinOp::Cap,
                Some(TlaTokenKind::Setminus) => TlaBinOp::Setminus,
                Some(TlaTokenKind::CrossProduct) => TlaBinOp::CrossProd,
                _ => break,
            };
            self.advance();
            let right = self.parse_additive_expr()?;
            left = TlaExpr::binop(op, left, right);
        }

        Ok(left)
    }

    /// Parse additive expressions (including `..` range operator)
    fn parse_additive_expr(&mut self) -> ParseResult<TlaExpr> {
        let mut left = self.parse_multiplicative_expr()?;

        loop {
            let op = match self.peek_kind() {
                Some(TlaTokenKind::Plus) => TlaBinOp::Plus,
                Some(TlaTokenKind::Minus) => TlaBinOp::Minus,
                Some(TlaTokenKind::DotDot) => TlaBinOp::DotDot,
                _ => break,
            };
            self.advance();
            let right = self.parse_multiplicative_expr()?;
            left = TlaExpr::binop(op, left, right);
        }

        Ok(left)
    }

    /// Parse multiplicative expressions
    fn parse_multiplicative_expr(&mut self) -> ParseResult<TlaExpr> {
        let mut left = self.parse_unary_expr()?;

        loop {
            let op = match self.peek_kind() {
                Some(TlaTokenKind::Star) => TlaBinOp::Times,
                Some(TlaTokenKind::Slash) => TlaBinOp::Slash,
                Some(TlaTokenKind::Div) => TlaBinOp::Div,
                Some(TlaTokenKind::Mod) => TlaBinOp::Mod,
                Some(TlaTokenKind::Percent) => TlaBinOp::Mod,
                _ => break,
            };
            self.advance();
            let right = self.parse_unary_expr()?;
            left = TlaExpr::binop(op, left, right);
        }

        Ok(left)
    }

    /// Parse unary expressions
    fn parse_unary_expr(&mut self) -> ParseResult<TlaExpr> {
        match self.peek_kind() {
            Some(TlaTokenKind::Not) => {
                self.advance();
                let operand = self.parse_unary_expr()?;
                Ok(TlaExpr::unary(TlaUnaryOp::Not, operand))
            }
            Some(TlaTokenKind::Minus) => {
                self.advance();
                let operand = self.parse_unary_expr()?;
                Ok(TlaExpr::unary(TlaUnaryOp::Neg, operand))
            }
            Some(TlaTokenKind::Domain) => {
                self.advance();
                let operand = self.parse_unary_expr()?;
                Ok(TlaExpr::unary(TlaUnaryOp::Domain, operand))
            }
            Some(TlaTokenKind::Subset) => {
                self.advance();
                let operand = self.parse_unary_expr()?;
                Ok(TlaExpr::unary(TlaUnaryOp::Subset, operand))
            }
            Some(TlaTokenKind::Union) => {
                self.advance();
                let operand = self.parse_unary_expr()?;
                Ok(TlaExpr::unary(TlaUnaryOp::Union, operand))
            }
            _ => self.parse_postfix_expr(),
        }
    }

    /// Parse postfix expressions (prime, function application, field access)
    fn parse_postfix_expr(&mut self) -> ParseResult<TlaExpr> {
        let expr = self.parse_primary_expr()?;
        self.parse_postfix_chain(expr)
    }

    /// Continue parsing postfix operations from an already-parsed base expression.
    /// Handles `.field`, `[index]`, `(args)`, and `'` (prime).
    fn parse_postfix_chain(&mut self, mut expr: TlaExpr) -> ParseResult<TlaExpr> {
        loop {
            match self.peek_kind() {
                Some(TlaTokenKind::Prime) => {
                    self.advance();
                    expr = TlaExpr::prime(expr);
                }
                Some(TlaTokenKind::LBracket) => {
                    self.advance();
                    let arg = self.parse_expr()?;
                    self.expect(TlaTokenKind::RBracket)?;
                    expr = TlaExpr::FnApply {
                        func: Box::new(expr),
                        arg: Box::new(arg),
                    };
                }
                Some(TlaTokenKind::Dot) => {
                    self.advance();
                    let field = self.expect_ident()?;
                    expr = TlaExpr::RecordAccess {
                        record: Box::new(expr),
                        field,
                    };
                }
                Some(TlaTokenKind::LParen) => {
                    // Operator application
                    self.advance();
                    let mut args = Vec::new();
                    if !self.check(TlaTokenKind::RParen) {
                        args.push(self.parse_expr()?);
                        while self.check(TlaTokenKind::Comma) {
                            self.advance();
                            args.push(self.parse_expr()?);
                        }
                    }
                    self.expect(TlaTokenKind::RParen)?;
                    expr = TlaExpr::OpApply {
                        op: Box::new(expr),
                        args,
                    };
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    /// Parse primary expressions
    fn parse_primary_expr(&mut self) -> ParseResult<TlaExpr> {
        match self.peek_kind() {
            // Identifiers
            Some(TlaTokenKind::Ident(_)) => {
                let name = self.expect_ident()?;
                Ok(TlaExpr::ident(name))
            }
            // Numbers
            Some(TlaTokenKind::Number(_)) => {
                let num_str = self.expect_number()?;
                let number = if num_str.starts_with("0b") {
                    TlaNumber::Binary(num_str)
                } else if num_str.starts_with("0o") {
                    TlaNumber::Octal(num_str)
                } else if num_str.starts_with("0x") {
                    TlaNumber::Hex(num_str)
                } else {
                    TlaNumber::Decimal(num_str)
                };
                Ok(TlaExpr::Number(number))
            }
            // Strings
            Some(TlaTokenKind::String(_)) => {
                let s = self.expect_string()?;
                Ok(TlaExpr::string(s))
            }
            // Booleans
            Some(TlaTokenKind::True) => {
                self.advance();
                Ok(TlaExpr::bool(true))
            }
            Some(TlaTokenKind::False) => {
                self.advance();
                Ok(TlaExpr::bool(false))
            }
            // Parenthesized expression
            Some(TlaTokenKind::LParen) => {
                self.advance();
                let expr = self.parse_expr()?;
                self.expect(TlaTokenKind::RParen)?;
                Ok(expr)
            }
            // `@` inside an EXCEPT update: the value the updated component had
            // before the update, as in `[f EXCEPT ![i] = @ + 1]`. It is only
            // meaningful inside `EXCEPT`, which the parser does not track, so it
            // is carried as the reserved identifier `@` and interpreted by
            // whoever walks the FnExcept node.
            Some(TlaTokenKind::At) => {
                self.advance();
                Ok(TlaExpr::ident("@"))
            }
            // Set enumeration or comprehension
            Some(TlaTokenKind::LBrace) => self.parse_set_expr_inner(),
            // Tuple/sequence
            Some(TlaTokenKind::LAngle) => self.parse_tuple(),
            // Function construction or record
            Some(TlaTokenKind::LBracket) => self.parse_bracket_expr(),
            // IF-THEN-ELSE
            Some(TlaTokenKind::If) => self.parse_if_then_else(),
            // LET-IN
            Some(TlaTokenKind::Let) => self.parse_let_in(),
            // CASE
            Some(TlaTokenKind::Case) => self.parse_case(),
            // Quantifiers
            Some(TlaTokenKind::Forall) => self.parse_forall(),
            Some(TlaTokenKind::Exists) => self.parse_exists(),
            Some(TlaTokenKind::Choose) => self.parse_choose(),
            // UNCHANGED
            Some(TlaTokenKind::Unchanged) => self.parse_unchanged(),
            // ENABLED
            Some(TlaTokenKind::Enabled) => {
                self.advance();
                let operand = self.parse_unary_expr()?;
                Ok(TlaExpr::Enabled(Box::new(operand)))
            }
            // Temporal operators
            Some(TlaTokenKind::Always) => {
                self.advance();
                let operand = self.parse_unary_expr()?;
                Ok(TlaExpr::Always(Box::new(operand)))
            }
            Some(TlaTokenKind::Eventually) => {
                self.advance();
                let operand = self.parse_unary_expr()?;
                Ok(TlaExpr::Eventually(Box::new(operand)))
            }
            // Fairness operators
            Some(TlaTokenKind::WeakFairness(vars)) => {
                self.advance();
                self.expect(TlaTokenKind::LParen)?;
                let action = self.parse_expr()?;
                self.expect(TlaTokenKind::RParen)?;
                Ok(TlaExpr::WeakFairness {
                    vars: Box::new(TlaExpr::ident(vars)),
                    action: Box::new(action),
                })
            }
            Some(TlaTokenKind::StrongFairness(vars)) => {
                self.advance();
                self.expect(TlaTokenKind::LParen)?;
                let action = self.parse_expr()?;
                self.expect(TlaTokenKind::RParen)?;
                Ok(TlaExpr::StrongFairness {
                    vars: Box::new(TlaExpr::ident(vars)),
                    action: Box::new(action),
                })
            }
            Some(kind) => Err(TlaParseError::new(
                format!("Unexpected token in expression: {:?}", kind),
                self.current_span(),
            )),
            None => Err(TlaParseError::unexpected_eof("expression")),
        }
    }

    /// Parse set enumeration or comprehension
    /// Handles:
    /// - Set enumeration: `{1, 2, 3}`
    /// - Set filter: `{x \in S : P(x)}`
    /// - Set map: `{f(x) : x \in S}`
    fn parse_set_expr_inner(&mut self) -> ParseResult<TlaExpr> {
        self.expect(TlaTokenKind::LBrace)?;

        // Empty set
        if self.check(TlaTokenKind::RBrace) {
            self.advance();
            return Ok(TlaExpr::SetEnum(Vec::new()));
        }

        // Parse first element
        let first = self.parse_expr()?;

        // Check for set comprehension patterns
        if self.check(TlaTokenKind::Colon) {
            self.advance();
            let second = self.parse_expr()?;
            self.expect(TlaTokenKind::RBrace)?;

            // Determine if this is filter or map based on structure:
            // Filter: {x \in S : P(x)} - first is "x \in S", second is predicate
            // Map: {f(x) : x \in S} - first is expression, second is "x \in S"
            if let TlaExpr::BinOp {
                op: TlaBinOp::In,
                left,
                right,
            } = &first
            {
                // Filter form: {x \in S : P(x)}
                if let TlaExpr::Ident(var) = left.as_ref() {
                    return Ok(TlaExpr::SetFilter {
                        var: var.clone(),
                        set: right.clone(),
                        filter: Box::new(second),
                    });
                }
            }

            // Check if second is the binding (map form)
            if let TlaExpr::BinOp {
                op: TlaBinOp::In,
                left,
                right,
            } = &second
            {
                // Map form: {f(x) : x \in S}
                if let TlaExpr::Ident(var) = left.as_ref() {
                    return Ok(TlaExpr::SetMap {
                        expr: Box::new(first),
                        var: var.clone(),
                        set: right.clone(),
                    });
                }
            }

            return Err(TlaParseError::new(
                "Invalid set comprehension syntax",
                self.current_span(),
            ));
        }

        // Set enumeration
        let mut elements = vec![first];
        while self.check(TlaTokenKind::Comma) {
            self.advance();
            elements.push(self.parse_expr()?);
        }

        self.expect(TlaTokenKind::RBrace)?;
        Ok(TlaExpr::SetEnum(elements))
    }

    /// Parse tuple: <<a, b, c>>
    fn parse_tuple(&mut self) -> ParseResult<TlaExpr> {
        self.expect(TlaTokenKind::LAngle)?;

        let mut elements = Vec::new();
        if !self.check(TlaTokenKind::RAngle) {
            elements.push(self.parse_expr()?);
            while self.check(TlaTokenKind::Comma) {
                self.advance();
                elements.push(self.parse_expr()?);
            }
        }

        self.expect(TlaTokenKind::RAngle)?;
        let tuple = TlaExpr::Tuple(elements);

        // Angle-bracket action subscript: `<<A>>_vars` is `A /\ ~UNCHANGED vars`
        // (the dual of `[A]_vars`), used to state that a step is not stuttering.
        if self.check(TlaTokenKind::Underscore) {
            self.advance();
            let subscript = self.parse_subscript_vars()?;
            let action = match tuple {
                TlaExpr::Tuple(mut elements) if elements.len() == 1 => elements.remove(0),
                other => other,
            };
            return Ok(TlaExpr::binop(
                TlaBinOp::And,
                action,
                TlaExpr::unary(TlaUnaryOp::Not, TlaExpr::Unchanged(subscript)),
            ));
        }

        Ok(tuple)
    }

    /// Parse bracket expression (function, record, EXCEPT, or function set type)
    fn parse_bracket_expr(&mut self) -> ParseResult<TlaExpr> {
        self.expect(TlaTokenKind::LBracket)?;

        // Check for function construction: [x \in S |-> expr]
        // vs record: [a |-> 1, b |-> 2]
        // vs EXCEPT: [f EXCEPT ![i] = v]
        // vs function set type: [Domain -> Range]

        if self.check(TlaTokenKind::RBracket) {
            self.advance();
            return Ok(TlaExpr::Record(Vec::new()));
        }

        let first_ident = if self.check_ident() {
            let name = self.expect_ident()?;

            // Check what follows the identifier
            if self.check(TlaTokenKind::SetIn) {
                // Function construction: [x \in S |-> expr]
                self.advance();
                let domain = self.parse_expr()?;
                self.expect(TlaTokenKind::MapsTo)?;
                let body = self.parse_expr()?;
                self.expect(TlaTokenKind::RBracket)?;
                return Ok(TlaExpr::FnConstruct {
                    var: name,
                    domain: Box::new(domain),
                    body: Box::new(body),
                });
            } else if self.check(TlaTokenKind::MapsTo) {
                // Record: [a |-> 1, ...]
                self.advance();
                let value = self.parse_expr()?;
                let mut fields = vec![(name, value)];

                while self.check(TlaTokenKind::Comma) {
                    self.advance();
                    let field_name = self.expect_ident()?;
                    self.expect(TlaTokenKind::MapsTo)?;
                    let field_value = self.parse_expr()?;
                    fields.push((field_name, field_value));
                }

                self.expect(TlaTokenKind::RBracket)?;
                return Ok(TlaExpr::Record(fields));
            } else if self.check(TlaTokenKind::Except) {
                // EXCEPT with simple identifier base: [f EXCEPT ![i] = v]
                self.advance();
                let updates = self.parse_except_updates()?;
                self.expect(TlaTokenKind::RBracket)?;
                return Ok(TlaExpr::FnExcept {
                    func: Box::new(TlaExpr::ident(name)),
                    updates,
                });
            } else if self.check(TlaTokenKind::RightArrow) {
                // Function set type: [Domain -> Range]
                self.advance();
                let range = self.parse_expr()?;
                self.expect(TlaTokenKind::RBracket)?;
                return Ok(TlaExpr::FnSet {
                    domain: Box::new(TlaExpr::ident(name)),
                    range: Box::new(range),
                });
            }

            // Otherwise, fall through to general expression parsing
            Some(name)
        } else {
            None
        };

        // Fallback: build full expression with postfix chain (.field, (args), [idx])
        let expr = if let Some(name) = first_ident {
            self.parse_postfix_chain(TlaExpr::ident(name))?
        } else {
            self.parse_expr()?
        };

        // Check if followed by EXCEPT
        if self.check(TlaTokenKind::Except) {
            self.advance();
            let updates = self.parse_except_updates()?;
            self.expect(TlaTokenKind::RBracket)?;
            return Ok(TlaExpr::FnExcept {
                func: Box::new(expr),
                updates,
            });
        }

        // Check if followed by -> (function set type with complex domain)
        if self.check(TlaTokenKind::RightArrow) {
            self.advance();
            let range = self.parse_expr()?;
            self.expect(TlaTokenKind::RBracket)?;
            return Ok(TlaExpr::FnSet {
                domain: Box::new(expr),
                range: Box::new(range),
            });
        }

        self.expect(TlaTokenKind::RBracket)?;

        // Action subscript: `[A]_vars` is by definition `A \/ UNCHANGED vars`.
        // Desugaring here keeps the AST free of a construct that means exactly
        // a disjunction, and makes `Spec == Init /\ [][Next]_vars` parse.
        if self.check(TlaTokenKind::Underscore) {
            self.advance();
            let subscript = self.parse_subscript_vars()?;
            return Ok(TlaExpr::binop(
                TlaBinOp::Or,
                expr,
                TlaExpr::Unchanged(subscript),
            ));
        }

        Ok(expr)
    }

    /// Parse the variable list of an action subscript (`_vars` or `_<<x, y>>`).
    fn parse_subscript_vars(&mut self) -> ParseResult<Vec<TlaExpr>> {
        if self.check(TlaTokenKind::LAngle) {
            match self.parse_tuple()? {
                TlaExpr::Tuple(elements) => Ok(elements),
                other => Ok(vec![other]),
            }
        } else {
            Ok(vec![self.parse_primary_expr()?])
        }
    }

    /// Parse EXCEPT updates
    fn parse_except_updates(&mut self) -> ParseResult<Vec<TlaExceptUpdate>> {
        let mut updates = Vec::new();
        updates.push(self.parse_except_update()?);

        while self.check(TlaTokenKind::Comma) {
            self.advance();
            updates.push(self.parse_except_update()?);
        }

        Ok(updates)
    }

    /// Parse a single EXCEPT update: ![i] = v or !.field = v
    fn parse_except_update(&mut self) -> ParseResult<TlaExceptUpdate> {
        self.expect(TlaTokenKind::Bang)?;

        let mut path = Vec::new();
        loop {
            if self.check(TlaTokenKind::LBracket) {
                self.advance();
                let index = self.parse_expr()?;
                self.expect(TlaTokenKind::RBracket)?;
                path.push(TlaExceptPath::Index(index));
            } else if self.check(TlaTokenKind::Dot) {
                self.advance();
                let field = self.expect_ident()?;
                path.push(TlaExceptPath::Field(field));
            } else {
                break;
            }
        }

        self.expect(TlaTokenKind::Eq)?;
        let value = self.parse_expr()?;

        Ok(TlaExceptUpdate { path, value })
    }

    /// Parse IF-THEN-ELSE expression
    fn parse_if_then_else(&mut self) -> ParseResult<TlaExpr> {
        self.expect(TlaTokenKind::If)?;
        let cond = self.parse_expr()?;
        self.expect(TlaTokenKind::Then)?;
        let then_expr = self.parse_expr()?;
        self.expect(TlaTokenKind::Else)?;
        // Parse ELSE with implication-level precedence so top-level conjunction/disjunction
        // outside the IF expression is not absorbed into the ELSE branch.
        let else_expr = self.parse_implies_expr()?;

        Ok(TlaExpr::IfThenElse {
            cond: Box::new(cond),
            then_expr: Box::new(then_expr),
            else_expr: Box::new(else_expr),
        })
    }

    /// Parse LET-IN expression
    fn parse_let_in(&mut self) -> ParseResult<TlaExpr> {
        self.expect(TlaTokenKind::Let)?;

        let mut defs = Vec::new();
        defs.push(self.parse_operator_def()?);

        // Multiple definitions before IN
        while !self.check(TlaTokenKind::KwIn) && self.check_ident() {
            defs.push(self.parse_operator_def()?);
        }

        self.expect(TlaTokenKind::KwIn)?;
        let body = self.parse_expr()?;

        Ok(TlaExpr::LetIn {
            defs,
            body: Box::new(body),
        })
    }

    /// Parse CASE expression
    fn parse_case(&mut self) -> ParseResult<TlaExpr> {
        self.expect(TlaTokenKind::Case)?;

        let mut arms = Vec::new();
        let cond = self.parse_expr()?;
        self.expect(TlaTokenKind::RightArrow)?;
        let result = self.parse_expr()?;
        arms.push((cond, result));

        // Parse additional arms
        while self.check(TlaTokenKind::LBracket)
            && self.peek_ahead_kind(1) == Some(TlaTokenKind::RBracket)
        {
            self.advance(); // [
            self.advance(); // ]
            let cond = self.parse_expr()?;
            self.expect(TlaTokenKind::RightArrow)?;
            let result = self.parse_expr()?;
            arms.push((cond, result));
        }

        // Parse optional OTHER
        let other = if self.check(TlaTokenKind::LBracket)
            && self.peek_ahead_kind(1) == Some(TlaTokenKind::RBracket)
        {
            self.advance(); // [
            self.advance(); // ]
            self.expect(TlaTokenKind::Other)?;
            self.expect(TlaTokenKind::RightArrow)?;
            Some(Box::new(self.parse_expr()?))
        } else {
            None
        };

        Ok(TlaExpr::Case { arms, other })
    }

    /// Parse FORALL expression
    fn parse_forall(&mut self) -> ParseResult<TlaExpr> {
        self.expect(TlaTokenKind::Forall)?;
        let vars = self.parse_quant_bounds()?;
        self.expect(TlaTokenKind::Colon)?;
        let body = self.parse_expr()?;

        Ok(TlaExpr::Forall {
            vars,
            body: Box::new(body),
        })
    }

    /// Parse EXISTS expression
    fn parse_exists(&mut self) -> ParseResult<TlaExpr> {
        self.expect(TlaTokenKind::Exists)?;
        let vars = self.parse_quant_bounds()?;
        self.expect(TlaTokenKind::Colon)?;
        let body = self.parse_expr()?;

        Ok(TlaExpr::Exists {
            vars,
            body: Box::new(body),
        })
    }

    /// Parse CHOOSE expression
    fn parse_choose(&mut self) -> ParseResult<TlaExpr> {
        self.expect(TlaTokenKind::Choose)?;
        let var = self.expect_ident()?;

        let set = if self.check(TlaTokenKind::SetIn) {
            self.advance();
            Some(Box::new(self.parse_expr()?))
        } else {
            None
        };

        self.expect(TlaTokenKind::Colon)?;
        let body = self.parse_expr()?;

        Ok(TlaExpr::Choose {
            var,
            set,
            body: Box::new(body),
        })
    }

    /// Parse quantifier bounds
    fn parse_quant_bounds(&mut self) -> ParseResult<Vec<TlaQuantBound>> {
        let mut bounds = Vec::new();
        // TLA+ allows `x1, x2, ..., xn \in S` where all variables share the same set.
        // Also allows multiple groups: `x \in S1, y \in S2` or mixed `x, y \in S, z \in T`.
        // We collect comma-separated identifiers, then when we see `\in`, assign the set to all.
        loop {
            let mut group_vars: Vec<String> = vec![self.expect_ident()?];
            // Collect comma-separated variable names until we hit `\in` or `:`
            while self.check(TlaTokenKind::Comma) {
                // Peek ahead: if the token after comma and ident is `\in`, it's still same group.
                // But if we see `:`, the group is done. We need to be careful.
                // In TLA+, `\A x, y \in S : P` means both x,y in S.
                // `\A x \in S, y \in T : P` means separate bindings.
                // So we greedily collect idents until we see `\in`.
                let saved_pos = self.pos;
                self.advance(); // consume comma
                if self.peek_kind() == Some(TlaTokenKind::Colon) {
                    // No more variables — the colon starts the body
                    self.pos = saved_pos;
                    break;
                }
                let next_var = self.expect_ident()?;
                group_vars.push(next_var);
            }

            if self.check(TlaTokenKind::SetIn) {
                self.advance();
                let set = self.parse_set_expr()?;
                for var in group_vars {
                    bounds.push(TlaQuantBound {
                        var,
                        set: Some(set.clone()),
                    });
                }
            } else {
                // No set binding for this group
                for var in group_vars {
                    bounds.push(TlaQuantBound { var, set: None });
                }
            }

            // Check if there's another binding group after comma
            if self.check(TlaTokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }

        Ok(bounds)
    }

    /// Parse UNCHANGED expression
    fn parse_unchanged(&mut self) -> ParseResult<TlaExpr> {
        self.expect(TlaTokenKind::Unchanged)?;

        // UNCHANGED can be followed by a single variable or <<vars>>
        if self.check(TlaTokenKind::LAngle) {
            self.advance();
            let mut vars = Vec::new();
            if !self.check(TlaTokenKind::RAngle) {
                vars.push(self.parse_expr()?);
                while self.check(TlaTokenKind::Comma) {
                    self.advance();
                    vars.push(self.parse_expr()?);
                }
            }
            self.expect(TlaTokenKind::RAngle)?;
            Ok(TlaExpr::Unchanged(vars))
        } else {
            let var = self.parse_primary_expr()?;
            Ok(TlaExpr::Unchanged(vec![var]))
        }
    }

    // =========== Helper methods ===========

    /// Check if we're at the end of tokens
    fn is_at_end(&self) -> bool {
        self.pos >= self.tokens.len() || self.peek_kind() == Some(TlaTokenKind::Eof)
    }

    /// Get current token
    fn peek(&self) -> Option<&TlaToken> {
        self.tokens.get(self.pos)
    }

    /// Get current token kind
    fn peek_kind(&self) -> Option<TlaTokenKind> {
        self.peek().map(|t| t.kind.clone())
    }

    /// Look ahead n tokens
    fn peek_ahead_kind(&self, n: usize) -> Option<TlaTokenKind> {
        self.tokens.get(self.pos + n).map(|t| t.kind.clone())
    }

    /// Get current span
    fn current_span(&self) -> Option<Span> {
        self.peek().map(|t| t.span)
    }

    /// Check if current token matches
    fn check(&self, kind: TlaTokenKind) -> bool {
        self.peek_kind() == Some(kind)
    }

    /// Check if current token is an identifier
    fn check_ident(&self) -> bool {
        matches!(self.peek_kind(), Some(TlaTokenKind::Ident(_)))
    }

    /// Check for a keyword-like identifier
    fn check_keyword(&self, kw: &str) -> bool {
        matches!(self.peek_kind(), Some(TlaTokenKind::Ident(ref s)) if s == kw)
    }

    /// Advance to next token
    fn advance(&mut self) -> Option<&TlaToken> {
        if !self.is_at_end() {
            self.pos += 1;
        }
        self.tokens.get(self.pos - 1)
    }

    /// Expect a specific token kind
    fn expect(&mut self, kind: TlaTokenKind) -> ParseResult<()> {
        if self.check(kind.clone()) {
            self.advance();
            Ok(())
        } else if let Some(token) = self.peek() {
            Err(TlaParseError::unexpected_token(
                &format!("{:?}", kind),
                token,
            ))
        } else {
            Err(TlaParseError::unexpected_eof(&format!("{:?}", kind)))
        }
    }

    /// Expect and return an identifier
    fn expect_ident(&mut self) -> ParseResult<String> {
        if let Some(TlaTokenKind::Ident(name)) = self.peek_kind() {
            self.advance();
            Ok(name)
        } else if let Some(token) = self.peek() {
            Err(TlaParseError::unexpected_token("identifier", token))
        } else {
            Err(TlaParseError::unexpected_eof("identifier"))
        }
    }

    /// Expect and return a number
    fn expect_number(&mut self) -> ParseResult<String> {
        if let Some(TlaTokenKind::Number(num)) = self.peek_kind() {
            self.advance();
            Ok(num)
        } else if let Some(token) = self.peek() {
            Err(TlaParseError::unexpected_token("number", token))
        } else {
            Err(TlaParseError::unexpected_eof("number"))
        }
    }

    /// Expect and return a string
    fn expect_string(&mut self) -> ParseResult<String> {
        if let Some(TlaTokenKind::String(s)) = self.peek_kind() {
            self.advance();
            Ok(s)
        } else if let Some(token) = self.peek() {
            Err(TlaParseError::unexpected_token("string", token))
        } else {
            Err(TlaParseError::unexpected_eof("string"))
        }
    }
}

/// Convenience function to parse a module from source
pub fn parse_module(source: &str) -> ParseResult<TlaModule> {
    let mut parser = TlaParser::new(source)?;
    parser.parse_module()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_empty_module() {
        let source = r"
            ---- MODULE Empty ----
            ====
        ";
        let module = parse_module(source).unwrap();
        assert_eq!(module.name, "Empty");
        assert!(module.extends.is_empty());
        assert!(module.variables.is_empty());
    }

    #[test]
    fn test_parse_extends() {
        let source = r"
            ---- MODULE Test ----
            EXTENDS Naturals, Sequences
            ====
        ";
        let module = parse_module(source).unwrap();
        assert_eq!(module.name, "Test");
        assert_eq!(module.extends, vec!["Naturals", "Sequences"]);
    }

    #[test]
    fn test_parse_constants() {
        let source = r"
            ---- MODULE Test ----
            CONSTANT N
            CONSTANTS A, B, C
            ====
        ";
        let module = parse_module(source).unwrap();
        assert_eq!(module.constants.len(), 4);
        assert_eq!(module.constants[0].name, "N");
        assert_eq!(module.constants[1].name, "A");
    }

    #[test]
    fn test_parse_variables() {
        let source = r"
            ---- MODULE Test ----
            VARIABLE x
            VARIABLES a, b, c
            ====
        ";
        let module = parse_module(source).unwrap();
        assert_eq!(module.variables, vec!["x", "a", "b", "c"]);
    }

    #[test]
    fn test_parse_simple_operator() {
        let source = r"
            ---- MODULE Test ----
            Init == x = 0
            ====
        ";
        let module = parse_module(source).unwrap();
        assert_eq!(module.operators.len(), 1);
        assert_eq!(module.operators[0].name, "Init");
    }

    #[test]
    fn test_parse_operator_with_params() {
        let source = r"
            ---- MODULE Test ----
            Add(a, b) == a + b
            ====
        ";
        let module = parse_module(source).unwrap();
        assert_eq!(module.operators.len(), 1);
        assert_eq!(module.operators[0].name, "Add");
        assert_eq!(module.operators[0].params.len(), 2);
    }

    #[test]
    fn test_parse_if_then_else() {
        let source = r"
            ---- MODULE Test ----
            Max(a, b) == IF a > b THEN a ELSE b
            ====
        ";
        let module = parse_module(source).unwrap();
        let op = &module.operators[0];
        assert!(matches!(op.body, TlaExpr::IfThenElse { .. }));
    }

    #[test]
    fn test_parse_if_else_does_not_absorb_following_bullet_conjunct() {
        let source = r"
            ---- MODULE Test ----
            Foo(s, s_) ==
                /\ s_.x = IF s.x = 0 THEN 1 ELSE s.x
                /\ s_.y = s.y
            ====
        ";
        let module = parse_module(source).unwrap();
        let op = &module.operators[0];

        let TlaExpr::BinOp {
            op: TlaBinOp::And,
            left,
            right,
        } = &op.body
        else {
            panic!("Expected top-level conjunction, got {:?}", op.body);
        };

        let TlaExpr::BinOp {
            op: TlaBinOp::Eq,
            right: first_rhs,
            ..
        } = left.as_ref()
        else {
            panic!("Expected first conjunct to be assignment, got {:?}", left);
        };
        let TlaExpr::IfThenElse { else_expr, .. } = first_rhs.as_ref() else {
            panic!(
                "Expected IF expression on first conjunct rhs, got {:?}",
                first_rhs
            );
        };
        assert!(
            !matches!(
                else_expr.as_ref(),
                TlaExpr::BinOp {
                    op: TlaBinOp::And,
                    ..
                }
            ),
            "ELSE branch should not absorb following /\\ conjunct: {:?}",
            else_expr
        );

        assert!(
            matches!(
                right.as_ref(),
                TlaExpr::BinOp {
                    op: TlaBinOp::Eq,
                    ..
                }
            ),
            "Expected second conjunct to remain separate assignment, got {:?}",
            right
        );
    }

    #[test]
    fn test_parse_quantifier() {
        let source = r"
            ---- MODULE Test ----
            AllPositive(S) == \A x \in S : x > 0
            ====
        ";
        let module = parse_module(source).unwrap();
        let op = &module.operators[0];
        assert!(matches!(op.body, TlaExpr::Forall { .. }));
    }

    #[test]
    fn test_parse_set_enum() {
        let source = r"
            ---- MODULE Test ----
            S == {1, 2, 3}
            ====
        ";
        let module = parse_module(source).unwrap();
        let op = &module.operators[0];
        match &op.body {
            TlaExpr::SetEnum(elements) => assert_eq!(elements.len(), 3),
            _ => panic!("Expected SetEnum"),
        }
    }

    #[test]
    fn test_parse_tuple() {
        let source = r"
            ---- MODULE Test ----
            T == <<1, 2, 3>>
            ====
        ";
        let module = parse_module(source).unwrap();
        let op = &module.operators[0];
        match &op.body {
            TlaExpr::Tuple(elements) => assert_eq!(elements.len(), 3),
            _ => panic!("Expected Tuple"),
        }
    }

    #[test]
    fn test_parse_record() {
        let source = r"
            ---- MODULE Test ----
            R == [a |-> 1, b |-> 2]
            ====
        ";
        let module = parse_module(source).unwrap();
        let op = &module.operators[0];
        match &op.body {
            TlaExpr::Record(fields) => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0, "a");
            }
            _ => panic!("Expected Record"),
        }
    }

    #[test]
    fn test_parse_function_construct() {
        let source = r"
            ---- MODULE Test ----
            F == [x \in S |-> x + 1]
            ====
        ";
        let module = parse_module(source).unwrap();
        let op = &module.operators[0];
        match &op.body {
            TlaExpr::FnConstruct { var, .. } => assert_eq!(var, "x"),
            _ => panic!("Expected FnConstruct"),
        }
    }

    #[test]
    fn test_parse_primed_variable() {
        let source = r"
            ---- MODULE Test ----
            Next == x' = x + 1
            ====
        ";
        let module = parse_module(source).unwrap();
        let op = &module.operators[0];
        match &op.body {
            TlaExpr::BinOp { left, .. } => {
                assert!(matches!(**left, TlaExpr::Prime(_)));
            }
            _ => panic!("Expected BinOp with Prime"),
        }
    }

    #[test]
    fn test_parse_unchanged() {
        let source = r"
            ---- MODULE Test ----
            Stutter == UNCHANGED <<x, y>>
            ====
        ";
        let module = parse_module(source).unwrap();
        let op = &module.operators[0];
        match &op.body {
            TlaExpr::Unchanged(vars) => assert_eq!(vars.len(), 2),
            _ => panic!("Expected Unchanged"),
        }
    }

    #[test]
    fn test_parse_leads_to() {
        let source = r"
            ---- MODULE Test ----
            Liveness == P ~> Q
            ====
        ";
        let module = parse_module(source).unwrap();
        let op = &module.operators[0];
        match &op.body {
            TlaExpr::LeadsTo { left, right } => {
                assert!(matches!(**left, TlaExpr::Ident(_)));
                assert!(matches!(**right, TlaExpr::Ident(_)));
            }
            _ => panic!("Expected LeadsTo"),
        }
    }

    #[test]
    fn test_parse_set_map() {
        let source = r"
            ---- MODULE Test ----
            Doubles == {x * 2 : x \in S}
            ====
        ";
        let module = parse_module(source).unwrap();
        let op = &module.operators[0];
        match &op.body {
            TlaExpr::SetMap { var, .. } => assert_eq!(var, "x"),
            _ => panic!("Expected SetMap, got {:?}", op.body),
        }
    }

    #[test]
    fn test_parse_weak_fairness() {
        let source = r"
            ---- MODULE Test ----
            Fair == WF_vars(Next)
            ====
        ";
        let module = parse_module(source).unwrap();
        let op = &module.operators[0];
        match &op.body {
            TlaExpr::WeakFairness { vars, action } => {
                if let TlaExpr::Ident(v) = vars.as_ref() {
                    assert_eq!(v, "vars");
                } else {
                    panic!("Expected Ident for vars");
                }
                assert!(matches!(**action, TlaExpr::Ident(_)));
            }
            _ => panic!("Expected WeakFairness, got {:?}", op.body),
        }
    }

    #[test]
    fn test_parse_strong_fairness() {
        let source = r"
            ---- MODULE Test ----
            Fair == SF_x(Action)
            ====
        ";
        let module = parse_module(source).unwrap();
        let op = &module.operators[0];
        match &op.body {
            TlaExpr::StrongFairness { vars, action } => {
                if let TlaExpr::Ident(v) = vars.as_ref() {
                    assert_eq!(v, "x");
                } else {
                    panic!("Expected Ident for vars");
                }
                assert!(matches!(**action, TlaExpr::Ident(_)));
            }
            _ => panic!("Expected StrongFairness, got {:?}", op.body),
        }
    }

    #[test]
    fn test_parse_temporal_spec() {
        let source = r"
            ---- MODULE Test ----
            Spec == Init /\ []Next /\ WF_vars(Next)
            ====
        ";
        let module = parse_module(source).unwrap();
        assert_eq!(module.operators.len(), 1);
        // Just verify it parses without error - complex expression structure
    }

    #[test]
    fn test_parse_bullet_conjunction() {
        // Bullet-list conjunction style: /\ at the start of the operator body
        let source = r#"
            ---- MODULE Test ----
            Init(s) ==
                /\ s.x = 0
                /\ s.y = 1
                /\ s.z = TRUE
            ====
        "#;
        let module = parse_module(source).unwrap();
        assert_eq!(module.operators.len(), 1);
        let op = &module.operators[0];
        assert_eq!(op.name, "Init");
        // Body should be And(And(s.x = 0, s.y = 1), s.z = TRUE) — left-associative
        match &op.body {
            TlaExpr::BinOp {
                op: TlaBinOp::And, ..
            } => {} // OK
            other => panic!("Expected conjunction, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_bullet_disjunction() {
        // Bullet-list disjunction style: \/ at the start of the operator body
        let source = r#"
            ---- MODULE Test ----
            Next(s, s_) ==
                \/ Action1(s, s_)
                \/ Action2(s, s_)
                \/ Action3(s, s_)
            ====
        "#;
        let module = parse_module(source).unwrap();
        assert_eq!(module.operators.len(), 1);
        let op = &module.operators[0];
        assert_eq!(op.name, "Next");
        match &op.body {
            TlaExpr::BinOp {
                op: TlaBinOp::Or, ..
            } => {} // OK
            other => panic!("Expected disjunction, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_bullet_conjunction_with_disjunction() {
        // Nested: bullet-list disjunction containing inline conjunctions
        let source = r#"
            ---- MODULE Test ----
            Next(s, s_, c) ==
                \/ s.x = 0 /\ s_.x = 1
                \/ s.x = 1 /\ s_.x = 0
            ====
        "#;
        let module = parse_module(source).unwrap();
        assert_eq!(module.operators.len(), 1);
        // Top level should be Or
        match &module.operators[0].body {
            TlaExpr::BinOp {
                op: TlaBinOp::Or, ..
            } => {} // OK
            other => panic!("Expected Or at top level, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_bullet_conjunction_with_exists() {
        // Bullet-list disjunction with existential quantifier (generated by verus2tla)
        let source = r#"
            ---- MODULE Test ----
            Next(s, s_, c) ==
                \/ Action1(s, s_, c)
                \/ \E val \in Int : Action2(s, s_, c, val)
            ====
        "#;
        let module = parse_module(source).unwrap();
        assert_eq!(module.operators.len(), 1);
        match &module.operators[0].body {
            TlaExpr::BinOp {
                op: TlaBinOp::Or, ..
            } => {} // OK
            other => panic!("Expected Or, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_verus2tla_output_format() {
        // Full module in the format generated by verus2tla (the format that was failing)
        let source = r#"
            ---- MODULE test ----
            EXTENDS Integers, Sequences, FiniteSets
            CONSTANTS State, Constants

            Init(s, c) ==
                /\ s.role = Primary
                /\ s.count = 0
                /\ s.active = TRUE

            Step(s, s_, c) ==
                /\ s.role = Primary
                /\ s.active = TRUE
                /\ s_.role = s.role
                /\ s_.count = s.count + 1
                /\ s_.active = s.active

            Next(s, s_, c) ==
                \/ Step(s, s_, c)

            ====
        "#;
        let module = parse_module(source).unwrap();
        assert_eq!(module.operators.len(), 3);
        assert_eq!(module.operators[0].name, "Init");
        assert_eq!(module.operators[1].name, "Step");
        assert_eq!(module.operators[2].name, "Next");
    }

    #[test]
    fn test_parse_single_bullet_conjunction() {
        // Edge case: single bullet conjunction item
        let source = r#"
            ---- MODULE Test ----
            Op(s) ==
                /\ s.x = 0
            ====
        "#;
        let module = parse_module(source).unwrap();
        assert_eq!(module.operators.len(), 1);
        // Single conjunction item should just be the expression (s.x = 0)
        match &module.operators[0].body {
            TlaExpr::BinOp {
                op: TlaBinOp::Eq, ..
            } => {} // OK - just the comparison
            other => panic!("Expected equality, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_except_with_dotted_base() {
        // [s.field EXCEPT ![key] = val] - dotted expression as EXCEPT base
        let source = r#"
            ---- MODULE Test ----
            Op(s, s_, key, val) == s_ = [s.field EXCEPT ![key] = val]
            ====
        "#;
        let module = parse_module(source).unwrap();
        assert_eq!(module.operators.len(), 1);
        // Should parse successfully with FnExcept whose func is a RecordAccess
        match &module.operators[0].body {
            TlaExpr::BinOp {
                op: TlaBinOp::Eq,
                right,
                ..
            } => match right.as_ref() {
                TlaExpr::FnExcept { func, updates } => {
                    match func.as_ref() {
                        TlaExpr::RecordAccess { field, .. } => {
                            assert_eq!(field, "field");
                        }
                        other => panic!("Expected RecordAccess, got {:?}", other),
                    }
                    assert_eq!(updates.len(), 1);
                }
                other => panic!("Expected FnExcept, got {:?}", other),
            },
            other => panic!("Expected BinOp Eq, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_except_with_function_call_base() {
        // [f(x) EXCEPT ![i] = v] - function call as EXCEPT base
        let source = r#"
            ---- MODULE Test ----
            Op(f, x, i, v) == [f(x) EXCEPT ![i] = v]
            ====
        "#;
        let module = parse_module(source).unwrap();
        assert_eq!(module.operators.len(), 1);
        match &module.operators[0].body {
            TlaExpr::FnExcept { func, updates } => {
                match func.as_ref() {
                    TlaExpr::OpApply { args, .. } => {
                        assert_eq!(args.len(), 1);
                    }
                    other => panic!("Expected OpApply, got {:?}", other),
                }
                assert_eq!(updates.len(), 1);
            }
            other => panic!("Expected FnExcept, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_function_set_type() {
        // [Domain -> Range] - function set type notation
        let source = r#"
            ---- MODULE Test ----
            FuncSet == [Int -> Int]
            ====
        "#;
        let module = parse_module(source).unwrap();
        assert_eq!(module.operators.len(), 1);
        match &module.operators[0].body {
            TlaExpr::FnSet { domain, range } => match (domain.as_ref(), range.as_ref()) {
                (TlaExpr::Ident(d), TlaExpr::Ident(r)) => {
                    assert_eq!(d, "Int");
                    assert_eq!(r, "Int");
                }
                other => panic!("Expected Ident/Ident, got {:?}", other),
            },
            other => panic!("Expected FnSet, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_function_set_in_record() {
        // [field |-> [u64 -> u64]] - function set type nested in a record
        let source = r#"
            ---- MODULE Test ----
            RecordType == [match_index |-> [u64 -> u64], next_index |-> [u64 -> u64]]
            ====
        "#;
        let module = parse_module(source).unwrap();
        assert_eq!(module.operators.len(), 1);
        match &module.operators[0].body {
            TlaExpr::Record(fields) => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0, "match_index");
                match &fields[0].1 {
                    TlaExpr::FnSet { .. } => {}
                    other => panic!("Expected FnSet, got {:?}", other),
                }
            }
            other => panic!("Expected Record, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_named_assume() {
        // TLAPS-style named assumption: the name is bound for proof citation
        // and carries no semantic content for us.
        let source = r#"
            ---- MODULE Test ----
            CONSTANT N
            ASSUME NAssump == (N \in Nat) /\ (N > 0)
            ====
        "#;
        let module = parse_module(source).unwrap();
        assert_eq!(module.assumptions.len(), 1);
        match &module.assumptions[0] {
            TlaExpr::BinOp {
                op: TlaBinOp::And, ..
            } => {}
            other => panic!("Expected the assumed conjunction, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_infix_operator_definition_and_application() {
        // Bakery defines \prec as lexicographic less-than on pairs.
        let source = r#"
            ---- MODULE Test ----
            a \prec b == \/ a[1] < b[1]
                         \/ /\ a[1] = b[1]
                            /\ a[2] < b[2]
            Cmp == <<1, 2>> \prec <<1, 3>>
            ====
        "#;
        let module = parse_module(source).unwrap();
        let def = module
            .operators
            .iter()
            .find(|o| o.name == "\\prec")
            .expect("infix definition should be recorded under its operator name");
        assert_eq!(
            def.params.len(),
            2,
            "infix def takes both operands as params"
        );
        assert_eq!(def.params[0].name, "a");
        assert_eq!(def.params[1].name, "b");

        let cmp = module.operators.iter().find(|o| o.name == "Cmp").unwrap();
        match &cmp.body {
            TlaExpr::OpApply { op, args } => {
                assert_eq!(**op, TlaExpr::Ident("\\prec".to_string()));
                assert_eq!(args.len(), 2);
            }
            other => panic!("Expected an infix application, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_union_and_intersect_aliases() {
        // \union / \intersect are the ASCII long names for \cup / \cap.
        let source = r#"
            ---- MODULE Test ----
            A == S \union {x}
            B == S \intersect T
            ====
        "#;
        let module = parse_module(source).unwrap();
        match &module.operators[0].body {
            TlaExpr::BinOp { op, .. } => assert_eq!(*op, TlaBinOp::Cup),
            other => panic!("Expected Cup, got {:?}", other),
        }
        match &module.operators[1].body {
            TlaExpr::BinOp { op, .. } => assert_eq!(*op, TlaBinOp::Cap),
            other => panic!("Expected Cap, got {:?}", other),
        }
    }

    #[test]
    fn test_backslash_o_is_concat_not_octal_without_digits() {
        // `\o` introduces an octal literal only when a digit follows it;
        // otherwise it is sequence concatenation.
        let source = r#"
            ---- MODULE Test ----
            Cat == s \o t
            Oct == \o777
            ====
        "#;
        let module = parse_module(source).unwrap();
        match &module.operators[0].body {
            TlaExpr::OpApply { op, args } => {
                assert_eq!(**op, TlaExpr::Ident("\\o".to_string()));
                assert_eq!(args.len(), 2);
            }
            other => panic!("Expected concat application, got {:?}", other),
        }
        match &module.operators[1].body {
            TlaExpr::Number(_) => {}
            other => panic!("Expected an octal literal, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_except_with_at() {
        // `@` is the pre-update value of the component being updated.
        let source = r#"
            ---- MODULE Test ----
            Bump == [clock EXCEPT ![p] = @ + 1]
            ====
        "#;
        let module = parse_module(source).unwrap();
        match &module.operators[0].body {
            TlaExpr::FnExcept { updates, .. } => {
                assert_eq!(updates.len(), 1);
                match &updates[0].value {
                    TlaExpr::BinOp { op, left, .. } => {
                        assert_eq!(*op, TlaBinOp::Plus);
                        assert_eq!(**left, TlaExpr::Ident("@".to_string()));
                    }
                    other => panic!("Expected `@ + 1`, got {:?}", other),
                }
            }
            other => panic!("Expected FnExcept, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_except_multi_index_path() {
        // Pairwise-FIFO networks index twice: `![q][p]`.
        let source = r#"
            ---- MODULE Test ----
            Recv == [network EXCEPT ![q][p] = Tail(@), ![p][q] = Append(@, m)]
            ====
        "#;
        let module = parse_module(source).unwrap();
        match &module.operators[0].body {
            TlaExpr::FnExcept { updates, .. } => {
                assert_eq!(updates.len(), 2, "both EXCEPT updates are kept");
                assert_eq!(updates[0].path.len(), 2, "![q][p] is a two-step path");
            }
            other => panic!("Expected FnExcept, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_action_subscript_desugars_to_its_meaning() {
        // `[A]_vars` IS `A \/ UNCHANGED vars` in TLA+, so the parser stores that
        // rather than inventing a node for it.
        let source = r#"
            ---- MODULE Test ----
            Spec == Init /\ [][Next]_vars
            ====
        "#;
        let module = parse_module(source).unwrap();
        let body = &module.operators[0].body;
        let TlaExpr::BinOp { op, right, .. } = body else {
            panic!("Expected a conjunction, got {:?}", body)
        };
        assert_eq!(*op, TlaBinOp::And);
        let TlaExpr::Always(inner) = &**right else {
            panic!(
                "Expected [] applied to the subscripted action, got {:?}",
                right
            )
        };
        match &**inner {
            TlaExpr::BinOp { op, left, right } => {
                assert_eq!(*op, TlaBinOp::Or);
                assert_eq!(**left, TlaExpr::Ident("Next".to_string()));
                assert!(matches!(**right, TlaExpr::Unchanged(_)));
            }
            other => panic!("Expected `Next \\/ UNCHANGED vars`, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_angle_action_subscript() {
        // `<<A>>_vars` is the non-stuttering dual: `A /\ ~UNCHANGED vars`.
        let source = r#"
            ---- MODULE Test ----
            Live == WF_vars(Next) /\ <<Next>>_vars
            ====
        "#;
        let module = parse_module(source).unwrap();
        let TlaExpr::BinOp { right, .. } = &module.operators[0].body else {
            panic!("Expected a conjunction")
        };
        match &**right {
            TlaExpr::BinOp { op, left, right } => {
                assert_eq!(*op, TlaBinOp::And);
                assert_eq!(**left, TlaExpr::Ident("Next".to_string()));
                assert!(matches!(
                    &**right,
                    TlaExpr::UnaryOp {
                        op: TlaUnaryOp::Not,
                        ..
                    }
                ));
            }
            other => panic!("Expected `Next /\\ ~UNCHANGED vars`, got {:?}", other),
        }
    }

    #[test]
    fn test_underscore_is_not_an_identifier_prefix() {
        // `_vars` in `[Next]_vars` is `_` + `vars`, not one identifier. Getting
        // this wrong silently truncates the enclosing definition.
        let source = r#"
            ---- MODULE Test ----
            Spec == [][Next]_vars
            After == 1
            ====
        "#;
        let module = parse_module(source).unwrap();
        assert_eq!(
            module.operators.len(),
            2,
            "the definition after a subscripted action must still be seen"
        );
        assert_eq!(module.operators[1].name, "After");
    }
}
