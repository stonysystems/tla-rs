//! TLA+ tokenizer implementation.
//!
//! This module tokenizes TLA+ source code into a stream of tokens that can be
//! consumed by the parser. It handles:
//!
//! - Keywords: VARIABLE, CONSTANT, EXTENDS, MODULE, etc.
//! - Operators: \in, \notin, \cup, \cap, /\, \/, =>, etc.
//! - Special symbols: <<, >>, [, ], {, }, etc.
//! - Quantifiers: \A, \E, CHOOSE
//! - Temporal operators: [], <>, ~>, -+->
//! - Comments: \* line comments and (* ... *) block comments
//! - Identifiers and literals

use std::fmt;
use std::iter::Peekable;
use std::str::Chars;

/// Position in the source code
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Position {
    /// Line number (1-indexed)
    pub line: usize,
    /// Column number (1-indexed)
    pub column: usize,
    /// Byte offset from the start
    pub offset: usize,
}

impl Position {
    pub fn new(line: usize, column: usize, offset: usize) -> Self {
        Self {
            line,
            column,
            offset,
        }
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

/// Span in the source code
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Span {
    pub start: Position,
    pub end: Position,
}

impl Span {
    pub fn new(start: Position, end: Position) -> Self {
        Self { start, end }
    }
}

/// Token kind enumeration for TLA+
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TlaTokenKind {
    // Keywords
    Module,
    Extends,
    Variable,
    Variables,
    Constant,
    Constants,
    Assume,
    Theorem,
    Instance,
    Local,
    Let,
    KwIn, // IN keyword (as in LET x == ... IN ...)
    Recursive,
    If,
    Then,
    Else,
    Case,
    Other,
    Domain,
    Except,
    Enabled,
    Unchanged,
    Subset,
    Union,

    // Quantifiers
    Forall, // \A
    Exists, // \E
    Choose, // CHOOSE

    // Set Operators
    SetIn,        // \in (set membership)
    NotIn,        // \notin
    Subseteq,     // \subseteq
    Cup,          // \cup
    Cap,          // \cap
    Setminus,     // \
    CrossProduct, // \X or \times

    // Logical Operators
    And,     // /\ or \land
    Or,      // \/ or \lor
    Not,     // ~ or \lnot or \neg
    Implies, // => or \implies
    Iff,     // <=> or \equiv
    True,    // TRUE
    False,   // FALSE

    // Temporal Operators
    Always,     // []
    Eventually, // <>
    LeadsTo,    // ~>
    PlusMinus,  // -+->

    // Arithmetic Operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Caret,  // ^
    DotDot, // .. (range)
    Div,    // \div
    Mod,    // \mod

    // Comparison Operators
    Eq,  // =
    Neq, // # or /= or \neq
    Lt,  // <
    Gt,  // >
    Leq, // <= or \leq or =<
    Geq, // >= or \geq

    // Assignment/Definition
    DefEq,   // ==
    ColonEq, // :=
    Prime,   // '

    // Brackets and Delimiters
    LParen,   // (
    RParen,   // )
    LBracket, // [
    RBracket, // ]
    LBrace,   // {
    RBrace,   // }
    LAngle,   // <<
    RAngle,   // >>
    Comma,
    Colon,
    Semicolon,
    Dot,
    At,         // @
    Underscore, // _
    Bang,       // ! (used in EXCEPT syntax: ![i])

    // Module Structure
    ModuleDashes, // ---- or ====

    // Maps and Functions
    MapsTo,     // |->
    RightArrow, // ->
    LeftArrow,  // <-

    // Identifiers and Literals
    Ident(String),
    Number(String),
    String(String),

    // Special
    Eof,
    Newline,
}

impl fmt::Display for TlaTokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TlaTokenKind::Module => write!(f, "MODULE"),
            TlaTokenKind::Extends => write!(f, "EXTENDS"),
            TlaTokenKind::Variable => write!(f, "VARIABLE"),
            TlaTokenKind::Variables => write!(f, "VARIABLES"),
            TlaTokenKind::Constant => write!(f, "CONSTANT"),
            TlaTokenKind::Constants => write!(f, "CONSTANTS"),
            TlaTokenKind::Assume => write!(f, "ASSUME"),
            TlaTokenKind::Theorem => write!(f, "THEOREM"),
            TlaTokenKind::Instance => write!(f, "INSTANCE"),
            TlaTokenKind::Local => write!(f, "LOCAL"),
            TlaTokenKind::Let => write!(f, "LET"),
            TlaTokenKind::KwIn => write!(f, "IN"),
            TlaTokenKind::Recursive => write!(f, "RECURSIVE"),
            TlaTokenKind::If => write!(f, "IF"),
            TlaTokenKind::Then => write!(f, "THEN"),
            TlaTokenKind::Else => write!(f, "ELSE"),
            TlaTokenKind::Case => write!(f, "CASE"),
            TlaTokenKind::Other => write!(f, "OTHER"),
            TlaTokenKind::Domain => write!(f, "DOMAIN"),
            TlaTokenKind::Except => write!(f, "EXCEPT"),
            TlaTokenKind::Enabled => write!(f, "ENABLED"),
            TlaTokenKind::Unchanged => write!(f, "UNCHANGED"),
            TlaTokenKind::Subset => write!(f, "SUBSET"),
            TlaTokenKind::Union => write!(f, "UNION"),
            TlaTokenKind::Forall => write!(f, "\\A"),
            TlaTokenKind::Exists => write!(f, "\\E"),
            TlaTokenKind::Choose => write!(f, "CHOOSE"),
            TlaTokenKind::SetIn => write!(f, "\\in"),
            TlaTokenKind::NotIn => write!(f, "\\notin"),
            TlaTokenKind::Subseteq => write!(f, "\\subseteq"),
            TlaTokenKind::Cup => write!(f, "\\cup"),
            TlaTokenKind::Cap => write!(f, "\\cap"),
            TlaTokenKind::Setminus => write!(f, "\\"),
            TlaTokenKind::CrossProduct => write!(f, "\\X"),
            TlaTokenKind::And => write!(f, "/\\"),
            TlaTokenKind::Or => write!(f, "\\/"),
            TlaTokenKind::Not => write!(f, "~"),
            TlaTokenKind::Implies => write!(f, "=>"),
            TlaTokenKind::Iff => write!(f, "<=>"),
            TlaTokenKind::True => write!(f, "TRUE"),
            TlaTokenKind::False => write!(f, "FALSE"),
            TlaTokenKind::Always => write!(f, "[]"),
            TlaTokenKind::Eventually => write!(f, "<>"),
            TlaTokenKind::LeadsTo => write!(f, "~>"),
            TlaTokenKind::PlusMinus => write!(f, "-+->"),
            TlaTokenKind::Plus => write!(f, "+"),
            TlaTokenKind::Minus => write!(f, "-"),
            TlaTokenKind::Star => write!(f, "*"),
            TlaTokenKind::Slash => write!(f, "/"),
            TlaTokenKind::Percent => write!(f, "%"),
            TlaTokenKind::Caret => write!(f, "^"),
            TlaTokenKind::DotDot => write!(f, ".."),
            TlaTokenKind::Div => write!(f, "\\div"),
            TlaTokenKind::Mod => write!(f, "\\mod"),
            TlaTokenKind::Eq => write!(f, "="),
            TlaTokenKind::Neq => write!(f, "#"),
            TlaTokenKind::Lt => write!(f, "<"),
            TlaTokenKind::Gt => write!(f, ">"),
            TlaTokenKind::Leq => write!(f, "<="),
            TlaTokenKind::Geq => write!(f, ">="),
            TlaTokenKind::DefEq => write!(f, "=="),
            TlaTokenKind::ColonEq => write!(f, ":="),
            TlaTokenKind::Prime => write!(f, "'"),
            TlaTokenKind::LParen => write!(f, "("),
            TlaTokenKind::RParen => write!(f, ")"),
            TlaTokenKind::LBracket => write!(f, "["),
            TlaTokenKind::RBracket => write!(f, "]"),
            TlaTokenKind::LBrace => write!(f, "{{"),
            TlaTokenKind::RBrace => write!(f, "}}"),
            TlaTokenKind::LAngle => write!(f, "<<"),
            TlaTokenKind::RAngle => write!(f, ">>"),
            TlaTokenKind::Comma => write!(f, ","),
            TlaTokenKind::Colon => write!(f, ":"),
            TlaTokenKind::Semicolon => write!(f, ";"),
            TlaTokenKind::Dot => write!(f, "."),
            TlaTokenKind::At => write!(f, "@"),
            TlaTokenKind::Underscore => write!(f, "_"),
            TlaTokenKind::Bang => write!(f, "!"),
            TlaTokenKind::ModuleDashes => write!(f, "----"),
            TlaTokenKind::MapsTo => write!(f, "|->"),
            TlaTokenKind::RightArrow => write!(f, "->"),
            TlaTokenKind::LeftArrow => write!(f, "<-"),
            TlaTokenKind::Ident(s) => write!(f, "{}", s),
            TlaTokenKind::Number(s) => write!(f, "{}", s),
            TlaTokenKind::String(s) => write!(f, "\"{}\"", s),
            TlaTokenKind::Eof => write!(f, "EOF"),
            TlaTokenKind::Newline => write!(f, "\\n"),
        }
    }
}

/// A token with its span information
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlaToken {
    pub kind: TlaTokenKind,
    pub span: Span,
}

impl TlaToken {
    pub fn new(kind: TlaTokenKind, span: Span) -> Self {
        Self { kind, span }
    }
}

/// Tokenizer error
#[derive(Debug, Clone)]
pub struct TlaTokenizerError {
    pub message: String,
    pub position: Position,
}

impl TlaTokenizerError {
    pub fn new(message: impl Into<String>, position: Position) -> Self {
        Self {
            message: message.into(),
            position,
        }
    }
}

impl fmt::Display for TlaTokenizerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Tokenizer error at {}: {}", self.position, self.message)
    }
}

impl std::error::Error for TlaTokenizerError {}

/// TLA+ tokenizer
pub struct TlaTokenizer<'a> {
    source: &'a str,
    chars: Peekable<Chars<'a>>,
    position: Position,
    /// Accumulated tokens
    tokens: Vec<TlaToken>,
}

impl<'a> TlaTokenizer<'a> {
    /// Create a new tokenizer for the given source
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            chars: source.chars().peekable(),
            position: Position::new(1, 1, 0),
            tokens: Vec::new(),
        }
    }

    /// Tokenize the entire source and return all tokens
    pub fn tokenize(&mut self) -> Result<Vec<TlaToken>, TlaTokenizerError> {
        while !self.is_at_end() {
            self.skip_whitespace_and_comments()?;
            if self.is_at_end() {
                break;
            }
            let token = self.next_token()?;
            self.tokens.push(token);
        }

        // Add EOF token
        self.tokens.push(TlaToken::new(
            TlaTokenKind::Eof,
            Span::new(self.position, self.position),
        ));

        Ok(self.tokens.clone())
    }

    /// Check if we've reached the end of input
    fn is_at_end(&mut self) -> bool {
        self.chars.peek().is_none()
    }

    /// Peek at the current character without consuming it
    fn peek(&mut self) -> Option<char> {
        self.chars.peek().copied()
    }

    /// Consume and return the current character
    fn advance(&mut self) -> Option<char> {
        let c = self.chars.next()?;
        self.position.offset += c.len_utf8();
        if c == '\n' {
            self.position.line += 1;
            self.position.column = 1;
        } else {
            self.position.column += 1;
        }
        Some(c)
    }

    /// Check if current char matches and consume if so
    fn match_char(&mut self, expected: char) -> bool {
        if self.peek() == Some(expected) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Skip whitespace and comments
    fn skip_whitespace_and_comments(&mut self) -> Result<(), TlaTokenizerError> {
        loop {
            match self.peek() {
                // Skip whitespace (but not newlines - they might be significant)
                Some(' ') | Some('\t') | Some('\r') | Some('\n') => {
                    self.advance();
                }
                // Line comment: \*
                Some('\\') => {
                    let start_pos = self.position;
                    self.advance();
                    if self.match_char('*') {
                        // Skip until end of line
                        while let Some(c) = self.peek() {
                            if c == '\n' {
                                break;
                            }
                            self.advance();
                        }
                    } else {
                        // Not a comment, put back the position context
                        // We can't really "put back" in this implementation,
                        // but the next_token will handle the backslash
                        self.position = start_pos;
                        self.chars = self.source[start_pos.offset..].chars().peekable();
                        return Ok(());
                    }
                }
                // Block comment: (* ... *)
                Some('(') => {
                    let start_pos = self.position;
                    self.advance();
                    if self.match_char('*') {
                        // Skip until *)
                        let comment_start = start_pos;
                        loop {
                            match self.peek() {
                                Some('*') => {
                                    self.advance();
                                    if self.match_char(')') {
                                        break;
                                    }
                                }
                                Some(_) => {
                                    self.advance();
                                }
                                None => {
                                    return Err(TlaTokenizerError::new(
                                        "Unterminated block comment",
                                        comment_start,
                                    ));
                                }
                            }
                        }
                    } else {
                        // Not a comment, reset
                        self.position = start_pos;
                        self.chars = self.source[start_pos.offset..].chars().peekable();
                        return Ok(());
                    }
                }
                _ => return Ok(()),
            }
        }
    }

    /// Read the next token
    fn next_token(&mut self) -> Result<TlaToken, TlaTokenizerError> {
        let start = self.position;

        let c = match self.advance() {
            Some(c) => c,
            None => {
                return Ok(TlaToken::new(
                    TlaTokenKind::Eof,
                    Span::new(start, self.position),
                ));
            }
        };

        let kind = match c {
            // Single character tokens
            '(' => TlaTokenKind::LParen,
            ')' => TlaTokenKind::RParen,
            '[' => {
                if self.match_char(']') {
                    TlaTokenKind::Always // []
                } else {
                    TlaTokenKind::LBracket
                }
            }
            ']' => TlaTokenKind::RBracket,
            '{' => TlaTokenKind::LBrace,
            '}' => TlaTokenKind::RBrace,
            ',' => TlaTokenKind::Comma,
            ';' => TlaTokenKind::Semicolon,
            '@' => TlaTokenKind::At,
            '\'' => TlaTokenKind::Prime,
            '^' => TlaTokenKind::Caret,
            '%' => TlaTokenKind::Percent,
            '+' => TlaTokenKind::Plus,
            '*' => TlaTokenKind::Star,
            '#' => TlaTokenKind::Neq,
            '!' => TlaTokenKind::Bang, // Used in EXCEPT syntax: ![i]

            // Multi-character operators starting with specific chars
            ':' => {
                if self.match_char('=') {
                    TlaTokenKind::ColonEq
                } else {
                    TlaTokenKind::Colon
                }
            }
            '.' => {
                if self.match_char('.') {
                    TlaTokenKind::DotDot
                } else {
                    TlaTokenKind::Dot
                }
            }
            '-' => {
                // Check for ---- (module separator), -->, -+->
                if self.match_char('-') {
                    // Could be ---- or more
                    let mut dash_count = 2;
                    while self.match_char('-') {
                        dash_count += 1;
                    }
                    if dash_count >= 4 {
                        TlaTokenKind::ModuleDashes
                    } else {
                        // Just -- which is not standard, treat as two minuses?
                        // For now, treat as module dashes if >= 2
                        TlaTokenKind::ModuleDashes
                    }
                } else if self.match_char('+') {
                    if self.match_char('-') && self.match_char('>') {
                        TlaTokenKind::PlusMinus
                    } else {
                        // Not -+->, just return minus and let + be separate
                        TlaTokenKind::Minus
                    }
                } else if self.match_char('>') {
                    TlaTokenKind::RightArrow
                } else {
                    TlaTokenKind::Minus
                }
            }
            '=' => {
                if self.match_char('=') {
                    // Could be == or ==== (module closing)
                    let mut eq_count = 2;
                    while self.match_char('=') {
                        eq_count += 1;
                    }
                    if eq_count >= 4 {
                        TlaTokenKind::ModuleDashes
                    } else {
                        TlaTokenKind::DefEq
                    }
                } else if self.match_char('>') {
                    TlaTokenKind::Implies
                } else if self.match_char('<') {
                    TlaTokenKind::Leq // =<
                } else {
                    TlaTokenKind::Eq
                }
            }
            '/' => {
                if self.match_char('\\') {
                    TlaTokenKind::And
                } else if self.match_char('=') {
                    TlaTokenKind::Neq
                } else {
                    TlaTokenKind::Slash
                }
            }
            '<' => {
                if self.match_char('<') {
                    TlaTokenKind::LAngle // <<
                } else if self.match_char('=') {
                    if self.match_char('>') {
                        TlaTokenKind::Iff // <=>
                    } else {
                        TlaTokenKind::Leq // <=
                    }
                } else if self.match_char('>') {
                    TlaTokenKind::Eventually // <>
                } else if self.match_char('-') {
                    TlaTokenKind::LeftArrow // <-
                } else {
                    TlaTokenKind::Lt
                }
            }
            '>' => {
                if self.match_char('>') {
                    TlaTokenKind::RAngle // >>
                } else if self.match_char('=') {
                    TlaTokenKind::Geq
                } else {
                    TlaTokenKind::Gt
                }
            }
            '~' => {
                if self.match_char('>') {
                    TlaTokenKind::LeadsTo // ~>
                } else {
                    TlaTokenKind::Not
                }
            }
            '|' => {
                if self.match_char('-') && self.match_char('>') {
                    TlaTokenKind::MapsTo // |->
                } else {
                    // Just | is not standard in TLA+, but handle gracefully
                    return Err(TlaTokenizerError::new("Unexpected character: |", start));
                }
            }

            // Backslash operators
            '\\' => self.scan_backslash_operator(start)?,

            // String literal
            '"' => self.scan_string(start)?,

            // Numbers
            '0'..='9' => self.scan_number(c, start)?,

            // Identifiers and keywords
            'a'..='z' | 'A'..='Z' | '_' => self.scan_identifier(c, start)?,

            _ => {
                return Err(TlaTokenizerError::new(
                    format!("Unexpected character: {}", c),
                    start,
                ));
            }
        };

        Ok(TlaToken::new(kind, Span::new(start, self.position)))
    }

    /// Scan a backslash operator or number literal
    fn scan_backslash_operator(
        &mut self,
        start: Position,
    ) -> Result<TlaTokenKind, TlaTokenizerError> {
        // Check for number literals: \b (binary), \o (octal), \h (hex)
        match self.peek() {
            Some('b') | Some('B') => {
                self.advance();
                return self.scan_binary_number(start);
            }
            Some('o') | Some('O') => {
                self.advance();
                return self.scan_octal_number(start);
            }
            Some('h') | Some('H') => {
                self.advance();
                return self.scan_hex_number(start);
            }
            _ => {}
        }

        // Collect the operator name after backslash
        let mut name = String::new();
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                name.push(c);
                self.advance();
            } else {
                break;
            }
        }

        // Match known backslash operators
        match name.as_str() {
            "A" => Ok(TlaTokenKind::Forall),
            "E" => Ok(TlaTokenKind::Exists),
            "in" => Ok(TlaTokenKind::SetIn),
            "notin" => Ok(TlaTokenKind::NotIn),
            "subseteq" => Ok(TlaTokenKind::Subseteq),
            "cup" => Ok(TlaTokenKind::Cup),
            "cap" => Ok(TlaTokenKind::Cap),
            "X" | "times" => Ok(TlaTokenKind::CrossProduct),
            "land" => Ok(TlaTokenKind::And),
            "lor" => Ok(TlaTokenKind::Or),
            "lnot" | "neg" => Ok(TlaTokenKind::Not),
            "implies" => Ok(TlaTokenKind::Implies),
            "equiv" => Ok(TlaTokenKind::Iff),
            "leq" => Ok(TlaTokenKind::Leq),
            "geq" => Ok(TlaTokenKind::Geq),
            "neq" => Ok(TlaTokenKind::Neq),
            "div" => Ok(TlaTokenKind::Div),
            "mod" => Ok(TlaTokenKind::Mod),
            "" => {
                // Just a backslash followed by /
                if self.match_char('/') {
                    Ok(TlaTokenKind::Or)
                } else {
                    Ok(TlaTokenKind::Setminus)
                }
            }
            _ => Err(TlaTokenizerError::new(
                format!("Unknown backslash operator: \\{}", name),
                start,
            )),
        }
    }

    /// Scan a binary number literal (\b...)
    fn scan_binary_number(&mut self, start: Position) -> Result<TlaTokenKind, TlaTokenizerError> {
        let mut value = String::from("0b");
        let mut has_digits = false;

        while let Some(c) = self.peek() {
            if c == '0' || c == '1' {
                value.push(c);
                self.advance();
                has_digits = true;
            } else if c == '_' {
                // Allow underscores as separators
                self.advance();
            } else {
                break;
            }
        }

        if !has_digits {
            return Err(TlaTokenizerError::new(
                "Expected binary digits after \\b",
                start,
            ));
        }

        Ok(TlaTokenKind::Number(value))
    }

    /// Scan an octal number literal (\o...)
    fn scan_octal_number(&mut self, start: Position) -> Result<TlaTokenKind, TlaTokenizerError> {
        let mut value = String::from("0o");
        let mut has_digits = false;

        while let Some(c) = self.peek() {
            if c.is_ascii_digit() && c < '8' {
                value.push(c);
                self.advance();
                has_digits = true;
            } else if c == '_' {
                self.advance();
            } else {
                break;
            }
        }

        if !has_digits {
            return Err(TlaTokenizerError::new(
                "Expected octal digits after \\o",
                start,
            ));
        }

        Ok(TlaTokenKind::Number(value))
    }

    /// Scan a hexadecimal number literal (\h...)
    fn scan_hex_number(&mut self, start: Position) -> Result<TlaTokenKind, TlaTokenizerError> {
        let mut value = String::from("0x");
        let mut has_digits = false;

        while let Some(c) = self.peek() {
            if c.is_ascii_hexdigit() {
                value.push(c);
                self.advance();
                has_digits = true;
            } else if c == '_' {
                self.advance();
            } else {
                break;
            }
        }

        if !has_digits {
            return Err(TlaTokenizerError::new(
                "Expected hexadecimal digits after \\h",
                start,
            ));
        }

        Ok(TlaTokenKind::Number(value))
    }

    /// Scan a string literal
    fn scan_string(&mut self, start: Position) -> Result<TlaTokenKind, TlaTokenizerError> {
        let mut value = String::new();

        loop {
            match self.peek() {
                Some('"') => {
                    self.advance();
                    break;
                }
                Some('\\') => {
                    self.advance();
                    match self.peek() {
                        Some('n') => {
                            self.advance();
                            value.push('\n');
                        }
                        Some('t') => {
                            self.advance();
                            value.push('\t');
                        }
                        Some('r') => {
                            self.advance();
                            value.push('\r');
                        }
                        Some('"') => {
                            self.advance();
                            value.push('"');
                        }
                        Some('\\') => {
                            self.advance();
                            value.push('\\');
                        }
                        Some(c) => {
                            return Err(TlaTokenizerError::new(
                                format!("Invalid escape sequence: \\{}", c),
                                self.position,
                            ));
                        }
                        None => {
                            return Err(TlaTokenizerError::new(
                                "Unterminated string literal",
                                start,
                            ));
                        }
                    }
                }
                Some(c) => {
                    self.advance();
                    value.push(c);
                }
                None => {
                    return Err(TlaTokenizerError::new("Unterminated string literal", start));
                }
            }
        }

        Ok(TlaTokenKind::String(value))
    }

    /// Scan a number literal
    fn scan_number(
        &mut self,
        first: char,
        _start: Position,
    ) -> Result<TlaTokenKind, TlaTokenizerError> {
        let mut value = String::new();
        value.push(first);

        // Check for special number formats: \b, \o, \h
        if first == '0' {
            // Could be binary, octal, or hex (TLA+ style)
            // TLA+ uses \b for binary, \o for octal, \h for hex
            // But these are written as 0\bXXX, not 0bXXX
            // For now, just handle decimal
        }

        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                value.push(c);
                self.advance();
            } else {
                break;
            }
        }

        Ok(TlaTokenKind::Number(value))
    }

    /// Scan an identifier or keyword
    fn scan_identifier(
        &mut self,
        first: char,
        _start: Position,
    ) -> Result<TlaTokenKind, TlaTokenizerError> {
        let mut name = String::new();
        name.push(first);

        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                name.push(c);
                self.advance();
            } else {
                break;
            }
        }

        // Check for keywords
        let kind = match name.as_str() {
            "MODULE" => TlaTokenKind::Module,
            "EXTENDS" => TlaTokenKind::Extends,
            "VARIABLE" => TlaTokenKind::Variable,
            "VARIABLES" => TlaTokenKind::Variables,
            "CONSTANT" => TlaTokenKind::Constant,
            "CONSTANTS" => TlaTokenKind::Constants,
            "ASSUME" => TlaTokenKind::Assume,
            "THEOREM" => TlaTokenKind::Theorem,
            "INSTANCE" => TlaTokenKind::Instance,
            "LOCAL" => TlaTokenKind::Local,
            "LET" => TlaTokenKind::Let,
            "IN" => TlaTokenKind::KwIn,
            "RECURSIVE" => TlaTokenKind::Recursive,
            "IF" => TlaTokenKind::If,
            "THEN" => TlaTokenKind::Then,
            "ELSE" => TlaTokenKind::Else,
            "CASE" => TlaTokenKind::Case,
            "OTHER" => TlaTokenKind::Other,
            "DOMAIN" => TlaTokenKind::Domain,
            "EXCEPT" => TlaTokenKind::Except,
            "ENABLED" => TlaTokenKind::Enabled,
            "UNCHANGED" => TlaTokenKind::Unchanged,
            "SUBSET" => TlaTokenKind::Subset,
            "UNION" => TlaTokenKind::Union,
            "CHOOSE" => TlaTokenKind::Choose,
            "TRUE" => TlaTokenKind::True,
            "FALSE" => TlaTokenKind::False,
            _ => TlaTokenKind::Ident(name),
        };

        Ok(kind)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize(source: &str) -> Result<Vec<TlaToken>, TlaTokenizerError> {
        let mut tokenizer = TlaTokenizer::new(source);
        tokenizer.tokenize()
    }

    fn token_kinds(source: &str) -> Result<Vec<TlaTokenKind>, TlaTokenizerError> {
        Ok(tokenize(source)?
            .into_iter()
            .map(|t| t.kind)
            .filter(|k| *k != TlaTokenKind::Eof)
            .collect())
    }

    #[test]
    fn test_empty_source() {
        let tokens = tokenize("").unwrap();
        assert_eq!(tokens.len(), 1);
        assert_eq!(tokens[0].kind, TlaTokenKind::Eof);
    }

    #[test]
    fn test_keywords() {
        let kinds = token_kinds("MODULE EXTENDS VARIABLE CONSTANT").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Module,
                TlaTokenKind::Extends,
                TlaTokenKind::Variable,
                TlaTokenKind::Constant,
            ]
        );
    }

    #[test]
    fn test_identifiers() {
        let kinds = token_kinds("x y foo_bar Baz123").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Ident("x".to_string()),
                TlaTokenKind::Ident("y".to_string()),
                TlaTokenKind::Ident("foo_bar".to_string()),
                TlaTokenKind::Ident("Baz123".to_string()),
            ]
        );
    }

    #[test]
    fn test_numbers() {
        let kinds = token_kinds("42 0 123456").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Number("42".to_string()),
                TlaTokenKind::Number("0".to_string()),
                TlaTokenKind::Number("123456".to_string()),
            ]
        );
    }

    #[test]
    fn test_binary_numbers() {
        let kinds = token_kinds(r"\b1010 \B1111 \b0").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Number("0b1010".to_string()),
                TlaTokenKind::Number("0b1111".to_string()),
                TlaTokenKind::Number("0b0".to_string()),
            ]
        );
    }

    #[test]
    fn test_octal_numbers() {
        let kinds = token_kinds(r"\o777 \O123 \o0").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Number("0o777".to_string()),
                TlaTokenKind::Number("0o123".to_string()),
                TlaTokenKind::Number("0o0".to_string()),
            ]
        );
    }

    #[test]
    fn test_hex_numbers() {
        let kinds = token_kinds(r"\hFF \H1a2b \h0").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Number("0xFF".to_string()),
                TlaTokenKind::Number("0x1a2b".to_string()),
                TlaTokenKind::Number("0x0".to_string()),
            ]
        );
    }

    #[test]
    fn test_invalid_binary_number() {
        let result = tokenize(r"\b");
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("binary digits"));
    }

    #[test]
    fn test_invalid_octal_number() {
        let result = tokenize(r"\o");
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("octal digits"));
    }

    #[test]
    fn test_invalid_hex_number() {
        let result = tokenize(r"\h");
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("hexadecimal digits"));
    }

    #[test]
    fn test_strings() {
        let kinds = token_kinds(r#""hello" "world""#).unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::String("hello".to_string()),
                TlaTokenKind::String("world".to_string()),
            ]
        );
    }

    #[test]
    fn test_string_escapes() {
        let kinds = token_kinds(r#""hello\nworld""#).unwrap();
        assert_eq!(
            kinds,
            vec![TlaTokenKind::String("hello\nworld".to_string()),]
        );
    }

    #[test]
    fn test_logical_operators() {
        let kinds = token_kinds(r"/\ \/ => <=> ~ TRUE FALSE").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::And,
                TlaTokenKind::Or,
                TlaTokenKind::Implies,
                TlaTokenKind::Iff,
                TlaTokenKind::Not,
                TlaTokenKind::True,
                TlaTokenKind::False,
            ]
        );
    }

    #[test]
    fn test_set_operators() {
        let kinds = token_kinds(r"\in \notin \subseteq \cup \cap \X").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::SetIn,
                TlaTokenKind::NotIn,
                TlaTokenKind::Subseteq,
                TlaTokenKind::Cup,
                TlaTokenKind::Cap,
                TlaTokenKind::CrossProduct,
            ]
        );
    }

    #[test]
    fn test_quantifiers() {
        let kinds = token_kinds(r"\A \E CHOOSE").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Forall,
                TlaTokenKind::Exists,
                TlaTokenKind::Choose,
            ]
        );
    }

    #[test]
    fn test_temporal_operators() {
        let kinds = token_kinds("[] <> ~>").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Always,
                TlaTokenKind::Eventually,
                TlaTokenKind::LeadsTo,
            ]
        );
    }

    #[test]
    fn test_comparison_operators() {
        let kinds = token_kinds("= # < > <= >= ==").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Eq,
                TlaTokenKind::Neq,
                TlaTokenKind::Lt,
                TlaTokenKind::Gt,
                TlaTokenKind::Leq,
                TlaTokenKind::Geq,
                TlaTokenKind::DefEq,
            ]
        );
    }

    #[test]
    fn test_brackets_and_delimiters() {
        let kinds = token_kinds("( ) [ ] { } << >> , : ; . @").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::LParen,
                TlaTokenKind::RParen,
                TlaTokenKind::LBracket,
                TlaTokenKind::RBracket,
                TlaTokenKind::LBrace,
                TlaTokenKind::RBrace,
                TlaTokenKind::LAngle,
                TlaTokenKind::RAngle,
                TlaTokenKind::Comma,
                TlaTokenKind::Colon,
                TlaTokenKind::Semicolon,
                TlaTokenKind::Dot,
                TlaTokenKind::At,
            ]
        );
    }

    #[test]
    fn test_arithmetic_operators() {
        let kinds = token_kinds("+ - * / ^ .. %").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Plus,
                TlaTokenKind::Minus,
                TlaTokenKind::Star,
                TlaTokenKind::Slash,
                TlaTokenKind::Caret,
                TlaTokenKind::DotDot,
                TlaTokenKind::Percent,
            ]
        );
    }

    #[test]
    fn test_function_operators() {
        let kinds = token_kinds("|-> -> <- '").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::MapsTo,
                TlaTokenKind::RightArrow,
                TlaTokenKind::LeftArrow,
                TlaTokenKind::Prime,
            ]
        );
    }

    #[test]
    fn test_module_dashes() {
        let kinds = token_kinds("---- MODULE Test ----").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::ModuleDashes,
                TlaTokenKind::Module,
                TlaTokenKind::Ident("Test".to_string()),
                TlaTokenKind::ModuleDashes,
            ]
        );
    }

    #[test]
    fn test_line_comment() {
        let kinds = token_kinds("x \\* this is a comment\ny").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Ident("x".to_string()),
                TlaTokenKind::Ident("y".to_string()),
            ]
        );
    }

    #[test]
    fn test_block_comment() {
        let kinds = token_kinds("x (* this is\na block\ncomment *) y").unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Ident("x".to_string()),
                TlaTokenKind::Ident("y".to_string()),
            ]
        );
    }

    #[test]
    fn test_simple_predicate() {
        let source = r"Init == x = 0 /\ y = 0";
        let kinds = token_kinds(source).unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Ident("Init".to_string()),
                TlaTokenKind::DefEq,
                TlaTokenKind::Ident("x".to_string()),
                TlaTokenKind::Eq,
                TlaTokenKind::Number("0".to_string()),
                TlaTokenKind::And,
                TlaTokenKind::Ident("y".to_string()),
                TlaTokenKind::Eq,
                TlaTokenKind::Number("0".to_string()),
            ]
        );
    }

    #[test]
    fn test_quantifier_expression() {
        let source = r"\A x \in S : P(x)";
        let kinds = token_kinds(source).unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Forall,
                TlaTokenKind::Ident("x".to_string()),
                TlaTokenKind::SetIn,
                TlaTokenKind::Ident("S".to_string()),
                TlaTokenKind::Colon,
                TlaTokenKind::Ident("P".to_string()),
                TlaTokenKind::LParen,
                TlaTokenKind::Ident("x".to_string()),
                TlaTokenKind::RParen,
            ]
        );
    }

    #[test]
    fn test_function_definition() {
        let source = "[x \\in S |-> f(x)]";
        let kinds = token_kinds(source).unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::LBracket,
                TlaTokenKind::Ident("x".to_string()),
                TlaTokenKind::SetIn,
                TlaTokenKind::Ident("S".to_string()),
                TlaTokenKind::MapsTo,
                TlaTokenKind::Ident("f".to_string()),
                TlaTokenKind::LParen,
                TlaTokenKind::Ident("x".to_string()),
                TlaTokenKind::RParen,
                TlaTokenKind::RBracket,
            ]
        );
    }

    #[test]
    fn test_primed_variables() {
        let source = "x' = x + 1";
        let kinds = token_kinds(source).unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::Ident("x".to_string()),
                TlaTokenKind::Prime,
                TlaTokenKind::Eq,
                TlaTokenKind::Ident("x".to_string()),
                TlaTokenKind::Plus,
                TlaTokenKind::Number("1".to_string()),
            ]
        );
    }

    #[test]
    fn test_record_syntax() {
        let source = "[a |-> 1, b |-> 2]";
        let kinds = token_kinds(source).unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::LBracket,
                TlaTokenKind::Ident("a".to_string()),
                TlaTokenKind::MapsTo,
                TlaTokenKind::Number("1".to_string()),
                TlaTokenKind::Comma,
                TlaTokenKind::Ident("b".to_string()),
                TlaTokenKind::MapsTo,
                TlaTokenKind::Number("2".to_string()),
                TlaTokenKind::RBracket,
            ]
        );
    }

    #[test]
    fn test_tuple_syntax() {
        let source = "<<a, b, c>>";
        let kinds = token_kinds(source).unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::LAngle,
                TlaTokenKind::Ident("a".to_string()),
                TlaTokenKind::Comma,
                TlaTokenKind::Ident("b".to_string()),
                TlaTokenKind::Comma,
                TlaTokenKind::Ident("c".to_string()),
                TlaTokenKind::RAngle,
            ]
        );
    }

    #[test]
    fn test_except_syntax() {
        let source = "[f EXCEPT ![i] = v]";
        let kinds = token_kinds(source).unwrap();
        assert_eq!(
            kinds,
            vec![
                TlaTokenKind::LBracket,
                TlaTokenKind::Ident("f".to_string()),
                TlaTokenKind::Except,
                TlaTokenKind::Bang, // ! in EXCEPT syntax
                TlaTokenKind::LBracket,
                TlaTokenKind::Ident("i".to_string()),
                TlaTokenKind::RBracket,
                TlaTokenKind::Eq,
                TlaTokenKind::Ident("v".to_string()),
                TlaTokenKind::RBracket,
            ]
        );
    }

    #[test]
    fn test_unterminated_string() {
        let result = tokenize(r#""hello"#);
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("Unterminated"));
    }

    #[test]
    fn test_unterminated_block_comment() {
        let result = tokenize("(* this never ends");
        assert!(result.is_err());
        assert!(result.unwrap_err().message.contains("Unterminated"));
    }
}
