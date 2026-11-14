//! The Stage 1b lexer, parser, and lexical name resolver.
//!
//! Identifiers are ASCII; offsets are UTF-8 byte offsets and diagnostic columns
//! count Unicode scalar values. No source fragment is ever emitted as Lean code.

use std::collections::HashMap;

mod authority;
mod declarations;
mod exact_float;
mod expressions;
mod indexed_parser;
mod resolver;
mod resource_parser;
mod types;
use resolver::Resolver;
pub(crate) use resource_parser::{MAX_RESOURCE_VALUE_BLOCKS, value_blocks};

pub use crate::ir::Diagnostic;
use crate::ir::{
    ABSTRACT_PROTOCOL_VERSION, AbstractMethod, AbstractType, Block, Expr, ExprKind, Function,
    Generic, GenericParam, Index, Method, Module, PROTOCOL_VERSION, Param, Span, Statement,
    StatementKind, Subtype, Type, TypePath,
};

const BUILTINS: &[&str] = &[
    "Affine",
    "Base",
    "origin",
    "id",
    "compose",
    "apply",
    "dimension",
    "int",
    "pair",
    "pair_first",
    "pair_second",
];
// The seven geometric operations of `BUILTINS`. A module may take one of these
// names, as `nature::dimension`; every other declaration and binding may not.
// Mirrors `geometricOperation` in the kernel's NamespaceChecker.
const GEOMETRIC_OPERATIONS: &[&str] = &[
    "Affine",
    "Base",
    "origin",
    "id",
    "compose",
    "apply",
    "dimension",
];
// Reserved spellings that may name actual indexed declarations, as in
// `pub use super::Point;`. Mirrors `indexedSpelling` in the kernel's
// NamespaceChecker, which validates such imports.
const INDEXED_SPELLINGS: &[&str] = &[
    "Scheme",
    "CInfScheme",
    "Point",
    "Morphism",
    "Pointed",
    "QQ",
    "CInfReal",
    "Affine",
    "Base",
    "origin",
    "id",
    "compose",
    "apply",
    "dimension",
];
const KEYWORDS: &[&str] = &[
    "fn", "let", "unpack", "as", "pack", "if", "else", "true", "false", "return", "while", "for",
    "loop", "mut", "generic", "method", "domain", "requires", "abstract", "type", "subtype",
];
const TYPES: &[&str] = &[
    "Nat",
    "Int",
    "Bool",
    "Unit",
    "Scheme",
    "CInfScheme",
    "Point",
    "Morphism",
    "Pointed",
    "Fn",
    "Pair",
    "Any",
    "Number",
];

// Bound recursive descent before it consumes the process stack. The separate
// tree limit also catches left-associated Pratt chains, which are parsed in a
// loop but would otherwise recurse without a bound in resolution and serde.
use crate::limits::{MAX_AST_DEPTH, MAX_MODULE_NESTING, MAX_PARSE_NESTING};

fn diagnostic(code: &str, message: impl Into<String>, span: Span) -> Diagnostic {
    Diagnostic {
        code: code.into(),
        message: message.into(),
        span,
    }
}

pub(crate) fn reserved(name: &str) -> bool {
    name.starts_with("__vastitas_")
        || BUILTINS.contains(&name)
        || KEYWORDS.contains(&name)
        || TYPES.contains(&name)
        || matches!(name, "QQ" | "CInfReal")
}

/// `E_RESERVED` at `span` when `name` may not be the name of a declaration or
/// a binding, including a name that `use` binds.
pub(crate) fn check_binding_name(name: &str, span: Span) -> Result<(), Diagnostic> {
    if reserved(name) || ["mod", "use", "pub", "self", "super"].contains(&name) {
        Err(diagnostic(
            "E_RESERVED",
            if BUILTINS.contains(&name) {
                let reason = match name {
                    "int" => "Nat-to-Int conversion",
                    "pair" | "pair_first" | "pair_second" => "Pair construction or projection",
                    _ => "geometry operations",
                };
                format!(
                    "`{name}` is reserved for builtin {reason}; choose another declaration or binding name"
                )
            } else {
                format!("`{name}` is reserved and cannot be used as a declaration or binding name")
            },
            span,
        ))
    } else {
        Ok(())
    }
}

// Levenshtein distance over bytes; only used for short ASCII keyword hints.
fn edit_distance(left: &str, right: &str) -> usize {
    let right = right.as_bytes();
    let mut row: Vec<usize> = (0..=right.len()).collect();
    for (i, a) in left.bytes().enumerate() {
        let mut diagonal = row[0];
        row[0] = i + 1;
        for (j, &b) in right.iter().enumerate() {
            let substitution = diagonal + usize::from(a != b);
            diagonal = row[j + 1];
            row[j + 1] = substitution.min(row[j] + 1).min(diagonal + 1);
        }
    }
    row[right.len()]
}

fn unsupported_keyword(name: &str) -> Option<&'static str> {
    match name {
        "return" => {
            Some("`return` is not supported; the final expression of a block is its result")
        }
        "while" | "for" | "loop" => Some("loops are not supported"),
        "mut" => Some("mutable bindings are not supported"),
        _ => None,
    }
}

// Unicode 16.0 Default_Ignorable_Code_Point
// (scripts/identifier_data/DerivedCoreProperties-16.0.0.txt).
fn default_ignorable(ch: char) -> bool {
    matches!(
        ch as u32,
        0x00AD
            | 0x034F
            | 0x061C
            | 0x115F..=0x1160
            | 0x17B4..=0x17B5
            | 0x180B..=0x180F
            | 0x200B..=0x200F
            | 0x202A..=0x202E
            | 0x2060..=0x206F
            | 0x3164
            | 0xFE00..=0xFE0F
            | 0xFEFF
            | 0xFFA0
            | 0xFFF0..=0xFFF8
            | 0x1BCA0..=0x1BCA3
            | 0x1D173..=0x1D17A
            | 0xE0000..=0xE0FFF
    )
}

// Characters that can make a comment display differently from how the source
// is parsed: every Bidi_Control character (Trojan Source), and invisible
// characters with no text-shaping role. Joiners, variation selectors and tag
// characters remain allowed, since prose and emoji sequences use them.
fn deceptive_in_comment(ch: char) -> bool {
    matches!(
        ch as u32,
        0x061C | 0x200B | 0x200E | 0x200F | 0x202A..=0x202E | 0x2060..=0x206F | 0xFEFF
    )
}

// Whether a diagnostic may echo `ch` to the terminal. Control, format and
// whitespace characters are named by code point instead.
pub(crate) fn echoable(ch: char) -> bool {
    !(ch.is_control() || ch.is_whitespace() || default_ignorable(ch))
}

// Name a source character in a diagnostic without echoing control, format or
// whitespace characters to the terminal.
pub(crate) fn character(ch: char) -> String {
    if echoable(ch) {
        format!("`{ch}` (U+{:04X})", ch as u32)
    } else {
        format!("U+{:04X}", ch as u32)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TokenKind {
    Name(String),
    Number(String),
    Floating(String),
    // An undecoded string literal. No grammar rule accepts one; the token only
    // lets the parser explain the removed `module("…")` recipient form.
    Text,
    Symbol(String),
    Eof,
}

#[derive(Debug, Clone)]
struct Token {
    kind: TokenKind,
    span: Span,
}

impl Token {
    fn is(&self, value: &str) -> bool {
        match &self.kind {
            TokenKind::Name(name) | TokenKind::Symbol(name) => name == value,
            _ => false,
        }
    }

    fn description(&self) -> String {
        match &self.kind {
            // The lexer admits only ASCII spellings, so tokens never carry
            // control or format characters into diagnostics.
            TokenKind::Name(s)
            | TokenKind::Number(s)
            | TokenKind::Floating(s)
            | TokenKind::Symbol(s) => format!("`{s}`"),
            TokenKind::Text => "a string literal".into(),
            TokenKind::Eof => "end of file".into(),
        }
    }
}

struct Lexer<'a> {
    source: &'a str,
    offset: usize,
    line: usize,
    column: usize,
}

impl<'a> Lexer<'a> {
    fn new(source: &'a str) -> Self {
        Self {
            source,
            offset: 0,
            line: 1,
            column: 1,
        }
    }

    fn span(&self) -> Span {
        Span {
            start: self.offset,
            end: self.offset,
            line: self.line,
            column: self.column,
        }
    }

    fn peek(&self) -> Option<char> {
        self.source[self.offset..].chars().next()
    }

    fn advance(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.offset += ch.len_utf8();
        if ch == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        Some(ch)
    }

    fn check_line_break(&self, ch: char) -> Result<(), Diagnostic> {
        if (ch == '\r' && !self.source[self.offset..].starts_with("\r\n"))
            || matches!(
                ch,
                '\u{b}' | '\u{c}' | '\u{1c}'..='\u{1e}' | '\u{85}' | '\u{2028}' | '\u{2029}'
            )
        {
            return Err(diagnostic(
                "E_LEX",
                format!(
                    "unsupported line separator U+{:04X}; use LF or CRLF line endings, including in comments",
                    ch as u32
                ),
                Span {
                    end: self.offset + ch.len_utf8(),
                    ..self.span()
                },
            ));
        }
        Ok(())
    }

    fn float_tail(&mut self) {
        if self.peek() == Some('.') {
            self.advance();
            while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                self.advance();
            }
        }
        if matches!(self.peek(), Some('e' | 'E')) {
            self.advance();
            if matches!(self.peek(), Some('+' | '-')) {
                self.advance();
            }
            while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                self.advance();
            }
        }
        if self.source[self.offset..].starts_with("f32")
            || self.source[self.offset..].starts_with("f64")
        {
            for _ in 0..3 {
                self.advance();
            }
        }
    }

    fn float_token(&mut self, span: Span) -> TokenKind {
        self.float_tail();
        TokenKind::Floating(self.source[span.start..self.offset].into())
    }

    fn hex_float_token(&mut self, mut span: Span) -> Result<TokenKind, Diagnostic> {
        self.advance(); // 0
        self.advance(); // x/X
        while self
            .peek()
            .is_some_and(|c| c.is_ascii_hexdigit() || c == '.')
        {
            self.advance();
        }
        if !matches!(self.peek(), Some('p' | 'P')) {
            span.end = self.offset;
            return Err(diagnostic(
                "E_LEX",
                "hexadecimal payloads require a binary exponent (for example f64(0x1.8p0)); integer literals use decimal digits without radix prefixes",
                span,
            ));
        }
        self.advance();
        if matches!(self.peek(), Some('+' | '-')) {
            self.advance();
        }
        while self
            .peek()
            .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
        {
            self.advance();
        }
        Ok(TokenKind::Floating(
            self.source[span.start..self.offset].into(),
        ))
    }

    fn tokenize(mut self) -> Result<Vec<Token>, Diagnostic> {
        let mut tokens = Vec::new();
        while let Some(ch) = self.peek() {
            self.check_line_break(ch)?;
            if ch.is_whitespace() {
                self.advance();
                continue;
            }
            if self.source[self.offset..].starts_with("//") {
                while let Some(ch) = self.peek().filter(|ch| *ch != '\n') {
                    self.check_line_break(ch)?;
                    if deceptive_in_comment(ch) {
                        return Err(diagnostic(
                            "E_LEX",
                            format!(
                                "comments cannot contain the bidirectional control or invisible character U+{:04X}; it can make source display differently from how it is parsed",
                                ch as u32
                            ),
                            Span {
                                end: self.offset + ch.len_utf8(),
                                ..self.span()
                            },
                        ));
                    }
                    self.advance();
                }
                continue;
            }
            let mut span = self.span();
            if ch == '\u{feff}' {
                self.advance();
                span.end = self.offset;
                return Err(diagnostic(
                    "E_LEX",
                    "UTF-8 byte order mark (BOM) is not supported; save the source as UTF-8 without BOM",
                    span,
                ));
            }
            if self.source[self.offset..].starts_with("/*") {
                self.advance();
                self.advance();
                span.end = self.offset;
                return Err(diagnostic(
                    "E_UNSUPPORTED",
                    "block comments are not supported; use // line comments",
                    span,
                ));
            }
            let kind = if ch.is_ascii_alphabetic() || ch == '_' {
                while self
                    .peek()
                    .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
                {
                    self.advance();
                }
                let name = &self.source[span.start..self.offset];
                TokenKind::Name(name.into())
            } else if ch == '"' {
                // Never decode the literal: its escapes must not reach
                // diagnostics or terminal output.
                self.advance();
                let mut escaped = false;
                while let Some(c) = self.peek() {
                    self.check_line_break(c)?;
                    self.advance();
                    if !escaped && c == '"' {
                        break;
                    }
                    escaped = !escaped && c == '\\';
                }
                TokenKind::Text
            } else if self.source[self.offset..].starts_with("0x")
                || self.source[self.offset..].starts_with("0X")
            {
                self.hex_float_token(span)?
            } else if ch.is_ascii_digit() {
                while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    self.advance();
                }
                let tail = &self.source[self.offset..];
                if (tail.starts_with('.') && !tail.starts_with(".."))
                    || matches!(self.peek(), Some('e' | 'E'))
                    || tail.starts_with("f32")
                    || tail.starts_with("f64")
                {
                    self.float_token(span)
                } else if self
                    .peek()
                    .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                {
                    while self
                        .peek()
                        .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
                    {
                        self.advance();
                    }
                    span.end = self.offset;
                    return Err(diagnostic(
                        "E_LEX",
                        "integer literals use decimal digits without separators, radix prefixes or type suffixes",
                        span,
                    ));
                } else {
                    TokenKind::Number(self.source[span.start..self.offset].into())
                }
            } else {
                let tail = &self.source[self.offset..];
                if ch == '.' && tail.chars().nth(1).is_some_and(|c| c.is_ascii_digit()) {
                    self.float_token(span)
                } else if ch == '/' || ch == '%' {
                    self.advance();
                    span.end = self.offset;
                    return Err(diagnostic(
                        "E_UNSUPPORTED",
                        if ch == '/' {
                            "division is not supported"
                        } else {
                            "remainder is not supported"
                        },
                        span,
                    ));
                } else if let Some(op) = ["->", "==", "!=", "<=", ">=", "&&", "||", "::", "<:"]
                    .into_iter()
                    .find(|op| tail.starts_with(op))
                {
                    self.advance();
                    self.advance();
                    TokenKind::Symbol(op.into())
                } else if "(){}[]<>,:;=+-*!.^".contains(ch) {
                    self.advance();
                    TokenKind::Symbol(ch.to_string())
                } else {
                    self.advance();
                    span.end = self.offset;
                    return Err(diagnostic(
                        "E_LEX",
                        format!(
                            "unsupported character {}; use ASCII identifiers and integer literals",
                            character(ch)
                        ),
                        span,
                    ));
                }
            };
            span.end = self.offset;
            tokens.push(Token { kind, span });
        }
        tokens.push(Token {
            kind: TokenKind::Eof,
            span: self.span(),
        });
        Ok(tokens)
    }
}

struct Parser {
    tokens: Vec<Token>,
    position: usize,
    split_closer: Option<Token>,
    nesting: usize,
    packages: bool,
    indexed: bool,
    // Open `else if` links. Each consumes one level of the nesting budget.
    else_if_links: usize,
}

impl Parser {
    fn from_source(input: &SourceInput<'_>, packages: bool) -> Result<Self, Diagnostic> {
        if input.offset.checked_add(input.source.len()).is_none() {
            return Err(diagnostic(
                "E_LIMIT",
                "source byte positions exceed the supported range",
                Span {
                    start: input.offset,
                    end: input.offset,
                    line: 1,
                    column: 1,
                },
            ));
        }
        let shift = |span: &mut Span| {
            span.start += input.offset;
            span.end += input.offset;
        };
        let mut tokens = Lexer::new(input.source).tokenize().map_err(|mut error| {
            shift(&mut error.span);
            error
        })?;
        for token in &mut tokens {
            shift(&mut token.span);
        }
        Ok(Self {
            tokens,
            position: 0,
            split_closer: None,
            nesting: 0,
            packages,
            indexed: false,
            else_if_links: 0,
        })
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.position]
    }
    fn previous(&self) -> &Token {
        self.split_closer
            .as_ref()
            .unwrap_or_else(|| &self.tokens[self.position - 1])
    }

    fn advance(&mut self) -> Token {
        let token = self.peek().clone();
        self.split_closer = None;
        if token.kind != TokenKind::Eof {
            self.position += 1;
        }
        token
    }

    fn consume(&mut self, value: &str) -> bool {
        if self.peek().is(value) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, value: &str) -> Result<Token, Diagnostic> {
        if self.peek().is(value) {
            Ok(self.advance())
        } else {
            Err(diagnostic(
                "E_PARSE",
                format!("expected `{value}`, found {}", self.peek().description()),
                self.peek().span,
            ))
        }
    }

    fn type_close(&mut self) -> Result<Token, Diagnostic> {
        // Longest-match lexing is still correct for expressions. Only a type
        // argument list can split `>=` into its closing `>` and an assignment.
        if self.peek().is(">=") {
            let span = self.peek().span;
            let closer = Token {
                kind: TokenKind::Symbol(">".into()),
                span: Span {
                    end: span.start + 1,
                    ..span
                },
            };
            // Leave the unconsumed `=` at the current position. Remember the
            // virtual `>` for previous(), without shifting the token suffix.
            self.tokens[self.position] = Token {
                kind: TokenKind::Symbol("=".into()),
                span: Span {
                    start: span.start + 1,
                    column: span.column + 1,
                    ..span
                },
            };
            self.split_closer = Some(closer.clone());
            return Ok(closer);
        }
        self.expect(">")
    }

    // `open`, items separated by `,` with an optional trailing `,`, and
    // `close`. The list may be empty.
    fn delimited_list<T>(
        &mut self,
        open: &str,
        close: &str,
        item: impl FnMut(&mut Self) -> Result<T, Diagnostic>,
    ) -> Result<Vec<T>, Diagnostic> {
        self.expect(open)?;
        self.delimited_tail(close, item)
    }

    // The items and the `close` of a delimited list whose opener has been
    // consumed.
    fn delimited_tail<T>(
        &mut self,
        close: &str,
        mut item: impl FnMut(&mut Self) -> Result<T, Diagnostic>,
    ) -> Result<Vec<T>, Diagnostic> {
        let mut values = Vec::new();
        if !self.consume(close) {
            loop {
                values.push(item(self)?);
                if self.consume(close) {
                    break;
                }
                self.expect(",")?;
                if self.consume(close) {
                    break;
                }
            }
        }
        Ok(values)
    }

    fn name(&mut self) -> Result<(String, Span), Diagnostic> {
        let token = self.advance();
        match token.kind {
            TokenKind::Name(ref name)
                if matches!(name.as_str(), "while" | "for" | "loop" | "mut") =>
            {
                Err(diagnostic(
                    "E_RESERVED",
                    format!("`{name}` is reserved and cannot be used as a name"),
                    token.span,
                ))
            }
            TokenKind::Name(ref name) if name == "return" => Err(diagnostic(
                "E_UNSUPPORTED",
                unsupported_keyword(name).unwrap(),
                token.span,
            )),
            TokenKind::Name(name) if !KEYWORDS.contains(&name.as_str()) => Ok((name, token.span)),
            _ => Err(diagnostic("E_PARSE", "expected an identifier", token.span)),
        }
    }

    fn binding_name(&mut self) -> Result<(String, Span), Diagnostic> {
        let (name, span) = self.name()?;
        self.check_binding_name(&name, span)?;
        Ok((name, span))
    }

    // The name of a `mod` declaration. It may be one of the seven geometric
    // operations, which stay reserved for every other declaration and binding,
    // including the name that a `use` binds. The kernel's `moduleName` agrees.
    fn module_name(&mut self) -> Result<(String, Span), Diagnostic> {
        let (name, span) = self.name()?;
        if !GEOMETRIC_OPERATIONS.contains(&name.as_str()) {
            self.check_binding_name(&name, span)?;
        }
        Ok((name, span))
    }

    // The names of modules and paths are reserved in flat mode too. The kernel
    // rejects them as well, at the declaration or the statement that binds
    // them; the frontend reports them at the name (#747).
    fn check_binding_name(&self, name: &str, span: Span) -> Result<(), Diagnostic> {
        check_binding_name(name, span)
    }
}

/// One independently parsed source in a compilation unit.
///
/// `offset` allocates the file a nonoverlapping range of byte positions in the
/// driver's source map. Line and column numbers remain local to this file.
pub struct SourceInput<'a> {
    pub source: &'a str,
    pub file: &'a str,
    pub offset: usize,
}

/// Parse files separately, then resolve all declarations in one compilation
/// unit. This permits cross-file calls without allowing syntax to cross a file
/// boundary. Semantic acceptance still belongs to Lean.
pub fn parse_sources(sources: &[SourceInput<'_>]) -> Result<Module, Vec<Diagnostic>> {
    let Some(first) = sources.first() else {
        return Err(vec![diagnostic(
            "E_INPUT",
            "a compilation unit needs at least one source file",
            Span {
                start: 0,
                end: 0,
                line: 1,
                column: 1,
            },
        )]);
    };
    let mut module = Module {
        version: PROTOCOL_VERSION,
        input: None,
        file: first.file.into(),
        functions: Vec::new(),
        generics: Vec::new(),
        methods: Vec::new(),
        abstract_types: Vec::new(),
        subtypes: Vec::new(),
        abstract_methods: Vec::new(),
    };
    for input in sources {
        Parser::from_source(input, false)
            .and_then(|mut parser| parser.flat_declarations(&mut module))
            .map_err(|error| vec![error])?;
    }
    if !module.abstract_types.is_empty()
        || !module.subtypes.is_empty()
        || !module.abstract_methods.is_empty()
    {
        module.version = ABSTRACT_PROTOCOL_VERSION;
        module.input = Some("flat".into());
    }
    let errors = Resolver::module(&module);
    if errors.is_empty() {
        Ok(module)
    } else {
        Err(errors)
    }
}

/// Parse package syntax without flattening or resolving its namespace. Lean
/// independently accepts names and owners from the preserved protocol-3 graph.
pub(crate) fn parse_module_source(
    input: SourceInput<'_>,
    path: Vec<String>,
    public: bool,
    declaration: Option<Span>,
) -> Result<crate::packages::Parsed, Diagnostic> {
    let mut parser = Parser::from_source(&input, true)?;
    let span = declaration.unwrap_or(parser.peek().span);
    let mut parsed = crate::packages::Parsed {
        modules: Vec::new(),
        external: Vec::new(),
    };
    parser.namespace(path, public, span, false, &mut parsed)?;
    Ok(parsed)
}

/// Parse and resolve a single `.vast` source. Semantic acceptance belongs to Lean.
pub fn parse(source: &str, file: &str) -> Result<Module, Vec<Diagnostic>> {
    parse_sources(&[SourceInput {
        source,
        file,
        offset: 0,
    }])
}

#[cfg(test)]
mod tests;
