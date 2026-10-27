//! The Stage 1b lexer, parser, and lexical name resolver.
//!
//! Identifiers are ASCII; offsets are UTF-8 byte offsets and diagnostic columns
//! count Unicode scalar values. No source fragment is ever emitted as Lean code.

use std::collections::{HashMap, HashSet};

pub use crate::ir::Diagnostic;
use crate::ir::{
    Block, Expr, ExprKind, Function, Generic, GenericParam, Index, Method, Module,
    PROTOCOL_VERSION, Param, Span, Statement, StatementKind, Type,
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
];
const KEYWORDS: &[&str] = &[
    "fn", "let", "unpack", "as", "pack", "if", "else", "true", "false", "return", "while", "for",
    "loop", "mut", "generic", "method", "domain", "requires",
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
    "Any",
    "Number",
];

// Bound recursive descent before it consumes the process stack. The separate
// tree limit also catches left-associated Pratt chains, which are parsed in a
// loop but would otherwise recurse without a bound in resolution and serde.
const MAX_PARSE_NESTING: usize = 64;
const MAX_AST_DEPTH: usize = 128;

fn diagnostic(code: &str, message: impl Into<String>, span: Span) -> Diagnostic {
    Diagnostic {
        code: code.into(),
        message: message.into(),
        span,
    }
}

fn reserved(name: &str) -> bool {
    name.starts_with("__vastitas_")
        || BUILTINS.contains(&name)
        || KEYWORDS.contains(&name)
        || TYPES.contains(&name)
        || matches!(name, "QQ" | "CInfReal")
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

#[derive(Debug, Clone, PartialEq, Eq)]
enum TokenKind {
    Name(String),
    Number(String),
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
            TokenKind::Name(s) | TokenKind::Number(s) | TokenKind::Symbol(s) => format!("`{s}`"),
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

    fn reject_float(&mut self, mut span: Span) -> Diagnostic {
        self.float_tail();
        span.end = self.offset;
        diagnostic(
            "E_UNSUPPORTED",
            "floating-point literals are not supported; use an exact Nat or Int literal",
            span,
        )
    }

    fn tokenize(mut self) -> Result<Vec<Token>, Diagnostic> {
        let mut tokens = Vec::new();
        while let Some(ch) = self.peek() {
            if ch.is_whitespace() {
                self.advance();
                continue;
            }
            if self.source[self.offset..].starts_with("//") {
                while self.peek().is_some_and(|ch| ch != '\n') {
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
                if let Some(message) = unsupported_keyword(name) {
                    span.end = self.offset;
                    return Err(diagnostic("E_UNSUPPORTED", message, span));
                }
                TokenKind::Name(name.into())
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
                    return Err(self.reject_float(span));
                }
                TokenKind::Number(self.source[span.start..self.offset].into())
            } else {
                let tail = &self.source[self.offset..];
                if ch == '.' && tail.chars().nth(1).is_some_and(|c| c.is_ascii_digit()) {
                    return Err(self.reject_float(span));
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
                } else if let Some(op) = ["->", "==", "!=", "<=", ">=", "&&", "||", "::"]
                    .into_iter()
                    .find(|op| tail.starts_with(op))
                {
                    self.advance();
                    self.advance();
                    TokenKind::Symbol(op.into())
                } else if "(){}<>,:;=+-*!".contains(ch) {
                    self.advance();
                    TokenKind::Symbol(ch.to_string())
                } else {
                    self.advance();
                    span.end = self.offset;
                    return Err(diagnostic(
                        "E_LEX",
                        format!(
                            "unsupported character `{ch}`; use ASCII identifiers and integer literals"
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
    nesting: usize,
    packages: bool,
}

impl Parser {
    fn peek(&self) -> &Token {
        &self.tokens[self.position]
    }
    fn previous(&self) -> &Token {
        &self.tokens[self.position - 1]
    }

    fn advance(&mut self) -> Token {
        let token = self.peek().clone();
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
            self.tokens[self.position] = Token {
                kind: TokenKind::Symbol(">".into()),
                span: Span {
                    end: span.start + 1,
                    ..span
                },
            };
            self.tokens.insert(
                self.position + 1,
                Token {
                    kind: TokenKind::Symbol("=".into()),
                    span: Span {
                        start: span.start + 1,
                        column: span.column + 1,
                        ..span
                    },
                },
            );
        }
        self.expect(">")
    }

    fn name(&mut self) -> Result<(String, Span), Diagnostic> {
        let token = self.advance();
        match token.kind {
            TokenKind::Name(name) if !KEYWORDS.contains(&name.as_str()) => Ok((name, token.span)),
            _ => Err(diagnostic("E_PARSE", "expected an identifier", token.span)),
        }
    }

    fn binding_name(&mut self) -> Result<(String, Span), Diagnostic> {
        let (name, span) = self.name()?;
        if reserved(&name)
            || (self.packages && ["mod", "use", "pub", "self", "super"].contains(&name.as_str()))
        {
            Err(diagnostic(
                "E_RESERVED",
                format!("`{name}` is reserved and cannot be used as a binding name"),
                span,
            ))
        } else {
            Ok((name, span))
        }
    }

    fn module(&mut self, file: &str) -> Result<Module, Diagnostic> {
        let mut functions = Vec::new();
        let mut generics = Vec::new();
        let mut methods = Vec::new();
        while self.peek().kind != TokenKind::Eof {
            if self.peek().is("fn") {
                functions.push(self.function()?);
            } else if self.peek().is("generic") {
                generics.push(self.generic()?);
            } else if self.peek().is("method") {
                methods.push(self.method()?);
            } else {
                return Err(diagnostic(
                    "E_UNSUPPORTED",
                    "modules contain named `fn`, `generic`, and `method` declarations",
                    self.peek().span,
                ));
            }
        }
        Ok(Module {
            version: PROTOCOL_VERSION,
            file: file.into(),
            functions,
            generics,
            methods,
        })
    }

    fn reference_path(&mut self) -> Result<(String, Span), Diagnostic> {
        let (mut path, start) = self.name()?;
        while self.consume("::") {
            let (component, _) = self.name()?;
            path.push_str("::");
            path.push_str(&component);
        }
        Ok((path, start.through(self.previous().span)))
    }

    fn namespace(
        &mut self,
        path: Vec<String>,
        public: bool,
        span: Span,
        inline: bool,
        parsed: &mut crate::packages::Parsed,
    ) -> Result<(), Diagnostic> {
        use crate::packages::{External, Import, Module as NamespaceModule, Public};
        if path.len() > MAX_PARSE_NESTING {
            return Err(diagnostic("E_LIMIT", "module nesting exceeds 64", span));
        }
        let mut module = NamespaceModule {
            path: path.clone(),
            public,
            span,
            imports: Vec::new(),
            functions: Vec::new(),
            generics: Vec::new(),
            methods: Vec::new(),
        };
        while self.peek().kind != TokenKind::Eof && !(inline && self.peek().is("}")) {
            let public = self.consume("pub");
            if self.peek().is("fn") {
                module.functions.push(Public {
                    declaration: self.function()?,
                    public,
                });
            } else if self.peek().is("generic") {
                module.generics.push(Public {
                    declaration: self.generic()?,
                    public,
                });
            } else if self.peek().is("method") && !public {
                module.methods.push(self.method()?);
            } else if self.consume("mod") {
                let start = self.previous().span;
                let (name, _) = self.binding_name()?;
                let mut child = path.clone();
                child.push(name);
                if self.consume(";") {
                    parsed.external.push(External {
                        path: child,
                        public,
                        span: start.through(self.previous().span),
                    });
                } else {
                    self.expect("{")?;
                    self.namespace(child, public, start, true, parsed)?;
                    self.expect("}")?;
                }
            } else if self.consume("use") {
                let start = self.previous().span;
                let (name, _) = self.reference_path()?;
                let components: Vec<String> = name.split("::").map(str::to_owned).collect();
                let alias = if self.consume("as") {
                    self.binding_name()?.0
                } else {
                    components.last().unwrap().clone()
                };
                let end = self.expect(";")?.span;
                module.imports.push(Import {
                    path: components,
                    alias,
                    public,
                    span: start.through(end),
                });
            } else {
                return Err(diagnostic(
                    "E_PARSE",
                    "expected a module-level fn, generic, method, mod, or use declaration; methods cannot be pub",
                    self.peek().span,
                ));
            }
        }
        parsed.modules.push(module);
        Ok(())
    }

    fn parameters(&mut self, selectors: bool) -> Result<Vec<Param>, Diagnostic> {
        self.expect("(")?;
        let mut params = Vec::new();
        if !self.consume(")") {
            loop {
                let (name, start) = self.binding_name()?;
                self.expect(":")?;
                let ty = if selectors {
                    self.dispatch_type(true)?
                } else {
                    self.ty()?
                };
                params.push(Param {
                    name,
                    ty,
                    span: start.through(self.previous().span),
                });
                if self.consume(")") {
                    break;
                }
                self.expect(",")?;
                if self.consume(")") {
                    break;
                }
            }
        }
        Ok(params)
    }

    fn function(&mut self) -> Result<Function, Diagnostic> {
        let start = self.expect("fn")?.span;
        let (name, _) = self.binding_name()?;
        let params = self.parameters(false)?;
        self.expect("->")?;
        let return_type = self.ty()?;
        let body = self.block()?;
        let span = start.through(body.span);
        Ok(Function {
            name,
            params,
            return_type,
            body,
            span,
        })
    }

    fn dispatch_type(&mut self, selector: bool) -> Result<Type, Diagnostic> {
        let (name, span) = self.name()?;
        if matches!(name.as_str(), "Nat" | "Int" | "Bool" | "Unit")
            || (selector && matches!(name.as_str(), "Any" | "Number"))
        {
            Ok(Type::Named { name })
        } else {
            Err(diagnostic(
                "E_TYPE",
                if selector {
                    "a method selector must be Nat, Int, Bool, Unit, Number, or Any"
                } else {
                    "dispatch domains and method results require a concrete scalar type: Nat, Int, Bool, or Unit"
                },
                span,
            ))
        }
    }

    fn generic(&mut self) -> Result<Generic, Diagnostic> {
        let start = self.expect("generic")?.span;
        let (name, _) = self.binding_name()?;
        self.expect("(")?;
        let mut params = Vec::new();
        if !self.consume(")") {
            loop {
                let (name, span) = self.binding_name()?;
                params.push(GenericParam { name, span });
                if self.consume(")") {
                    break;
                }
                self.expect(",")?;
                if self.consume(")") {
                    break;
                }
            }
        }
        self.expect("{")?;
        self.expect("domain")?;
        let mut domain = Vec::new();
        if !self.consume(";") {
            loop {
                self.expect("(")?;
                let mut key = Vec::new();
                if !self.consume(")") {
                    loop {
                        key.push(self.dispatch_type(false)?);
                        if self.consume(")") {
                            break;
                        }
                        self.expect(",")?;
                        if self.consume(")") {
                            break;
                        }
                    }
                }
                domain.push(key);
                if self.consume(";") {
                    break;
                }
                self.expect(",")?;
                if self.consume(";") {
                    break;
                }
            }
        }
        let end = self.expect("}")?.span;
        Ok(Generic {
            name,
            params,
            domain,
            span: start.through(end),
        })
    }

    fn requirements(&mut self) -> Result<Vec<String>, Diagnostic> {
        self.expect("(")?;
        let mut requires = Vec::new();
        if !self.consume(")") {
            loop {
                requires.push(self.name()?.0);
                if self.consume(")") {
                    break;
                }
                self.expect(",")?;
                if self.consume(")") {
                    break;
                }
            }
        }
        Ok(requires)
    }

    fn method(&mut self) -> Result<Method, Diagnostic> {
        let start = self.expect("method")?.span;
        let (name, _) = if self.packages {
            self.reference_path()?
        } else {
            self.binding_name()?
        };
        let params = self.parameters(true)?;
        let before_arrow = self.consume("requires");
        let mut requires = if before_arrow {
            self.requirements()?
        } else {
            Vec::new()
        };
        self.expect("->")?;
        let return_type = self.dispatch_type(false)?;
        if self.peek().is("requires") {
            if before_arrow {
                return Err(diagnostic(
                    "E_PARSE",
                    "a method has only one `requires` clause",
                    self.peek().span,
                ));
            }
            self.advance();
            requires = self.requirements()?;
        }
        let body = self.block()?;
        Ok(Method {
            name,
            params,
            return_type,
            requires,
            span: start.through(body.span),
            body,
        })
    }

    fn ty(&mut self) -> Result<Type, Diagnostic> {
        if self.nesting >= MAX_PARSE_NESTING {
            return Err(diagnostic(
                "E_LIMIT",
                "type nesting exceeds the supported limit",
                self.peek().span,
            ));
        }
        self.nesting += 1;
        let result = self.ty_inner();
        self.nesting -= 1;
        result
    }

    fn ty_inner(&mut self) -> Result<Type, Diagnostic> {
        let (name, span) = self.name()?;
        match name.as_str() {
            "Fn" => {
                self.expect("<")?;
                let mut params = Vec::new();
                if self.consume("(") {
                    if !self.consume(")") {
                        loop {
                            params.push(self.ty()?);
                            if self.consume(")") {
                                break;
                            }
                            self.expect(",")?;
                            if self.consume(")") {
                                break;
                            }
                        }
                    }
                } else {
                    params.push(self.ty()?);
                }
                self.expect(",")?;
                let return_type = Box::new(self.ty()?);
                self.type_close()?;
                Ok(Type::Function {
                    params,
                    return_type,
                })
            }
            "fn" => Err(diagnostic(
                "E_PARSE",
                "function types use Fn<Input, Output>; fn(...) -> ... introduces a function expression",
                span,
            )),
            "Nat" | "Int" | "Bool" | "Unit" | "Scheme" | "CInfScheme" => Ok(Type::Named { name }),
            "Point" => {
                self.expect("<")?;
                let target = self.index()?;
                self.expect(",")?;
                let source = self.index()?;
                self.type_close()?;
                Ok(Type::Point { target, source })
            }
            "Morphism" => {
                self.expect("<")?;
                let source = self.index()?;
                self.expect(",")?;
                let target = self.index()?;
                self.type_close()?;
                Ok(Type::Morphism { source, target })
            }
            "Pointed" => {
                self.expect("<")?;
                let (setting, _) = self.name()?;
                self.expect(",")?;
                let (base, _) = self.name()?;
                self.type_close()?;
                if !matches!(setting.as_str(), "Scheme" | "CInfScheme")
                    || !matches!(base.as_str(), "QQ" | "CInfReal")
                {
                    return Err(diagnostic(
                        "E_TYPE",
                        "Pointed expects a geometric setting and base, such as Pointed<Scheme, QQ>",
                        span,
                    ));
                }
                Ok(Type::Pointed { setting, base })
            }
            _ => Err(diagnostic(
                "E_UNSUPPORTED",
                format!("type `{name}` is not supported"),
                span,
            )),
        }
    }

    fn package_field(&mut self, name: &str) -> Result<(), Diagnostic> {
        if !self.peek().is(name) {
            return Err(diagnostic(
                "E_PARSE",
                "package fields must be written as `scheme`, then `point`",
                self.peek().span,
            ));
        }
        self.advance();
        Ok(())
    }

    fn index(&mut self) -> Result<Index, Diagnostic> {
        let (name, span) = self.name()?;
        if name == "Base" {
            self.expect("(")?;
            let (ring, ring_span) = self.name()?;
            if !matches!(ring.as_str(), "QQ" | "CInfReal") {
                return Err(diagnostic(
                    "E_TYPE",
                    "Base expects QQ or CInfReal",
                    ring_span,
                ));
            }
            self.expect(")")?;
            Ok(Index::Base { ring })
        } else if name.starts_with("__vastitas_") {
            Err(diagnostic(
                "E_RESERVED",
                "the `__vastitas_` prefix is reserved for compiler-generated names",
                span,
            ))
        } else if reserved(&name) {
            Err(diagnostic(
                "E_TYPE",
                "an endpoint index must name an object or use Base(QQ)/Base(CInfReal)",
                span,
            ))
        } else {
            Ok(Index::Name { name })
        }
    }

    fn block(&mut self) -> Result<Block, Diagnostic> {
        let start = self.expect("{")?.span;
        let mut statements = Vec::new();
        while self.peek().is("let") || self.peek().is("unpack") {
            statements.push(self.statement()?);
        }
        if self.peek().is("}") {
            let end = self.advance().span;
            return Ok(Block {
                statements,
                result: Box::new(Expr {
                    kind: ExprKind::Unit,
                    span: end,
                }),
                span: start.through(end),
            });
        }
        let result = self.expression(0)?;
        if self.peek().is(";") {
            return Err(diagnostic(
                "E_UNSUPPORTED",
                "expression statements are not supported; use a `let` binding or leave the final expression without `;`",
                self.peek().span,
            ));
        }
        let end = self.expect("}")?.span;
        Ok(Block {
            statements,
            result: Box::new(result),
            span: start.through(end),
        })
    }

    fn statement(&mut self) -> Result<Statement, Diagnostic> {
        let token = self.advance();
        if token.is("let") {
            let (name, _) = self.binding_name()?;
            let annotation = if self.consume(":") {
                Some(self.ty()?)
            } else {
                None
            };
            self.expect("=")?;
            let value = self.expression(0)?;
            let end = self.expect(";")?.span;
            Ok(Statement {
                kind: StatementKind::Let {
                    name,
                    annotation,
                    value,
                },
                span: token.span.through(end),
            })
        } else {
            let value = self.expression(0)?;
            self.expect("as")?;
            self.expect("{")?;
            self.package_field("scheme")?;
            self.expect(":")?;
            let (scheme, _) = self.binding_name()?;
            self.expect(",")?;
            self.package_field("point")?;
            self.expect(":")?;
            let (point, _) = self.binding_name()?;
            self.consume(",");
            self.expect("}")?;
            let end = self.expect(";")?.span;
            Ok(Statement {
                kind: StatementKind::Unpack {
                    value,
                    scheme,
                    point,
                },
                span: token.span.through(end),
            })
        }
    }

    fn expression(&mut self, min_binding_power: u8) -> Result<Expr, Diagnostic> {
        if self.nesting >= MAX_PARSE_NESTING {
            return Err(diagnostic(
                "E_LIMIT",
                format!("expression nesting exceeds the supported limit of {MAX_PARSE_NESTING}"),
                self.peek().span,
            ));
        }
        self.nesting += 1;
        let result = self.expression_inner(min_binding_power);
        self.nesting -= 1;
        result
    }

    fn expression_inner(&mut self, min_binding_power: u8) -> Result<Expr, Diagnostic> {
        let mut left = self.prefix()?;
        // A prefix may contain a parenthesized comparison, which is a valid
        // operand. Only comparisons consumed by this Pratt invocation chain.
        let mut comparison = false;
        check_expression_depth(&left)?;
        while let TokenKind::Symbol(op) = &self.peek().kind {
            if op == "(" {
                // Else-if parsing requests only the conditional prefix; leave
                // its trailing invocation for the enclosing expression.
                if min_binding_power == u8::MAX {
                    break;
                }
                self.advance();
                let mut args = Vec::new();
                if !self.consume(")") {
                    loop {
                        args.push(self.expression(0)?);
                        if self.consume(")") {
                            break;
                        }
                        self.expect(",")?;
                        if self.consume(")") {
                            break;
                        }
                    }
                }
                let span = left.span.through(self.previous().span);
                left = Expr {
                    kind: match left.kind {
                        ExprKind::Variable { name } => ExprKind::Call { callee: name, args },
                        _ => ExprKind::Invoke {
                            callee: Box::new(left),
                            args,
                        },
                    },
                    span,
                };
                check_expression_depth(&left)?;
                continue;
            }
            let op = op.as_str();
            let power = match op {
                "||" => 1,
                "&&" => 3,
                "==" | "!=" | "<" | "<=" | ">" | ">=" => 5,
                "+" | "-" => 9,
                "*" => 11,
                _ => break,
            };
            if power < min_binding_power {
                break;
            }
            let next_comparison = power == 5;
            if next_comparison && comparison {
                return Err(diagnostic(
                    "E_PARSE",
                    "comparisons cannot be chained; use parentheses or combine comparisons with `&&`",
                    self.peek().span,
                ));
            }
            let op = op.to_string();
            self.advance();
            let right = self.expression(power + 1)?;
            let span = left.span.through(right.span);
            left = Expr {
                kind: ExprKind::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                span,
            };
            comparison = next_comparison;
            check_expression_depth(&left)?;
        }
        Ok(left)
    }

    fn prefix(&mut self) -> Result<Expr, Diagnostic> {
        let token = self.advance();
        let start = token.span;
        let kind = match token.kind {
            TokenKind::Number(value) => {
                let stripped = value.trim_start_matches('0');
                ExprKind::Integer {
                    value: if stripped.is_empty() {
                        "0".into()
                    } else {
                        stripped.into()
                    },
                }
            }
            TokenKind::Name(ref name) if name == "true" || name == "false" => ExprKind::Boolean {
                value: name == "true",
            },
            TokenKind::Name(ref name) if name == "if" => {
                let condition = Box::new(self.expression(0)?);
                let then_branch = self.block()?;
                self.expect("else")?;
                let else_branch = if self.peek().is("if") {
                    // Parse just the conditional prefix with the usual depth
                    // guard. Operators after its final block still belong to
                    // the surrounding expression, not the synthetic block.
                    let result = self.expression(u8::MAX)?;
                    Block {
                        span: result.span,
                        statements: Vec::new(),
                        result: Box::new(result),
                    }
                } else {
                    self.block()?
                };
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                }
            }
            TokenKind::Name(ref name) if name == "pack" => {
                self.expect("{")?;
                self.package_field("scheme")?;
                self.expect(":")?;
                let scheme = Box::new(self.expression(0)?);
                self.expect(",")?;
                self.package_field("point")?;
                self.expect(":")?;
                let point = Box::new(self.expression(0)?);
                self.consume(",");
                self.expect("}")?;
                ExprKind::Pack { scheme, point }
            }
            TokenKind::Name(ref name) if name == "fn" => {
                let params = self.parameters(false)?;
                self.expect("->")?;
                let return_type = self.ty()?;
                let body = self.block()?;
                ExprKind::Lambda {
                    params,
                    return_type,
                    body,
                }
            }
            TokenKind::Name(mut name) if !KEYWORDS.contains(&name.as_str()) => {
                if self.packages {
                    while self.consume("::") {
                        let (component, _) = self.name()?;
                        name.push_str("::");
                        name.push_str(&component);
                    }
                }
                ExprKind::Variable { name }
            }
            TokenKind::Symbol(ref op) if op == "-" || op == "!" => ExprKind::Unary {
                op: op.clone(),
                operand: Box::new(self.expression(13)?),
            },
            TokenKind::Symbol(ref symbol) if symbol == "(" => {
                if self.consume(")") {
                    ExprKind::Unit
                } else {
                    let inner = self.expression(0)?;
                    self.expect(")")?;
                    return Ok(Expr {
                        span: start.through(self.previous().span),
                        ..inner
                    });
                }
            }
            TokenKind::Symbol(ref symbol) if symbol == "{" => {
                self.position -= 1;
                ExprKind::Block {
                    body: self.block()?,
                }
            }
            _ => {
                return Err(diagnostic(
                    "E_PARSE",
                    format!("expected an expression, found {}", token.description()),
                    start,
                ));
            }
        };
        Ok(Expr {
            kind,
            span: start.through(self.previous().span),
        })
    }
}

/// Inspect the AST without recursion, before handing it to recursive consumers.
/// Each child tree has already passed this check. A rejected parent adds only
/// its bounded syntax layers, so unwinding and dropping it are bounded as well.
fn check_expression_depth(root: &Expr) -> Result<(), Diagnostic> {
    enum Node<'a> {
        Expr(&'a Expr),
        Block(&'a Block),
        Statement(&'a Statement),
    }
    let mut pending = vec![(Node::Expr(root), 1)];
    while let Some((node, depth)) = pending.pop() {
        if depth > MAX_AST_DEPTH {
            return Err(diagnostic(
                "E_LIMIT",
                format!("expression tree exceeds the supported depth limit of {MAX_AST_DEPTH}"),
                root.span,
            ));
        }
        let next = depth + 1;
        match node {
            Node::Expr(expr) => match &expr.kind {
                ExprKind::Lambda { body, .. } => pending.push((Node::Block(body), next)),
                ExprKind::Invoke { callee, args } => {
                    pending.push((Node::Expr(callee), next));
                    pending.extend(args.iter().map(|arg| (Node::Expr(arg), next)));
                }
                ExprKind::Call { args, .. } => {
                    pending.extend(args.iter().map(|arg| (Node::Expr(arg), next)));
                }
                ExprKind::Unary { operand, .. } => {
                    pending.push((Node::Expr(operand), next));
                }
                ExprKind::Binary { left, right, .. } => {
                    pending.push((Node::Expr(left), next));
                    pending.push((Node::Expr(right), next));
                }
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push((Node::Expr(condition), next));
                    pending.push((Node::Block(then_branch), next));
                    pending.push((Node::Block(else_branch), next));
                }
                ExprKind::Block { body } => pending.push((Node::Block(body), next)),
                ExprKind::Pack { scheme, point } => {
                    pending.push((Node::Expr(scheme), next));
                    pending.push((Node::Expr(point), next));
                }
                ExprKind::Integer { .. }
                | ExprKind::Boolean { .. }
                | ExprKind::Unit
                | ExprKind::Variable { .. } => {}
            },
            Node::Block(block) => {
                pending.push((Node::Expr(&block.result), next));
                pending.extend(
                    block
                        .statements
                        .iter()
                        .map(|statement| (Node::Statement(statement), next)),
                );
            }
            Node::Statement(statement) => match &statement.kind {
                StatementKind::Let { value, .. } | StatementKind::Unpack { value, .. } => {
                    pending.push((Node::Expr(value), next));
                }
            },
        }
    }
    Ok(())
}

struct Resolver<'a> {
    functions: HashMap<&'a str, usize>,
    generics: HashSet<&'a str>,
    errors: Vec<Diagnostic>,
    calls: Vec<Vec<usize>>,
    forbidden: Vec<HashSet<&'a str>>,
}

impl<'a> Resolver<'a> {
    fn module(module: &'a Module) -> Vec<Diagnostic> {
        let mut this = Self {
            functions: HashMap::new(),
            generics: HashSet::new(),
            errors: Vec::new(),
            calls: vec![Vec::new(); module.functions.len()],
            forbidden: Vec::new(),
        };
        for (i, function) in module.functions.iter().enumerate() {
            if this.functions.insert(&function.name, i).is_some() {
                this.errors.push(diagnostic(
                    "E_DUPLICATE",
                    format!("function `{}` is defined more than once", function.name),
                    function.span,
                ));
            }
        }
        for generic in &module.generics {
            if !this.generics.insert(&generic.name)
                || this.functions.contains_key(generic.name.as_str())
            {
                this.errors.push(diagnostic(
                    "E_DUPLICATE",
                    format!("callable `{}` is defined more than once", generic.name),
                    generic.span,
                ));
            }
            if generic.name == "main" {
                this.errors.push(diagnostic(
                    "E_MAIN",
                    "the entrypoint must be an ordinary `fn main() -> Int`, not a generic",
                    generic.span,
                ));
            }
        }
        for generic in &module.generics {
            let mut scope = HashSet::new();
            for param in &generic.params {
                this.bind(&param.name, &mut scope, param.span);
            }
        }
        for (i, function) in module.functions.iter().enumerate() {
            let mut scope = HashSet::new();
            for param in &function.params {
                this.ty(&param.ty, &scope, param.span);
                this.bind(&param.name, &mut scope, param.span);
            }
            this.ty(&function.return_type, &scope, function.span);
            this.block(&function.body, &scope, Some(i));
        }
        for method in &module.methods {
            if !this.generics.contains(method.name.as_str()) {
                this.errors.push(diagnostic(
                    "E_NAME",
                    format!(
                        "method `{}` requires a declared generic of the same name",
                        method.name
                    ),
                    method.span,
                ));
            }
            let mut scope = HashSet::new();
            for param in &method.params {
                this.bind(&param.name, &mut scope, param.span);
            }
            // The backend resolves generic calls after specialization. Adding
            // family-name edges here could invent cycles between disjoint
            // concrete method instances.
            this.block(&method.body, &scope, None);
        }
        let mut marks = vec![0; module.functions.len()];
        for i in 0..module.functions.len() {
            if let Some(cycle) = this.cycle(i, &mut marks) {
                let path = cycle
                    .iter()
                    .map(|&id| format!("`{}`", module.functions[id].name))
                    .collect::<Vec<_>>()
                    .join(" → ");
                this.errors.push(diagnostic(
                    "E_RECURSION",
                    format!("recursive call cycle {path} is not supported"),
                    module.functions[cycle[0]].span,
                ));
                break;
            }
        }
        this.errors
    }

    fn cycle(&self, current: usize, marks: &mut [u8]) -> Option<Vec<usize>> {
        if marks[current] != 0 {
            return None;
        }
        marks[current] = 1;
        // Call chains are independent of expression depth, so keep DFS frames
        // on the heap. Only the current path is active (mark 1); shared callees
        // that have finished (mark 2) do not indicate recursion.
        let mut pending = vec![(current, 0)];
        while let Some((current, edge)) = pending.last_mut() {
            if let Some(&next) = self.calls[*current].get(*edge) {
                *edge += 1;
                match marks[next] {
                    1 => {
                        let start = pending.iter().position(|&(id, _)| id == next).unwrap();
                        let mut cycle: Vec<_> =
                            pending[start..].iter().map(|&(id, _)| id).collect();
                        cycle.push(next);
                        return Some(cycle);
                    }
                    0 => {
                        marks[next] = 1;
                        pending.push((next, 0));
                    }
                    _ => {}
                }
            } else {
                marks[*current] = 2;
                pending.pop();
            }
        }
        None
    }

    fn bind(&mut self, name: &'a str, scope: &mut HashSet<&'a str>, span: Span) {
        if self.functions.contains_key(name) || self.generics.contains(name) {
            self.errors.push(diagnostic(
                "E_SHADOW",
                format!("binding `{name}` shadows a callable; use a distinct name"),
                span,
            ));
        }
        if !scope.insert(name) {
            self.errors.push(diagnostic(
                "E_DUPLICATE",
                format!(
                    "binding `{name}` already exists in this scope; shadowing is not supported"
                ),
                span,
            ));
        }
    }

    fn index(&mut self, index: &Index, scope: &HashSet<&str>, span: Span) {
        if let Index::Name { name } = index
            && name.starts_with("__vastitas_")
        {
            self.errors.push(diagnostic(
                "E_RESERVED",
                "the `__vastitas_` prefix is reserved for compiler-generated names",
                span,
            ));
            return;
        }
        if let Index::Name { name } = index
            && !scope.contains(name.as_str())
        {
            if self
                .forbidden
                .iter()
                .any(|outer| outer.contains(name.as_str()))
            {
                self.errors.push(diagnostic("E_CAPTURE", format!("independent lambda cannot capture endpoint `{name}`; pass it as an explicit parameter"), span));
                return;
            }
            self.errors.push(diagnostic("E_NAME", format!("unknown endpoint object `{name}`; dependent types can refer only to earlier bindings"), span));
        }
    }

    fn ty(&mut self, ty: &Type, scope: &HashSet<&str>, span: Span) {
        match ty {
            Type::Function {
                params,
                return_type,
            } => {
                for param in params {
                    self.ty(param, scope, span);
                }
                self.ty(return_type, scope, span);
            }
            Type::Point { target, source } | Type::Morphism { target, source } => {
                self.index(target, scope, span);
                self.index(source, scope, span);
            }
            _ => {}
        }
    }

    fn block(&mut self, block: &'a Block, outer: &HashSet<&'a str>, function: Option<usize>) {
        let mut scope = outer.clone();
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Let {
                    name,
                    annotation,
                    value,
                } => {
                    if let Some(ty) = annotation {
                        self.ty(ty, &scope, statement.span);
                    }
                    self.expr(value, &scope, function, false);
                    self.bind(name, &mut scope, statement.span);
                }
                StatementKind::Unpack {
                    value,
                    scheme,
                    point,
                } => {
                    self.expr(value, &scope, function, false);
                    self.bind(scheme, &mut scope, statement.span);
                    self.bind(point, &mut scope, statement.span);
                }
            }
        }
        self.expr(&block.result, &scope, function, false);
    }

    fn expr(
        &mut self,
        expr: &'a Expr,
        scope: &HashSet<&'a str>,
        function: Option<usize>,
        ring_position: bool,
    ) {
        match &expr.kind {
            ExprKind::Lambda {
                params,
                return_type,
                body,
            } => {
                self.forbidden.push(scope.clone());
                let mut local = HashSet::new();
                for param in params {
                    self.ty(&param.ty, &local, param.span);
                    self.bind(&param.name, &mut local, param.span);
                }
                self.ty(return_type, &local, expr.span);
                // The lambda is an independent definition. Its calls are not
                // edges from the enclosing function; Lean checks them after
                // lifting and static specialization.
                self.block(body, &local, None);
                self.forbidden.pop();
            }
            ExprKind::Invoke { callee, args } => {
                self.expr(callee, scope, function, false);
                for arg in args {
                    self.expr(arg, scope, function, false);
                }
            }
            ExprKind::Variable { name } => {
                if name.starts_with("__vastitas_") {
                    self.errors.push(diagnostic(
                        "E_RESERVED",
                        "the `__vastitas_` prefix is reserved for compiler-generated names",
                        expr.span,
                    ));
                } else if matches!(name.as_str(), "QQ" | "CInfReal") {
                    if !ring_position {
                        self.errors.push(diagnostic("E_RING", format!("`{name}` is a coefficient-ring marker, usable only in Affine or Base"), expr.span));
                    }
                } else if !scope.contains(name.as_str())
                    && !self.functions.contains_key(name.as_str())
                {
                    if self
                        .forbidden
                        .iter()
                        .any(|outer| outer.contains(name.as_str()))
                    {
                        self.errors.push(diagnostic("E_CAPTURE", format!("independent lambda cannot capture `{name}`; pass it as an explicit parameter"), expr.span));
                        return;
                    }
                    if self.generics.contains(name.as_str()) {
                        self.errors.push(diagnostic("E_TYPE", "a generic is not a Fn value; use an explicit ordinary-function wrapper", expr.span));
                        return;
                    }
                    self.errors.push(diagnostic(
                        "E_NAME",
                        format!("unknown value `{name}`"),
                        expr.span,
                    ));
                }
            }
            ExprKind::Call { callee, args } => {
                if callee.starts_with("__vastitas_") {
                    self.errors.push(diagnostic(
                        "E_RESERVED",
                        "the `__vastitas_` prefix is reserved for compiler-generated names",
                        expr.span,
                    ));
                } else if let Some(&target) = self.functions.get(callee.as_str()) {
                    if let Some(function) = function {
                        self.calls[function].push(target);
                    }
                } else if scope.contains(callee.as_str()) {
                    // Function-valued bindings are checked independently by Lean.
                } else if self
                    .forbidden
                    .iter()
                    .any(|outer| outer.contains(callee.as_str()))
                {
                    self.errors.push(diagnostic("E_CAPTURE", format!("independent lambda cannot capture `{callee}`; pass it as an explicit parameter"), expr.span));
                } else if !self.generics.contains(callee.as_str())
                    && !BUILTINS.contains(&callee.as_str())
                {
                    self.errors.push(diagnostic("E_NAME", format!("unknown function `{callee}`; calls require a declared function, generic, or supported builtin"), expr.span));
                }
                for (i, arg) in args.iter().enumerate() {
                    self.expr(
                        arg,
                        scope,
                        function,
                        i == 0 && matches!(callee.as_str(), "Affine" | "Base"),
                    );
                }
            }
            ExprKind::Unary { operand, .. } => self.expr(operand, scope, function, false),
            ExprKind::Binary { left, right, .. } => {
                self.expr(left, scope, function, false);
                self.expr(right, scope, function, false);
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition, scope, function, false);
                self.block(then_branch, scope, function);
                self.block(else_branch, scope, function);
            }
            ExprKind::Block { body } => self.block(body, scope, function),
            ExprKind::Pack { scheme, point } => {
                self.expr(scheme, scope, function, false);
                self.expr(point, scope, function, false);
            }
            ExprKind::Integer { .. } | ExprKind::Boolean { .. } | ExprKind::Unit => {}
        }
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
        file: first.file.into(),
        functions: Vec::new(),
        generics: Vec::new(),
        methods: Vec::new(),
    };
    for input in sources {
        if input.offset.checked_add(input.source.len()).is_none() {
            return Err(vec![diagnostic(
                "E_LIMIT",
                "source byte positions exceed the supported range",
                Span {
                    start: input.offset,
                    end: input.offset,
                    line: 1,
                    column: 1,
                },
            )]);
        }
        let shift = |span: &mut Span| {
            span.start += input.offset;
            span.end += input.offset;
        };
        let mut tokens = Lexer::new(input.source).tokenize().map_err(|mut error| {
            shift(&mut error.span);
            vec![error]
        })?;
        for token in &mut tokens {
            shift(&mut token.span);
        }
        let parsed = Parser {
            tokens,
            position: 0,
            nesting: 0,
            packages: false,
        }
        .module(input.file)
        .map_err(|error| vec![error])?;
        module.functions.extend(parsed.functions);
        module.generics.extend(parsed.generics);
        module.methods.extend(parsed.methods);
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
    let span = declaration.unwrap_or(tokens[0].span);
    let mut parser = Parser {
        tokens,
        position: 0,
        nesting: 0,
        packages: true,
    };
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
mod tests {
    use super::*;

    #[test]
    fn parses_and_serializes_generic_families_without_selecting_methods() {
        let source = "method choose(x: Number) -> Int requires (HasOrder, HasEq) { 1 }
generic choose(x) { domain (Int), (Nat); }
method choose(x: Any) requires (HasEq) -> Int { 2 }
fn main() -> Int { choose(10) }";
        let module = parse(source, "dispatch.vast").unwrap();
        assert_eq!(module.version, 2);
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.generics.len(), 1);
        assert_eq!(module.methods.len(), 2);
        assert_eq!(module.generics[0].params[0].name, "x");
        assert_eq!(module.methods[0].requires, ["HasOrder", "HasEq"]);
        assert_eq!(module.methods[1].requires, ["HasEq"]);
        assert!(matches!(
            &module.functions[0].body.result.kind,
            ExprKind::Call { callee, .. } if callee == "choose"
        ));
        let encoded = serde_json::to_value(&module).unwrap();
        assert_eq!(encoded["version"], 2);
        assert_eq!(encoded["generics"][0]["domain"][0][0]["name"], "Int");
        assert_eq!(encoded["methods"][0]["params"][0]["ty"]["name"], "Number");
        assert_eq!(encoded["methods"][1]["return_type"]["name"], "Int");
        let decoded: Module = serde_json::from_value(encoded).unwrap();
        assert_eq!(decoded, module);
    }

    #[test]
    fn separate_sources_preserve_all_dispatch_declarations_and_spans() {
        let application = "fn main() -> Int { choose(1) }";
        let family = "// family\ngeneric choose(value) { domain (Int); }";
        let implementation = "// implementation\nmethod choose(x: Int) -> Int { helper(x) }";
        let helper = "fn helper(n: Int) -> Int { n + 1 }";
        let module = parse_sources(&[
            SourceInput {
                source: application,
                file: "main.vast",
                offset: 0,
            },
            SourceInput {
                source: family,
                file: "interface.vast",
                offset: 100,
            },
            SourceInput {
                source: implementation,
                file: "implementation.vast",
                offset: 200,
            },
            SourceInput {
                source: helper,
                file: "helper.vast",
                offset: 300,
            },
        ])
        .unwrap();
        assert_eq!(module.functions.len(), 2);
        assert_eq!(module.generics.len(), 1);
        assert_eq!(module.methods.len(), 1);
        assert_eq!(
            module.generics[0].span.start,
            100 + family.find("generic").unwrap()
        );
        assert_eq!(module.generics[0].span.line, 2);
        assert_eq!(
            module.generics[0].params[0].span.start,
            100 + family.find("value").unwrap()
        );
        assert_eq!(
            module.methods[0].span.start,
            200 + implementation.find("method").unwrap()
        );
        assert_eq!(module.methods[0].span.line, 2);
        assert_eq!(
            module.methods[0].body.result.span.start,
            200 + implementation.find("helper").unwrap()
        );
    }

    #[test]
    fn dispatch_domains_support_empty_and_zero_argument_families() {
        let module = parse(
            "generic empty(x,) { domain; }
generic constant() { domain (),; }
method constant() -> Int requires () { 42 }",
            "empty.vast",
        )
        .unwrap();
        assert!(module.generics[0].domain.is_empty());
        assert_eq!(module.generics[1].domain, vec![vec![]]);
        assert!(module.methods[0].params.is_empty());
        assert!(module.methods[0].requires.is_empty());
    }

    #[test]
    fn dispatch_selectors_are_not_ordinary_value_types() {
        for source in [
            "generic f(x) { domain (Number); }",
            "generic f(x) { domain (Scheme); }",
            "generic f(x) { domain (Int); } method f(x: Scheme) -> Int { 0 }",
            "generic f(x) { domain (Int); } method f(x: Int) -> Any { x }",
            "generic f(x) { domain (Int); } method f(x: Int) -> Pointed<Scheme, QQ> { x }",
        ] {
            assert_eq!(parse(source, "types.vast").unwrap_err()[0].code, "E_TYPE");
        }
        for source in [
            "fn f(x: Any) -> Int { 0 }",
            "generic f(x) { domain (Int); } method f(x: Number) -> Int { let y: Number = x; 0 }",
        ] {
            assert_eq!(
                parse(source, "types.vast").unwrap_err()[0].code,
                "E_UNSUPPORTED"
            );
        }
    }

    #[test]
    fn generic_namespace_and_method_lexical_scope_are_checked() {
        for (source, code) in [
            (
                "generic f(x) { domain; } generic f(x) { domain; }",
                "E_DUPLICATE",
            ),
            (
                "fn f() -> Int { 0 } generic f(x) { domain; }",
                "E_DUPLICATE",
            ),
            ("method missing(x: Int) -> Int { x }", "E_NAME"),
            ("generic main() { domain (); }", "E_MAIN"),
            ("generic f(x, x) { domain; }", "E_DUPLICATE"),
            (
                "generic f(x) { domain; } fn g() -> Int { let f = 1; f }",
                "E_SHADOW",
            ),
            (
                "generic f(x) { domain (Int); } method f(f: Int) -> Int { f }",
                "E_SHADOW",
            ),
            (
                "generic f(x) { domain (Int); } method f(x: Int) -> Int { hidden }",
                "E_NAME",
            ),
            (
                "generic f(x) { domain (Int); } method f(x: Int) -> Int { let x = 1; x }",
                "E_DUPLICATE",
            ),
            (
                "generic f(x) { domain (Int); } method f(x: Int) -> Int { x } method f(y: Nat) -> Int { x }",
                "E_NAME",
            ),
        ] {
            let errors = parse(source, "names.vast").unwrap_err();
            assert_eq!(errors[0].code, code, "{source}");
        }
        let invalid_method = "\nmethod f(x: Int) -> Int { unknown }";
        let errors = parse_sources(&[
            SourceInput {
                source: "generic f(x) { domain (Int); }",
                file: "family.vast",
                offset: 0,
            },
            SourceInput {
                source: invalid_method,
                file: "method.vast",
                offset: 100,
            },
        ])
        .unwrap_err();
        assert_eq!(errors[0].code, "E_NAME");
        assert_eq!(errors[0].span.line, 2);
        assert_eq!(
            errors[0].span.start,
            100 + invalid_method.find("unknown").unwrap()
        );
    }

    #[test]
    fn generic_recursion_and_capability_semantics_are_deferred_to_lean() {
        // The Int instance can call the Bool instance without recursion. Only
        // the backend knows which concrete method an application selects.
        let module = parse(
            "generic choose(x) { domain (Int), (Bool); }
method choose(x: Int) -> Int { choose(true) }
method choose(x: Bool) -> Int { 1 }
fn main() -> Int { choose(0) }",
            "instances.vast",
        )
        .unwrap();
        assert_eq!(module.methods.len(), 2);
        // The frontend also keeps genuinely cyclic generic calls intact; Lean
        // must reject the eventual cycle after independently selecting targets.
        parse(
            "generic f(x) { domain (Int); } method f(x: Int) -> Int { f(x) }",
            "cycle.vast",
        )
        .unwrap();
        let module = parse(
            "generic f(x) { domain (Int); } method f(x: Int) -> Int requires (HasMetric) { 0 }",
            "capability.vast",
        )
        .unwrap();
        assert_eq!(module.methods[0].requires, ["HasMetric"]);
    }

    #[test]
    fn rejects_duplicate_requires_and_compiler_private_names() {
        let errors = parse(
            "generic f(x) { domain (Int); } method f(x: Int) requires () -> Int requires () { 0 }",
            "requires.vast",
        )
        .unwrap_err();
        assert_eq!(errors[0].code, "E_PARSE");
        assert!(errors[0].message.contains("only one `requires`"));
        for source in [
            "fn __vastitas_internal() -> Int { 0 }",
            "generic __vastitas_internal(x) { domain; }",
            "fn main() -> Int { __vastitas_method_1(0) }",
            "fn main() -> Int { __vastitas_value }",
            "fn f(X: Scheme, p: Point<__vastitas_object, Base(QQ)>) -> Int { 0 }",
        ] {
            assert_eq!(
                parse(source, "private.vast").unwrap_err()[0].code,
                "E_RESERVED"
            );
        }
    }

    #[test]
    fn resolves_forward_calls_across_separately_parsed_files() {
        let sources = [
            SourceInput {
                source: "fn main() -> Int { helper(21) }",
                file: "main.vast",
                offset: 0,
            },
            SourceInput {
                source: "fn helper(x: Int) -> Int { x + x }",
                file: "library.vast",
                offset: 100,
            },
        ];
        let module = parse_sources(&sources).unwrap();
        assert_eq!(module.file, "main.vast");
        assert_eq!(module.functions.len(), 2);
        assert_eq!(module.functions[1].span.start, 100);
        assert_eq!(module.functions[1].span.line, 1);
        serde_json::to_vec(&module).unwrap();
    }

    #[test]
    fn syntax_cannot_continue_into_another_file() {
        let unfinished = "fn main() -> Int {";
        let errors = parse_sources(&[
            SourceInput {
                source: unfinished,
                file: "main.vast",
                offset: 0,
            },
            SourceInput {
                source: "1 }",
                file: "library.vast",
                offset: 100,
            },
        ])
        .unwrap_err();
        assert_eq!(errors[0].span.start, unfinished.len());
        assert!(errors[0].message.contains("end of file"));
    }

    #[test]
    fn multifile_diagnostics_keep_local_lines_and_global_byte_offsets() {
        let bad = "// 数学\nfn bad() -> Int { missing }";
        let errors = parse_sources(&[
            SourceInput {
                source: "fn main() -> Int { 0 }",
                file: "main.vast",
                offset: 0,
            },
            SourceInput {
                source: bad,
                file: "library.vast",
                offset: 100,
            },
        ])
        .unwrap_err();
        assert_eq!(errors[0].code, "E_NAME");
        assert_eq!(errors[0].span.start, 100 + bad.find("missing").unwrap());
        assert_eq!(errors[0].span.line, 2);
        assert_eq!(errors[0].span.column, 19);

        let errors = parse_sources(&[SourceInput {
            source: "// 数学\n@",
            file: "library.vast",
            offset: 100,
        }])
        .unwrap_err();
        assert_eq!(errors[0].span.start, 100 + "// 数学\n".len());
        assert_eq!(errors[0].span.line, 2);
        assert_eq!(errors[0].span.column, 1);
    }

    #[test]
    fn rejects_duplicate_and_recursive_definitions_across_files() {
        let errors = parse_sources(&[
            SourceInput {
                source: "fn value() -> Int { 1 }",
                file: "first.vast",
                offset: 0,
            },
            SourceInput {
                source: "fn value() -> Int { 2 }",
                file: "second.vast",
                offset: 100,
            },
        ])
        .unwrap_err();
        assert_eq!(errors[0].code, "E_DUPLICATE");
        assert_eq!(errors[0].span.start, 100);

        let errors = parse_sources(&[
            SourceInput {
                source: "fn first() -> Int { second() }",
                file: "first.vast",
                offset: 0,
            },
            SourceInput {
                source: "fn second() -> Int { first() }",
                file: "second.vast",
                offset: 100,
            },
        ])
        .unwrap_err();
        assert_eq!(errors[0].code, "E_RECURSION");
    }

    #[test]
    fn rejects_empty_source_lists_and_overflowing_offsets() {
        assert_eq!(parse_sources(&[]).unwrap_err()[0].code, "E_INPUT");
        let errors = parse_sources(&[SourceInput {
            source: "fn main() -> Int { 1 }",
            file: "main.vast",
            offset: usize::MAX,
        }])
        .unwrap_err();
        assert_eq!(errors[0].code, "E_LIMIT");
    }

    fn assert_limit(expression: &str) {
        let source =
            format!("fn passthrough(x: Int) -> Int {{ x }} fn main() -> Int {{ {expression} }}");
        let errors = parse(&source, "depth.vast").unwrap_err();
        assert_eq!(errors[0].code, "E_LIMIT", "unexpected error: {errors:?}");
    }

    #[test]
    fn rejects_deep_parentheses_unary_calls_blocks_and_conditionals() {
        assert_limit(&format!("{}1{}", "(".repeat(512), ")".repeat(512)));
        assert_limit(&format!("{}1", "-".repeat(512)));
        assert_limit(&format!(
            "{}1{}",
            "passthrough(".repeat(512),
            ")".repeat(512)
        ));
        assert_limit(&format!("{}1{}", "{".repeat(512), "}".repeat(512)));
        assert_limit(&format!(
            "{}1{}",
            "if true { 0 } else { ".repeat(512),
            "}".repeat(512)
        ));
    }

    #[test]
    fn caps_left_associated_trees_before_recursive_consumers() {
        assert_limit(&vec!["1"; MAX_AST_DEPTH + 1].join(" + "));
        // Each inner chain is individually shallow. Their combined AST depth
        // must still be bounded, rather than applying only a per-loop limit.
        let inner = vec!["1"; 100].join(" + ");
        let mut outer = vec!["1"; 100];
        let wrapped = format!("({inner})");
        outer.insert(0, &wrapped);
        assert_limit(&outer.join(" + "));
    }

    #[test]
    fn ordinary_nesting_and_bounded_chains_still_parse_and_serialize() {
        let nested = format!("{}1{}", "(".repeat(16), ")".repeat(16));
        let chain = vec!["1"; 64].join(" + ");
        for expr in [nested, chain] {
            let source = format!("fn main() -> Int {{ {expr} }}");
            let module = parse(&source, "bounded.vast").unwrap();
            serde_json::to_vec(&module).unwrap();
        }
    }

    #[test]
    fn precedence_and_arbitrary_precision_survive_serialization() {
        let module = parse(
            "fn main() -> Int { 123456789012345678901234567890 + 2 * 3 }",
            "arithmetic.vast",
        )
        .unwrap();
        let ExprKind::Binary { op, left, right } = &module.functions[0].body.result.kind else {
            panic!("binary expression expected")
        };
        assert_eq!(op, "+");
        assert!(
            matches!(&left.kind, ExprKind::Integer { value } if value == "123456789012345678901234567890")
        );
        assert!(matches!(&right.kind, ExprKind::Binary { op, .. } if op == "*"));
        let json = serde_json::to_value(&module).unwrap();
        assert_eq!(json["functions"][0]["body"]["result"]["kind"], "binary");
        let decoded: Module = serde_json::from_value(json).unwrap();
        assert_eq!(module, decoded);
    }

    #[test]
    fn parses_dependent_point_package_and_forward_calls() {
        let source = r#"
fn main() -> Int {
    let problem = make_origin(2);
    unpack problem as { scheme: X, point: p };
    let q: Point<X, Base(QQ)> = keep(X, p);
    0
}
fn keep(X: Scheme, p: Point<X, Base(QQ)>) -> Point<X, Base(QQ)> {
    apply(id(X), p)
}
fn make_origin(n: Nat) -> Pointed<Scheme, QQ> {
    let X = Affine(QQ, n);
    pack { scheme: X, point: origin(X) }
}
"#;
        let module = parse(source, "geometry.vast").unwrap();
        assert_eq!(module.functions.len(), 3);
        assert!(matches!(
            module.functions[1].return_type,
            Type::Point { .. }
        ));
    }

    #[test]
    fn unicode_comments_keep_byte_offsets_and_character_columns() {
        let source = "// 幾何\nfn main() -> Int {　missing }";
        let errors = parse(source, "unicode.vast").unwrap_err();
        assert_eq!(errors[0].span.line, 2);
        assert_eq!(errors[0].span.column, 20);
        assert_eq!(&source[errors[0].span.start..errors[0].span.end], "missing");
    }

    #[test]
    fn catches_mutual_recursion() {
        let errors =
            parse("fn a() -> Int { b() } fn b() -> Int { a() }", "cycle.vast").unwrap_err();
        assert!(errors.iter().any(|e| e.code == "E_RECURSION"));
    }

    #[test]
    fn recursion_diagnostic_names_the_cycle_not_its_caller() {
        let source = "fn main() -> Int { a() }\nfn a() -> Int { b() }\nfn b() -> Int { a() }";
        let errors = parse(source, "cycle.vast").unwrap_err();
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].code, "E_RECURSION");
        assert_eq!(
            errors[0].message,
            "recursive call cycle `a` → `b` → `a` is not supported"
        );
        assert_eq!(errors[0].span.line, 2);
        assert_eq!(errors[0].span.start, source.find("fn a").unwrap());
    }

    #[test]
    fn handles_long_call_chains_and_late_cycles_without_stack_recursion() {
        use std::fmt::Write;

        const COUNT: usize = 50_000;
        let mut source = String::new();
        for i in 0..COUNT - 1 {
            writeln!(source, "fn f{i}() -> Int {{ f{}() }}", i + 1).unwrap();
        }
        let tail = source.len();
        writeln!(source, "fn f{}() -> Int {{ 0 }}", COUNT - 1).unwrap();
        assert_eq!(parse(&source, "chain.vast").unwrap().functions.len(), COUNT);

        source.truncate(tail);
        writeln!(source, "fn f{}() -> Int {{ f{}() }}", COUNT - 1, COUNT / 2).unwrap();
        let errors = parse(&source, "cycle.vast").unwrap_err();
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].code, "E_RECURSION");
        assert!(errors[0].message.contains("`f25000` → `f25001`"));
        assert!(errors[0].message.contains("`f49999` → `f25000`"));
        assert!(!errors[0].message.contains("`f0`"));
        assert_eq!(errors[0].span.line, COUNT / 2 + 1);
    }

    #[test]
    fn shared_callees_are_not_cycles_and_disconnected_cycles_are_checked() {
        let source = "fn root() -> Int { left() + right() + left() }
fn left() -> Int { leaf() }
fn right() -> Int { leaf() }
fn leaf() -> Int { 0 }";
        parse(source, "diamond.vast").unwrap();
        let errors = parse(
            &format!("{source}\nfn looped() -> Int {{ looped() }}"),
            "disconnected.vast",
        )
        .unwrap_err();
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].code, "E_RECURSION");
        assert!(errors[0].message.contains("`looped`"));
        assert_eq!(errors[0].span.line, 5);
    }

    #[test]
    fn rejects_unknown_endpoint_and_scope_escape() {
        let errors = parse(
            "fn main() -> Int { let q = { let n = 2; n }; n }",
            "scope.vast",
        )
        .unwrap_err();
        assert!(errors.iter().any(|e| e.message == "unknown value `n`"));
        let errors = parse(
            "fn f(p: Point<X, Base(QQ)>, X: Scheme) -> Int { 0 }",
            "forward.vast",
        )
        .unwrap_err();
        assert!(
            errors
                .iter()
                .any(|e| e.message.contains("unknown endpoint object `X`"))
        );
    }

    #[test]
    fn type_closer_can_touch_assignment_without_changing_comparisons() {
        let source = "fn f(X: Scheme) -> Int {
    let p: Point<X, Base(QQ)>= origin(X);
    let m: Morphism<X, X>= id(X);
    let package: Pointed<Scheme, QQ>= pack { scheme: X, point: p };
    if 3 >= 2 { 1 } else { 0 }
}";
        let module = parse(source, "type-close.vast").unwrap();
        assert_eq!(module.functions[0].body.statements.len(), 3);
        let ExprKind::If { condition, .. } = &module.functions[0].body.result.kind else {
            panic!("expected conditional");
        };
        assert!(matches!(&condition.kind, ExprKind::Binary { op, .. } if op == ">="));

        let tokens = Lexer::new(">=").tokenize().unwrap();
        let mut parser = Parser {
            tokens,
            position: 0,
            nesting: 0,
            packages: false,
        };
        let close = parser.type_close().unwrap();
        let assignment = parser.expect("=").unwrap();
        assert_eq!(
            (close.span.start, close.span.end, close.span.column),
            (0, 1, 1)
        );
        assert_eq!(
            (
                assignment.span.start,
                assignment.span.end,
                assignment.span.column
            ),
            (1, 2, 2)
        );
    }

    #[test]
    fn comparison_chains_require_explicit_grouping() {
        for expression in [
            "1 == 1 == true",
            "1 < 2 < 3",
            "1 < 2 == true",
            "true == 1 < 2",
            "1 != 2 >= 3",
            "(1) < 2 < 3",
            "true == (1) < 2",
        ] {
            let source = format!("fn f() -> Bool {{ {expression} }}");
            let errors = parse(&source, "comparison.vast").unwrap_err();
            assert_eq!(errors[0].code, "E_PARSE", "{expression}");
            assert!(errors[0].message.contains("comparisons cannot be chained"));
            assert!(matches!(
                &source[errors[0].span.start..errors[0].span.end],
                "==" | "<" | ">="
            ));
        }
        for expression in [
            "(1 == 1) == true",
            "true == (1 < 2)",
            "((1 < 2)) == true",
            "1 < 2 && 2 < 3",
            "1 == 2 || 3 != 4 && 5 >= 6",
            "1 + 2 * 3 < 8 - 1",
        ] {
            parse(
                &format!("fn f() -> Bool {{ {expression} }}"),
                "comparison.vast",
            )
            .unwrap();
        }
    }

    #[test]
    fn rejects_reserved_names_ring_values_and_captures() {
        assert_eq!(
            parse("fn Affine() -> Int { 0 }", "bad.vast").unwrap_err()[0].code,
            "E_RESERVED"
        );
        assert_eq!(
            parse("fn main() -> Int { QQ }", "bad.vast").unwrap_err()[0].code,
            "E_RING"
        );
        assert_eq!(
            parse(
                "fn main() -> Int { let x = 1; let f = fn(y: Int) -> Int { x + y }; 0 }",
                "bad.vast"
            )
            .unwrap_err()[0]
                .code,
            "E_CAPTURE"
        );
    }

    #[test]
    fn recognizes_explicit_integer_conversion_as_a_reserved_builtin() {
        parse("fn convert(n: Nat) -> Int { int(n) }", "conversion.vast").unwrap();
        let errors = parse("fn int() -> Int { 0 }", "reserved.vast").unwrap_err();
        assert_eq!(errors[0].code, "E_RESERVED");
    }

    #[test]
    fn else_if_uses_nested_blocks_and_preserves_operator_binding_and_spans() {
        let source = "fn f() -> Int { if false { 1 } else if true { 2 } else { 3 } + 4 }";
        let module = parse(source, "else-if.vast").unwrap();
        let ExprKind::Binary { op, left, .. } = &module.functions[0].body.result.kind else {
            panic!("addition must surround the entire conditional");
        };
        assert_eq!(op, "+");
        let ExprKind::If { else_branch, .. } = &left.kind else {
            panic!("expected outer conditional");
        };
        assert!(else_branch.statements.is_empty());
        assert!(matches!(else_branch.result.kind, ExprKind::If { .. }));
        assert_eq!(
            &source[else_branch.span.start..else_branch.span.end],
            "if true { 2 } else { 3 }"
        );
        assert_eq!(else_branch.span, else_branch.result.span);
        serde_json::to_vec(&module).unwrap();
    }

    #[test]
    fn else_if_keeps_scope_and_nesting_limits() {
        let source = "fn f() -> Int { if false { let x = 1; x } else if true { x } else { 0 } }";
        let errors = parse(source, "scope.vast").unwrap_err();
        assert_eq!(errors[0].code, "E_NAME");
        assert!(errors[0].message.contains("unknown value `x`"));
        let source = format!(
            "fn f() -> Int {{ {}{{ 1 }} }}",
            "if false { 0 } else ".repeat(512)
        );
        let errors = parse(&source, "depth.vast").unwrap_err();
        assert_eq!(errors[0].code, "E_LIMIT");
    }

    #[test]
    fn unsupported_arithmetic_and_float_literals_have_precise_spans() {
        for (expression, fragment, message) in [
            ("7 / 2", "/", "division"),
            ("7 % 2", "%", "remainder"),
            ("1.25", "1.25", "floating-point"),
            ("1.", "1.", "floating-point"),
            (".25", ".25", "floating-point"),
            ("1e10", "1e10", "floating-point"),
            ("2E-3", "2E-3", "floating-point"),
            ("1.25e+2f64", "1.25e+2f64", "floating-point"),
            ("2f32", "2f32", "floating-point"),
            ("-0.5", "0.5", "floating-point"),
        ] {
            let prefix = "// 数学\nfn f() -> Int {　";
            let source = format!("{prefix}{expression} }}");
            let errors = parse(&source, "unsupported.vast").unwrap_err();
            let error = &errors[0];
            assert_eq!(error.code, "E_UNSUPPORTED", "{expression}");
            assert!(error.message.contains(message));
            assert_eq!(&source[error.span.start..error.span.end], fragment);
            assert_eq!(error.span.line, 2);
            assert_eq!(
                error.span.column,
                "fn f() -> Int {　".chars().count() + expression.find(fragment).unwrap() + 1
            );
        }
        parse(
            "// return while for loop mut / % 1.25\nfn f() -> Int { 125 // .5 / 2\n }",
            "comments.vast",
        )
        .unwrap();
    }

    #[test]
    fn unsupported_control_keywords_are_reserved_and_explained() {
        for (word, explanation) in [
            ("return", "final expression of a block"),
            ("while", "loops"),
            ("for", "loops"),
            ("loop", "loops"),
            ("mut", "mutable bindings"),
        ] {
            for body in [format!("{word} 1;"), format!("let {word} = 1; 0")] {
                let source = format!("fn f() -> Int {{ {body} }}");
                let errors = parse(&source, "unsupported.vast").unwrap_err();
                assert_eq!(errors[0].code, "E_UNSUPPORTED");
                assert!(errors[0].message.contains(explanation));
                assert_eq!(&source[errors[0].span.start..errors[0].span.end], word);
            }
        }
    }

    #[test]
    fn branches_have_separate_lexical_scopes() {
        parse(
            "fn f(n: Int) -> Int { if n < 0 { let x = -n; x } else { let x = n * n; x } }",
            "if.vast",
        )
        .unwrap();
        assert!(
            parse(
                "fn f(n: Int) -> Int { if n < 0 { let x = 1; x } else { x } }",
                "bad.vast"
            )
            .is_err()
        );
    }

    #[test]
    fn malformed_input_reports_location_without_panicking() {
        for source in [
            "",
            "fn",
            "fn f(",
            "fn f() -> Int {",
            "fn f() -> Int { 1; }",
            "fn f() -> Int { 1 / 2 }",
        ] {
            let result = parse(source, "broken.vast");
            if !source.is_empty() {
                assert!(result.is_err(), "accepted malformed source {source:?}");
            }
        }
    }
}
