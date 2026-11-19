use super::*;
use crate::namespace::Public;
use std::collections::HashSet;

pub(super) enum Declaration {
    Header(Generic),
    Body(Function, Vec<String>, Span),
    Contract(AbstractMethod),
}

impl Declaration {
    fn name(&self) -> &str {
        match self {
            Self::Header(header) => &header.name,
            Self::Body(function, ..) => &function.name,
            Self::Contract(contract) => &contract.name,
        }
    }

    fn span(&self) -> Span {
        match self {
            Self::Header(header) => header.span,
            Self::Body(function, ..) => function.span,
            Self::Contract(contract) => contract.span,
        }
    }

    fn needs_dispatch(&self) -> bool {
        let Self::Body(function, requires, _) = self else {
            return true;
        };
        !requires.is_empty()
            || function.params.iter().any(|param| {
                matches!(&param.ty, Type::Named { name }
                if !TYPES.contains(&name.as_str()) || matches!(name.as_str(), "Any" | "Number"))
            })
    }
}

#[derive(Default)]
pub(super) struct Declarations {
    items: Vec<Public<Declaration>>,
    imports: HashSet<String>,
}

#[derive(Default)]
pub(super) struct Grouped {
    pub functions: Vec<Public<Function>>,
    pub generics: Vec<Public<Generic>>,
    pub methods: Vec<Method>,
    pub contracts: Vec<AbstractMethod>,
}

fn selector(ty: &Type) -> bool {
    matches!(ty, Type::Named { name } if !matches!(name.as_str(), "Scheme" | "CInfScheme"))
}

fn method_result(ty: &Type) -> bool {
    matches!(ty, Type::Pair { .. })
        || matches!(ty, Type::Named { name } if matches!(name.as_str(), "Nat" | "Int" | "Bool" | "Unit"))
}

fn check_signature(params: &[Param], result: &Type, span: Span) -> Result<(), Diagnostic> {
    if let Some(param) = params.iter().find(|param| !selector(&param.ty)) {
        return Err(diagnostic(
            "E_TYPE",
            "dispatch parameters require scalar or abstract selectors",
            param.span,
        ));
    }
    if !method_result(result) {
        return Err(diagnostic(
            "E_TYPE",
            "method results require Nat, Int, Bool, Unit, Pair<Nat>, or Pair<Int>",
            span,
        ));
    }
    Ok(())
}

impl Declarations {
    pub fn push(&mut self, public: bool, declaration: Declaration) {
        self.items.push(Public {
            public,
            declaration,
        });
    }

    pub fn imports(&mut self, module: &crate::namespace::Module) {
        for item in &module.imports {
            // A self-import of the identical name still collides with the
            // local declaration. It cannot introduce an external edit target.
            let same_local = match item.path.as_slice() {
                [name] => name == &item.alias,
                [prefix, name] => prefix == "self" && name == &item.alias,
                _ => false,
            };
            if !same_local {
                self.imports.insert(item.alias.clone());
            }
        }
    }

    pub fn lower_flat(self) -> Result<Grouped, Diagnostic> {
        // The entry file and its --lib inputs share a single entrypoint.
        // Diagnose the second body at its source before inferring a family.
        let mut entry_bodies = self
            .items
            .iter()
            .filter_map(|item| match &item.declaration {
                Declaration::Body(f, ..) if f.name == "main" => Some(f.span),
                _ => None,
            });
        if let Some(second) = entry_bodies.nth(1) {
            return Err(diagnostic(
                "E_DUPLICATE",
                "function `main` is defined more than once",
                second,
            ));
        }
        self.lower()
    }

    pub fn lower(self) -> Result<Grouped, Diagnostic> {
        let mut headers = HashMap::new();
        let mut counts = HashMap::new();
        for item in &self.items {
            let name = item.declaration.name().to_owned();
            let (total, all_finite) = counts.entry(name.clone()).or_insert((0usize, true));
            *total += 1;
            *all_finite &= matches!(&item.declaration, Declaration::Body(f, ..) if !f.finite_binders.is_empty());
            if matches!(item.declaration, Declaration::Header(_))
                && headers.insert(name, item.public).is_some()
            {
                return Err(diagnostic(
                    "E_DUPLICATE",
                    "a function family may have only one explicit domain header",
                    item.declaration.span(),
                ));
            }
        }
        let mut inferred = HashMap::new();
        let mut grouped = Grouped::default();
        for item in self.items {
            let name = item.declaration.name();
            let references_family = name.contains("::") || self.imports.contains(name);
            let (total, all_finite) = counts[name];
            let dispatch = references_family
                || (total > 1 && !all_finite)
                || item.declaration.needs_dispatch();
            if dispatch
                && matches!(&item.declaration, Declaration::Body(f, ..) if !f.finite_binders.is_empty())
            {
                return Err(diagnostic(
                    "E_TYPE",
                    "finite-indexed methods must belong to a local family of finite-indexed functions",
                    item.declaration.span(),
                ));
            }
            if dispatch && !headers.contains_key(name) && !references_family {
                if let Some(public) = inferred.get(name) {
                    if item.public != *public {
                        return Err(diagnostic(
                            "E_OWNER",
                            "all declarations of an inferred function family must have the same visibility",
                            item.declaration.span(),
                        ));
                    }
                } else {
                    let params = match &item.declaration {
                        Declaration::Body(function, ..) => &function.params,
                        Declaration::Contract(contract) => &contract.params,
                        Declaration::Header(_) => unreachable!(),
                    };
                    inferred.insert(name.to_owned(), item.public);
                    grouped.generics.push(Public {
                        public: item.public,
                        declaration: inferred_header(name, params, item.declaration.span()),
                    });
                }
            } else if item.public && headers.get(name) == Some(&false) {
                return Err(diagnostic(
                    "E_OWNER",
                    "a public method cannot widen its private family header",
                    item.declaration.span(),
                ));
            }
            match item.declaration {
                Declaration::Header(declaration) => grouped.generics.push(Public {
                    public: item.public,
                    declaration,
                }),
                Declaration::Contract(contract) => grouped.contracts.push(contract),
                Declaration::Body(function, ..) if !dispatch => grouped.functions.push(Public {
                    public: item.public,
                    declaration: function,
                }),
                Declaration::Body(function, requires, result_span) => {
                    check_signature(&function.params, &function.return_type, result_span)?;
                    if !function.observations.is_empty() {
                        return Err(diagnostic(
                            "E_MAIN",
                            "an overloaded entrypoint cannot observe results",
                            function.span,
                        ));
                    }
                    grouped.methods.push(method_body(function, requires));
                }
            }
        }
        Ok(grouped)
    }
}

fn inferred_header(name: &str, params: &[Param], span: Span) -> Generic {
    Generic {
        name: name.to_owned(),
        params: params
            .iter()
            .map(|p| GenericParam {
                name: p.name.clone(),
                span: p.span,
            })
            .collect(),
        domain: None,
        span,
    }
}

fn method_body(function: Function, requires: Vec<String>) -> Method {
    Method {
        name: function.name,
        params: function.params,
        return_type: function.return_type,
        requires,
        body: function.body,
        span: function.span,
    }
}

/// A singleton presented to the finite dispatch checker by an explicit edit.
/// All signatures, bodies and unresolved references remain in the request.
pub(crate) fn editable_singleton(function: &Function) -> bool {
    function.name != "main"
        && function.finite_binders.is_empty()
        && function.observations.is_empty()
        && method_result(&function.return_type)
        && function.params.iter().all(|p| selector(&p.ty))
}

pub(crate) fn singleton_family(function: Public<Function>) -> (Public<Generic>, Method) {
    let f = function.declaration;
    (
        Public {
            public: function.public,
            declaration: inferred_header(&f.name, &f.params, f.span),
        },
        method_body(f, Vec::new()),
    )
}

impl Parser {
    pub(super) fn retired_function_start(&self) -> bool {
        self.peek().is("generic")
            || self.peek().is("method")
            || self.peek().is("abstract") && self.second_is("method")
    }

    pub(super) fn retired_function_error(&self) -> Diagnostic {
        diagnostic(
            "E_PARSE",
            "edition 2026 uses `fn` for function families, method bodies and bodyless contracts",
            self.peek().span,
        )
    }

    fn requirements(&mut self, binders: &[StaticBinder]) -> Result<Vec<String>, Diagnostic> {
        if !binders.is_empty() {
            return Err(diagnostic(
                "E_TYPE",
                "a finite-indexed fn cannot have dispatch requirements",
                self.previous().span,
            ));
        }
        self.delimited_list("(", ")", |parser| Ok(parser.name()?.0))
    }

    fn parameter_type(&mut self) -> Result<Type, Diagnostic> {
        let mut end = self.position + 1;
        while self.tokens.get(end).is_some_and(|token| token.is("::")) {
            end += 2;
        }
        if self
            .tokens
            .get(end)
            .is_some_and(|token| token.is(")") || token.is(","))
            && !matches!(&self.peek().kind, TokenKind::Name(name) if TYPES.contains(&name.as_str()) && !matches!(name.as_str(), "Any" | "Number"))
        {
            self.dispatch_type(true)
        } else {
            self.ty()
        }
    }

    fn finite_binders(&mut self) -> Result<Vec<StaticBinder>, Diagnostic> {
        if !self.consume("<") {
            return Ok(Vec::new());
        }
        self.indexed = true;
        if self.peek().is(">") {
            return Err(diagnostic(
                "E_PARSE",
                "expected a finite category or object binder",
                self.peek().span,
            ));
        }
        self.delimited_tail(">", |parser| {
            let (name, start) = parser.binding_name()?;
            parser.expect(":")?;
            if parser.peek().is("Obj") && parser.second_is("<") {
                parser.advance();
                parser.expect("<")?;
                let (owner, _) = parser.binding_name()?;
                if parser.consume("::") {
                    parser.expect("category")?;
                    let end = parser.type_close()?.span;
                    return Ok(StaticBinder::MonadObject {
                        name,
                        monad: owner,
                        span: start.through(end),
                    });
                }
                let end = parser.type_close()?.span;
                return Ok(StaticBinder::Object {
                    name,
                    category: owner,
                    span: start.through(end),
                });
            }
            let schema = parser.type_path()?;
            if schema.path == ["Type"] {
                return Err(diagnostic(
                    "E_TYPE",
                    "fn model binders require a finite category or Monad schema",
                    schema.span,
                ));
            }
            Ok(StaticBinder::Category {
                name,
                span: start.through(schema.span),
                schema,
            })
        })
    }

    pub(super) fn function_declaration(&mut self) -> Result<Declaration, Diagnostic> {
        let start = self.expect("fn")?.span;
        let mut segments = Vec::new();
        while self.packages && self.second_is("::") {
            segments.push(self.path_component()?.0);
            self.expect("::")?;
        }
        if self.packages && self.peek().is("compose") && self.second_is("<") {
            segments.push(self.name()?.0);
        } else {
            segments.push(self.binding_name()?.0);
        }
        let name = segments.join("::");
        let finite_binders = self.finite_binders()?;
        self.expect("(")?;
        let params = self.delimited_tail(")", |parser| {
            let (name, span) = parser.binding_name()?;
            let ty = if parser.consume(":") {
                let type_start = parser.peek().span;
                Some((
                    parser.parameter_type()?,
                    type_start.through(parser.previous().span),
                ))
            } else {
                None
            };
            Ok((name, span, ty))
        })?;
        if self.consume("domain") {
            if !finite_binders.is_empty() {
                return Err(diagnostic(
                    "E_TYPE",
                    "a finite-indexed fn requires a body",
                    start,
                ));
            }
            if name.contains("::") {
                return Err(diagnostic(
                    "E_OWNER",
                    "a function domain header must name a family in its defining module",
                    start,
                ));
            }
            let params = params
                .into_iter()
                .map(|(name, span, ty)| {
                    if ty.is_some() {
                        Err(diagnostic(
                            "E_PARSE",
                            "typed domain contracts require a result type after `->`",
                            span,
                        ))
                    } else {
                        Ok(GenericParam { name, span })
                    }
                })
                .collect::<Result<_, _>>()?;
            let domain = self.delimited_list("(", ")", |parser| {
                parser.delimited_list("(", ")", |parser| parser.dispatch_type(false))
            })?;
            let end = self.expect(";")?.span;
            return Ok(Declaration::Header(Generic {
                name,
                params,
                domain: Some(domain),
                span: start.through(end),
            }));
        }
        let mut selectors = Vec::new();
        let params = params
            .into_iter()
            .map(|(name, span, ty)| {
                let (ty, end) = ty.ok_or_else(|| {
                    diagnostic(
                        "E_PARSE",
                        "expected a parameter type or an untyped family domain header",
                        span,
                    )
                })?;
                if let Type::Named { name } = &ty {
                    selectors.push(TypePath {
                        path: name.split("::").map(str::to_owned).collect(),
                        span: end,
                    });
                }
                Ok(Param {
                    name,
                    span: span.through(end),
                    ty,
                })
            })
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        let before_arrow = self.consume("requires");
        let mut requires = if before_arrow {
            self.requirements(&finite_binders)?
        } else {
            vec![]
        };
        self.expect("->")?;
        if self.peek().is("Any") || self.peek().is("Number") {
            return Err(diagnostic(
                "E_TYPE",
                "method results require Nat, Int, Bool, Unit, Pair<Nat>, or Pair<Int>",
                self.peek().span,
            ));
        }
        let result_start = self.peek().span;
        let return_type = self.ty()?;
        let result_span = result_start.through(self.previous().span);
        if self.consume("requires") {
            if before_arrow {
                return Err(diagnostic(
                    "E_PARSE",
                    "a method has only one `requires` clause",
                    self.previous().span,
                ));
            }
            requires = self.requirements(&finite_binders)?;
        }
        if self.peek().is("domain") || self.peek().is(";") {
            if !finite_binders.is_empty() {
                return Err(diagnostic(
                    "E_TYPE",
                    "a finite-indexed fn requires a body",
                    start,
                ));
            }
            check_signature(&params, &return_type, result_span)?;
            let domain = if self.consume("domain") {
                self.delimited_list("(", ")", |parser| {
                    parser.delimited_list("(", ")", Self::type_path)
                })?
            } else {
                vec![selectors]
            };
            let end = self.expect(";")?.span;
            return Ok(Declaration::Contract(AbstractMethod {
                name,
                params,
                return_type,
                requires,
                domain,
                span: start.through(end),
            }));
        }
        self.observing = name == "main" && self.entry_module;
        let body = self.block();
        self.observing = false;
        let body = body?;
        let observations = std::mem::take(&mut self.observations);
        let span = start.through(body.span);
        Ok(Declaration::Body(
            Function {
                name,
                finite_binders,
                params,
                return_type,
                body,
                observations,
                span,
            },
            requires,
            result_span,
        ))
    }

    pub(super) fn method(&mut self) -> Result<Method, Diagnostic> {
        if self.retired_function_start() {
            return Err(self.retired_function_error());
        }
        let declaration = self.function_declaration()?;
        let Declaration::Body(function, requires, result_span) = declaration else {
            return Err(diagnostic(
                "E_PARSE",
                "a contribution requires concrete fn bodies",
                declaration.span(),
            ));
        };
        if !function.observations.is_empty() {
            return Err(misplaced_show(function.observations[0].span));
        }
        if !function.finite_binders.is_empty() {
            return Err(diagnostic(
                "E_TYPE",
                "a contribution cannot define a finite-indexed fn",
                function.span,
            ));
        }
        check_signature(&function.params, &function.return_type, result_span)?;
        Ok(method_body(function, requires))
    }
}
