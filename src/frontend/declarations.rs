//! Flat and namespace declarations: functions, parameters, generics, methods,
//! abstract types, subtypes and their dispatch domains.
use super::*;

struct MethodHeader {
    name: String,
    params: Vec<Param>,
    return_type: Type,
    requires: Vec<String>,
    span: Span,
}

impl Parser {
    pub(super) fn flat_declarations(&mut self, module: &mut Module) -> Result<(), Diagnostic> {
        while self.peek().kind != TokenKind::Eof {
            if self.peek().is("fn") {
                module.functions.push(self.function()?);
            } else if self.peek().is("generic") {
                module.generics.push(self.generic()?);
            } else if self.peek().is("method") {
                module.methods.push(self.method()?);
            } else if self.abstract_method_start() {
                module.abstract_methods.push(self.abstract_method()?);
            } else if self.peek().is("abstract") {
                module.abstract_types.push(self.abstract_type()?);
            } else if self.peek().is("subtype") {
                module.subtypes.push(self.subtype()?);
            } else {
                return Err(self.flat_declaration_error());
            }
        }
        Ok(())
    }

    // Name package-only syntax precisely; anything else is an unexpected token.
    fn flat_declaration_error(&self) -> Diagnostic {
        let token = self.peek();
        let next_is = |value| {
            self.tokens
                .get(self.position + 1)
                .is_some_and(|next| next.is(value))
        };
        let package_only = if token.is("resource") && next_is("fn") {
            Some("`resource fn` declarations require")
        } else if token.is("mod") {
            Some("`mod` declarations require")
        } else if token.is("use") {
            Some("`use` imports require")
        } else if token.is("pub") {
            Some("`pub` visibility requires")
        } else if token.is("indexed") {
            Some("`indexed` declarations require")
        } else if [
            "grant",
            "delegation",
            "transfer",
            "contribution",
            "assembly",
        ]
        .iter()
        .any(|keyword| token.is(keyword))
        {
            Some("edit-authority declarations require")
        } else {
            None
        };
        if let Some(subject) = package_only {
            return diagnostic(
                "E_UNSUPPORTED",
                format!(
                    "{subject} manifest mode; put the source in a package and run `vastitas check --manifest-path Vastitas.toml`"
                ),
                token.span,
            );
        }
        const FLAT: [&str; 5] = ["fn", "generic", "method", "abstract", "subtype"];
        let hint = match &token.kind {
            TokenKind::Name(name) => FLAT
                .iter()
                .find(|keyword| edit_distance(name, keyword) <= 1 + keyword.len() / 4)
                .map(|keyword| format!("; help: did you mean `{keyword}`?"))
                .unwrap_or_default(),
            _ => String::new(),
        };
        diagnostic(
            "E_PARSE",
            format!(
                "expected a top-level `fn`, `generic`, `method`, `abstract type`, `subtype` or `abstract method` declaration, found {}{hint}",
                token.description()
            ),
            token.span,
        )
    }

    pub(super) fn reference_path(&mut self) -> Result<(String, Span), Diagnostic> {
        let (mut path, start) = self.path_component()?;
        while self.consume("::") {
            let (component, _) = self.path_component()?;
            path.push_str("::");
            path.push_str(&component);
        }
        Ok((path, start.through(self.previous().span)))
    }

    // `generic` remains a declaration keyword and forbidden binding name, but
    // is a contextual module component (e.g. arithmetic::generic::promote).
    pub(super) fn path_component(&mut self) -> Result<(String, Span), Diagnostic> {
        if self.packages && self.peek().is("generic") {
            let token = self.advance();
            Ok(("generic".into(), token.span))
        } else {
            self.name()
        }
    }

    pub(super) fn namespace(
        &mut self,
        path: Vec<String>,
        public: bool,
        span: Span,
        inline: bool,
        parsed: &mut crate::packages::Parsed,
    ) -> Result<(), Diagnostic> {
        use crate::packages::{External, Import, Module as NamespaceModule, Public};
        if path.len() > MAX_MODULE_NESTING {
            return Err(diagnostic(
                "E_LIMIT",
                format!("module nesting exceeds {MAX_MODULE_NESTING}"),
                span,
            ));
        }
        let mut module = NamespaceModule {
            path: path.clone(),
            public,
            span,
            imports: Vec::new(),
            functions: Vec::new(),
            resource_functions: Vec::new(),
            generics: Vec::new(),
            methods: Vec::new(),
            indexed_declarations: Vec::new(),
            uses_indexed: false,
            abstract_types: Vec::new(),
            subtypes: Vec::new(),
            abstract_methods: Vec::new(),
            grants: Vec::new(),
            delegations: Vec::new(),
            transfers: Vec::new(),
            contributions: Vec::new(),
            assembly: None,
        };
        while self.peek().kind != TokenKind::Eof && !(inline && self.peek().is("}")) {
            let public = self.consume("pub");
            if self.peek().is("indexed") {
                module.indexed_declarations.push(Public {
                    declaration: self.indexed_declaration()?,
                    public,
                });
            } else if self.peek().is("resource")
                && self
                    .tokens
                    .get(self.position + 1)
                    .is_some_and(|token| token.is("fn"))
            {
                module.resource_functions.push(Public {
                    declaration: self.resource_function()?,
                    public,
                });
            } else if self.peek().is("fn") {
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
            } else if self.abstract_method_start() {
                if public {
                    return Err(diagnostic(
                        "E_PARSE",
                        "abstract methods cannot be pub; they have no visibility",
                        self.peek().span,
                    ));
                }
                module.abstract_methods.push(self.abstract_method()?);
            } else if self.peek().is("abstract") {
                module.abstract_types.push(Public {
                    declaration: self.abstract_type()?,
                    public,
                });
            } else if self.peek().is("subtype") && !public {
                module.subtypes.push(self.subtype()?);
            } else if self.peek().is("grant") {
                module.grants.push(Public {
                    declaration: self.grant("grant")?,
                    public,
                });
            } else if self.peek().is("delegation") {
                module.delegations.push(Public {
                    declaration: self.grant("delegation")?,
                    public,
                });
            } else if self.peek().is("transfer") {
                module.transfers.push(Public {
                    declaration: self.transfer()?,
                    public,
                });
            } else if self.peek().is("contribution") {
                module.contributions.push(Public {
                    declaration: self.contribution()?,
                    public,
                });
            } else if self.peek().is("assembly") && !public {
                if module.assembly.is_some() {
                    return Err(diagnostic(
                        "E_DUPLICATE",
                        "a module may contain only one assembly",
                        self.peek().span,
                    ));
                }
                module.assembly = Some(self.assembly()?);
            } else if self.consume("mod") {
                let start = self.previous().span;
                let (name, name_span) = if self.peek().is("generic") {
                    self.path_component()?
                } else {
                    self.module_name()?
                };
                // The kernel refuses this name too, but only at the span of
                // the module, which is its `mod` item.
                if name == "package" {
                    return Err(diagnostic(
                        "E_RESERVED",
                        "`package` is reserved as a path prefix and cannot be the name of a module",
                        name_span,
                    ));
                }
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
                let last = self.previous().span;
                let components: Vec<String> = name.split("::").map(str::to_owned).collect();
                let (alias, bound, deferred_name) = if self.consume("as") {
                    let (alias, bound) = self.binding_name()?;
                    (alias, bound, None)
                } else {
                    let alias = components.last().unwrap().clone();
                    // An implicit alias binds like `as`. Compatibility
                    // spellings may still name imported indexed declarations.
                    // Once every package is loaded, the loader rejects such a
                    // `use` of a module at the name; the kernel decides the
                    // rest.
                    if INDEXED_SPELLINGS.contains(&alias.as_str()) {
                        (alias, last, Some(last))
                    } else {
                        self.check_binding_name(&alias, last)?;
                        (alias, last, None)
                    }
                };
                // `package` is no name of a namespace: the kernel refuses it
                // as the name that a `use` binds. It prices every import
                // first, so `use package;`, which names itself, reached the
                // user as a cycle of imports (#704).
                if alias == "package" {
                    return Err(diagnostic(
                        "E_RESERVED",
                        "`package` is reserved as a path prefix and cannot be a name that `use` binds",
                        bound,
                    ));
                }
                let end = self.expect(";")?.span;
                module.imports.push(Import {
                    path: components,
                    alias,
                    public,
                    span: start.through(end),
                    deferred_name,
                });
            } else {
                return Err(diagnostic(
                    "E_PARSE",
                    "expected a module-level fn, generic, method, mod, or use declaration; methods cannot be pub",
                    self.peek().span,
                ));
            }
        }
        module.uses_indexed = self.indexed;
        parsed.modules.push(module);
        Ok(())
    }

    pub(super) fn parameters(&mut self, selectors: bool) -> Result<Vec<Param>, Diagnostic> {
        self.delimited_list("(", ")", |parser| {
            let (name, start) = parser.binding_name()?;
            parser.expect(":")?;
            let ty = if selectors {
                parser.dispatch_type(true)?
            } else {
                parser.ty()?
            };
            Ok(Param {
                name,
                ty,
                span: start.through(parser.previous().span),
            })
        })
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

    // Generic, contract and grant domains share tuple/list punctuation.
    pub(super) fn domain_list<T>(
        &mut self,
        mut element: impl FnMut(&mut Self) -> Result<T, Diagnostic>,
    ) -> Result<Vec<Vec<T>>, Diagnostic> {
        self.delimited_tail(";", |parser| parser.delimited_list("(", ")", &mut element))
    }

    pub(super) fn type_path(&mut self) -> Result<TypePath, Diagnostic> {
        let (name, span) = self.reference_path()?;
        if !self.packages && name.contains("::") {
            return Err(diagnostic(
                "E_NAME",
                "qualified type paths require package input",
                span,
            ));
        }
        Ok(TypePath {
            path: name.split("::").map(str::to_owned).collect(),
            span,
        })
    }

    fn abstract_type(&mut self) -> Result<AbstractType, Diagnostic> {
        let start = self.expect("abstract")?.span;
        self.expect("type")?;
        let (name, _) = self.binding_name()?;
        let mut parents = Vec::new();
        if self.consume("<:") {
            if self.consume("(") {
                loop {
                    parents.push(self.type_path()?);
                    if self.consume(")") {
                        break;
                    }
                    self.expect(",")?;
                }
            } else {
                parents.push(self.type_path()?);
            }
        }
        let end = self.expect(";")?.span;
        Ok(AbstractType {
            name,
            parents,
            span: start.through(end),
        })
    }

    fn subtype(&mut self) -> Result<Subtype, Diagnostic> {
        let start = self.expect("subtype")?.span;
        let (scalar, _) = self.name()?;
        self.expect("<:")?;
        let target = self.type_path()?;
        let end = self.expect(";")?.span;
        Ok(Subtype {
            scalar,
            target,
            span: start.through(end),
        })
    }

    pub(super) fn dispatch_type(&mut self, selector: bool) -> Result<Type, Diagnostic> {
        let (name, span) = if selector {
            let path = self.type_path()?;
            (path.path.join("::"), path.span)
        } else {
            self.name()?
        };
        if matches!(name.as_str(), "Nat" | "Int" | "Bool" | "Unit")
            || (selector && (matches!(name.as_str(), "Any" | "Number") || !reserved(&name)))
        {
            Ok(Type::Named { name })
        } else {
            Err(diagnostic(
                "E_TYPE",
                if selector {
                    "a method selector must be Nat, Int, Bool, Unit, Number, or Any"
                } else {
                    "dispatch domains require a concrete scalar type: Nat, Int, Bool, or Unit"
                },
                span,
            ))
        }
    }

    fn generic(&mut self) -> Result<Generic, Diagnostic> {
        let start = self.expect("generic")?.span;
        let (name, _) = self.binding_name()?;
        let params = self.delimited_list("(", ")", |parser| {
            let (name, span) = parser.binding_name()?;
            Ok(GenericParam { name, span })
        })?;
        self.expect("{")?;
        self.expect("domain")?;
        let domain = self.domain_list(|parser| parser.dispatch_type(false))?;
        let end = self.expect("}")?.span;
        Ok(Generic {
            name,
            params,
            domain,
            span: start.through(end),
        })
    }

    fn requirements(&mut self) -> Result<Vec<String>, Diagnostic> {
        self.delimited_list("(", ")", |parser| Ok(parser.name()?.0))
    }

    fn method_result(&mut self) -> Result<Type, Diagnostic> {
        let start = self.peek().span;
        let mut span = start;
        if ["Nat", "Int", "Bool", "Unit", "Pair"]
            .iter()
            .any(|name| self.peek().is(name))
        {
            let ty = self.ty()?;
            // One of these names can also begin an indexed path, such as
            // `Nat::Family<X>`, which the kernel's decoder refuses here.
            if matches!(ty, Type::Named { .. } | Type::Pair { .. }) {
                return Ok(ty);
            }
            span = start.through(self.previous().span);
        }
        Err(diagnostic(
            "E_TYPE",
            "method results require Nat, Int, Bool, Unit, Pair<Nat>, or Pair<Int>",
            span,
        ))
    }

    fn method_header(&mut self) -> Result<MethodHeader, Diagnostic> {
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
        let return_type = self.method_result()?;
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
        Ok(MethodHeader {
            name,
            params,
            return_type,
            requires,
            span: start,
        })
    }

    pub(super) fn method(&mut self) -> Result<Method, Diagnostic> {
        let header = self.method_header()?;
        let body = self.block()?;
        Ok(Method {
            name: header.name,
            params: header.params,
            return_type: header.return_type,
            requires: header.requires,
            span: header.span.through(body.span),
            body,
        })
    }

    fn abstract_method_start(&self) -> bool {
        self.peek().is("abstract")
            && self
                .tokens
                .get(self.position + 1)
                .is_some_and(|t| t.is("method"))
    }

    fn abstract_method(&mut self) -> Result<AbstractMethod, Diagnostic> {
        let start = self.expect("abstract")?.span;
        let header = self.method_header()?;
        self.expect("{")?;
        self.expect("domain")?;
        let domain = self.domain_list(Self::type_path)?;
        let end = self.expect("}")?.span;
        Ok(AbstractMethod {
            name: header.name,
            params: header.params,
            return_type: header.return_type,
            requires: header.requires,
            domain,
            span: start.through(end),
        })
    }
}
