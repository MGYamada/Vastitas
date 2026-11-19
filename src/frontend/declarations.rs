//! Flat and namespace declarations: functions, parameters, generics, methods,
//! abstract types, subtypes and their dispatch domains.
use super::families::Declarations;
use super::*;

impl Parser {
    pub(super) fn flat_declarations(
        &mut self,
        module: &mut Module,
        families: &mut Declarations,
    ) -> Result<(), Diagnostic> {
        while self.peek().kind != TokenKind::Eof {
            if self.peek().is("fn") {
                families.push(false, self.function_declaration()?);
            } else if self.retired_function_start() {
                return Err(self.retired_function_error());
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
        if token.is("assembly") {
            return self.retired_assembly();
        }
        let package_only = if token.is("resource") && self.second_is("fn") {
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
            "assemble",
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
        const FLAT: [&str; 3] = ["fn", "abstract", "subtype"];
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
                "expected a top-level `fn`, `abstract type` or `subtype` declaration, found {}{hint}",
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

    // The reserved spelling `generic` can still name a module path component.
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
        parsed: &mut crate::namespace::Parsed,
    ) -> Result<(), Diagnostic> {
        if path.len() > MAX_MODULE_NESTING {
            return Err(diagnostic(
                "E_LIMIT",
                format!("module nesting exceeds {MAX_MODULE_NESTING}"),
                span,
            ));
        }
        let entry_module = std::mem::replace(&mut self.entry_module, path.is_empty());
        let result = self.namespace_items(path, public, span, inline, parsed);
        self.entry_module = entry_module;
        result
    }

    fn namespace_items(
        &mut self,
        path: Vec<String>,
        public: bool,
        span: Span,
        inline: bool,
        parsed: &mut crate::namespace::Parsed,
    ) -> Result<(), Diagnostic> {
        use crate::namespace::{External, Import, Module as NamespaceModule, Public};
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
        let mut families = Declarations::default();
        while self.peek().kind != TokenKind::Eof && !(inline && self.peek().is("}")) {
            let public = self.consume("pub");
            if self.peek().is("indexed") {
                module.indexed_declarations.push(Public {
                    declaration: self.indexed_declaration()?,
                    public,
                });
            } else if self.peek().is("resource") && self.second_is("fn") {
                module.resource_functions.push(Public {
                    declaration: self.resource_function()?,
                    public,
                });
            } else if self.peek().is("fn") {
                families.push(public, self.function_declaration()?);
            } else if self.retired_function_start() {
                return Err(self.retired_function_error());
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
            } else if self.peek().is("assembly") {
                return Err(self.retired_assembly());
            } else if self.peek().is("assemble") && !public {
                self.assemble(&mut module.assembly)?;
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
                        check_binding_name(&alias, last)?;
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
                    "expected a module-level fn, mod, use or other declaration",
                    self.peek().span,
                ));
            }
        }
        families.imports(&module);
        let grouped = families.lower()?;
        module.functions = grouped.functions;
        module.generics = grouped.generics;
        module.methods = grouped.methods;
        module.abstract_methods = grouped.contracts;
        module.uses_indexed = self.indexed;
        if let Some(assembly) = &mut module.assembly {
            assembly.lower();
        }
        parsed.modules.push(module);
        Ok(())
    }

    pub(super) fn lambda_parameters(&mut self) -> Result<Vec<Param>, Diagnostic> {
        self.delimited_list("(", ")", |parser| {
            let (name, start) = parser.binding_name()?;
            parser.expect(":")?;
            let ty = parser.ty()?;
            Ok(Param {
                name,
                ty,
                span: start.through(parser.previous().span),
            })
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
}
