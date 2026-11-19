//! Edit-authority declarations: grants, delegations, transfers, contributions
//! and assemblies.
use super::*;

impl Parser {
    fn edit_path(&mut self) -> Result<Vec<String>, Diagnostic> {
        Ok(self
            .reference_path()?
            .0
            .split("::")
            .map(str::to_owned)
            .collect())
    }

    fn edit_recipient(&mut self) -> Result<(String, Vec<String>), Diagnostic> {
        if self.peek().is("module") && self.second_is("(") {
            return Err(diagnostic(
                "E_UNSUPPORTED",
                "manifest-path edit recipients were removed; use `to package_name::module` (or `to package_name` for its root), with the recipient's manifest name, not a dependency alias",
                self.peek().span,
            ));
        }
        let mut path = self.edit_path()?.into_iter();
        let package = path.next().expect("a parsed path has its first component");
        Ok((package, path.collect()))
    }

    pub(super) fn grant(&mut self, keyword: &str) -> Result<crate::namespace::Grant, Diagnostic> {
        let start = self.expect(keyword)?.span;
        let name = self.binding_name()?.0;
        self.expect(":")?;
        let target = self.edit_path()?;
        self.expect("to")?;
        let (grantee_package, grantee_path) = self.edit_recipient()?;
        let delegable = self.consume("delegable");
        self.expect("{")?;
        self.expect("domain")?;
        let region = self.domain_list(|parser| {
            let Type::Named { name } = parser.dispatch_type(false)? else {
                unreachable!()
            };
            Ok(name)
        })?;
        let end = self.expect("}")?.span;
        Ok(crate::namespace::Grant {
            name,
            target,
            grantee_package,
            grantee_path,
            region,
            delegable,
            span: start.through(end),
        })
    }

    pub(super) fn transfer(&mut self) -> Result<crate::namespace::Transfer, Diagnostic> {
        let start = self.expect("transfer")?.span;
        let name = self.binding_name()?.0;
        self.expect(":")?;
        let target = self.edit_path()?;
        self.expect("to")?;
        let (grantee_package, grantee_path) = self.edit_recipient()?;
        let end = self.expect(";")?.span;
        Ok(crate::namespace::Transfer {
            name,
            target,
            grantee_package,
            grantee_path,
            span: start.through(end),
        })
    }

    pub(super) fn contribution(&mut self) -> Result<crate::namespace::Contribution, Diagnostic> {
        let start = self.expect("contribution")?.span;
        let name = self.binding_name()?.0;
        self.expect(":")?;
        let target = self.edit_path()?;
        self.expect("{")?;
        let mut methods = Vec::new();
        while !self.peek().is("}") {
            methods.push(self.method()?);
        }
        let end = self.expect("}")?.span;
        Ok(crate::namespace::Contribution {
            name,
            target,
            methods,
            span: start.through(end),
        })
    }

    pub(super) fn retired_assembly(&self) -> Diagnostic {
        diagnostic(
            "E_UNSUPPORTED",
            "flat `assembly` was removed; use `assemble family { ... }` with scoped loans",
            self.peek().span,
        )
    }

    pub(super) fn assemble(
        &mut self,
        assembly: &mut Option<crate::namespace::Assembly>,
    ) -> Result<(), Diagnostic> {
        use crate::namespace::{Assembly, AssemblyItem};
        let start = self.expect("assemble")?.span;
        let target = self.edit_path()?;
        let header = start.through(self.expect("{")?.span);
        let assembly = assembly.get_or_insert_with(|| Assembly {
            source: Vec::new(),
            events: Vec::new(),
            span: start,
            expanded_count: 0,
        });
        assembly.source.push(AssemblyItem::Family {
            target,
            span: header,
        });
        let limit = crate::limits::MAX_ASSEMBLY_EVENTS;
        let overflow = |span: Span| {
            diagnostic(
                "E_LIMIT",
                format!(
                    "assembly exceeds the limit of {limit} events (first excess event at line {}, column {})",
                    span.line, span.column
                ),
                start,
            )
        };
        // A scalar depth admits the full wire event budget without Rust or JSON recursion.
        let mut depth = 0usize;
        loop {
            let command = self.advance();
            let (item, count) = if command.is("}") {
                (AssemblyItem::Close { span: command.span }, 1)
            } else if command.is("borrow") || command.is("delegate") {
                if command.is("borrow") && depth != 0 {
                    return Err(diagnostic(
                        "E_PARSE",
                        "`borrow` cannot be nested; use `delegate` inside a loan",
                        command.span,
                    ));
                }
                if command.is("delegate") && depth == 0 {
                    return Err(diagnostic(
                        "E_PARSE",
                        "`delegate` must be inside a `borrow` or `delegate` block",
                        command.span,
                    ));
                }
                let path = self.edit_path()?;
                let label = if self.consume("as") {
                    Some(self.binding_name()?.0)
                } else {
                    None
                };
                let span = command.span.through(self.expect("{")?.span);
                depth += 1;
                if command.is("borrow") {
                    (
                        AssemblyItem::Borrow {
                            grant: path,
                            label,
                            span,
                        },
                        1,
                    )
                } else {
                    (
                        AssemblyItem::Delegate {
                            delegation: path,
                            label,
                            span,
                        },
                        1,
                    )
                }
            } else if command.is("apply") {
                let mut contributions = vec![self.edit_path()?];
                while self.consume(",") {
                    if assembly.expanded_count + contributions.len() >= limit {
                        return Err(overflow(self.peek().span));
                    }
                    contributions.push(self.edit_path()?);
                }
                if self.peek().is("using") {
                    return Err(diagnostic(
                        "E_PARSE",
                        "`using` was removed; `apply` uses its innermost `assemble` loan",
                        self.peek().span,
                    ));
                }
                let span = command.span.through(self.expect(";")?.span);
                let count = contributions.len();
                (
                    AssemblyItem::Apply {
                        contributions,
                        span,
                    },
                    count,
                )
            } else if command.is("transfer") {
                if depth != 0 {
                    return Err(diagnostic(
                        "E_PARSE",
                        "`transfer` cannot occur while an edit loan is active",
                        command.span,
                    ));
                }
                let declaration = self.edit_path()?;
                let span = command.span.through(self.expect(";")?.span);
                (AssemblyItem::Transfer { declaration, span }, 1)
            } else {
                return Err(diagnostic(
                    "E_PARSE",
                    "expected a scoped `borrow`, `delegate`, `apply`, `transfer` or closing `}` in `assemble`; returns and seals are implicit",
                    command.span,
                ));
            };
            assembly.expanded_count += count;
            if assembly.expanded_count > limit {
                return Err(overflow(command.span));
            }
            assembly.source.push(item);
            if command.is("}") {
                if depth == 0 {
                    assembly.span = assembly.span.through(command.span);
                    return Ok(());
                }
                depth -= 1;
            }
        }
    }
}

impl crate::namespace::Assembly {
    pub(super) fn lower(&mut self) {
        use crate::namespace::{AssemblyItem, EditEvent};
        let labels: std::collections::HashSet<_> = self
            .source
            .iter()
            .filter_map(|item| match item {
                AssemblyItem::Borrow { label, .. } | AssemblyItem::Delegate { label, .. } => {
                    label.as_deref()
                }
                _ => None,
            })
            .collect();
        let mut next = 0usize;
        let mut loan_name = |path: &[String], label: &Option<String>| {
            if let Some(label) = label {
                return label.clone();
            }
            let base = path.last().expect("a parsed path is nonempty");
            loop {
                let name = format!("loan_{next}_{base}");
                next += 1;
                if !labels.contains(name.as_str()) {
                    return name;
                }
            }
        };
        let mut loans: Vec<String> = Vec::new();
        let mut family = None;
        self.events.reserve(self.expanded_count);
        for item in &self.source {
            let event = match item {
                AssemblyItem::Family { target, .. } => {
                    family = Some(target);
                    continue;
                }
                AssemblyItem::Borrow { grant, label, span } => {
                    let loan = loan_name(grant, label);
                    loans.push(loan.clone());
                    EditEvent::Borrow {
                        grant: grant.clone(),
                        loan,
                        span: *span,
                    }
                }
                AssemblyItem::Delegate {
                    delegation,
                    label,
                    span,
                } => {
                    let parent = loans.last().expect("delegate is inside a loan").clone();
                    let loan = loan_name(delegation, label);
                    loans.push(loan.clone());
                    EditEvent::Reborrow {
                        parent,
                        delegation: delegation.clone(),
                        loan,
                        span: *span,
                    }
                }
                AssemblyItem::Apply {
                    contributions,
                    span,
                } => {
                    self.events
                        .extend(contributions.iter().map(|c| EditEvent::Apply {
                            contribution: c.clone(),
                            loan: loans.last().cloned(),
                            span: *span,
                        }));
                    continue;
                }
                AssemblyItem::Transfer { declaration, span } => EditEvent::Transfer {
                    declaration: declaration.clone(),
                    span: *span,
                },
                AssemblyItem::Close { span } => match loans.pop() {
                    Some(loan) => EditEvent::Return { loan, span: *span },
                    None => EditEvent::Seal {
                        target: family.take().expect("close is inside a family").clone(),
                        span: *span,
                    },
                },
            };
            self.events.push(event);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value, json};

    fn events(source: &str) -> Result<Value, Diagnostic> {
        let input = SourceInput {
            source,
            file: "assemble.vast",
            offset: 111,
        };
        let parsed = parse_module_source(input, Vec::new(), true, None)?;
        Ok(serde_json::to_value(&parsed.modules[0].assembly.as_ref().unwrap().events).unwrap())
    }

    #[test]
    fn scoped_source_matches_the_ordered_trace_and_original_spans() {
        let src = "use foo as loan_1_edit;\nassemble base::f {\n  borrow a::edit { delegate d as leaf { apply c, m::e; } }\n  transfer t; apply m::owned;\n}\nassemble alias { borrow b as loan_0_edit {} }";
        let trace = events(src).unwrap();
        assert_eq!(trace, events(src).unwrap());
        let mut actual = Vec::new();
        let mut spelling = Vec::new();
        for mut event in trace.as_array().unwrap().clone() {
            let s = event.as_object_mut().unwrap().remove("span").unwrap();
            let start = s["start"].as_u64().unwrap() as usize - 111;
            let end = s["end"].as_u64().unwrap() as usize - 111;
            spelling.push(&src[start..end]);
            assert_eq!(s["line"], 1 + src[..start].matches('\n').count());
            assert_eq!(
                s["column"],
                1 + src[..start].rsplit('\n').next().unwrap().len()
            );
            actual.push(event);
        }
        assert_eq!(
            json!(actual),
            json!([
                {"op":"borrow","grant":["a","edit"],"loan":"loan_1_edit"},
                {"op":"reborrow","parent":"loan_1_edit","delegation":["d"],"loan":"leaf"},
                {"op":"apply","contribution":["c"],"loan":"leaf"},
                {"op":"apply","contribution":["m","e"],"loan":"leaf"},
                {"op":"return","loan":"leaf"}, {"op":"return","loan":"loan_1_edit"},
                {"op":"transfer","declaration":["t"]}, {"op":"apply","contribution":["m","owned"],"loan":null},
                {"op":"seal","target":["base","f"]},
                {"op":"borrow","grant":["b"],"loan":"loan_0_edit"}, {"op":"return","loan":"loan_0_edit"},
                {"op":"seal","target":["alias"]}
            ])
        );
        assert_eq!(
            spelling,
            [
                "borrow a::edit {",
                "delegate d as leaf {",
                "apply c, m::e;",
                "apply c, m::e;",
                "}",
                "}",
                "transfer t;",
                "apply m::owned;",
                "}",
                "borrow b as loan_0_edit {",
                "}",
                "}"
            ]
        );
        let braces: Vec<_> = trace
            .as_array()
            .unwrap()
            .iter()
            .filter(|e| e["op"] == "seal" || e["op"] == "return")
            .map(|e| e["span"]["start"].as_u64().unwrap() as usize - 111)
            .collect();
        assert_eq!(
            braces,
            src.match_indices('}').map(|(i, _)| i).collect::<Vec<_>>()
        );
    }

    #[test]
    fn malformed_scopes_reject_at_the_original_token() {
        for (body, token) in [
            ("delegate d {}", "delegate"),
            ("borrow a { borrow b {} }", "borrow b"),
            ("borrow a { transfer t; }", "transfer"),
            ("apply a using label;", "using"),
            ("return label;", "return"),
            ("seal f;", "seal"),
            ("reborrow a via d as b;", "reborrow"),
        ] {
            let src = format!("assemble f {{ {body} }}");
            let error = events(&src).unwrap_err();
            assert_eq!(error.code, "E_PARSE", "{error:?}");
            assert_eq!(error.span.start, src.find(token).unwrap() + 111);
        }
        let error = events("assembly { }").unwrap_err();
        assert_eq!(error.code, "E_UNSUPPORTED");
        assert!(error.message.contains("assemble family"));
    }

    #[test]
    fn implicit_returns_and_seals_share_one_budget_across_blocks() {
        let limit = crate::limits::MAX_ASSEMBLY_EVENTS;
        let full = format!(
            "assemble one {{ borrow grant {{ apply {}; }} }}",
            vec!["c"; limit - 3].join(",")
        );
        assert_eq!(events(&full).unwrap().as_array().unwrap().len(), limit);
        let error = events(&format!("{full}\nassemble two {{}}")).unwrap_err();
        assert_eq!(error.code, "E_LIMIT");
        assert_eq!(error.span.start, 111 + full.len() + 1);
        assert!(
            error
                .message
                .contains("first excess event at line 2, column 15")
        );
        let inner = format!(
            "assemble f {{ borrow g {{ apply {};
}}
}}",
            vec!["c"; limit - 1].join(",")
        );
        let error = events(&inner).unwrap_err();
        assert_eq!(error.span.start, 111);
        assert!(
            error
                .message
                .contains("first excess event at line 2, column 1")
        );
    }
}
