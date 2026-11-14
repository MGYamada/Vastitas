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
        if self.peek().is("module")
            && self
                .tokens
                .get(self.position + 1)
                .is_some_and(|t| t.is("("))
        {
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

    pub(super) fn grant(&mut self, keyword: &str) -> Result<crate::packages::Grant, Diagnostic> {
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
        Ok(crate::packages::Grant {
            name,
            target,
            grantee_package,
            grantee_path,
            region,
            delegable,
            span: start.through(end),
        })
    }

    pub(super) fn transfer(&mut self) -> Result<crate::packages::Transfer, Diagnostic> {
        let start = self.expect("transfer")?.span;
        let name = self.binding_name()?.0;
        self.expect(":")?;
        let target = self.edit_path()?;
        self.expect("to")?;
        let (grantee_package, grantee_path) = self.edit_recipient()?;
        let end = self.expect(";")?.span;
        Ok(crate::packages::Transfer {
            name,
            target,
            grantee_package,
            grantee_path,
            span: start.through(end),
        })
    }

    pub(super) fn contribution(&mut self) -> Result<crate::packages::Contribution, Diagnostic> {
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
        Ok(crate::packages::Contribution {
            name,
            target,
            methods,
            span: start.through(end),
        })
    }

    pub(super) fn assembly(&mut self) -> Result<crate::packages::Assembly, Diagnostic> {
        use crate::packages::EditEvent;
        let start = self.expect("assembly")?.span;
        self.expect("{")?;
        let mut events = Vec::new();
        while !self.peek().is("}") {
            let command = self.advance();
            let event = if command.is("borrow") {
                let grant = self.edit_path()?;
                self.expect("as")?;
                let loan = self.binding_name()?.0;
                let span = command.span.through(self.expect(";")?.span);
                EditEvent::Borrow { grant, loan, span }
            } else if command.is("apply") {
                let contribution = self.edit_path()?;
                let loan = if self.consume("using") {
                    Some(self.binding_name()?.0)
                } else {
                    None
                };
                let span = command.span.through(self.expect(";")?.span);
                EditEvent::Apply {
                    contribution,
                    loan,
                    span,
                }
            } else if command.is("return") {
                let loan = self.binding_name()?.0;
                let span = command.span.through(self.expect(";")?.span);
                EditEvent::Return { loan, span }
            } else if command.is("seal") {
                let target = self.edit_path()?;
                let span = command.span.through(self.expect(";")?.span);
                EditEvent::Seal { target, span }
            } else if command.is("reborrow") {
                let parent = self.binding_name()?.0;
                self.expect("via")?;
                let delegation = self.edit_path()?;
                self.expect("as")?;
                let loan = self.binding_name()?.0;
                let span = command.span.through(self.expect(";")?.span);
                EditEvent::Reborrow {
                    parent,
                    delegation,
                    loan,
                    span,
                }
            } else if command.is("transfer") {
                let declaration = self.edit_path()?;
                let span = command.span.through(self.expect(";")?.span);
                EditEvent::Transfer { declaration, span }
            } else {
                return Err(diagnostic(
                    "E_PARSE",
                    "expected borrow, reborrow, apply, return, transfer or seal in assembly",
                    command.span,
                ));
            };
            events.push(event);
        }
        let end = self.expect("}")?.span;
        // The kernel's decoder refuses a longer event list as a malformed
        // request, so the frontend reports the limit at the block (#703).
        if events.len() > crate::limits::MAX_ASSEMBLY_EVENTS {
            return Err(diagnostic(
                "E_LIMIT",
                format!(
                    "assembly exceeds the limit of {} events",
                    crate::limits::MAX_ASSEMBLY_EVENTS
                ),
                start.through(end),
            ));
        }
        Ok(crate::packages::Assembly {
            events,
            span: start.through(end),
        })
    }
}
