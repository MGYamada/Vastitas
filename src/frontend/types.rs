//! Types and endpoint indices.
use super::*;

impl Parser {
    pub(super) fn ty(&mut self) -> Result<Type, Diagnostic> {
        if self.nesting >= MAX_PARSE_NESTING {
            return Err(self.nesting_limit());
        }
        self.nesting += 1;
        let result = self.ty_inner();
        self.nesting -= 1;
        result
    }

    fn ty_inner(&mut self) -> Result<Type, Diagnostic> {
        if self.peek().is("fn") {
            return Err(diagnostic(
                "E_PARSE",
                "function types use Fn<Input, Output>; fn(...) -> ... introduces a function expression",
                self.advance().span,
            ));
        }
        let (name, span) = self.name()?;
        if self.packages
            && (self.peek().is("::")
                || name == "Object"
                || !TYPES.contains(&name.as_str()) && self.peek().is("<"))
        {
            return self.indexed_type(name, span);
        }
        match name.as_str() {
            "Pair" => {
                self.expect("<")?;
                let (element, element_span) = self.name()?;
                if !matches!(element.as_str(), "Nat" | "Int") {
                    return Err(diagnostic(
                        "E_TYPE",
                        "Pair elements must be Nat or Int",
                        element_span,
                    ));
                }
                self.type_close()?;
                Ok(Type::Pair { element })
            }
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

    pub(super) fn package_field(&mut self, name: &str) -> Result<(), Diagnostic> {
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
}
