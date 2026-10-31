use super::*;
use crate::storage::{
    Access, Coefficient, GemmMode, Layout, Literal, NumericalPolicy, Scalar,
    functions::OwnedType,
    source::{Action, Numerical, Parameter},
};

impl Parser {
    fn resource_number(&mut self) -> Result<u64, Diagnostic> {
        let token = self.advance();
        if let TokenKind::Number(number) = token.kind {
            return number.parse().map_err(|_| {
                diagnostic(
                    "E_RESOURCE_LIMIT",
                    "resource integer exceeds 64 bits",
                    token.span,
                )
            });
        }
        Err(diagnostic(
            "E_PARSE",
            "expected a nonnegative resource integer",
            token.span,
        ))
    }

    fn resource_scalar(&mut self) -> Result<Scalar, Diagnostic> {
        if self.consume("F64") {
            return Ok(Scalar::F64);
        }
        if self.consume("Complex") {
            self.expect("<")?;
            self.expect("F64")?;
            self.expect(">")?;
            return Ok(Scalar::ComplexF64);
        }
        Err(diagnostic(
            "E_TYPE",
            "resource elements require F64 or Complex<F64>",
            self.peek().span,
        ))
    }

    fn resource_layout(&mut self) -> Result<Layout, Diagnostic> {
        self.expect("layout")?;
        self.expect("(")?;
        let offset = self.resource_number()?;
        self.expect(",")?;
        let rows = self.resource_number()?;
        self.expect(",")?;
        let columns = self.resource_number()?;
        self.expect(",")?;
        let leading = self.resource_number()?;
        self.expect(",")?;
        let transposed = self.resource_boolean()?;
        self.expect(")")?;
        Ok(Layout {
            offset,
            rows,
            columns,
            leading,
            transposed,
        })
    }

    fn resource_boolean(&mut self) -> Result<bool, Diagnostic> {
        if self.consume("true") {
            Ok(true)
        } else if self.consume("false") {
            Ok(false)
        } else {
            Err(diagnostic(
                "E_RESOURCE_TYPE",
                "this resource profile requires a literal condition",
                self.peek().span,
            ))
        }
    }

    fn resource_owned(&mut self) -> Result<OwnedType, Diagnostic> {
        self.expect("Owned")?;
        self.expect("<")?;
        let scalar = self.resource_scalar()?;
        self.expect(",")?;
        let elements = self.resource_number()?;
        self.expect(">")?;
        let initialized = if self.consume("initialized") {
            self.indexed_list("[", "]", Self::resource_layout)?
        } else {
            Vec::new()
        };
        Ok(OwnedType {
            scalar,
            elements,
            initialized,
        })
    }

    fn resource_parameter(&mut self) -> Result<Parameter, Diagnostic> {
        let (name, start) = self.binding_name()?;
        self.expect(":")?;
        if self.peek().is("Owned") {
            let ty = self.resource_owned()?;
            return Ok(Parameter::Owned {
                name,
                ty,
                span: start.through(self.previous().span),
            });
        }
        if self.consume("Space") {
            self.expect("<")?;
            let implementation = self.type_path()?;
            self.expect(",")?;
            let dimension = self.resource_number()?;
            self.expect(">")?;
            return Ok(Parameter::Space {
                name,
                implementation,
                dimension,
                span: start.through(self.previous().span),
            });
        }
        if self.consume("Basis") {
            self.expect("<")?;
            let (space, _) = self.binding_name()?;
            self.expect(">")?;
            return Ok(Parameter::Basis {
                name,
                space,
                span: start.through(self.previous().span),
            });
        }
        let map_access = if self.consume("ReadMap") {
            Some(Access::Read)
        } else if self.consume("WriteMap") {
            Some(Access::Write)
        } else if self.consume("ReadWriteMap") {
            Some(Access::ReadWrite)
        } else {
            None
        };
        if let Some(access) = map_access {
            self.expect("<")?;
            let (source, _) = self.binding_name()?;
            self.expect(",")?;
            let (target, _) = self.binding_name()?;
            self.expect(">")?;
            let initializes = self.consume("initializes");
            return Ok(Parameter::Map {
                name,
                source,
                target,
                access,
                initializes,
                span: start.through(self.previous().span),
            });
        }
        let access = if self.consume("Read") {
            Access::Read
        } else if self.consume("Write") {
            Access::Write
        } else if self.consume("ReadWrite") {
            Access::ReadWrite
        } else {
            return Err(diagnostic(
                "E_TYPE",
                "resource parameters require Owned, Read/Write/ReadWrite, Space, Basis or ReadMap/WriteMap/ReadWriteMap",
                self.peek().span,
            ));
        };
        self.expect("<")?;
        let scalar = self.resource_scalar()?;
        self.expect(",")?;
        let rows = self.resource_number()?;
        self.expect(",")?;
        let columns = self.resource_number()?;
        self.expect(">")?;
        let initializes = self.consume("initializes");
        Ok(Parameter::Borrowed {
            name,
            scalar,
            rows,
            columns,
            access,
            initializes,
            span: start.through(self.previous().span),
        })
    }

    fn resource_literal(&mut self) -> Result<Literal, Diagnostic> {
        let complex = if self.consume("f64_bits") {
            false
        } else if self.consume("complex_bits") {
            true
        } else {
            return Err(diagnostic(
                "E_TYPE",
                "resource payloads use f64_bits or complex_bits",
                self.peek().span,
            ));
        };
        self.expect("(")?;
        let real = self.resource_number()?;
        let value = if complex {
            self.expect(",")?;
            Literal::ComplexF64 {
                real,
                imaginary: self.resource_number()?,
            }
        } else {
            Literal::F64 { bits: real }
        };
        self.expect(")")?;
        Ok(value)
    }

    fn resource_names(&mut self) -> Result<Vec<String>, Diagnostic> {
        self.indexed_list("(", ")", |p| Ok(p.name()?.0))
    }

    fn resource_action(&mut self) -> Result<Action, Diagnostic> {
        if self.consume("allocate") {
            let owner = self.binding_name()?.0;
            self.expect(":")?;
            let scalar = self.resource_scalar()?;
            self.expect("[")?;
            let elements = self.resource_number()?;
            self.expect("]")?;
            return Ok(Action::Allocate {
                owner,
                scalar,
                elements,
            });
        }
        if self.consume("move") {
            let source = self.name()?.0;
            self.expect("->")?;
            let target = self.binding_name()?.0;
            return Ok(Action::Move { source, target });
        }
        if self.consume("borrow") {
            let name = self.binding_name()?.0;
            self.expect("=")?;
            let access = if self.consume("read") {
                Access::Read
            } else if self.consume("write") {
                Access::Write
            } else if self.consume("read_write") {
                Access::ReadWrite
            } else {
                return Err(diagnostic(
                    "E_TYPE",
                    "borrow requires read, write or read_write",
                    self.peek().span,
                ));
            };
            self.expect("(")?;
            let source = self.name()?.0;
            self.expect(",")?;
            let layout = self.resource_layout()?;
            self.expect(")")?;
            return Ok(Action::Borrow {
                name,
                source,
                layout,
                access,
            });
        }
        let operation = self.name()?.0;
        self.expect("(")?;
        let loan = self.name()?.0;
        let action = match operation.as_str() {
            "drop" => Action::Drop { owner: loan },
            "release" => Action::Release { loan },
            "transpose" => Action::Transpose { loan },
            "fill" => {
                self.expect(",")?;
                Action::Fill {
                    loan,
                    value: self.resource_literal()?,
                }
            }
            "copy" => {
                self.expect(",")?;
                Action::Copy {
                    source: loan,
                    target: self.name()?.0,
                }
            }
            "store" | "expect" => {
                self.expect(",")?;
                let row = self.resource_number()?;
                self.expect(",")?;
                let column = self.resource_number()?;
                self.expect(",")?;
                let value = self.resource_literal()?;
                if operation == "store" {
                    Action::Store {
                        loan,
                        row,
                        column,
                        value,
                    }
                } else {
                    Action::Expect {
                        loan,
                        row,
                        column,
                        value,
                    }
                }
            }
            _ => {
                return Err(diagnostic(
                    "E_PARSE",
                    "unknown resource operation",
                    self.previous().span,
                ));
            }
        };
        self.expect(")")?;
        Ok(action)
    }

    fn numerical_coefficient(&mut self) -> Result<Coefficient<String>, Diagnostic> {
        if self.consume("coefficient") {
            self.expect("(")?;
            let loan = self.name()?.0;
            self.expect(")")?;
            Ok(Coefficient::Loan { loan })
        } else {
            Ok(Coefficient::Literal {
                value: self.resource_literal()?,
            })
        }
    }

    fn numerical_operation(&mut self) -> Result<Numerical, Diagnostic> {
        if self.consume("space") {
            let name = self.binding_name()?.0;
            self.expect("=")?;
            self.expect("linear")?;
            self.expect("(")?;
            let implementation = self.type_path()?;
            self.expect(",")?;
            let dimension = self.resource_number()?;
            self.expect(")")?;
            return Ok(Numerical::Space {
                name,
                implementation,
                dimension,
            });
        }
        if self.consume("basis") {
            let name = self.binding_name()?.0;
            self.expect("=")?;
            self.expect("basis")?;
            self.expect("(")?;
            let space = self.name()?.0;
            self.expect(")")?;
            return Ok(Numerical::Basis { name, space });
        }
        if self.consume("map") {
            let name = self.binding_name()?.0;
            self.expect("=")?;
            self.expect("view")?;
            self.expect("(")?;
            let loan = self.name()?.0;
            self.expect(",")?;
            let source = self.name()?.0;
            self.expect(",")?;
            let target = self.name()?.0;
            self.expect(")")?;
            return Ok(Numerical::Map {
                name,
                loan,
                source,
                target,
            });
        }
        self.expect("gemm")?;
        self.expect("(")?;
        let left = self.name()?.0;
        self.expect(",")?;
        let right = self.name()?.0;
        self.expect(",")?;
        let output = self.name()?.0;
        self.expect(",")?;
        let mode = if self.consume("overwrite") {
            GemmMode::Overwrite
        } else if self.consume("accumulate") {
            GemmMode::Accumulate
        } else {
            return Err(diagnostic(
                "E_NUMERICAL_TYPE",
                "GEMM requires overwrite or accumulate",
                self.peek().span,
            ));
        };
        self.expect(",")?;
        self.expect("NativeFast")?;
        let mut alpha = None;
        let mut beta = None;
        while self.consume(",") {
            let target = if self.consume("alpha") {
                &mut alpha
            } else if self.consume("beta") {
                &mut beta
            } else {
                return Err(diagnostic(
                    "E_NUMERICAL_TYPE",
                    "expected alpha or beta coefficient",
                    self.peek().span,
                ));
            };
            if target.is_some() {
                return Err(diagnostic(
                    "E_DUPLICATE",
                    "GEMM coefficient is specified twice",
                    self.previous().span,
                ));
            }
            self.expect("=")?;
            *target = Some(self.numerical_coefficient()?);
        }
        self.expect(")")?;
        Ok(Numerical::Gemm {
            left,
            right,
            output,
            mode,
            policy: NumericalPolicy::NativeFast,
            alpha,
            beta,
        })
    }

    fn resource_statements(
        &mut self,
        depth: usize,
    ) -> Result<Vec<crate::storage::source::Statement>, Diagnostic> {
        if depth > MAX_PARSE_NESTING {
            return Err(diagnostic(
                "E_LIMIT",
                "resource branch nesting exceeds the parser limit",
                self.peek().span,
            ));
        }
        let mut body = Vec::new();
        while !self.peek().is("}") && !self.peek().is("value") {
            let start = self.peek().span;
            let statement = if self.consume("if") {
                let condition = self.resource_boolean()?;
                self.expect("{")?;
                let yes = self.resource_statements(depth + 1)?;
                self.expect("}")?;
                self.expect("else")?;
                self.expect("{")?;
                let no = self.resource_statements(depth + 1)?;
                self.expect("}")?;
                crate::storage::source::Statement::Branch {
                    condition,
                    yes,
                    no,
                    span: start.through(self.previous().span),
                }
            } else if self.consume("call") {
                let callee = self.reference_path()?.0;
                let arguments = self.resource_names()?;
                self.expect("->")?;
                let results = self.resource_names()?;
                self.expect(";")?;
                crate::storage::source::Statement::Call {
                    callee,
                    arguments,
                    results,
                    span: start.through(self.previous().span),
                }
            } else if ["space", "basis", "map", "gemm"]
                .iter()
                .any(|word| self.peek().is(word))
            {
                let operation = self.numerical_operation()?;
                self.expect(";")?;
                crate::storage::source::Statement::Numerical {
                    operation,
                    span: start.through(self.previous().span),
                }
            } else {
                let action = self.resource_action()?;
                self.expect(";")?;
                crate::storage::source::Statement::Action {
                    action,
                    span: start.through(self.previous().span),
                }
            };
            body.push(statement);
        }
        Ok(body)
    }

    pub(super) fn resource_function(
        &mut self,
    ) -> Result<crate::storage::source::Function, Diagnostic> {
        let start = self.expect("resource")?.span;
        self.expect("fn")?;
        let name = self.binding_name()?.0;
        let parameters = self.indexed_list("(", ")", Self::resource_parameter)?;
        let results = if self.consume("returns") {
            self.indexed_list("(", ")", |p| {
                let name = p.name()?.0;
                p.expect(":")?;
                Ok(crate::storage::source::Result {
                    name,
                    ty: p.resource_owned()?,
                })
            })?
        } else {
            Vec::new()
        };
        self.expect("->")?;
        let value_type = self.ty()?;
        self.expect("{")?;
        let body = self.resource_statements(0)?;
        self.expect("value")?;
        let value_body = self.block()?;
        self.expect("}")?;
        Ok(crate::storage::source::Function {
            name,
            parameters,
            results,
            body,
            value_type,
            value_body,
            span: start.through(self.previous().span),
        })
    }
}
