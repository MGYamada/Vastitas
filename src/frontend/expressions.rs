//! Blocks, statements and the Pratt expression parser.
use super::*;

impl Parser {
    // For root bodies only. A block nested in an expression must contribute
    // its depth through block_with_depth.
    pub(super) fn block(&mut self) -> Result<Block, Diagnostic> {
        Ok(self.block_with_depth()?.0)
    }

    // A block is one level deeper than its result and its statement values;
    // each statement value also counts its statement edge.
    fn block_with_depth(&mut self) -> Result<(Block, usize), Diagnostic> {
        let start = self.expect("{")?.span;
        let mut statements = Vec::new();
        let mut depth = 0;
        while self.peek().is("let") || self.peek().is("unpack") {
            let (statement, value) = self.statement()?;
            depth = depth.max(value + 1);
            statements.push(statement);
        }
        if self.peek().is("}") {
            let end = self.advance().span;
            let block = Block {
                statements,
                result: Box::new(Expr {
                    kind: ExprKind::Unit,
                    span: end,
                }),
                span: start.through(end),
            };
            return Ok((block, 1 + depth.max(1)));
        }
        let (result, result_depth) = self.expression_with_depth(0)?;
        if self.peek().is("as")
            && self
                .tokens
                .get(self.position + 1)
                .is_some_and(|token| token.is("{"))
        {
            return Err(diagnostic(
                "E_PARSE",
                "to open a package, write `unpack value as { scheme: X, point: p };`",
                self.peek().span,
            ));
        }
        if self.peek().is(";") {
            return Err(diagnostic(
                "E_UNSUPPORTED",
                "expression statements are not supported; use a `let` binding or leave the final expression without `;`",
                self.peek().span,
            ));
        }
        let end = self.expect("}")?.span;
        let block = Block {
            statements,
            result: Box::new(result),
            span: start.through(end),
        };
        Ok((block, 1 + depth.max(result_depth)))
    }

    // Also returns the depth of the statement's value expression.
    fn statement(&mut self) -> Result<(Statement, usize), Diagnostic> {
        let token = self.advance();
        if token.is("let") {
            if self.peek().is("mut")
                && self
                    .tokens
                    .get(self.position + 1)
                    .is_some_and(|next| matches!(next.kind, TokenKind::Name(_)))
            {
                return Err(diagnostic(
                    "E_UNSUPPORTED",
                    "mutable bindings are not supported",
                    self.peek().span,
                ));
            }
            let (name, _) = self.binding_name()?;
            let annotation = if self.consume(":") {
                Some(self.ty()?)
            } else {
                None
            };
            self.expect("=")?;
            let (value, depth) = self.expression_with_depth(0)?;
            let end = self.expect(";")?.span;
            let statement = Statement {
                kind: StatementKind::Let {
                    name,
                    annotation,
                    value,
                },
                span: token.span.through(end),
            };
            Ok((statement, depth))
        } else {
            let (value, depth) = self.expression_with_depth(0)?;
            self.expect("as")?;
            self.expect("{")?;
            if self.packages && self.peek().is("witness") {
                self.indexed = true;
                self.expect("witness")?;
                self.expect(":")?;
                let witness = self.binding_name()?.0;
                self.expect(",")?;
                self.expect("fields")?;
                self.expect(":")?;
                let fields = self.delimited_list("[", "]", |p| Ok(p.binding_name()?.0))?;
                self.consume(",");
                self.expect("}")?;
                let end = self.expect(";")?.span;
                let statement = Statement {
                    kind: StatementKind::UnpackFields {
                        value,
                        witness,
                        fields,
                    },
                    span: token.span.through(end),
                };
                return Ok((statement, depth));
            }
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
            let statement = Statement {
                kind: StatementKind::Unpack {
                    value,
                    scheme,
                    point,
                },
                span: token.span.through(end),
            };
            Ok((statement, depth))
        }
    }

    // Every node returns its depth with it, so parents combine checked child
    // depths directly. Leaves have depth 1.
    fn tree_depth(children: usize, span: Span) -> Result<usize, Diagnostic> {
        let depth = children + 1;
        if depth > MAX_AST_DEPTH {
            return Err(diagnostic(
                "E_LIMIT",
                format!("expression tree exceeds the supported depth limit of {MAX_AST_DEPTH}"),
                span,
            ));
        }
        Ok(depth)
    }

    // The message is chosen from parser state, not from another diagnostic:
    // an `else if` chain is named only when its open links consume most of the
    // exhausted budget.
    pub(super) fn nesting_limit(&self) -> Diagnostic {
        let message = if 2 * self.else_if_links > MAX_PARSE_NESTING {
            format!(
                "`else if` chain exceeds the supported nesting limit; a standalone chain supports at most {} conditions, and enclosing expressions also consume nesting budget",
                MAX_PARSE_NESTING - 2
            )
        } else {
            format!(
                "combined type/expression nesting exceeds the supported limit of {MAX_PARSE_NESTING}"
            )
        };
        diagnostic("E_LIMIT", message, self.peek().span)
    }

    pub(super) fn expression_with_depth(
        &mut self,
        min_binding_power: u8,
    ) -> Result<(Expr, usize), Diagnostic> {
        if self.nesting >= MAX_PARSE_NESTING {
            return Err(self.nesting_limit());
        }
        self.nesting += 1;
        let result = self.expression_inner(min_binding_power);
        self.nesting -= 1;
        result
    }

    fn expression_inner(&mut self, min_binding_power: u8) -> Result<(Expr, usize), Diagnostic> {
        let (mut left, mut depth) = self.prefix()?;
        // A prefix may contain a parenthesized comparison, which is a valid
        // operand. Only comparisons consumed by this Pratt invocation chain.
        let mut comparison = false;
        while let TokenKind::Symbol(op) = &self.peek().kind {
            if op == "(" {
                // Else-if parsing requests only the conditional prefix; leave
                // its trailing invocation for the enclosing expression.
                if min_binding_power == u8::MAX {
                    break;
                }
                self.advance();
                (left, depth) = self.call(left, depth)?;
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
            let (right, right_depth) = self.expression_with_depth(power + 1)?;
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
            depth = Self::tree_depth(depth.max(right_depth), span)?;
        }
        Ok((left, depth))
    }

    // Parse the arguments after a consumed `(` and build the call node. The
    // loop is not `delimited_tail`: its closure would add frames to the
    // recursion through nested calls.
    #[inline(never)]
    fn call(&mut self, callee: Expr, callee_depth: usize) -> Result<(Expr, usize), Diagnostic> {
        let mut args = Vec::new();
        let mut children = 0;
        if !self.consume(")") {
            loop {
                let (arg, arg_depth) = self.expression_with_depth(0)?;
                children = children.max(arg_depth);
                args.push(arg);
                if self.consume(")") {
                    break;
                }
                self.expect(",")?;
                if self.consume(")") {
                    break;
                }
            }
        }
        let span = callee.span.through(self.previous().span);
        let kind = match callee.kind {
            // A named callee is part of the call node, not a child.
            ExprKind::Variable { name } => ExprKind::Call { callee: name, args },
            _ => {
                children = children.max(callee_depth);
                ExprKind::Invoke {
                    callee: Box::new(callee),
                    args,
                }
            }
        };
        let depth = Self::tree_depth(children, span)?;
        Ok((Expr { kind, span }, depth))
    }

    // Compound forms are parsed out of line, so the recursive path through
    // prefix keeps a small frame and the nesting limit is reached before stack
    // exhaustion, also in unoptimized builds.
    fn prefix(&mut self) -> Result<(Expr, usize), Diagnostic> {
        let token = self.advance();
        let start = token.span;
        // The node's kind and its deepest child; zero for a leaf.
        let (kind, children) = match token.kind {
            TokenKind::Text => {
                return Err(diagnostic(
                    "E_UNSUPPORTED",
                    "string literals are not supported",
                    token.span,
                ));
            }
            TokenKind::Floating(_) => {
                return Err(diagnostic(
                    "E_UNSUPPORTED",
                    "floating-point literals are only supported as exact resource payloads inside f64(...) or complex(...); pure expressions require Nat or Int literals",
                    token.span,
                ));
            }
            TokenKind::Name(ref name) if unsupported_keyword(name).is_some() => {
                return Err(diagnostic(
                    "E_UNSUPPORTED",
                    unsupported_keyword(name).unwrap(),
                    token.span,
                ));
            }
            TokenKind::Number(value) => {
                let stripped = value.trim_start_matches('0');
                let value = if stripped.is_empty() {
                    "0".into()
                } else {
                    stripped.into()
                };
                (ExprKind::Integer { value }, 0)
            }
            TokenKind::Name(ref name) if name == "true" || name == "false" => (
                ExprKind::Boolean {
                    value: name == "true",
                },
                0,
            ),
            TokenKind::Name(ref name) if name == "if" => self.conditional()?,
            TokenKind::Name(ref name) if name == "pack" => {
                if self.packages && !self.peek().is("{") {
                    self.indexed_pack()?
                } else {
                    self.pack()?
                }
            }
            TokenKind::Name(ref name) if name == "fn" => self.lambda()?,
            TokenKind::Name(mut name)
                if !KEYWORDS.contains(&name.as_str())
                    || (self.packages && name == "generic" && self.peek().is("::")) =>
            {
                if self.packages {
                    while self.consume("::") {
                        let (component, _) = self.path_component()?;
                        name.push_str("::");
                        name.push_str(&component);
                    }
                }
                (ExprKind::Variable { name }, 0)
            }
            TokenKind::Symbol(op) if op == "-" || op == "!" => self.unary(op)?,
            TokenKind::Symbol(ref symbol) if symbol == "(" => {
                if self.consume(")") {
                    (ExprKind::Unit, 0)
                } else {
                    return self.parenthesized(start);
                }
            }
            TokenKind::Symbol(ref symbol) if symbol == "{" => {
                self.position -= 1;
                self.block_expression()?
            }
            _ => {
                return Err(diagnostic(
                    "E_PARSE",
                    format!("expected an expression, found {}", token.description()),
                    start,
                ));
            }
        };
        let span = start.through(self.previous().span);
        let depth = Self::tree_depth(children, span)?;
        Ok((Expr { kind, span }, depth))
    }

    #[inline(never)]
    fn conditional(&mut self) -> Result<(ExprKind, usize), Diagnostic> {
        let (condition, condition_depth) = self.expression_with_depth(0)?;
        let (then_branch, then_depth) = self.block_with_depth()?;
        self.expect("else")?;
        let (else_branch, else_depth) = if self.peek().is("if") {
            // Parse just the conditional prefix with the usual depth guard.
            // Operators after its final block still belong to the surrounding
            // expression, not the synthetic block.
            self.else_if_links += 1;
            let result = self.expression_with_depth(u8::MAX);
            self.else_if_links -= 1;
            let (result, result_depth) = result?;
            let block = Block {
                span: result.span,
                statements: Vec::new(),
                result: Box::new(result),
            };
            (block, 1 + result_depth)
        } else {
            self.block_with_depth()?
        };
        let kind = ExprKind::If {
            condition: Box::new(condition),
            then_branch,
            else_branch,
        };
        Ok((kind, condition_depth.max(then_depth).max(else_depth)))
    }

    #[inline(never)]
    fn pack(&mut self) -> Result<(ExprKind, usize), Diagnostic> {
        self.expect("{")?;
        self.package_field("scheme")?;
        self.expect(":")?;
        let (scheme, scheme_depth) = self.expression_with_depth(0)?;
        self.expect(",")?;
        self.package_field("point")?;
        self.expect(":")?;
        let (point, point_depth) = self.expression_with_depth(0)?;
        self.consume(",");
        self.expect("}")?;
        let kind = ExprKind::Pack {
            scheme: Box::new(scheme),
            point: Box::new(point),
        };
        Ok((kind, scheme_depth.max(point_depth)))
    }

    #[inline(never)]
    fn lambda(&mut self) -> Result<(ExprKind, usize), Diagnostic> {
        let params = self.parameters(false)?;
        self.expect("->")?;
        let return_type = self.ty()?;
        let (body, depth) = self.block_with_depth()?;
        let kind = ExprKind::Lambda {
            params,
            return_type,
            body,
        };
        Ok((kind, depth))
    }

    #[inline(never)]
    fn unary(&mut self, op: String) -> Result<(ExprKind, usize), Diagnostic> {
        let (operand, depth) = self.expression_with_depth(13)?;
        let kind = ExprKind::Unary {
            op,
            operand: Box::new(operand),
        };
        Ok((kind, depth))
    }

    // Parentheses widen the span but add no tree node.
    #[inline(never)]
    fn parenthesized(&mut self, start: Span) -> Result<(Expr, usize), Diagnostic> {
        let (inner, depth) = self.expression_with_depth(0)?;
        self.expect(")")?;
        let expr = Expr {
            span: start.through(self.previous().span),
            ..inner
        };
        Ok((expr, depth))
    }

    #[inline(never)]
    fn block_expression(&mut self) -> Result<(ExprKind, usize), Diagnostic> {
        let (body, depth) = self.block_with_depth()?;
        Ok((ExprKind::Block { body }, depth))
    }
}
