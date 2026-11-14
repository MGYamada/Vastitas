//! Lexical name resolution of a flat compilation unit.
use super::*;

/// Lexical bindings, kept as one stack so that entering a block or lambda never
/// copies the enclosing scope. Each lambda opens a frame; bindings of enclosing
/// frames are visible only as capture/shadowing errors.
#[derive(Default)]
struct Scope<'a> {
    names: Vec<&'a str>,
    // The frames that currently bind each name, innermost last.
    frames: HashMap<&'a str, Vec<usize>>,
    frame: usize,
}

impl<'a> Scope<'a> {
    fn contains(&self, name: &str) -> bool {
        self.frames.get(name).and_then(|frames| frames.last()) == Some(&self.frame)
    }

    fn enclosing(&self, name: &str) -> bool {
        self.frames
            .get(name)
            .and_then(|frames| frames.first())
            .is_some_and(|&frame| frame < self.frame)
    }

    fn push(&mut self, name: &'a str) {
        self.names.push(name);
        self.frames.entry(name).or_default().push(self.frame);
    }

    fn mark(&self) -> usize {
        self.names.len()
    }

    fn truncate(&mut self, mark: usize) {
        while self.names.len() > mark {
            let name = self.names.pop().unwrap();
            let frames = self.frames.get_mut(name).unwrap();
            frames.pop();
            if frames.is_empty() {
                self.frames.remove(name);
            }
        }
    }
}

pub(super) struct Resolver<'a> {
    functions: HashMap<&'a str, usize>,
    generics: HashMap<&'a str, Span>,
    abstract_types: HashMap<&'a str, Span>,
    errors: Vec<Diagnostic>,
    calls: Vec<Vec<usize>>,
    scope: Scope<'a>,
}

impl<'a> Resolver<'a> {
    pub(super) fn module(module: &'a Module) -> Vec<Diagnostic> {
        let mut this = Self {
            functions: HashMap::new(),
            generics: HashMap::new(),
            abstract_types: HashMap::new(),
            errors: Vec::new(),
            calls: vec![Vec::new(); module.functions.len()],
            scope: Scope::default(),
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
        // Two declarations of one name are reported at the later one in the
        // file, whatever their kinds (#747).
        let later = |span: Span, earlier: Span| {
            if earlier.start > span.start {
                earlier
            } else {
                span
            }
        };
        for generic in &module.generics {
            let earlier = this
                .generics
                .get(generic.name.as_str())
                .copied()
                .or_else(|| {
                    this.functions
                        .get(generic.name.as_str())
                        .map(|&index| module.functions[index].span)
                });
            if let Some(earlier) = earlier {
                this.errors.push(diagnostic(
                    "E_DUPLICATE",
                    format!("callable `{}` is defined more than once", generic.name),
                    later(generic.span, earlier),
                ));
            }
            this.generics.entry(&generic.name).or_insert(generic.span);
            if generic.name == "main" {
                this.errors.push(diagnostic(
                    "E_MAIN",
                    "the entrypoint must be an ordinary `fn main() -> Int`, not a generic",
                    generic.span,
                ));
            }
        }
        for declaration in &module.abstract_types {
            let name = declaration.name.as_str();
            let earlier = this
                .abstract_types
                .get(name)
                .or_else(|| this.generics.get(name))
                .copied()
                .or_else(|| {
                    this.functions
                        .get(name)
                        .map(|&index| module.functions[index].span)
                });
            if let Some(earlier) = earlier {
                this.errors.push(diagnostic(
                    "E_DUPLICATE",
                    format!(
                        "declaration `{}` is defined more than once",
                        declaration.name
                    ),
                    later(declaration.span, earlier),
                ));
            }
            this.abstract_types
                .entry(&declaration.name)
                .or_insert(declaration.span);
        }
        for generic in &module.generics {
            for param in &generic.params {
                this.bind(&param.name, param.span);
            }
            this.scope.truncate(0);
        }
        for (i, function) in module.functions.iter().enumerate() {
            for param in &function.params {
                this.ty(&param.ty, param.span);
                this.bind(&param.name, param.span);
            }
            this.ty(&function.return_type, function.span);
            this.block(&function.body, Some(i));
            this.scope.truncate(0);
        }
        for method in &module.methods {
            if !this.generics.contains_key(method.name.as_str()) {
                this.errors.push(diagnostic(
                    "E_NAME",
                    format!(
                        "method `{}` requires a declared generic of the same name",
                        method.name
                    ),
                    method.span,
                ));
            }
            for param in &method.params {
                this.bind(&param.name, param.span);
            }
            // The backend resolves generic calls after specialization. Adding
            // family-name edges here could invent cycles between disjoint
            // concrete method instances.
            this.block(&method.body, None);
            this.scope.truncate(0);
        }
        for contract in &module.abstract_methods {
            if !this.generics.contains_key(contract.name.as_str()) {
                this.errors.push(diagnostic(
                    "E_NAME",
                    format!(
                        "abstract method `{}` requires a declared generic",
                        contract.name
                    ),
                    contract.span,
                ));
            }
            for param in &contract.params {
                this.bind(&param.name, param.span);
            }
            this.scope.truncate(0);
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

    fn bind(&mut self, name: &'a str, span: Span) {
        if self.functions.contains_key(name)
            || self.generics.contains_key(name)
            || self.abstract_types.contains_key(name)
        {
            self.errors.push(diagnostic(
                "E_SHADOW",
                format!("binding `{name}` shadows a callable; use a distinct name"),
                span,
            ));
        }
        if self.scope.enclosing(name) {
            self.errors.push(diagnostic(
                "E_SHADOW",
                format!("binding `{name}` shadows an enclosing binding; use a distinct name"),
                span,
            ));
        }
        if self.scope.contains(name) {
            self.errors.push(diagnostic(
                "E_DUPLICATE",
                format!(
                    "binding `{name}` already exists in this scope; shadowing is not supported"
                ),
                span,
            ));
        }
        self.scope.push(name);
    }

    fn index(&mut self, index: &Index, span: Span) {
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
            && !self.scope.contains(name)
        {
            if self.scope.enclosing(name) {
                self.errors.push(diagnostic("E_CAPTURE", format!("independent lambda cannot capture endpoint `{name}`; pass it as an explicit parameter"), span));
                return;
            }
            self.errors.push(diagnostic("E_NAME", format!("unknown endpoint object `{name}`; dependent types can refer only to earlier bindings"), span));
        }
    }

    fn ty(&mut self, ty: &Type, span: Span) {
        match ty {
            Type::Function {
                params,
                return_type,
            } => {
                for param in params {
                    self.ty(param, span);
                }
                self.ty(return_type, span);
            }
            Type::Point { target, source } | Type::Morphism { target, source } => {
                self.index(target, span);
                self.index(source, span);
            }
            _ => {}
        }
    }

    fn block(&mut self, block: &'a Block, function: Option<usize>) {
        let mark = self.scope.mark();
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Let {
                    name,
                    annotation,
                    value,
                } => {
                    if let Some(ty) = annotation {
                        self.ty(ty, statement.span);
                    }
                    self.expr(value, function, false);
                    self.bind(name, statement.span);
                }
                StatementKind::Unpack {
                    value,
                    scheme,
                    point,
                } => {
                    self.expr(value, function, false);
                    self.bind(scheme, statement.span);
                    self.bind(point, statement.span);
                }
                StatementKind::UnpackFields {
                    value,
                    witness,
                    fields,
                } => {
                    self.expr(value, function, false);
                    self.bind(witness, statement.span);
                    for field in fields {
                        self.bind(field, statement.span);
                    }
                }
            }
        }
        self.expr(&block.result, function, false);
        self.scope.truncate(mark);
    }

    fn expr(&mut self, expr: &'a Expr, function: Option<usize>, ring_position: bool) {
        match &expr.kind {
            ExprKind::Lambda {
                params,
                return_type,
                body,
            } => {
                let mark = self.scope.mark();
                self.scope.frame += 1;
                for param in params {
                    self.ty(&param.ty, param.span);
                    self.bind(&param.name, param.span);
                }
                self.ty(return_type, expr.span);
                // The lambda is an independent definition. Its calls are not
                // edges from the enclosing function; Lean checks them after
                // lifting and static specialization.
                self.block(body, None);
                self.scope.truncate(mark);
                self.scope.frame -= 1;
            }
            ExprKind::Invoke { callee, args } => {
                self.expr(callee, function, false);
                for arg in args {
                    self.expr(arg, function, false);
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
                } else if !self.scope.contains(name) && !self.functions.contains_key(name.as_str())
                {
                    if self.scope.enclosing(name) {
                        self.errors.push(diagnostic("E_CAPTURE", format!("independent lambda cannot capture `{name}`; pass it as an explicit parameter"), expr.span));
                        return;
                    }
                    if self.generics.contains_key(name.as_str()) {
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
                } else if self.scope.contains(callee) {
                    // Function-valued bindings are checked independently by Lean.
                } else if self.scope.enclosing(callee) {
                    self.errors.push(diagnostic("E_CAPTURE", format!("independent lambda cannot capture `{callee}`; pass it as an explicit parameter"), expr.span));
                } else if !self.generics.contains_key(callee.as_str())
                    && !BUILTINS.contains(&callee.as_str())
                {
                    let hint = if callee == "nat_to_int" {
                        "; help: nat_to_int is defined by the arithmetic standard library (include it with --lib or a package import); the builtin conversion is int(...)"
                    } else {
                        ""
                    };
                    self.errors.push(diagnostic("E_NAME", format!("unknown function `{callee}`; calls require a declared function, generic, or supported builtin{hint}"), expr.span));
                }
                for (i, arg) in args.iter().enumerate() {
                    self.expr(
                        arg,
                        function,
                        i == 0 && matches!(callee.as_str(), "Affine" | "Base"),
                    );
                }
            }
            ExprKind::Unary { operand, .. } => self.expr(operand, function, false),
            ExprKind::Binary { left, right, .. } => {
                self.expr(left, function, false);
                self.expr(right, function, false);
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition, function, false);
                self.block(then_branch, function);
                self.block(else_branch, function);
            }
            ExprKind::Block { body } => self.block(body, function),
            ExprKind::Pack { scheme, point } => {
                self.expr(scheme, function, false);
                self.expr(point, function, false);
            }
            ExprKind::IndexedPack {
                package,
                witness,
                fields,
            } => {
                self.ty(package, expr.span);
                self.expr(witness, function, false);
                for field in fields {
                    self.expr(field, function, false);
                }
            }
            ExprKind::Integer { .. } | ExprKind::Boolean { .. } | ExprKind::Unit => {}
        }
    }
}
