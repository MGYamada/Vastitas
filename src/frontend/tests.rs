use super::*;

#[test]
fn resource_realization_calls_keep_unresolved_paths_representation_and_destination() {
    let source = "use monad::float as ops;
resource fn main() -> Int {
    let r = ops::realize::<F64<RR>>(model::Line, model::Line::standard_chart);
    let e = ops::interpret(model::idL, r, NativeFast);
    let p = makePoint(r, input);
    let q = makePoint(r, output);
    execute(e, p) -> q;
    value { 0 }
}";
    let parsed = parse_module_source(
        SourceInput {
            source,
            file: "realization.vast",
            offset: 0,
        },
        vec![],
        true,
        None,
    )
    .unwrap();
    let body = &parsed.modules[0].resource_functions[0].declaration.body;
    let wire = serde_json::to_value(body).unwrap();
    assert_eq!(wire[0]["kind"], "realization");
    assert_eq!(wire[0]["representation"], "real64");
    assert_eq!(
        wire[0]["callee"]["path"],
        serde_json::json!(["ops", "realize"])
    );
    assert_eq!(
        wire[0]["arguments"][1]["path"],
        serde_json::json!(["model", "Line", "standard_chart"])
    );
    assert_eq!(wire[0]["result"], "r");
    assert_eq!(wire[0]["into"], false);
    assert_eq!(
        wire[1]["arguments"][2]["path"],
        serde_json::json!(["NativeFast"])
    );
    assert_eq!(wire[2]["callee"]["path"], serde_json::json!(["makePoint"]));
    assert_eq!(wire[4]["result"], "q");
    assert_eq!(wire[4]["into"], true);
    assert!(wire[4]["representation"].is_null());
    let crate::storage::source::Statement::Realization {
        callee,
        arguments,
        span,
        ..
    } = &body[0]
    else {
        panic!("expected a realization call")
    };
    assert_eq!(&source[callee.span.start..callee.span.end], "ops::realize");
    assert_eq!(
        &source[arguments[1].span.start..arguments[1].span.end],
        "model::Line::standard_chart"
    );
    assert!(source[span.start..span.end].ends_with("standard_chart);"));
    assert_eq!(
        serde_json::from_value::<Vec<crate::storage::source::Statement>>(wire).unwrap(),
        *body
    );
}

#[test]
fn resource_realization_grammar_has_finite_representations_and_bounded_arguments() {
    for (spelling, tag) in [
        ("F32<RR>", "real32"),
        ("F32<CC>", "complex32"),
        ("F64<CC>", "complex64"),
        ("F64<RR>", "real64"),
    ] {
        let source = format!(
            "resource fn test() -> Unit {{ let x = aliased::<{spelling}>(X, X::standard_chart); value {{ () }} }}"
        );
        let parsed = parse_module_source(
            SourceInput {
                source: &source,
                file: "r.vast",
                offset: 0,
            },
            vec![],
            true,
            None,
        )
        .unwrap();
        let statement = &parsed.modules[0].resource_functions[0].declaration.body[0];
        assert_eq!(
            serde_json::to_value(statement).unwrap()["representation"],
            tag
        );
    }
    for (call, code) in [
        ("let r = a::<F16<RR>>(X, chart);", "E_TYPE"),
        ("let r = a::<F64<QQ>>(X, chart);", "E_TYPE"),
        ("let r = a(X, Y, Z, W);", "E_ARITY"),
        ("ops::run(e,p) -> (q);", "E_PARSE"),
    ] {
        let source = format!("resource fn test() -> Unit {{ {call} value {{ () }} }}");
        assert_eq!(
            package_functions(&source).unwrap_err().code,
            code,
            "{source}"
        );
    }
}

fn package_functions(source: &str) -> Result<Vec<crate::namespace::Public<Function>>, Diagnostic> {
    let parsed = parse_module_source(
        SourceInput {
            source,
            file: "finite.vast",
            offset: 0,
        },
        Vec::new(),
        true,
        None,
    )?;
    Ok(parsed.modules.into_iter().next().unwrap().functions)
}

#[test]
fn finite_function_binders_and_calls_preserve_paths_and_source_spans() {
    let source =
        "pub fn compose<C: lib::Small, X: Obj<C>, Y: Obj<C>>(f: Hom<C,X,Y>) -> Hom<C,X,Y> { f }
fn run(x: Hom<Other,Nodes::lo,Nodes::hi>) -> Hom<Other,Nodes::lo,Nodes::hi> {
    package::compose::<Other,Nodes::lo,Nodes::hi,>(x)
}";
    let functions = package_functions(source).unwrap();
    let template = &functions[0].declaration;
    let [
        StaticBinder::Category { name, schema, span },
        StaticBinder::Object {
            name: x,
            category,
            span: object_span,
        },
        _,
    ] = template.finite_binders.as_slice()
    else {
        panic!("expected category and object binders")
    };
    assert_eq!(name, "C");
    assert_eq!(schema.path, ["lib", "Small"]);
    assert_eq!(&source[span.start..span.end], "C: lib::Small");
    assert_eq!(&source[schema.span.start..schema.span.end], "lib::Small");
    assert_eq!(x, "X");
    assert_eq!(category, "C");
    assert_eq!(&source[object_span.start..object_span.end], "X: Obj<C>");
    let template = serde_json::to_value(template).unwrap();
    assert_eq!(template["finite_binders"][0]["kind"], "category");
    assert_eq!(template["finite_binders"][1]["kind"], "object");
    assert_eq!(template["params"][0]["ty"]["kind"], "finite_hom");
    let caller = &functions[1].declaration;
    let ExprKind::FiniteCall {
        callee,
        indices,
        args,
    } = &caller.body.result.kind
    else {
        panic!("expected an explicit finite call")
    };
    assert_eq!(callee.path, ["package", "compose"]);
    assert_eq!(
        &source[callee.span.start..callee.span.end],
        "package::compose"
    );
    assert_eq!(indices.len(), 3);
    assert_eq!(
        indices
            .iter()
            .map(|p| &source[p.span.start..p.span.end])
            .collect::<Vec<_>>(),
        ["Other", "Nodes::lo", "Nodes::hi"]
    );
    assert!(matches!(&args[..], [Expr { kind: ExprKind::Variable { name }, .. }] if name == "x"));
    let wire = serde_json::to_value(caller).unwrap();
    assert!(wire.get("finite_binders").is_none());
    assert_eq!(wire["body"]["result"]["kind"], "finite_call");
    assert_eq!(serde_json::from_value::<Function>(wire).unwrap(), *caller);
}

#[test]
fn finite_monad_binders_and_endpoint_applications_retain_their_spelling_and_span() {
    let source = "fn mapped<M: witness::Structure, X: Obj<M::category>>(\n\
        f: Hom<M::category, X, M::T<X>>\n\
    ) -> Hom<M::category, M::T<X>, M::T<M::T<X>>> { finite::lookup::<M::arrows>(f) }";
    let functions = package_functions(source).unwrap();
    let template = &functions[0].declaration;
    let wire = serde_json::to_value(template).unwrap();
    assert_eq!(wire["finite_binders"][1]["kind"], "monad_object");
    assert_eq!(wire["finite_binders"][1]["monad"], "M");
    let StaticBinder::MonadObject { span, .. } = &template.finite_binders[1] else {
        panic!("expected a Monad category object binder");
    };
    assert_eq!(&source[span.start..span.end], "X: Obj<M::category>");
    let Type::FiniteHom {
        category,
        source: x,
        target,
    } = &template.return_type
    else {
        panic!("expected a Hom");
    };
    assert_eq!(category.path, ["M", "category"]);
    assert_eq!(x.path, ["M", "T<>", "X"]);
    assert_eq!(target.path, ["M", "T<>", "M", "T<>", "X"]);
    assert_eq!(&source[target.span.start..target.span.end], "M::T<M::T<X>>");
    assert_eq!(serde_json::from_value::<Function>(wire).unwrap(), *template);
    let concrete = source.replace("M::T<M::T<X>>", "M::T::X");
    let functions = package_functions(&concrete).unwrap();
    let Type::FiniteHom { target, .. } = &functions[0].declaration.return_type else {
        panic!("expected a Hom");
    };
    assert_eq!(target.path, ["M", "T", "X"]);
    assert_eq!(
        package_functions(&source.replace("M::T<X>", "M::F<X>"))
            .unwrap_err()
            .code,
        "E_TYPE"
    );
    let depth = MAX_PARSE_NESTING + 1;
    let nested = format!("{}X{}", "M::T<".repeat(depth), ">".repeat(depth));
    assert_eq!(
        package_functions(&source.replace("M::T<M::T<X>>", &nested))
            .unwrap_err()
            .code,
        "E_LIMIT"
    );
}

#[test]
fn derived_kleisli_declarations_preserve_the_selected_paths_and_spans() {
    let offset = 91;
    for (constructor, field) in [
        ("finite_kleisli", "kleisli"),
        ("finite_kleisli_triple", "kleisli_triple"),
    ] {
        let source = format!(
            "pub indexed schema Shape = {constructor}(algebra::Monad);\n\
             indexed instance Chosen : api::Shape = {constructor}(models::Closure);"
        );
        let parsed = parse_module_source(
            SourceInput {
                source: &source,
                file: "kleisli.vast",
                offset,
            },
            vec![],
            true,
            None,
        )
        .unwrap();
        let decls = &parsed.modules[0].indexed_declarations;
        assert_eq!(decls.len(), 2);
        let schema = serde_json::to_value(&decls[0]).unwrap();
        let instance = serde_json::to_value(&decls[1]).unwrap();
        assert_eq!(schema["kind"], "schema");
        assert_eq!(schema["public"], true);
        assert_eq!(schema["schema_kind"], constructor);
        assert_eq!(instance["kind"], "instance");
        assert_eq!(instance["public"], false);
        assert_eq!(instance[field].as_object().unwrap().len(), 1);
        for (json_path, spelling) in [
            (&schema["monad_schema"], "algebra::Monad"),
            (&instance["schema"], "api::Shape"),
            (&instance[field]["monad"], "models::Closure"),
        ] {
            let path: TypePath = serde_json::from_value(json_path.clone()).unwrap();
            assert_eq!(path.path, spelling.split("::").collect::<Vec<_>>());
            assert_eq!(path.span.start, offset + source.find(spelling).unwrap());
            assert_eq!(path.span.end, path.span.start + spelling.len());
        }
        for declaration in decls {
            let wire = serde_json::to_value(&declaration.declaration).unwrap();
            assert_eq!(
                serde_json::from_value::<crate::indexed::Declaration>(wire).unwrap(),
                declaration.declaration
            );
        }
    }
}

#[test]
fn only_derived_schemas_and_instances_take_one_monad_path() {
    for constructor in ["finite_kleisli", "finite_kleisli_triple"] {
        for prefix in ["indexed schema S = ", "indexed instance K : S = "] {
            for args in ["", "()", "(A, B)", "(A,)", "(A<B>)"] {
                let source = format!("{prefix}{constructor}{args};");
                assert_eq!(
                    package_functions(&source).unwrap_err().code,
                    "E_PARSE",
                    "{source}"
                );
            }
        }
    }
    for constructor in [
        "finite_category",
        "finite_functor",
        "finite_nat_trans",
        "finite_monad",
    ] {
        let source = format!("indexed schema S = {constructor};");
        let parsed = parse_module_source(
            SourceInput {
                source: &source,
                file: "schema.vast",
                offset: 0,
            },
            vec![],
            true,
            None,
        )
        .unwrap();
        let schema = &parsed.modules[0].indexed_declarations[0].declaration;
        assert_eq!(
            serde_json::to_value(schema).unwrap(),
            serde_json::json!({
                "name": "S", "kind": "schema", "schema_kind": constructor, "span": schema.span,
            })
        );
        let source = format!("indexed schema S = {constructor}(A);");
        assert_eq!(
            package_functions(&source).unwrap_err().code,
            "E_PARSE",
            "{source}"
        );
    }
}

#[test]
fn finite_function_grammar_rejects_general_parameters_and_unsupported_declarations() {
    for (source, code) in [
        ("fn f<T: Type>(x: Int) -> Int { x }", "E_TYPE"),
        ("fn f<C: Small>(x: Int) -> Int;", "E_TYPE"),
        ("fn f<C: Small>(x: Bool) requires() -> Bool { x }", "E_TYPE"),
        ("fn f<>(x: Int) -> Int { x }", "E_PARSE"),
        ("fn f<C: Small>(x) domain((Int));", "E_TYPE"),
        (
            "fn f<C: Small>(x: Int) -> Int { x } fn f(x: Int) -> Int { x }",
            "E_TYPE",
        ),
        ("fn f(x: Int) -> Int { f::<1>(x) }", "E_PARSE"),
        ("fn compose(x: Int) -> Int { x }", "E_RESERVED"),
    ] {
        assert_eq!(
            package_functions(source).unwrap_err().code,
            code,
            "{source}"
        );
    }
}

#[test]
fn inferred_family_keys_are_left_to_the_kernel() {
    let source = "fn convert(x: Number) -> Int { 0 }
        fn convert(x: Nat) -> Int { int(x) }
        fn convert(x: Number) -> Int;
        fn main() -> Int { let alias = convert; alias(42) }";
    let module = parse(source, "inferred.vast").unwrap();
    assert_eq!(module.generics.len(), 1);
    assert_eq!(module.generics[0].domain, None);
    assert_eq!(module.methods.len(), 2);
    assert_eq!(module.abstract_methods[0].domain[0][0].path, ["Number"]);
    let wire = serde_json::to_value(module).unwrap();
    assert_eq!(
        wire["generics"][0].get("domain"),
        Some(&serde_json::Value::Null)
    );
}

#[test]
fn rejects_retired_family_spelling_at_its_declaration() {
    for source in [
        "generic f(x) { domain (Int); }",
        "method f(x: Int) -> Int { x }",
        "abstract method f(x: Int) -> Int { domain (Int); }",
    ] {
        let error = parse(source, "old.vast").unwrap_err().remove(0);
        assert_eq!(error.code, "E_PARSE");
        assert_eq!(error.span.start, 0);
        assert!(error.message.contains("edition 2026 uses `fn`"));
    }
}

#[test]
fn method_result_diagnostics_describe_the_result_contract() {
    for result in ["Any", "Number", "Point<X, Base(QQ)>", "Fn<Int, Int>"] {
        let source = format!("fn f(x) domain((Int)); fn f(x: Int) -> {result} {{ 0 }}");
        let errors = parse(&source, "result.vast").unwrap_err();
        assert_eq!(errors[0].code, "E_TYPE");
        assert_eq!(
            errors[0].message,
            "method results require Nat, Int, Bool, Unit, Pair<Nat>, or Pair<Int>"
        );
    }
}

#[test]
fn parses_and_serializes_generic_families_without_selecting_methods() {
    let source = "fn choose(x: Number) -> Int requires (HasOrder, HasEq) { 1 }
fn choose(x) domain((Int), (Nat));
fn choose(x: Any) requires (HasEq) -> Int { 2 }
fn main() -> Int { choose(10) }";
    let module = parse(source, "dispatch.vast").unwrap();
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
    assert_eq!(encoded["generics"][0]["domain"][0][0]["name"], "Int");
    assert_eq!(encoded["methods"][0]["params"][0]["ty"]["name"], "Number");
    assert_eq!(encoded["methods"][1]["return_type"]["name"], "Int");
    let decoded: Module = serde_json::from_value(encoded).unwrap();
    assert_eq!(decoded, module);
}

#[test]
fn separate_sources_preserve_all_dispatch_declarations_and_spans() {
    let application = "fn main() -> Int { choose(1) }";
    let family = "// family\nfn choose(value) domain((Int));";
    let implementation = "// implementation\nfn choose(x: Int) -> Int { helper(x) }";
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
        100 + family.find("fn").unwrap()
    );
    assert_eq!(module.generics[0].span.line, 2);
    assert_eq!(
        module.generics[0].params[0].span.start,
        100 + family.find("value").unwrap()
    );
    assert_eq!(
        module.methods[0].span.start,
        200 + implementation.find("fn").unwrap()
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
        "fn empty(x,) domain();
fn constant() domain((),);
fn constant() -> Int requires () { 42 }",
        "empty.vast",
    )
    .unwrap();
    assert!(module.generics[0].domain == Some(vec![]));
    assert_eq!(module.generics[1].domain, Some(vec![vec![]]));
    assert!(module.methods[0].params.is_empty());
    assert!(module.methods[0].requires.is_empty());
}

#[test]
fn dispatch_selectors_are_not_ordinary_value_types() {
    for source in [
        "fn f(x) domain((Number));",
        "fn f(x) domain((Scheme));",
        "fn f(x) domain((Int)); fn f(x: Scheme) -> Int { 0 }",
        "fn f(x) domain((Int)); fn f(x: Int) -> Any { x }",
        "fn f(x) domain((Int)); fn f(x: Int) -> Pointed<Scheme, QQ> { x }",
    ] {
        assert_eq!(parse(source, "types.vast").unwrap_err()[0].code, "E_TYPE");
    }
    for source in [
        "fn f(x: Any) -> Int { let y: Any = x; 0 }",
        "fn f(x) domain((Int)); fn f(x: Number) -> Int { let y: Number = x; 0 }",
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
        ("fn f(x) domain(); fn f(x) domain();", "E_DUPLICATE"),
        ("fn f() -> Int { 0 } fn f(x: Int) -> Int { x }", "E_ARITY"),
        ("fn missing(x: Int) -> Int { undeclared }", "E_NAME"),
        ("fn main() domain(());", "E_MAIN"),
        ("fn f(x, x) domain();", "E_DUPLICATE"),
        (
            "fn f(x) domain(); fn g() -> Int { let f = 1; f }",
            "E_SHADOW",
        ),
        (
            "fn f(x) domain((Int)); fn f(f: Int) -> Int { f }",
            "E_SHADOW",
        ),
        (
            "fn f(x) domain((Int)); fn f(x: Int) -> Int { hidden }",
            "E_NAME",
        ),
        (
            "fn f(x) domain((Int)); fn f(x: Int) -> Int { let x = 1; x }",
            "E_DUPLICATE",
        ),
        (
            "fn f(x) domain((Int)); fn f(x: Int) -> Int { x } fn f(y: Nat) -> Int { x }",
            "E_NAME",
        ),
    ] {
        let errors = parse(source, "names.vast").unwrap_err();
        assert_eq!(errors[0].code, code, "{source}");
    }
    let invalid_method = "\nfn f(x: Int) -> Int { unknown }";
    let errors = parse_sources(&[
        SourceInput {
            source: "fn f(x) domain((Int));",
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
        "fn choose(x) domain((Int), (Bool));
fn choose(x: Int) -> Int { choose(true) }
fn choose(x: Bool) -> Int { 1 }
fn main() -> Int { choose(0) }",
        "instances.vast",
    )
    .unwrap();
    assert_eq!(module.methods.len(), 2);
    // The frontend also keeps genuinely cyclic generic calls intact; Lean
    // must reject the eventual cycle after independently selecting targets.
    parse(
        "fn f(x) domain((Int)); fn f(x: Int) -> Int { f(x) }",
        "cycle.vast",
    )
    .unwrap();
    let module = parse(
        "fn f(x) domain((Int)); fn f(x: Int) -> Int requires (HasMetric) { 0 }",
        "capability.vast",
    )
    .unwrap();
    assert_eq!(module.methods[0].requires, ["HasMetric"]);
}

#[test]
fn rejects_duplicate_requires_and_compiler_private_names() {
    let errors = parse(
        "fn f(x) domain((Int)); fn f(x: Int) requires () -> Int requires () { 0 }",
        "requires.vast",
    )
    .unwrap_err();
    assert_eq!(errors[0].code, "E_PARSE");
    assert!(errors[0].message.contains("only one `requires`"));
    for source in [
        "fn __vastitas_internal() -> Int { 0 }",
        "fn __vastitas_internal(x) domain();",
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
    let errors = parse("fn a() -> Int { b() } fn b() -> Int { a() }", "cycle.vast").unwrap_err();
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
fn unsupported_line_breaks_are_rejected_even_inside_comments_and_paths() {
    for separator in [
        '\r', '\u{b}', '\u{c}', '\u{1c}', '\u{1d}', '\u{1e}', '\u{85}', '\u{2028}', '\u{2029}',
    ] {
        for prefix in ["", "// 日本語", "\"path"] {
            let source = format!("\n{prefix}{separator}hidden");
            let error = Lexer::new(&source).tokenize().unwrap_err();
            let start = 1 + prefix.len();
            assert_eq!(error.code, "E_LEX");
            assert!(error.message.contains("use LF or CRLF"));
            assert_eq!(
                (error.span.start, error.span.end),
                (start, start + separator.len_utf8())
            );
            assert_eq!(
                (error.span.line, error.span.column),
                (2, 1 + prefix.chars().count())
            );
        }
    }
    let source = "// 日本語\r\nfn main() -> Int { missing }\r\n";
    let error = parse(source, "crlf.vast").unwrap_err().remove(0);
    assert_eq!(error.code, "E_NAME");
    assert_eq!((error.span.line, error.span.column), (2, 20));
    assert_eq!(&source[error.span.start..error.span.end], "missing");
}

#[test]
fn unsupported_integer_spellings_and_lowercase_function_types_are_explained() {
    for literal in ["1_000", "0x10", "0b10", "2u8"] {
        let source = format!("fn main() -> Int {{ {literal} }}");
        let error = parse(&source, "literal.vast").unwrap_err().remove(0);
        assert_eq!(error.code, "E_LEX");
        assert!(error.message.contains("decimal digits"));
        assert_eq!(&source[error.span.start..error.span.end], literal);
    }
    let source = "fn f(g: fn(Int) -> Int) -> Int { 0 }";
    let error = parse(source, "function-type.vast").unwrap_err().remove(0);
    assert!(error.message.contains("Fn<Input, Output>"));
    assert_eq!(&source[error.span.start..error.span.end], "fn");
}

#[test]
fn shared_type_and_expression_nesting_budget_is_named() {
    for source in [
        format!(
            "fn main() -> Int {{ {}0{} }}",
            "(".repeat(64),
            ")".repeat(64)
        ),
        format!(
            "fn f(x: {}Int{}) -> Int {{ 0 }}",
            "Fn<Int, ".repeat(64),
            ">".repeat(64)
        ),
    ] {
        let error = parse(&source, "nesting.vast").unwrap_err().remove(0);
        assert_eq!(error.code, "E_LIMIT");
        assert!(error.message.contains("combined type/expression nesting"));
    }
}

#[test]
fn builtin_names_and_missing_library_conversion_are_explained() {
    for (name, reason) in [
        ("compose", "geometry"),
        ("int", "Nat-to-Int"),
        ("pair", "Pair"),
    ] {
        for source in [
            format!("fn {name}() -> Int {{ 0 }}"),
            format!("fn main() -> Int {{ let {name}: Int = 0; 0 }}"),
        ] {
            let error = parse(&source, "builtin.vast").unwrap_err().remove(0);
            assert_eq!(error.code, "E_RESERVED");
            assert!(error.message.contains("builtin") && error.message.contains(reason));
        }
    }
    let error = parse("fn main() -> Int { nat_to_int(1) }", "conversion.vast")
        .unwrap_err()
        .remove(0);
    assert_eq!(error.code, "E_NAME");
    assert!(
        error.message.contains("arithmetic standard library") && error.message.contains("int(...)")
    );
    parse(
        "fn nat_to_int(x: Nat) -> Int { int(x) } fn main() -> Int { nat_to_int(1) }",
        "declared.vast",
    )
    .unwrap();
}

/// #778: the operation is `dim`, reserved like the other six; `dimension`
/// is an ordinary name, and a call of it that names nothing explains both.
#[test]
fn dim_is_the_operation_and_dimension_an_ordinary_name() {
    parse(
        "fn main() -> Int { let X = Affine(QQ, 2); int(dim(X)) }",
        "dim.vast",
    )
    .unwrap();
    for source in [
        "fn dim() -> Int { 0 }",
        "fn main() -> Int { let dim: Int = 0; 0 }",
        "fn f(dim: Int) -> Int { dim }",
    ] {
        let error = parse(source, "dim.vast").unwrap_err().remove(0);
        assert_eq!(error.code, "E_RESERVED", "{source}");
        assert!(
            error
                .message
                .contains("`dim` is reserved for builtin geometry operations")
        );
    }
    parse(
        "fn dimension(n: Nat) -> Nat { n } fn main() -> Int { int(dimension(2)) }",
        "dimension.vast",
    )
    .unwrap();
    parse(
        "fn f(dimension: Int) -> Int { dimension } fn main() -> Int { f(1) }",
        "dimension.vast",
    )
    .unwrap();
    let error = parse(
        "fn main() -> Int { let X = Affine(QQ, 2); int(dimension(X)) }",
        "dimension.vast",
    )
    .unwrap_err()
    .remove(0);
    assert_eq!(error.code, "E_NAME");
    assert!(
        error.message.starts_with("unknown function `dimension`")
            && error.message.contains(
                "note: the dimension of a vector or affine space is `dim(…)`, and physical dimensions are `nature::dimension`"
            ),
        "{}",
        error.message
    );
}

#[test]
fn indexed_type_closers_can_touch_assignment() {
    let source = "fn f(X: Object<D,M>) -> Int {
    let x: Object<D,M>= X;
    let y: Foo<X>= make(X);
    if 3 >= 2 { 1 } else { 0 }
}";
    let parsed = parse_module_source(
        SourceInput {
            source,
            file: "indexed.vast",
            offset: 0,
        },
        vec![],
        true,
        None,
    )
    .unwrap();
    let function = &parsed.modules[0].functions[0].declaration;
    assert_eq!(function.body.statements.len(), 2);
    let ExprKind::If { condition, .. } = &function.body.result.kind else {
        panic!("expected conditional");
    };
    assert!(matches!(&condition.kind, ExprKind::Binary { op, .. } if op == ">="));
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

    let input = SourceInput {
        source: ">=",
        file: "type-close.vast",
        offset: 0,
    };
    let mut parser = Parser::from_source(&input, false).unwrap();
    let token_count = parser.tokens.len();
    let close = parser.type_close().unwrap();
    assert_eq!(parser.previous().span, close.span);
    assert_eq!(parser.tokens.len(), token_count);
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
        ("n /= 2", "/=", "division assignment"),
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
            if body.starts_with("let ") && word != "return" {
                assert_eq!(errors[0].code, "E_RESERVED");
                assert!(errors[0].message.contains("reserved"));
            } else {
                assert_eq!(errors[0].code, "E_UNSUPPORTED");
                assert!(errors[0].message.contains(explanation));
            }
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
        "fn f() -> Int { 1 / }",
    ] {
        let result = parse(source, "broken.vast");
        if !source.is_empty() {
            assert!(result.is_err(), "accepted malformed source {source:?}");
        }
    }
}

/// The strict keywords are one list on each side: `KEYWORDS` here and the
/// kernel's `strictKeywords` (`lean-kernel/VastitasKernel/Keywords.lean`),
/// with which its audit of a spectrum's fiber coordinate rejects a strict
/// keyword as the source grammar does (#831). The two lists name the same
/// words.
#[test]
fn the_strict_keywords_are_the_kernels() {
    let kernel = include_str!("../../lean-kernel/VastitasKernel/Keywords.lean");
    let (_, list) = kernel
        .split_once("def strictKeywords : List String :=")
        .expect("the kernel defines strictKeywords");
    let list = &list[..list.find(']').expect("a list literal")];
    let mut kernel: Vec<&str> = list.split('"').skip(1).step_by(2).collect();
    let mut frontend = KEYWORDS.to_vec();
    kernel.sort_unstable();
    frontend.sort_unstable();
    assert_eq!(kernel, frontend);
    assert_eq!(frontend.len(), 21);
}
