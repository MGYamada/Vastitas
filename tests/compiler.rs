//! End-to-end tests require `lake -d lean-kernel build vastitas-kernel` first.
mod common;
use common::{Scratch, assert_rejected, cli, kernel, success as assert_success};
use serde_json::{Value, json};
use std::fs;
use std::path::PathBuf;
use std::process::Output;

impl Scratch {
    fn new() -> Self {
        Self::empty("compiler")
    }
    fn source(&self, text: &str) -> PathBuf {
        let file = self.0.join("input file.vast");
        fs::write(&file, text).unwrap();
        file
    }
}

fn check(source: &str) -> Output {
    common::check(source, "input file.vast")
}
fn reject(source: &str, code: &str) -> String {
    common::reject(source, code, "input file.vast")
}
fn native(source: &str, expected: &str) {
    common::native(source, &[], expected, "input file.vast");
}
fn request(source: &str) -> Value {
    common::request(source, "forged.vast")
}

#[test]
fn native_pointed_object_survives_return_unpack_and_dependent_call() {
    native(include_str!("../examples/pointed.vast"), "42");
}

#[test]
fn native_smooth_objects_preserve_their_setting() {
    native(include_str!("../examples/smooth.vast"), "2");
}

#[test]
fn native_arbitrary_precision_and_forward_calls() {
    native(
        include_str!("../examples/arithmetic.vast"),
        "1234567890123456789012345678900",
    );
}

#[test]
fn native_nat_subtraction_and_unit() {
    native(
        "fn empty() -> Unit {} fn main() -> Int { let u: Unit = empty(); let n: Nat = 2; if n - 5 == 0 { -42 } else { 1 } }",
        "-42",
    );
}

#[test]
fn aliases_preserve_object_identity() {
    assert_success(&check(
        "fn main() -> Int { let X = Affine(QQ, 2); let Y = X; let p: Point<Y, Base(QQ)> = origin(X); let q = apply(id(Y), p); 0 }",
    ));
}

#[test]
fn equal_dimensions_do_not_identify_objects() {
    reject(
        "fn main() -> Int { let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let p: Point<Y, Base(QQ)> = origin(X); 0 }",
        "E_TYPE",
    );
}

#[test]
fn mixed_settings_and_wrong_test_objects_are_rejected() {
    reject(
        "fn main() -> Int { let X: Scheme = Affine(CInfReal, 2); 0 }",
        "E_TYPE",
    );
    reject(
        "fn main() -> Int { let X = Affine(QQ, 2); let S = Affine(QQ, 0); let p: Point<X, S> = origin(X); 0 }",
        "E_TYPE",
    );
    reject(
        "fn main() -> Int { let X = Affine(QQ, 2); let p: Point<X, Base(CInfReal)> = origin(X); 0 }",
        "E_BASE",
    );
}

#[test]
fn dependent_arguments_are_substituted() {
    reject(
        "fn keep(X: Scheme, p: Point<X, Base(QQ)>) -> Point<X, Base(QQ)> { p } fn main() -> Int { let A = Affine(QQ, 2); let B = Affine(QQ, 2); let p = keep(A, origin(B)); 0 }",
        "E_TYPE",
    );
    assert_success(&check(
        "fn keep(X: Scheme, p: Point<X, Base(QQ)>) -> Point<X, Base(QQ)> { p } fn main() -> Int { let A = Affine(QQ, 2); let p: Point<A, Base(QQ)> = keep(A, origin(A)); 0 }",
    ));
}

#[test]
fn mismatched_morphism_endpoints_are_rejected() {
    reject(
        "fn main() -> Int { let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let f = compose(id(X), id(Y)); 0 }",
        "E_ENDPOINT",
    );
    reject(
        "fn main() -> Int { let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let p = apply(id(X), origin(Y)); 0 }",
        "E_ENDPOINT",
    );
}

#[test]
fn package_cannot_lie_about_its_point_or_base() {
    reject(
        "fn make() -> Pointed<Scheme, QQ> { let X = Affine(QQ, 2); let Y = Affine(QQ, 2); pack { scheme: X, point: origin(Y) } }",
        "E_ENDPOINT",
    );
    reject(
        "fn make() -> Pointed<Scheme, CInfReal> { let X = Affine(QQ, 2); pack { scheme: X, point: origin(X) } }",
        "E_BASE",
    );
}

#[test]
fn unsealed_local_point_cannot_escape_a_block() {
    reject(
        "fn main() -> Int { let p = { let X = Affine(QQ, 2); origin(X) }; 0 }",
        "E_ESCAPE",
    );
}

#[test]
fn independent_openings_do_not_share_a_nominal_identity() {
    reject(
        "fn main() -> Int { let X = Affine(QQ, 2); let q = pack { scheme: X, point: origin(X) }; unpack q as { scheme: A, point: a }; unpack q as { scheme: B, point: b }; let p: Point<A, Base(QQ)> = b; 0 }",
        "E_TYPE",
    );
}

#[test]
fn scalar_coercions_and_geometry_equality_are_rejected() {
    reject("fn main() -> Int { let n: Nat = 1; n }", "E_TYPE");
    reject(
        "fn main() -> Int { let X = Affine(QQ, 1); if X == X { 1 } else { 0 } }",
        "E_OPERATOR",
    );
}

#[test]
fn library_check_does_not_require_an_entrypoint_but_build_does() {
    let source = "fn f(x: Int) -> Int { x + 1 }";
    assert_success(&check(source));
    assert_rejected(request(source), "E_MAIN");
}

#[test]
fn malformed_ir_version_type_binding_and_literal_are_rejected() {
    let original = request("fn main() -> Int { 1 }");
    let mut value = original.clone();
    value["version"] = json!(1);
    assert_rejected(value, "E_PROTOCOL");
    let mut value = original.clone();
    value["functions"][0]["return_type"] = json!({"kind":"named", "name":"Bool"});
    assert_rejected(value, "E_MAIN");
    let mut value = original.clone();
    value["functions"][0]["body"]["result"]["kind"] = json!("boolean");
    value["functions"][0]["body"]["result"]["value"] = json!(true);
    assert_rejected(value, "E_TYPE");
    let mut value = original.clone();
    value["functions"][0]["body"]["result"]["kind"] = json!("variable");
    value["functions"][0]["body"]["result"]["name"] = json!("forged");
    assert_rejected(value, "E_NAME");
    let mut value = original.clone();
    value["functions"][0]["body"]["result"]["value"] = json!("1); IO.println 99");
    assert_rejected(value, "E_LITERAL");
    let mut value = original;
    value["functions"][0]["body"]["result"]["kind"] = json!("unsupported_operation");
    assert_rejected(value, "E_PROTOCOL");
}

#[test]
fn backend_checks_forged_endpoint_annotations_and_recursion() {
    let mut value = request(
        "fn main() -> Int { let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let p: Point<X, Base(QQ)> = origin(X); 0 }",
    );
    value["functions"][0]["body"]["statements"][2]["annotation"]["target"]["name"] = json!("Y");
    assert_rejected(value, "E_TYPE");
    let mut value = request("fn main() -> Int { 1 }");
    value["functions"][0]["body"]["result"] = json!({"kind":"call", "callee":"main", "args":[], "span":{"start":0,"end":1,"line":1,"column":1}});
    assert_rejected(value, "E_RECURSION");
}

#[test]
fn object_branch_merges_preserve_only_a_shared_identity() {
    assert_success(&check(
        "fn main() -> Int { let X = Affine(QQ, 2); let Z = if true { X } else { X }; let p: Point<X, Base(QQ)> = origin(Z); 0 }",
    ));
    reject(
        "fn main() -> Int { let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let Z = if true { X } else { Y }; let p: Point<X, Base(QQ)> = origin(Z); 0 }",
        "E_TYPE",
    );
}

#[test]
fn local_morphisms_cannot_escape_and_unpack_requires_a_package() {
    let message = reject(
        "fn main() -> Int { let f = { let X = Affine(QQ, 1); id(X) }; 0 }",
        "E_ESCAPE",
    );
    assert!(!message.contains("return its object and point together with pack"));
    reject(
        "fn main() -> Int { unpack 1 as { scheme: X, point: p }; 0 }",
        "E_TYPE",
    );
}

#[test]
fn anonymous_outer_endpoints_remain_in_scope_for_nested_returns() {
    assert_success(&check(
        "fn main() -> Int { let p = origin(Affine(QQ, 2)); let q = { p }; let r = { q }; let f = id(Affine(CInfReal, 2)); let g = { f }; let h = { g }; 0 }",
    ));
    reject(
        "fn main() -> Int { let p = { origin(Affine(QQ, 2)) }; 0 }",
        "E_ESCAPE",
    );
    reject(
        "fn main() -> Int { let f = { id(Affine(CInfReal, 2)) }; 0 }",
        "E_ESCAPE",
    );
}

#[test]
fn native_base_objects_pack_and_unpack_in_both_settings() {
    native(
        "fn main() -> Int { let X = Base(QQ); let Y = Base(CInfReal); let ordinary = pack { scheme: X, point: origin(X) }; let smooth = pack { scheme: Y, point: origin(Y) }; unpack ordinary as { scheme: A, point: a }; unpack smooth as { scheme: B, point: b }; let p: Point<A, Base(QQ)> = apply(id(A), a); let q: Point<B, Base(CInfReal)> = apply(id(B), b); if dimension(A) == 0 && dimension(B) == 0 { 42 } else { -1 } }",
        "42",
    );
}

#[test]
fn pair_literal_arguments_explain_independent_inference_without_changing_it() {
    let header = "fn first(p: Pair<Nat>) -> Nat { pair_first(p) } ";
    let message = reject(
        &format!("{header} fn main() -> Int {{ int(first(pair(0, 1))) }}"),
        "E_TYPE",
    );
    assert!(
        message.contains("expected Pair<Nat>, found Pair<Int>"),
        "{message}"
    );
    assert!(
        message.contains("help: pair infers its operands independently"),
        "{message}"
    );
    assert!(message.contains("let a: Nat = 0"), "{message}");
    for value in ["pair(-1, 1)", "pair(x, x)"] {
        let message = reject(
            &format!("{header} fn bad(x: Int) -> Nat {{ first({value}) }}"),
            "E_TYPE",
        );
        assert!(
            !message.contains("bind and annotate Nat operands first"),
            "{message}"
        );
    }
    native(
        &format!(
            "{header} fn main() -> Int {{ let a: Nat = 0; let b: Nat = 1; int(first(pair(a, b))) }}"
        ),
        "0",
    );
}

#[test]
fn conditional_literal_typing_is_symmetric_and_branch_order_is_preserved() {
    native(
        "fn first(n: Nat, choice: Bool) -> Nat { let x = if choice { n } else { 1 }; x } fn second(n: Nat, choice: Bool) -> Nat { let x = if choice { 1 } else { n }; x } fn main() -> Int { if first(7, true) == 7 && first(7, false) == 1 && second(7, true) == 1 && second(7, false) == 7 { 42 } else { -1 } }",
        "42",
    );
    for branches in ["if true { -1 } else { n }", "if true { n } else { -1 }"] {
        reject(
            &format!("fn f(n: Nat) -> Nat {{ let result = {branches}; result }}"),
            "E_TYPE",
        );
    }
    assert_success(&check(
        "fn f(n: Nat) -> Nat { let result: Nat = if true { 1 } else { n }; result }",
    ));
}

#[test]
fn recursion_diagnostics_identify_the_cycle_not_its_caller() {
    let message = reject(
        "fn main() -> Int { a() }\nfn a() -> Int { b() }\nfn b() -> Int { a() }",
        "E_RECURSION",
    );
    assert!(message.contains("input file.vast:2:1:"), "{message}");
    assert!(message.replace('`', "").contains("a → b → a"), "{message}");
    assert!(!message.contains("`main`"), "{message}");

    let mut forged =
        request("fn main() -> Int { a() }\nfn a() -> Int { b() }\nfn b() -> Int { 0 }");
    let result = &mut forged["functions"][2]["body"]["result"];
    result["kind"] = json!("call");
    result["callee"] = json!("a");
    result["args"] = json!([]);
    let response = assert_rejected(forged, "E_RECURSION");
    let diagnostic = &response["diagnostics"][0];
    assert_eq!(diagnostic["span"]["line"], 2);
    assert_eq!(diagnostic["span"]["column"], 1);
    let message = diagnostic["message"].as_str().unwrap();
    assert!(message.contains("`a` → `b` → `a`"), "{message}");
    assert!(!message.contains("main"), "{message}");
}

#[test]
fn shared_and_repeated_dependencies_have_a_valid_native_order() {
    native(
        "fn main() -> Int { left() + right() + left() } fn left() -> Int { leaf() } fn right() -> Int { leaf() } fn leaf() -> Int { 14 }",
        "42",
    );
    let mut forged = request(
        "fn main() -> Int { 0 }\nfn unused_a() -> Int { unused_b() }\nfn unused_b() -> Int { 1 }",
    );
    let result = &mut forged["functions"][2]["body"]["result"];
    result["kind"] = json!("call");
    result["callee"] = json!("unused_a");
    result["args"] = json!([]);
    assert_rejected(forged, "E_RECURSION");
}

#[test]
fn kernel_checks_twenty_thousand_functions_within_the_watchdog() {
    use std::fmt::Write;

    const COUNT: usize = 20_000;
    for (shared, reversed, lambda) in [
        (false, false, false),
        (false, false, true),
        (false, true, true),
        (true, false, true),
    ] {
        let mut declarations = Vec::new();
        for i in 0..COUNT - 1 {
            let callee = if shared { COUNT - 1 } else { i + 1 };
            declarations.push(format!("fn f{i}(x: Int) -> Int {{ f{callee}(x) }}"));
        }
        declarations.push(format!("fn f{}(x: Int) -> Int {{ x }}", COUNT - 1));
        if reversed {
            declarations.reverse();
        }
        let mut source = declarations.join("\n");
        if lambda {
            writeln!(
                source,
                "\nfn main() -> Int {{ let g = fn(x: Int) -> Int {{ x }}; g(f0(42)) }}"
            )
            .unwrap();
        } else {
            writeln!(source, "\nfn main() -> Int {{ f0(42) }}").unwrap();
        }
        let response = kernel(request(&source), "check");
        assert_eq!(
            response["ok"], true,
            "shared={shared}, reversed={reversed}, lambda={lambda}: {response}"
        );
    }
}

#[test]
fn native_long_straight_line_blocks_match_checker_limits() {
    use std::fmt::Write;

    let mut source = String::from("fn main() -> Int {\nlet x0 = 1;\n");
    for i in 1..4090 {
        writeln!(source, "let x{i} = x{} + 1;", i - 1).unwrap();
    }
    source.push_str("x4089\n}");
    assert_success(&check(&source));
    native(&source, "4090");
}

fn unpack_budget_source(extra_let: bool) -> String {
    use std::fmt::Write;

    let mut source = String::from(
        "fn main() -> Int {\nlet X = Affine(QQ, 2);\nlet package = pack { scheme: X, point: origin(X) };\n",
    );
    // 2 setup lets + 1,364 unpack expansions * 3 + 2 padding lets = 4,096.
    for i in 0..1364 {
        writeln!(source, "unpack package as {{ scheme: X{i}, point: p{i} }};").unwrap();
    }
    source.push_str("let first = 1;\nlet second = 2;\n");
    if extra_let {
        source.push_str("let excess = 0;\n");
    }
    source.push_str("if dimension(X1363) == 2 { second } else { first }\n}");
    source
}

#[test]
fn native_unpack_expansion_at_the_generated_let_budget() {
    let source = unpack_budget_source(false);
    assert_success(&check(&source));
    native(&source, "2");
}

#[test]
fn generated_let_budget_is_shared_by_check_and_build() {
    let source = unpack_budget_source(true);
    let message = reject(&source, "E_LIMIT");
    assert!(message.contains("4096"), "{message}");
    let scratch = Scratch::new();
    let output = scratch.0.join("previous output");
    fs::write(&output, "previous artifact").unwrap();
    let result = cli()
        .arg("build")
        .arg(scratch.source(&source))
        .arg("-o")
        .arg(&output)
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(1));
    let message = String::from_utf8_lossy(&result.stderr);
    assert!(message.contains(": E_LIMIT: "), "{message}");
    assert!(message.contains("4096"), "{message}");
    assert_eq!(fs::read_to_string(output).unwrap(), "previous artifact");
}

#[test]
fn argument_fuel_errors_report_the_library_call_site() {
    use std::fmt::Write;

    let scratch = Scratch::new();
    let source = scratch.source("fn main() -> Int { 0 }");
    let library = scratch.0.join("many arguments.vast");
    let mut body = String::from("fn target() -> Int { 0 }\nfn helper() -> Int {\n");
    // Statements and arguments share the fuel budget. Exhaust it immediately
    // before checking an empty argument list; many nonempty arguments instead
    // fail inside the last argument's expression, which already has its span.
    for i in 0..4092 {
        writeln!(body, "    let x{i} = 0;").unwrap();
    }
    body.push_str("    target()\n}");
    fs::write(&library, body).unwrap();
    let result = cli()
        .arg("check")
        .arg(&source)
        .arg("--lib")
        .arg(&library)
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(1));
    let message = String::from_utf8_lossy(&result.stderr);
    assert!(
        message.contains(&format!("{}:4095:5: E_LIMIT:", library.display())),
        "{message}"
    );
    assert!(message.contains("too many function arguments"), "{message}");
    assert!(!message.contains(&format!("{}:1:1:", source.display())));
}

#[test]
fn failed_compilation_preserves_existing_output() {
    let scratch = Scratch::new();
    let file = scratch.source("fn main() -> Int { true }");
    let output = scratch.0.join("existing");
    fs::write(&output, b"previous artifact").unwrap();
    let result = cli()
        .arg("build")
        .arg(file)
        .arg("-o")
        .arg(&output)
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert_eq!(fs::read(output).unwrap(), b"previous artifact");
}

#[test]
fn backend_is_required_and_failure_has_no_frontend_fallback() {
    let scratch = Scratch::new();
    let result = cli()
        .arg("check")
        .arg(scratch.source("fn main() -> Int { 1 }"))
        .env("VASTITAS_KERNEL", scratch.0.join("missing-kernel"))
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("E_BACKEND"));
}

#[test]
fn excessive_source_nesting_is_a_diagnostic_not_a_process_abort() {
    let source = format!(
        "fn main() -> Int {{ {}1{} }}",
        "(".repeat(512),
        ")".repeat(512)
    );
    let result = check(&source);
    assert_eq!(result.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&result.stderr).contains("E_LIMIT"));
}

#[test]
fn native_toolchain_failure_preserves_existing_output() {
    use std::os::unix::fs::PermissionsExt;
    let scratch = Scratch::new();
    let source = scratch.source("fn main() -> Int { 42 }");
    let output = scratch.0.join("existing");
    fs::write(&output, b"previous artifact").unwrap();
    let lake = scratch.0.join("lake");
    fs::write(
        &lake,
        "#!/bin/sh\necho 'test toolchain failure' >&2\nexit 12\n",
    )
    .unwrap();
    fs::set_permissions(&lake, fs::Permissions::from_mode(0o755)).unwrap();
    let paths = std::iter::once(scratch.0.clone()).chain(
        std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default()).collect::<Vec<_>>(),
    );
    let result = cli()
        .arg("build")
        .arg(source)
        .arg("-o")
        .arg(&output)
        .env("PATH", std::env::join_paths(paths).unwrap())
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("E_BUILD"));
    assert_eq!(fs::read(output).unwrap(), b"previous artifact");
}
