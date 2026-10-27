//! Stage 1b function values are independently checked and specialized by Lean.
mod common;
use common::{Scratch, cli, success};
use serde_json::{Value, json};
use std::fs;
use std::path::PathBuf;
use std::process::Output;

impl Scratch {
    fn new() -> Self {
        Self::empty("functions")
    }

    fn source(&self, source: &str) -> PathBuf {
        let path = self.0.join("function input.vast");
        fs::write(&path, source).unwrap();
        path
    }
}

fn check(source: &str) -> Output {
    common::check(source, "function input.vast")
}

fn reject(source: &str, code: &str) -> String {
    common::reject(source, code, "function input.vast")
}

fn native(source: &str, libraries: &[PathBuf], expected: &str) {
    common::native(source, libraries, expected, "function input.vast");
}

fn request(source: &str) -> Value {
    common::request(source, "forged-dispatch.vast")
}

fn kernel(request: Value) -> Value {
    common::kernel(request, "emit")
}

fn assert_rejected(request: Value, code: &str) {
    let response = common::assert_rejected(request, code);
    assert_eq!(response["version"], 2, "{response}");
}

#[test]
fn independent_function_budgets_do_not_depend_on_order_or_unused_lambdas() {
    let mut functions = vec!["fn main() -> Int { f0() }".to_owned()];
    for i in 0..1499 {
        functions.push(format!("fn f{i}() -> Int {{ f{}() }}", i + 1));
    }
    functions.push("fn f1499() -> Int { 42 }".to_owned());
    for reversed in [false, true] {
        if reversed {
            functions.reverse();
        }
        for lambda in [
            "",
            "\nfn unused() -> Int { let g = fn(x: Int) -> Int { x }; g(1) }",
        ] {
            success(&check(&(functions.join("\n") + lambda)));
        }
    }
    let body = (0..4100)
        .map(|i| format!("let x{i} = 0;\n"))
        .collect::<String>();
    for lambda in [
        "",
        "fn unused() -> Int { let g = fn(x: Int) -> Int { x }; g(1) }",
    ] {
        reject(
            &format!("fn main() -> Int {{ {body} 42 }}\n{lambda}"),
            "E_LIMIT",
        );
    }
}

#[test]
fn function_result_dependencies_resume_with_the_original_static_target() {
    native(
        "fn main() -> Int { first()(41) }\nfn first() -> Fn<Int, Int> { second() }\nfn second() -> Fn<Int, Int> { fn(value: Int) -> Int { value + 1 } }",
        &[],
        "42",
    );
    reject(
        "fn first() -> Fn<Int, Int> { second() }\nfn second() -> Fn<Int, Int> { first() }\nfn main() -> Int { first()(1) }",
        "E_RECURSION",
    );
}

#[test]
fn lambdas_cannot_shadow_enclosing_parameters_lets_or_unpacked_objects() {
    for source in [
        "fn main() -> Int { let x = 41; let f = fn(x: Int) -> Int { x + 1 }; f(x) }",
        "fn outer(x: Int) -> Int { let f = fn() -> Int { let x = 1; x }; f() }",
        "fn main() -> Int { let X = Affine(QQ, 1); let f = fn() -> Int { let p = { let Y = Affine(QQ, 1); pack { scheme: Y, point: origin(Y) } }; unpack p as { scheme: X, point: point }; 0 }; f() }",
    ] {
        reject(source, "E_SHADOW");
    }
    let mut forged =
        request("fn main() -> Int { let x = 41; let f = fn(y: Int) -> Int { y + 1 }; f(x) }");
    forged["functions"][0]["body"]["statements"][1]["value"]["params"][0]["name"] = json!("x");
    forged["functions"][0]["body"]["statements"][1]["value"]["body"]["result"]["left"]["name"] =
        json!("x");
    assert_rejected(forged, "E_SHADOW");
    native(
        "fn main() -> Int { let f = fn(x: Int) -> Int { x + 1 }; let g = fn(x: Int) -> Int { x + 1 }; f(g(40)) }",
        &[],
        "42",
    );
}

#[test]
fn native_function_values_pass_return_and_invoke() {
    native(include_str!("../examples/functions.vast"), &[], "42");
    native("fn inc(x: Int) -> Int { x + 1 }
fn keep(callback: Fn<Int, Int>) -> Fn<Int, Int> { callback }
fn choose(flag: Bool, a: Fn<Int, Int>, b: Fn<Int, Int>) -> Fn<Int, Int> { if flag { a } else { b } }
fn factory(unused: Int) -> Fn<Int, Int> { let checked = unused + 2; fn(x: Int) -> Int { x + 1 } }
fn main() -> Int { let first = keep(inc); let selected = choose(false, first, inc); selected(factory(8)(40)) }", &[], "42");
}

#[test]
fn native_function_arity_and_nested_fn_types() {
    native(
        "fn main() -> Int {
 let truth = fn(x: Bool) -> Bool { !x };
 let natural = fn(n: Nat) -> Nat { n - 1 };
 let ignore = fn(u: Unit) -> Unit { u };
 let done = ignore(());
 if truth(false) { int(natural(43)) } else { 0 }
}",
        &[],
        "42",
    );
    native("fn binary(callback: Fn<(Int, Int), Int>, x: Int, y: Int) -> Int { callback(x, y) }
fn nullary(callback: Fn<(), Int>) -> Int { callback() }
fn unitary(callback: Fn<Unit, Int>) -> Int { callback(()) }
fn main() -> Int {
 let transform: Fn<Fn<Int, Int>, Fn<Int, Int>> = fn(callback: Fn<Int, Int>) -> Fn<Int, Int> { callback };
 let plus: Fn<(Int, Int), Int> = fn(x: Int, y: Int) -> Int { x + y };
 let zero: Fn<(), Int> = fn() -> Int { 20 };
 let one: Fn<Unit, Int> = fn(ignored: Unit) -> Int { 21 };
 let inc = fn(x: Int) -> Int { x + 1 };
 transform(inc)(binary(plus, nullary(zero), unitary(one)))
}", &[], "42");
}

#[test]
fn native_nested_independent_lambdas_and_geometry_inside_bodies() {
    native("fn main() -> Int {
 let factory = fn(ignored: Int) -> Fn<Nat, Int> {
   fn(n: Nat) -> Int { let X = Affine(QQ, n); let p = origin(X); let q = apply(id(X), p); int(dimension(X)) }
 };
 factory(0)(42)
}", &[], "42");
}

#[test]
fn function_lowering_preserves_existing_dependent_geometry() {
    let source = include_str!("../examples/pointed.vast")
        .replace(
            "fn main() -> Int {",
            "fn main() -> Int { let scalar = fn(x: Int) -> Int { x };",
        )
        .replace("{ 42 } else", "{ scalar(42) } else");
    native(&source, &[], "42");
    reject(
        "fn main() -> Int {
 let callback = fn(x: Int) -> Int { x };
 let X = Affine(QQ, 1); let Y = Affine(QQ, 1);
 let p = origin(X); let q = apply(id(Y), p); callback(0)
}",
        "E_ENDPOINT",
    );
}

#[test]
fn named_functions_can_be_values_without_fn_annotations() {
    native(
        "fn main() -> Int { let unused = fn() -> Int { main() }; 42 }",
        &[],
        "42",
    );
    native(
        "fn inc(x: Int) -> Int { x + 1 } fn main() -> Int { let alias = inc; alias(41) }",
        &[],
        "42",
    );
    native(
        "fn inc(x: Int) -> Int { x + 1 } fn main() -> Int { (if true { inc } else { inc })(41) }",
        &[],
        "42",
    );
}

#[test]
fn invocation_after_else_if_applies_to_the_entire_chain() {
    let source = "fn inc(x: Int) -> Int { x + 1 }
fn factory() -> Fn<Int, Int> { inc }
fn main() -> Int {
 let first = if true { inc } else if false { inc } else { inc }(41);
 let middle = if false { inc } else if true { inc } else { inc }(41);
 let last = if false { inc } else if false { inc } else if false { inc } else { inc }(41);
 let chained = if true { factory } else if false { factory } else { factory }()(41);
 first + middle + last + chained
}";
    success(&check(source));
    native(source, &[], "168");
}

#[test]
fn functions_and_dispatch_call_each_other_and_keep_library_locations() {
    native(
        "generic offset(x) { domain (Int); }
method offset(x: Int) -> Int { run(fn(y: Int) -> Int { y + 1 }, x) }
fn run(callback: Fn<Int, Int>, x: Int) -> Int { callback(x) }
fn main() -> Int { let wrapped = fn(x: Int) -> Int { offset(x) }; run(wrapped, 41) }",
        &[],
        "42",
    );
    let scratch = Scratch::new();
    let library = scratch.0.join("functions.vast");
    fs::write(
        &library,
        "fn run(callback: Fn<Int, Int>, x: Int) -> Int { callback(x) }",
    )
    .unwrap();
    let helper = scratch.0.join("increment.vast");
    fs::write(&helper, "fn increment(x: Int) -> Int { x + 1 }").unwrap();
    native(
        "fn main() -> Int { run(increment, 41) }",
        &[library, helper],
        "42",
    );
}

#[test]
fn captures_including_function_values_are_rejected() {
    for source in [
        "fn main() -> Int { let x = 1; let f = fn(y: Int) -> Int { x + y }; f(41) }",
        "fn outer(callback: Fn<Int, Int>) -> Fn<Int, Int> { fn(x: Int) -> Int { callback(x) } }",
        "fn main() -> Int { let x = 1; let f = fn() -> Fn<(), Int> { fn() -> Int { x } }; 0 }",
        "fn main() -> Int { let X = Affine(QQ, 1); let f = fn() -> Int { let Y = Affine(QQ, 1); let p: Point<X, Base(QQ)> = origin(Y); 0 }; 0 }",
    ] {
        reject(source, "E_CAPTURE");
    }
}

#[test]
fn invalid_function_contracts_and_unresolved_targets_are_rejected() {
    for (source, code) in [
        (
            "fn main() -> Int { let f: fn(Int) -> Int = fn(x: Int) -> Int { x }; 0 }",
            "E_PARSE",
        ),
        ("fn Fn() -> Int { 0 }", "E_RESERVED"),
        (
            "fn main() -> Int { let trigger = fn() -> Int { 0 }; let value = 1; value() }",
            "E_TYPE",
        ),
        (
            "generic g(x) { domain (Int); } method g(x: Int) -> Int { x } fn main() -> Int { let callback = g; 0 }",
            "E_TYPE",
        ),
        (
            "fn main() -> Int { let callback = fn(x: Int) -> Int { missing }; 0 }",
            "E_NAME",
        ),
        (
            "fn main() -> Int { let f = fn(x: Int) -> Int { x }; f(true) }",
            "E_TYPE",
        ),
        (
            "fn main() -> Int { let f = fn() -> Int { 1 }; f(()) }",
            "E_ARITY",
        ),
        (
            "fn main() -> Int { let f: Fn<(), Int> = fn(u: Unit) -> Int { 0 }; 0 }",
            "E_TYPE",
        ),
        (
            "fn unused(callback: Fn<Int, Int>) -> Int { true }",
            "E_TYPE",
        ),
        (
            "fn unused(callback: Fn<Int, Int>) -> Int { callback(true) }",
            "E_TYPE",
        ),
        (
            "fn unused(callback: Fn<Int, Int>) -> Fn<Int, Int> { if true { fn(x: Int) -> Int { x } } else { fn(y: Int) -> Int { y + 1 } } }",
            "E_STATIC_CALL",
        ),
        (
            "fn unused(callback: Fn<Fn<Int, Int>, Int>) -> Int { callback(if 1 { fn(x: Int) -> Int { x } } else { fn(y: Int) -> Int { y } }) }",
            "E_TYPE",
        ),
        (
            "fn main() -> Int { let unused = fn(x: Int) -> Int { true }; 0 }",
            "E_TYPE",
        ),
        (
            "fn main() -> Int { let unused = fn(X: Scheme) -> Int { 0 }; 0 }",
            "E_TYPE",
        ),
        (
            "fn main() -> Int { let f = if true { fn(x: Int) -> Int { x } } else { fn(y: Int) -> Int { y } }; f(42) }",
            "E_STATIC_CALL",
        ),
        (
            "fn identity(x: Int) -> Int { x } fn main() -> Int { let f: Fn<Bool, Int> = identity; 0 }",
            "E_TYPE",
        ),
        ("fn main(callback: Fn<Int, Int>) -> Int { 0 }", "E_MAIN"),
        (
            "fn main() -> Int { let f = fn(x: Int) -> Int { x }; let f = 0; f }",
            "E_DUPLICATE",
        ),
    ] {
        reject(source, code);
    }
}

#[test]
fn recursion_through_function_values_is_rejected() {
    reject(
        "fn repeat(x: Int) -> Int { let callback = repeat; callback(x) }",
        "E_RECURSION",
    );
    reject(
        "fn run(callback: Fn<Int, Int>, x: Int) -> Int { callback(x) }
fn repeat(x: Int) -> Int { run(repeat, x) }",
        "E_RECURSION",
    );
}

#[test]
fn lambda_cycle_diagnostics_use_source_locations_in_flat_and_package_modes() {
    let source = "fn inc(x: Int) -> Int { x + 1 }\nfn f(h: Fn<Int, Int>) -> Int { let g = fn() -> Int { f(inc) }; g() }\nfn main() -> Int { 0 }";
    let scratch = Scratch::new();
    let input = scratch.source(source);
    let manifest = scratch.0.join("Vastitas.toml");
    fs::write(
        &manifest,
        "[package]\nname='cycle'\nversion='0.1.0'\nroot='function input.vast'\n",
    )
    .unwrap();
    for package in [false, true] {
        let mut command = cli();
        command.arg("check");
        if package {
            command.arg("--manifest-path").arg(&manifest);
        } else {
            command.arg(&input);
        }
        let output = command.output().unwrap();
        let message = String::from_utf8(output.stderr).unwrap();
        assert!(!output.status.success());
        assert!(message.contains("E_RECURSION"), "{message}");
        assert!(message.contains("lambda at 2:40"), "{message}");
        assert!(
            message.contains(":2:40: note: lambda defined here"),
            "{message}"
        );
        assert!(!message.contains("__vastitas_"), "{message}");
    }
}

#[test]
fn functions_do_not_hide_invalid_applicable_methods() {
    reject(
        "generic fallback(x) { domain; }
method fallback(x: Any) -> Int { let callback = fn(y: Int) -> Int { y }; x + callback(1) }
fn main() -> Int { 0 }",
        "E_TYPE",
    );
}

#[test]
fn forged_function_ir_cannot_capture_or_trust_span_identity() {
    let mut raw =
        request("fn main() -> Int { let secret = 42; let f = fn(x: Int) -> Int { x }; f(0) }");
    raw["functions"][0]["body"]["statements"][1]["value"]["body"]["result"]["name"] =
        json!("secret");
    assert_rejected(raw, "E_CAPTURE");

    let mut raw = request(
        "fn main() -> Int { let X = Affine(QQ, 1); let f = fn() -> Int { let Y = Affine(QQ, 1); let p: Point<Y, Base(QQ)> = origin(Y); 0 }; 0 }",
    );
    raw["functions"][0]["body"]["statements"][1]["value"]["body"]["statements"][1]["annotation"]
        ["target"]["name"] = json!("X");
    assert_rejected(raw, "E_CAPTURE");

    let mut raw = request("fn main() -> Int { let f = fn(x: Int) -> Int { x }; 0 }");
    raw["functions"][0]["body"]["statements"][0]["value"]["body"]["result"]["name"] =
        json!("missing");
    assert_rejected(raw, "E_NAME");

    let mut raw =
        request("fn use_it(callback: Fn<Int, Int>) -> Int { callback(1) } fn main() -> Int { 0 }");
    raw["functions"][0]["params"][0]["ty"]["params"][0] = json!({"kind":"named", "name":"Bool"});
    assert_rejected(raw, "E_TYPE");

    let mut raw = request("fn main() -> Int { let f = fn(x: Int) -> Int { x }; 0 }");
    raw["functions"][0]["body"]["statements"][0]["value"]["params"][0]["name"] = json!("Fn");
    raw["functions"][0]["body"]["statements"][0]["value"]["body"]["result"]["name"] = json!("Fn");
    assert_rejected(raw, "E_RESERVED");

    let mut raw = request(
        "fn main() -> Int { let f = if true { fn(x: Int) -> Int { x } } else { fn(y: Int) -> Int { y + 1 } }; f(0) }",
    );
    let first =
        raw["functions"][0]["body"]["statements"][0]["value"]["then_branch"]["result"]["span"]
            .clone();
    raw["functions"][0]["body"]["statements"][0]["value"]["else_branch"]["result"]["span"] = first;
    assert_rejected(raw, "E_STATIC_CALL");

    let mut raw = request("fn main() -> Int { 0 }");
    raw["functions"][0]["body"]["result"]["kind"] = json!("reference");
    assert_rejected(raw, "E_PROTOCOL");
}

#[test]
fn specialization_limit_checks_unused_functions_before_reachability() {
    let mut source = String::from("fn main() -> Int { 42 }\n");
    for index in 0..2048 {
        source.push_str(&format!(
            "fn factory{index}() -> Fn<(), Int> {{ fn() -> Int {{ 1 }} }}\n"
        ));
    }
    let response = kernel(request(&source));
    assert_eq!(response["ok"], true, "{response}");
    let generated = response["lean_source"].as_str().unwrap();
    assert_eq!(
        generated.matches("def f_").count(),
        1,
        "unused specializations leaked into codegen"
    );
    source.push_str("fn overflow() -> Fn<(), Int> { fn() -> Int { 0 } }");
    assert_rejected(request(&source), "E_LIMIT");
}

#[test]
fn function_type_depth_is_bounded_on_both_sides() {
    let ty = format!("{}Int{}", "Fn<Int, ".repeat(70), ">".repeat(70));
    reject(&format!("fn invalid(f: {ty}) -> Int {{ 0 }}"), "E_LIMIT");
    let mut raw = request("fn main() -> Int { let f = fn(x: Int) -> Int { x }; 0 }");
    let mut ty = json!({"kind": "named", "name": "Int"});
    for _ in 0..70 {
        ty = json!({"kind": "function", "params": [], "return_type": ty});
    }
    raw["functions"][0]["body"]["statements"][0]["value"]["return_type"] = ty;
    assert_rejected(raw, "E_PROTOCOL");
}

#[test]
fn lowered_type_reuse_preserves_contextual_literals_and_nominal_endpoints() {
    let declarations = "generic keep(x) { domain (Nat), (Int); }
method keep(x: Nat) -> Nat { x }
method keep(x: Int) -> Int { x }
fn point(X: Scheme) -> Point<X, Base(QQ)> { origin(X) }
fn natural(n: Nat) -> Nat { let zero: Nat = { let z: Nat = 0 + 0; z }; if true { 0 } else { keep(n) + zero } }
";
    let mut nested = "42".to_owned();
    for _ in 0..35 {
        nested = format!("keep({nested})");
    }
    for lambda in [
        "",
        "fn unused() -> Int { let f = fn(x: Int) -> Int { keep(x) }; f(0) }",
    ] {
        let source = format!(
            "{declarations}{lambda}
fn main() -> Int {{
 let X = Affine(QQ, 1);
 let Y = Affine(QQ, 1);
 let p: Point<X, Base(QQ)> = {{ let alias = X; point(alias) }};
 let q: Point<X, Base(QQ)> = apply(id(X), p);
 {nested} + int(natural(1))
}}"
        );
        native(&source, &[], "42");
        reject(
            &source.replace("let q: Point<X", "let q: Point<Y"),
            "E_TYPE",
        );
        reject(&source.replace(&nested, "int(keep(0))"), "E_TYPE");
    }
}
