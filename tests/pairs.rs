//! Pair values cross the frontend, independently checked core and native runtime.
mod common;
use common::{Scratch, exits, ran, shows, success};
use serde_json::{Value, json};
use std::fs;
use std::process::Command;

impl Scratch {
    fn new(source: &str) -> Self {
        let scratch = Self::empty("pairs");
        let path = &scratch.0;
        fs::write(path.join("main.vast"), source).unwrap();
        fs::write(
            path.join("Vastitas.toml"),
            "[package]\nedition = \"2026\"\nname='pairs'\nversion='0.1.0'\nroot='main.vast'\n",
        )
        .unwrap();
        scratch
    }
    /// The compiler in `mode` in this directory, on the package when
    /// `package` and on the flat program otherwise.
    fn compiler(&self, mode: &str, package: bool) -> Command {
        let mut command = self.cli();
        command.arg(mode);
        if package {
            command.args(["--manifest-path", "Vastitas.toml"]);
        } else {
            command.arg("main.vast");
        }
        command
    }
}
fn request(source: &str) -> Value {
    common::request(source, "pairs.vast")
}
fn backend(raw: &Value) -> Value {
    common::kernel(raw, "check")
}
#[track_caller]
fn rejects(raw: Value, code: &str) {
    let result = backend(&raw);
    common::assert_wire_rejected(&result, code);
}

#[test]
fn pairs_preserve_values_arguments_results_branches_and_lambda_bodies() {
    let scratch = Scratch::new(include_str!("../examples/book/values/pairs.vast"));
    for package in [false, true] {
        success(&scratch.compiler("check", package).output().unwrap());
        success(
            &scratch
                .compiler("build", package)
                .args(["-o", "program"])
                .output()
                .unwrap(),
        );
        let output = Command::new(scratch.0.join("program")).output().unwrap();
        assert_eq!(
            ran(&output),
            shows(&[
                "reverse(pair(big, zero)) = (0, 123456789012345678901234567890)",
                "choose(false, pair(0, 0), pair(-7, 42)) = (-7, 42)",
                "offset(40) = 42",
            ])
        );
    }
    let mut first_order =
        request("fn reverse(p: Pair<Int>) -> Pair<Int> { pair(pair_second(p), pair_first(p)) }");
    assert_eq!(
        common::flat_module(&mut first_order)["functions"][0]["return_type"],
        json!({"kind":"pair","element":"Int"})
    );
    assert_eq!(backend(&first_order)["ok"], true);
}

#[test]
fn pair_construction_infers_operands_without_conversion_or_expected_type_selection() {
    for (source, code) in [
        ("fn f() -> Pair<Nat> { pair(1, 2) }", "E_TYPE"),
        ("fn f(n: Nat) -> Pair<Int> { pair(n, 2) }", "E_TYPE"),
        ("fn f() -> Pair<Int> { pair(true, false) }", "E_TYPE"),
        ("fn f() -> Pair<Int> { pair((), ()) }", "E_TYPE"),
        (
            "fn f() -> Pair<Int> { pair(pair(1, 2), pair(3, 4)) }",
            "E_TYPE",
        ),
        (
            "fn f() -> Pair<Int> { let x = Affine(QQ, 1); pair(x, x) }",
            "E_TYPE",
        ),
        ("fn f() -> Pair<Int> { pair(1) }", "E_ARITY"),
        ("fn f() -> Int { pair_first(1) }", "E_TYPE"),
        ("fn f() -> Int { pair_second(pair(1, 2), 3) }", "E_ARITY"),
        (
            "fn f(n: Nat) -> Pair<Int> { if true { pair(n, n) } else { pair(1, 2) } }",
            "E_TYPE",
        ),
        ("fn f(p: Fn<Pair<Int>, Int>) -> Int { 0 }", "E_TYPE"),
        (
            "fn f() -> Int { let p = fn() -> Pair<Int> { pair(1, 2) }; 0 }",
            "E_TYPE",
        ),
    ] {
        let scratch = Scratch::new(source);
        let output = scratch.compiler("check", false).output().unwrap();
        assert!(!output.status.success(), "accepted: {source}");
        let error = String::from_utf8_lossy(&output.stderr);
        common::assert_first_code(&error, code);
        rejects(request(source), code);
    }
}

// #868: `==` and `!=` between two pairs of one type are `E_OPERATOR`, and the
// message names the pair type and the comparison of the components that takes
// their place, in flat and in manifest mode.
#[test]
fn pair_equality_names_the_pair_type_and_the_component_comparison() {
    for (operator, element, join) in [("==", "Int", "&&"), ("!=", "Nat", "||")] {
        let source = format!(
            "fn same(a: Pair<{element}>, b: Pair<{element}>) -> Bool {{ a {operator} b }}\nfn main() -> Int {{ 0 }}"
        );
        let expected = format!(
            "`{operator}` does not compare two values of type Pair<{element}>; compare their components, as in `pair_first(a) {operator} pair_first(b) {join} pair_second(a) {operator} pair_second(b)`"
        );
        let scratch = Scratch::new(&source);
        for package in [false, true] {
            let output = scratch.compiler("check", package).output().unwrap();
            let message = common::expect_code(&output, "E_OPERATOR");
            assert!(
                message.contains("main.vast:1:") && message.contains(&expected),
                "{message}"
            );
        }
    }
    // The program of the issue: a shown pair compared with the expected one.
    let scratch = Scratch::new(
        "fn main() -> Int {\n    let actual: Pair<Int> = show!(pair(33, 2));\n    let expected: Pair<Int> = pair(33, 2);\n    if actual == expected { 0 } else { 1 }\n}",
    );
    let output = scratch.compiler("check", false).output().unwrap();
    let message = common::expect_code(&output, "E_OPERATOR");
    assert!(
        message.contains("main.vast:4:8:") && message.contains("type Pair<Int>"),
        "{message}"
    );
}

#[test]
fn malformed_pair_types_and_dispatch_uses_are_rejected_independently() {
    for element in [
        "Bool",
        "Unit",
        "Number",
        "Scheme",
        "Pair<Int>",
        "__vastitas_l0",
    ] {
        // The decoder admits the elements `Nat` and `Int` alone.
        let mut raw = request("fn f() -> Pair<Int> { pair(1, 2) }");
        common::flat_module(&mut raw)["functions"][0]["return_type"]["element"] = json!(element);
        let result = backend(&raw);
        common::assert_wire_rejected(&result, "E_PROTOCOL");
        assert_eq!(
            result["diagnostics"][0]["message"], "Pair elements must be Nat or Int",
            "{element}: {result}"
        );
    }
    let mut raw = request("fn f() -> Pair<Int> { pair(1, 2) }");
    common::flat_module(&mut raw)["functions"][0]["return_type"]["element"] =
        json!({"kind":"named","name":"Int"});
    rejects(raw, "E_PROTOCOL");
    // A pair in a dispatch domain or as a method result is the checker's
    // `E_TYPE`; a selector's type is a named scalar for the decoder.
    for (field, code) in [
        ("domain", "E_TYPE"),
        ("selector", "E_PROTOCOL"),
        ("result", "E_TYPE"),
    ] {
        let mut raw = request("fn f(x) domain((Int)); fn f(x: Int) -> Int { 0 }");
        let pair = json!({"kind":"pair","element":"Int"});
        let module = common::flat_module(&mut raw);
        match field {
            "domain" => module["generics"][0]["domain"][0][0] = pair,
            "selector" => module["methods"][0]["params"][0]["ty"] = pair,
            _ => module["methods"][0]["return_type"] = pair,
        }
        rejects(raw, code);
    }
    for source in [
        "fn f(p: Pair<Bool>) -> Int { 0 }",
        "fn f(p: Pair<Pair<Int>>) -> Int { 0 }",
    ] {
        assert!(vastitas::frontend::parse(source, "pair.vast").is_err());
    }
}

const PAIR_METHODS: &str = "
fn choose(x, y) domain((Nat, Nat), (Nat, Int), (Int, Nat), (Int, Int));
fn choose(x: Nat, y: Nat) -> Pair<Nat> { pair(x, y) }
fn choose(x: Nat, y: Int) -> Pair<Int> { pair(int(x), y) }
fn choose(x: Int, y: Nat) -> Pair<Int> { pair(x, int(y)) }
fn choose(x: Int, y: Int) -> Pair<Int> { pair(x, y) }
";

#[test]
fn selected_pair_results_flow_to_projections_and_downstream_dispatch() {
    let caller = "
fn scalar(x) domain((Nat), (Int));
fn scalar(x: Nat) -> Int { int(x) }
fn scalar(x: Int) -> Int { x }
fn main() -> Int {
    let n: Nat = 20;
    let nn: Pair<Nat> = choose(n, n);
    let ni: Pair<Int> = choose(n, -7);
    let in_: Pair<Int> = choose(-7, n);
    let ii: Pair<Int> = choose(-7, 22);
    if scalar(pair_first(nn)) == 20 && pair_second(nn) == n &&
       pair_first(ni) == 20 && pair_second(ni) == -7 &&
       pair_first(in_) == -7 && pair_second(in_) == 20 &&
       pair_first(ii) == -7 && scalar(pair_second(ii)) == 22 { 42 } else { 0 }
}";
    // Exercise the common lowering with and without function constructs.
    for extra in [
        "",
        "fn unused() -> Int { let f = fn(x: Int) -> Int { pair_first(choose(x, x)) }; f(1) }",
    ] {
        let source = format!("{PAIR_METHODS}\n{caller}\n{extra}");
        assert_eq!(backend(&request(&source))["ok"], true);
        let scratch = Scratch::new(&source);
        for package in [false, true] {
            success(&scratch.compiler("check", package).output().unwrap());
            success(
                &scratch
                    .compiler("build", package)
                    .args(["-o", "program"])
                    .output()
                    .unwrap(),
            );
            let output = Command::new(scratch.0.join("program")).output().unwrap();
            assert_eq!(ran(&output), exits(42));
        }
    }
}

#[test]
fn pair_results_do_not_change_selection_or_whole_body_audits() {
    let cases = [
        (format!("{PAIR_METHODS} fn bad(n: Nat) -> Pair<Nat> {{ choose(n, 2) }}"), "E_TYPE"),
        (format!("{PAIR_METHODS} fn bad() -> Pair<Nat> {{ choose(1, 2) }}"), "E_TYPE"),
        (format!("{PAIR_METHODS} fn choose(x: Number, y: Number) -> Pair<Int> {{ pair(x, y) }}"), "E_TYPE"),
        ("fn g(x) domain((Int)); fn g(x: Int) -> Pair<Int> { pair(x, x) } fn g(x: Any) -> Pair<Int> { pair(x, x) }".into(), "E_TYPE"),
        ("fn g(x) domain((Int)); fn g(x: Int) -> Pair<Int> { pair(x, x) } fn g(x: Int) -> Int { x }".into(), "E_DUPLICATE"),
        ("fn g(x) domain((Int), (Nat)); fn g(x: Int) -> Pair<Int> { pair(x, x) }".into(), "E_DISPATCH_COVERAGE"),
        ("fn g(x, y) domain((Nat, Nat)); fn g(x: Nat, y: Number) -> Pair<Int> { pair(1, 2) } fn g(x: Number, y: Int) -> Int { 0 }".into(), "E_DISPATCH_AMBIGUOUS"),
    ];
    for (source, expected) in cases {
        for extra in [
            "",
            "fn probe() -> Int { let f = fn(x: Int) -> Int { x }; f(0) }",
        ] {
            let source = format!("{source}\n{extra}");
            let response = backend(&request(&source));
            assert_eq!(response["ok"], false, "{source}: {response}");
            common::assert_wire_rejected(&response, expected);
            let scratch = Scratch::new(&source);
            for package in [false, true] {
                let output = scratch.compiler("check", package).output().unwrap();
                assert!(!output.status.success());
                common::expect_code(&output, expected);
            }
        }
    }
    // A losing method may return a different type when its own body is valid.
    let valid = "fn g(x) domain((Int)); fn g(x: Int) -> Pair<Int> { pair(x, x) } fn g(x: Number) -> Bool { true } fn main() -> Int { pair_first(g(42)) }";
    assert_eq!(backend(&request(valid))["ok"], true);
}
