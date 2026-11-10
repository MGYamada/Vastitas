mod common;

use common::{Scratch, cli, kernel, success};
use serde_json::{Value, json};
use std::process::Command;

const FUNCTIONS: &str = r#"
resource fn choose(flag: Bool, n: Nat, delta: Int, token: Unit)
    returns (data: Owned<F64, 1> initialized [layout(0, 1, 1, 1, false)]) -> Bool {
    allocate data: F64[1];
    borrow output = write(data, layout(0, 1, 1, 1, false));
    if flag {
        fill(output, f64_bits(4607182418800017408));
    } else {
        fill(output, f64_bits(4611686018427387904));
    }
    release(output);
    let remainder: Nat = value { n - 123456789012345678901234567890 };
    let selected: Bool = value { if remainder == 0 { flag } else { false } };
    value { selected }
}
resource fn finish(input: Owned<F64, 1>, seed: Int) -> Int {
    drop(input);
    let next: Int = value { seed + 1 };
    value { next }
}
resource fn identity_unit(token: Unit) -> Unit { value { token } }
"#;

fn source(flag: bool) -> String {
    format!(
        "{FUNCTIONS}
resource fn main() -> Int {{
    let flag: Bool = value {{ {flag} }};
    let n: Nat = value {{ 123456789012345678901234567889 }};
    let seed: Int = value {{ 40 }};
    let token: Unit = value {{ () }};
    let selected: Bool = call choose(flag, n, seed, token) -> (data);
    borrow input = read(data, layout(0, 1, 1, 1, false));
    if selected {{
        expect(input, 0, 0, f64_bits(4607182418800017408));
    }} else {{
        expect(input, 0, 0, f64_bits(4611686018427387904));
    }}
    release(input);
    let answer: Int = call finish(data, seed) -> ();
    let done: Unit = call identity_unit(token) -> ();
    value {{ answer + 1 }}
}}
"
    )
}

fn fixture(source: &str) -> Scratch {
    let scratch = Scratch::empty("resource value flow");
    scratch.write(
        "Vastitas.toml",
        "[package]\nname = \"resource_values\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n",
    );
    scratch.write("main.vast", source);
    scratch
}

fn check(scratch: &Scratch) -> std::process::Output {
    cli()
        .args(["check", "--manifest-path"])
        .arg(scratch.0.join("Vastitas.toml"))
        .output()
        .unwrap()
}

fn request(scratch: &Scratch) -> Value {
    common::captured_wire(
        cli()
            .args(["check", "--manifest-path"])
            .arg(scratch.0.join("Vastitas.toml")),
        8,
    )
}

fn functions(raw: &Value) -> &Value {
    &raw["packages"][0]["modules"][0]["resource_functions"]
}

#[track_caller]
fn rejected(source: &str, code: &str) {
    let output = check(&fixture(source));
    assert!(
        !output.status.success(),
        "accepted invalid source: {source}"
    );
    common::expect_code(&output, code);
}

#[test]
fn parser_preserves_scalar_names_types_both_branches_and_old_literal_form() {
    let source = source(false).replace(
        "let answer: Int = call finish",
        "if true {} else {}\nlet answer: Int = call finish",
    );
    let raw = request(&fixture(&source));
    assert_eq!(raw["version"], 8);
    let functions = functions(&raw);
    for (index, ty) in ["Bool", "Nat", "Int", "Unit"].iter().enumerate() {
        assert_eq!(functions[0]["parameters"][index]["kind"], "value");
        assert_eq!(functions[0]["parameters"][index]["type"]["name"], *ty);
    }
    assert_eq!(functions[0]["body"][2]["kind"], "branch_value");
    assert_eq!(functions[0]["body"][2]["condition"], "flag");
    assert_eq!(functions[0]["body"][2]["yes"].as_array().unwrap().len(), 1);
    assert_eq!(functions[0]["body"][2]["no"].as_array().unwrap().len(), 1);
    let main = &functions[3];
    assert_eq!(main["body"][0]["kind"], "value");
    assert_eq!(main["body"][4]["kind"], "call_value");
    assert_eq!(main["body"][4]["value"], "selected");
    assert_eq!(main["body"][4]["callee"], "choose");
    assert_eq!(
        main["body"][4]["arguments"],
        json!(["flag", "n", "seed", "token"])
    );
    assert_eq!(main["body"][4]["results"], json!(["data"]));
    assert_eq!(main["body"][8]["kind"], "branch");
    assert_eq!(main["body"][8]["condition"], true);
    let span = &main["body"][4]["span"];
    let line = span["line"].as_u64().unwrap() as usize;
    let column = span["column"].as_u64().unwrap() as usize;
    let start = source
        .split_inclusive('\n')
        .take(line - 1)
        .map(str::len)
        .sum::<usize>()
        + column
        - 1;
    // Byte offsets are global across the manifest and module inputs, whereas
    // line/column remain local to this source file.
    let length = (span["end"].as_u64().unwrap() - span["start"].as_u64().unwrap()) as usize;
    assert_eq!(
        &source[start..start + length],
        "let selected: Bool = call choose(flag, n, seed, token) -> (data);"
    );
}

#[test]
fn discarded_legacy_pair_result_remains_valid_but_cannot_be_captured() {
    let source = "resource fn pair_result() -> Pair<Int> { value { pair(20, 22) } }
resource fn main() -> Int {
    call pair_result() -> ();
    value { 42 }
}";
    success(&check(&fixture(source)));
    rejected(
        &source.replace(
            "call pair_result() -> ();",
            "let result: Pair<Int> = call pair_result() -> ();",
        ),
        "E_RESOURCE_VALUE",
    );
}

#[test]
fn scalar_fragments_preserve_cross_module_calls_and_capture_free_lambdas() {
    let main = "mod helpers;
use helpers::compute;
use helpers::natural;
resource fn main() -> Int {
    let initial: Nat = value { 123456789012345678901234567890 };
    let n: Nat = call natural(initial) -> ();
    let flag: Bool = value { false };
    let result: Int = call compute(n, flag) -> ();
    value { result }
}";
    let helpers = "fn increment(input: Int) -> Int { input + 1 }
pub resource fn natural(input: Nat) -> Nat {
    value { input - 123456789012345678901234567849 }
}
pub resource fn compute(n: Nat, flag: Bool) -> Int {
    let converted: Int = value { int(n) };
    if flag {
        let local: Int = value { increment(converted) };
    } else {
        let local: Int = value { converted };
    }
    value {
        let identity: Fn<Int, Int> = fn(x: Int) -> Int { x };
        identity(increment(converted))
    }
}";
    let scratch = fixture(main);
    scratch.write("helpers.vast", helpers);
    success(&check(&scratch));
    let raw = request(&scratch);
    let emitted = kernel(raw, "emit");
    assert_eq!(emitted["ok"], true, "{emitted}");
    let executable = scratch.0.join("program");
    success(
        &cli()
            .args(["build", "--manifest-path"])
            .arg(scratch.0.join("Vastitas.toml"))
            .arg("-o")
            .arg(&executable)
            .output()
            .unwrap(),
    );
    let output = Command::new(executable).output().unwrap();
    success(&output);
    assert_eq!(output.stdout, b"42\n");
    for invalid in [
        helpers.replace("pub resource fn", "resource fn"),
        helpers.replace("increment(converted)", "missing(converted)"),
        helpers.replace("fn(x: Int) -> Int { x }", "fn(x: Int) -> Int { converted }"),
        helpers.replace("value { increment(converted) }", "value { true }"),
    ] {
        scratch.write("helpers.vast", &invalid);
        let output = check(&scratch);
        assert!(!output.status.success(), "accepted {invalid}");
    }
}

#[test]
fn scalar_calls_and_runtime_bool_branches_execute_with_owned_results() {
    for flag in [false, true] {
        let scratch = fixture(&source(flag));
        success(&check(&scratch));
        let raw = request(&scratch);
        let emitted = kernel(&raw, "emit");
        assert_eq!(emitted["ok"], true, "{emitted}");
        let emitted_source = emitted["lean_source"].as_str().unwrap();
        assert_eq!(emitted_source.matches("allocate arena").count(), 1);
        assert_eq!(emitted_source.matches("fill arena").count(), 2);
        assert!(!emitted_source.contains("copy arena"));
        let executable = scratch.0.join("program");
        success(
            &cli()
                .args(["build", "--manifest-path"])
                .arg(scratch.0.join("Vastitas.toml"))
                .arg("-o")
                .arg(&executable)
                .output()
                .unwrap(),
        );
        let output = Command::new(executable).output().unwrap();
        success(&output);
        assert_eq!(output.stdout, b"42\n");
    }
    // A demanded scalar result cannot publish success after its actual callee
    // has failed, even though that result's pure Core fragment is well typed.
    let failing = source(false).replace(
        "release(output);",
        "release(output);\nborrow inspect = read(data, layout(0, 1, 1, 1, false));\nexpect(inspect, 0, 0, f64_bits(0));\nrelease(inspect);",
    );
    let scratch = fixture(&failing);
    let executable = scratch.0.join("fails");
    success(
        &cli()
            .args(["build", "--manifest-path"])
            .arg(scratch.0.join("Vastitas.toml"))
            .arg("-o")
            .arg(&executable)
            .output()
            .unwrap(),
    );
    let output = Command::new(executable).output().unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    common::expect_code(&output, "E_NATIVE_EXPECT");
}

#[test]
fn scalar_value_flow_rejects_captures_types_scope_leaks_and_untaken_errors() {
    let valid = source(false);
    for (from, to, code) in [
        (
            "let seed: Int = value { 40 };",
            "let seed: Int = value { true };",
            "E_TYPE",
        ),
        (
            "let selected: Bool = call choose",
            "let selected: Int = call choose",
            // The later Bool branch is diagnosed first; the binding is also rejected.
            "E_RESOURCE_VALUE",
        ),
        (
            "choose(flag, n, seed, token)",
            "choose(seed, n, seed, token)",
            "E_RESOURCE_VALUE",
        ),
        ("if selected {", "if seed {", "E_RESOURCE_VALUE"),
        ("value { answer + 1 }", "value { data }", "E_NAME"),
        (
            "let seed: Int = value { 40 };",
            "let seed: Int = value { let f: Fn<Int, Int> = fn(x: Int) -> Int { if flag { x } else { 0 } }; f(40) };",
            "E_CAPTURE",
        ),
        (
            "if selected {",
            "if selected { let local: Int = value { 1 };",
            "E_NAME",
        ),
    ] {
        let mut changed = common::checked_replace(&valid, from, to);
        if to.contains("let local") {
            changed = common::checked_replace(&changed, "value { answer + 1 }", "value { local }");
        }
        rejected(&changed, code);
    }
    // The condition is false at run time; its true arm still needs independent
    // scalar and resource acceptance, including an unused local pure fragment.
    rejected(
        &valid.replace(
            "if selected {",
            "if selected { let invalid: Int = value { true };",
        ),
        "E_TYPE",
    );
    rejected(
        &valid.replace("fill(output, f64_bits(4607182418800017408));", ""),
        "E_RESOURCE_TYPE",
    );
    rejected(
        &valid.replace("let seed: Int", "let flag: Int"),
        "E_DUPLICATE",
    );
}

/// Asserts that `source` is rejected and that its first diagnostic line is
/// `expected` (`CODE: message prefix`) at the first occurrence of `marker` in
/// `main.vast`, with no wire error and no manifest position.
#[track_caller]
fn rejected_at(source: &str, marker: &str, expected: &str) {
    let output = check(&fixture(source));
    let stderr = common::expect_code(&output, expected.split(':').next().unwrap());
    let before = &source[..source.find(marker).expect("marker")];
    let line = before.matches('\n').count() + 1;
    let column = before.rsplit('\n').next().unwrap().chars().count() + 1;
    let first = stderr.lines().next().unwrap();
    assert!(
        first.contains(&format!("main.vast:{line}:{column}: {expected}")),
        "expected {expected} at {line}:{column}\n{stderr}"
    );
    assert!(!stderr.contains("E_PROTOCOL"), "{stderr}");
    assert!(!stderr.contains("Vastitas.toml:"), "{stderr}");
}

/// The wire carries only `Nat`, `Int`, `Bool`, `Unit`, `Pair<Nat>` and
/// `Pair<Int>` in the scalar positions of a resource function. Another type
/// there is a diagnostic at the type (#702). It used to reach the kernel's
/// decoder and come back as `E_PROTOCOL` at the first character of the
/// manifest.
#[test]
fn scalar_positions_report_other_types_at_the_type() {
    const VALUE: &str = "E_RESOURCE_VALUE: resource values require Nat, Int, Bool or Unit";
    const RESULT: &str =
        "E_TYPE: resource result types require Nat, Int, Bool, Unit, Pair<Nat>, or Pair<Int>";
    const PARAMETER: &str = "E_TYPE: resource parameters require Nat/Int/Bool/Unit values";
    for ty in [
        "Fn<Int, Int>",
        "Fn<(Int, Bool), Fn<Int, Int>>",
        "Scheme",
        "CInfScheme",
        "Point<X, Base(QQ)>",
        "Morphism<X, Y>",
        "Pointed<Scheme, QQ>",
        "Object<Domain, Marker>",
        "Family<X>",
        "profile::Family<X, 2>",
    ] {
        let binding = format!(
            "resource fn main() -> Int {{\n    let bound: {ty} = value {{ 1 }};\n    value {{ 42 }}\n}}\n"
        );
        rejected_at(&binding, ty, VALUE);
        let call = format!(
            "resource fn callee() -> Int {{ value {{ 1 }} }}\nresource fn main() -> Int {{\n    let bound: {ty} = call callee() -> ();\n    value {{ 42 }}\n}}\n"
        );
        rejected_at(&call, ty, VALUE);
        let result = format!(
            "resource fn helper() -> {ty} {{\n    value {{ 1 }}\n}}\nfn main() -> Int {{ 42 }}\n"
        );
        rejected_at(&result, ty, RESULT);
    }
    // A type closer may touch the `=` of the binding.
    rejected_at(
        "resource fn main() -> Int {\n    let bound: Fn<Int, Int>= value { 1 };\n    value { 42 }\n}\n",
        "Fn<Int, Int>",
        VALUE,
    );
    // A scalar name can begin an indexed path, in a parameter too.
    for ty in ["Nat::Family<X>", "Unit::Family<X>"] {
        let parameter = format!(
            "resource fn helper(x: {ty}) -> Int {{ value {{ 1 }} }}\nfn main() -> Int {{ 42 }}\n"
        );
        rejected_at(&parameter, ty, PARAMETER);
        let binding = format!(
            "resource fn main() -> Int {{\n    let bound: {ty} = value {{ 1 }};\n    value {{ 42 }}\n}}\n"
        );
        rejected_at(&binding, ty, VALUE);
    }
    // Every type that the decoder admits still checks through the kernel.
    for (ty, value) in [
        ("Nat", "1"),
        ("Int", "1"),
        ("Bool", "true"),
        ("Unit", "()"),
        ("Pair<Nat>", "let a: Nat = 1; let b: Nat = 2; pair(a, b)"),
        ("Pair<Int>", "pair(1, 2)"),
    ] {
        let result = format!(
            "resource fn helper() -> {ty} {{ value {{ {value} }} }}\nresource fn main() -> Int {{\n    call helper() -> ();\n    value {{ 42 }}\n}}\n"
        );
        success(&check(&fixture(&result)));
        let binding = format!(
            "resource fn main() -> Int {{\n    let bound: {ty} = value {{ {value} }};\n    value {{ 42 }}\n}}\n"
        );
        if ty.starts_with("Pair") {
            // The kernel decides where a pair is valid: not in a binding.
            rejected_at(&binding, "let bound", VALUE);
        } else {
            success(&check(&fixture(&binding)));
        }
    }
}

#[test]
fn forged_value_wire_cannot_bypass_scalar_audits_or_legacy_envelopes() {
    let raw = request(&fixture(&source(false)));
    let accepted = kernel(&raw, "check");
    assert_eq!(accepted["ok"], true, "{accepted}");
    let base = "/packages/0/modules/0/resource_functions";
    for (path, value, code) in [
        (
            "/0/parameters/0/type",
            json!({"kind":"pair","element":"Int"}),
            "E_RESOURCE_VALUE",
        ),
        (
            "/0/parameters/0/type",
            json!({"kind":"function","params":[],"return_type":{"kind":"named","name":"Bool"}}),
            "E_PROTOCOL",
        ),
        (
            "/3/body/4/type",
            json!({"kind":"named","name":"Int"}),
            "E_RESOURCE_VALUE",
        ),
        // The frontend sends no other type in a scalar position (#702); the
        // decoder still refuses one in a binding, a call binding and a result.
        (
            "/3/body/0/type",
            json!({"kind":"function","params":[],"return_type":{"kind":"named","name":"Bool"}}),
            "E_PROTOCOL",
        ),
        (
            "/3/body/4/type",
            json!({"kind":"named","name":"Scheme"}),
            "E_PROTOCOL",
        ),
        (
            "/3/value_type",
            json!({"kind":"function","params":[],"return_type":{"kind":"named","name":"Int"}}),
            "E_PROTOCOL",
        ),
        ("/3/body/6/condition", json!("seed"), "E_RESOURCE_VALUE"),
        (
            "/3/body/0/body/result",
            json!({"kind":"variable","name":"data","span":functions(&raw)[3]["body"][0]["body"]["result"]["span"]}),
            "E_NAME",
        ),
        ("/0/body/2/yes", json!([]), "E_RESOURCE_TYPE"),
    ] {
        let mut forged = raw.clone();
        *forged.pointer_mut(&format!("{base}{path}")).unwrap() = value;
        let response = kernel(forged, "emit");
        common::assert_wire_rejected(&response, code);
    }
    for (path, key, value) in [
        ("/3/body/0", "checked", json!(true)),
        ("/3/body/4", "target", json!(0)),
        ("/3/body/6", "condition", json!(false)),
    ] {
        let mut forged = raw.clone();
        forged.pointer_mut(&format!("{base}{path}")).unwrap()[key] = value;
        let response = kernel(forged, "emit");
        assert_eq!(response["ok"], false, "accepted {path}/{key}: {response}");
        assert_eq!(response["diagnostics"][0]["code"], "E_PROTOCOL");
    }
    for version in 2..8 {
        let mut old = raw.clone();
        old["version"] = json!(version);
        common::assert_wire_rejected(&kernel(old, "check"), "E_PROTOCOL");
    }
    let mut deep = raw.clone();
    let mut expression = functions(&raw)[3]["body"][0]["body"]["result"].clone();
    let span = expression["span"].clone();
    let limits: Value =
        serde_json::from_str(include_str!("../lean-kernel/compiler-limits.json")).unwrap();
    for _ in 0..limits["sourceNesting"].as_u64().unwrap() {
        expression = json!({"kind":"unary", "op":"!", "operand":expression, "span":span});
    }
    *deep
        .pointer_mut(&format!("{base}/3/body/0/body/result"))
        .unwrap() = expression;
    let response = kernel(deep, "emit");
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(response["diagnostics"][0]["code"], "E_PROTOCOL");
    assert!(
        response["diagnostics"][0]["message"]
            .as_str()
            .unwrap()
            .contains("IR nesting exceeds"),
        "{response}"
    );
    assert!(response.get("lean_source").is_none());
}

const RECURSION: &str = "resource fn leaf(n: Nat) -> Nat { value { n } }
resource fn ping(n: Nat) -> Nat {
    let m: Nat = call pong(n) -> ();
    value { m }
}
resource fn pong(n: Nat) -> Nat {
    let m: Nat = call leaf(n) -> ();
    value { m }
}
resource fn main() -> Int {
    let n: Nat = value { 1 };
    let m: Nat = call ping(n) -> ();
    value { 42 }
}";

// #557: E_RESOURCE_RECURSION on the public CLI and v8 wire paths, not only in
// the internal FunctionRegression fixture.
#[test]
fn public_resource_function_recursion_is_rejected_directly_mutually_and_unused() {
    success(&check(&fixture(RECURSION)));
    let mutual = common::checked_replace(RECURSION, "call leaf(n)", "call ping(n)");
    let direct = common::checked_replace(RECURSION, "call pong(n)", "call ping(n)");
    // An uncalled body is still audited.
    let unused = format!(
        "{RECURSION}\nresource fn unused(n: Nat) -> Nat {{\n    let m: Nat = call unused(n) -> ();\n    value {{ m }}\n}}"
    );
    for source in [&mutual, &direct, &unused] {
        let output = check(&fixture(source));
        let error = common::expect_code(&output, "E_RESOURCE_RECURSION");
        assert!(
            error.contains("resource functions cannot recurse"),
            "{error}"
        );
    }
    let raw = request(&fixture(RECURSION));
    assert_eq!(raw["version"], 8);
    assert_eq!(kernel(&raw, "check")["ok"], true);
    for (caller, callee) in [("ping", "ping"), ("pong", "ping")] {
        let mut forged = raw.clone();
        let call = forged["packages"][0]["modules"][0]["resource_functions"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|function| function["name"] == caller)
            .unwrap()["body"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|statement| statement["kind"] == "call_value")
            .unwrap();
        call["callee"] = json!(callee);
        common::assert_wire_rejected(&kernel(forged, "emit"), "E_RESOURCE_RECURSION");
    }
}
