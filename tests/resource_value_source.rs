mod common;

use common::{Scratch, cli, kernel, success};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;
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
    let capture = scratch.write(
        "capture",
        "#!/bin/sh\ncat > \"$(dirname \"$0\")/wire.json\"\nprintf '%s\\n' '{\"version\":8,\"ok\":false,\"diagnostics\":[{\"code\":\"E_CAPTURED\",\"message\":\"captured\"}]}'\nexit 1\n",
    );
    std::fs::set_permissions(&capture, std::fs::Permissions::from_mode(0o755)).unwrap();
    let result = cli()
        .env("VASTITAS_KERNEL", capture)
        .args(["check", "--manifest-path"])
        .arg(scratch.0.join("Vastitas.toml"))
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&result.stderr).contains("E_CAPTURED"),
        "{result:?}"
    );
    serde_json::from_slice(&std::fs::read(scratch.0.join("wire.json")).unwrap()).unwrap()
}

fn functions(raw: &Value) -> &Value {
    &raw["packages"][0]["modules"][0]["resource_functions"]
}

fn rejected(source: &str) {
    let output = check(&fixture(source));
    assert!(
        !output.status.success(),
        "accepted invalid source: {source}"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("E_"),
        "missing diagnostic: {output:?}"
    );
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
    rejected(&source.replace(
        "call pair_result() -> ();",
        "let result: Pair<Int> = call pair_result() -> ();",
    ));
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
    assert!(String::from_utf8_lossy(&output.stderr).contains("E_NATIVE_EXPECT"));
}

#[test]
fn scalar_value_flow_rejects_captures_types_scope_leaks_and_untaken_errors() {
    let valid = source(false);
    for (from, to) in [
        (
            "let seed: Int = value { 40 };",
            "let seed: Int = value { true };",
        ),
        (
            "let selected: Bool = call choose",
            "let selected: Int = call choose",
        ),
        (
            "choose(flag, n, seed, token)",
            "choose(seed, n, seed, token)",
        ),
        ("if selected {", "if seed {"),
        ("value { answer + 1 }", "value { data }"),
        (
            "let seed: Int = value { 40 };",
            "let seed: Int = value { let f: Fn<Int, Int> = fn(x: Int) -> Int { if flag { x } else { 0 } }; f(40) };",
        ),
        (
            "if selected {",
            "if selected { let local: Int = value { 1 };",
        ),
    ] {
        let mut changed = valid.replace(from, to);
        if to.contains("let local") {
            changed = changed.replace("value { answer + 1 }", "value { local }");
        }
        rejected(&changed);
    }
    // The condition is false at run time; its true arm still needs independent
    // scalar and resource acceptance, including an unused local pure fragment.
    rejected(&valid.replace(
        "if selected {",
        "if selected { let invalid: Int = value { true };",
    ));
    rejected(&valid.replace("fill(output, f64_bits(4607182418800017408));", ""));
    rejected(&valid.replace("let seed: Int", "let flag: Int"));
}

#[test]
fn forged_value_wire_cannot_bypass_scalar_audits_or_legacy_envelopes() {
    let raw = request(&fixture(&source(false)));
    let accepted = kernel(&raw, "check");
    assert_eq!(accepted["ok"], true, "{accepted}");
    let base = "/packages/0/modules/0/resource_functions";
    for (path, value) in [
        (
            "/0/parameters/0/type",
            json!({"kind":"pair","element":"Int"}),
        ),
        (
            "/0/parameters/0/type",
            json!({"kind":"function","params":[],"return_type":{"kind":"named","name":"Bool"}}),
        ),
        ("/3/body/4/type", json!({"kind":"named","name":"Int"})),
        ("/3/body/6/condition", json!("seed")),
        (
            "/3/body/0/body/result",
            json!({"kind":"variable","name":"data","span":functions(&raw)[3]["body"][0]["body"]["result"]["span"]}),
        ),
        ("/0/body/2/yes", json!([])),
    ] {
        let mut forged = raw.clone();
        *forged.pointer_mut(&format!("{base}{path}")).unwrap() = value;
        let response = kernel(forged, "emit");
        assert_eq!(response["ok"], false, "accepted {path}: {response}");
        assert!(response.get("lean_source").is_none(), "{response}");
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
        assert_eq!(kernel(old, "check")["ok"], false, "version {version}");
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
