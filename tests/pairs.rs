//! Pair values cross the frontend, independently checked core and native runtime.
use serde_json::{Value, json};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static SERIAL: AtomicU64 = AtomicU64::new(0);
struct Scratch(PathBuf);
impl Scratch {
    fn new(source: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "vastitas-pairs-{}-{}",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("main.vast"), source).unwrap();
        fs::write(
            path.join("Vastitas.toml"),
            "[package]\nname='pairs'\nversion='0.1.0'\nroot='main.vast'\n",
        )
        .unwrap();
        Self(path)
    }
    fn cli(&self, mode: &str, package: bool) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_vastitas"));
        command.current_dir(&self.0).arg(mode);
        if package {
            command.args(["--manifest-path", "Vastitas.toml"]);
        } else {
            command.arg("main.vast");
        }
        command
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn success(output: Output) {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
fn request(source: &str) -> Value {
    serde_json::to_value(vastitas::frontend::parse(source, "pairs.vast").unwrap()).unwrap()
}
fn backend(raw: &Value) -> Value {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("lean-kernel/.lake/build/bin/vastitas-kernel");
    let mut child = Command::new(path)
        .arg("check")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(&serde_json::to_vec(raw).unwrap())
        .unwrap();
    serde_json::from_slice(&child.wait_with_output().unwrap().stdout).unwrap()
}
fn rejects(raw: Value) {
    let result = backend(&raw);
    assert_eq!(result["ok"], false, "{result}");
}

#[test]
fn pairs_preserve_values_arguments_results_branches_and_lambda_bodies() {
    let scratch = Scratch::new(include_str!("../examples/pairs.vast"));
    for package in [false, true] {
        success(scratch.cli("check", package).output().unwrap());
        success(
            scratch
                .cli("build", package)
                .args(["-o", "program"])
                .output()
                .unwrap(),
        );
        let output = Command::new(scratch.0.join("program")).output().unwrap();
        assert_eq!(output.stdout, b"42\n");
        success(output);
    }
    let first_order =
        request("fn reverse(p: Pair<Int>) -> Pair<Int> { pair(pair_second(p), pair_first(p)) }");
    assert_eq!(
        first_order["functions"][0]["return_type"],
        json!({"kind":"pair","element":"Int"})
    );
    assert_eq!(backend(&first_order)["ok"], true);
}

#[test]
fn pair_construction_infers_operands_without_conversion_or_expected_type_selection() {
    for source in [
        "fn f() -> Pair<Nat> { pair(1, 2) }",
        "fn f(n: Nat) -> Pair<Int> { pair(n, 2) }",
        "fn f() -> Pair<Int> { pair(true, false) }",
        "fn f() -> Pair<Int> { pair((), ()) }",
        "fn f() -> Pair<Int> { pair(pair(1, 2), pair(3, 4)) }",
        "fn f() -> Pair<Int> { let x = Affine(QQ, 1); pair(x, x) }",
        "fn f() -> Pair<Int> { pair(1) }",
        "fn f() -> Int { pair_first(1) }",
        "fn f() -> Int { pair_second(pair(1, 2), 3) }",
        "fn f(n: Nat) -> Pair<Int> { if true { pair(n, n) } else { pair(1, 2) } }",
        "fn f(p: Fn<Pair<Int>, Int>) -> Int { 0 }",
        "fn f() -> Int { let p = fn() -> Pair<Int> { pair(1, 2) }; 0 }",
    ] {
        let scratch = Scratch::new(source);
        let output = scratch.cli("check", false).output().unwrap();
        assert!(!output.status.success(), "accepted: {source}");
        let error = String::from_utf8_lossy(&output.stderr);
        assert!(
            error.contains("E_TYPE") || error.contains("E_ARITY"),
            "{source}: {error}"
        );
        rejects(request(source));
    }
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
        let mut raw = request("fn f() -> Pair<Int> { pair(1, 2) }");
        raw["functions"][0]["return_type"]["element"] = json!(element);
        rejects(raw);
    }
    let mut raw = request("fn f() -> Pair<Int> { pair(1, 2) }");
    raw["functions"][0]["return_type"]["element"] = json!({"kind":"named","name":"Int"});
    rejects(raw);
    for field in ["domain", "selector", "result"] {
        let mut raw = request("generic f(x) { domain (Int); } method f(x: Int) -> Int { 0 }");
        let pair = json!({"kind":"pair","element":"Int"});
        match field {
            "domain" => raw["generics"][0]["domain"][0][0] = pair,
            "selector" => raw["methods"][0]["params"][0]["ty"] = pair,
            _ => raw["methods"][0]["return_type"] = pair,
        }
        rejects(raw);
    }
    for source in [
        "fn f(p: Pair<Bool>) -> Int { 0 }",
        "fn f(p: Pair<Pair<Int>>) -> Int { 0 }",
    ] {
        assert!(vastitas::frontend::parse(source, "pair.vast").is_err());
    }
}

const PAIR_METHODS: &str = "
generic choose(x, y) { domain (Nat, Nat), (Nat, Int), (Int, Nat), (Int, Int); }
method choose(x: Nat, y: Nat) -> Pair<Nat> { pair(x, y) }
method choose(x: Nat, y: Int) -> Pair<Int> { pair(int(x), y) }
method choose(x: Int, y: Nat) -> Pair<Int> { pair(x, int(y)) }
method choose(x: Int, y: Int) -> Pair<Int> { pair(x, y) }
";

#[test]
fn selected_pair_results_flow_to_projections_and_downstream_dispatch() {
    let caller = "
generic scalar(x) { domain (Nat), (Int); }
method scalar(x: Nat) -> Int { int(x) }
method scalar(x: Int) -> Int { x }
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
    // Force both the legacy and function-containing lowering paths.
    for extra in [
        "",
        "fn unused() -> Int { let f = fn(x: Int) -> Int { pair_first(choose(x, x)) }; f(1) }",
    ] {
        let source = format!("{PAIR_METHODS}\n{caller}\n{extra}");
        assert_eq!(backend(&request(&source))["ok"], true);
        let scratch = Scratch::new(&source);
        for package in [false, true] {
            success(scratch.cli("check", package).output().unwrap());
            success(
                scratch
                    .cli("build", package)
                    .args(["-o", "program"])
                    .output()
                    .unwrap(),
            );
            let output = Command::new(scratch.0.join("program")).output().unwrap();
            assert_eq!(output.stdout, b"42\n");
            success(output);
        }
    }
}

#[test]
fn pair_results_do_not_change_selection_or_whole_body_audits() {
    let cases = [
        (format!("{PAIR_METHODS} fn bad(n: Nat) -> Pair<Nat> {{ choose(n, 2) }}"), "E_TYPE"),
        (format!("{PAIR_METHODS} fn bad() -> Pair<Nat> {{ choose(1, 2) }}"), "E_TYPE"),
        (format!("{PAIR_METHODS} method choose(x: Number, y: Number) -> Pair<Int> {{ pair(x, y) }}"), "E_TYPE"),
        ("generic g(x) { domain (Int); } method g(x: Int) -> Pair<Int> { pair(x, x) } method g(x: Any) -> Pair<Int> { pair(x, x) }".into(), "E_TYPE"),
        ("generic g(x) { domain (Int); } method g(x: Int) -> Pair<Int> { pair(x, x) } method g(x: Int) -> Int { x }".into(), "E_DUPLICATE"),
        ("generic g(x) { domain (Int), (Nat); } method g(x: Int) -> Pair<Int> { pair(x, x) }".into(), "E_DISPATCH_COVERAGE"),
        ("generic g(x, y) { domain (Nat, Nat); } method g(x: Nat, y: Number) -> Pair<Int> { pair(1, 2) } method g(x: Number, y: Int) -> Int { 0 }".into(), "E_DISPATCH_AMBIGUOUS"),
    ];
    for (source, expected) in cases {
        for extra in [
            "",
            "fn probe() -> Int { let f = fn(x: Int) -> Int { x }; f(0) }",
        ] {
            let source = format!("{source}\n{extra}");
            let response = backend(&request(&source));
            assert_eq!(response["ok"], false, "{source}: {response}");
            assert!(
                response.to_string().contains(expected),
                "{source}: {response}"
            );
            let scratch = Scratch::new(&source);
            for package in [false, true] {
                let output = scratch.cli("check", package).output().unwrap();
                assert!(!output.status.success());
                assert!(
                    String::from_utf8_lossy(&output.stderr).contains(expected),
                    "{source}: {output:?}"
                );
            }
        }
    }
    // A losing method may return a different type when its own body is valid.
    let valid = "generic g(x) { domain (Int); } method g(x: Int) -> Pair<Int> { pair(x, x) } method g(x: Number) -> Bool { true } fn main() -> Int { pair_first(g(42)) }";
    assert_eq!(backend(&request(valid))["ok"], true);
}
