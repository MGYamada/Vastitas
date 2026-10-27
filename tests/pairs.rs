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
