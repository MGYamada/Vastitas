use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/lean_audit/proj_from_prop.ndjson")
}

fn run_audit(path: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_vastitas"))
        .arg("audit-lean")
        .arg(path)
        .output()
        .expect("run Vastitas audit-lean")
}

fn temporary_export(contents: &str) -> (PathBuf, Output) {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "vastitas-nanoda-{}-{nanos}.ndjson",
        std::process::id()
    ));
    fs::write(&path, contents).expect("write temporary Lean export");
    let output = run_audit(&path);
    fs::remove_file(&path).expect("remove temporary Lean export");
    (path, output)
}

fn rejected(output: &Output) -> String {
    assert!(!output.status.success(), "unexpected success: {output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        stderr.contains("E_LEAN_AUDIT"),
        "audit rejection did not reach the parent driver: {stderr}"
    );
    stderr
}

#[test]
fn checked_export_returns_internal_only_receipt() {
    let output = run_audit(&fixture());
    assert!(
        output.status.success(),
        "nanoda rejected reference fixture: {output:?}"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("internal-only Lean audit passed"));
    assert!(stdout.contains("NOT official Lean-kernel verification"));
    assert!(stdout.contains("no Vastitas Core or constitutional acceptance"));
}

#[test]
fn invalid_proof_term_is_rejected_without_crashing_the_parent() {
    // Change an actual definition's lambda to a constant of the wrong type.
    let original = include_str!("fixtures/lean_audit/proj_from_prop.ndjson");
    let modified = original.replacen(
        r#""type":37,"value":45}}"#,
        r#""type":37,"value":38}}"#,
        1,
    );
    assert_ne!(original, modified);
    rejected(&temporary_export(&modified).1);
}

#[test]
fn undeclared_axiom_is_a_hard_error_even_if_unused() {
    let original = include_str!("fixtures/lean_audit/proj_from_prop.ndjson");
    let header = original.lines().next().unwrap();
    let input = [
        header,
        r#"{"in":1,"str":{"pre":0,"str":"NotPermitted"}}"#,
        r#"{"ie":0,"sort":0}"#,
        r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
    ]
    .join("\n");
    let stderr = rejected(&temporary_export(&input).1);
    assert!(stderr.contains("unpermitted axiom"), "{stderr}");
}

#[test]
fn malformed_and_empty_exports_are_rejected() {
    rejected(&temporary_export("not-json\n").1);
    let original = include_str!("fixtures/lean_audit/proj_from_prop.ndjson");
    rejected(&temporary_export(original.lines().next().unwrap()).1);
}

#[test]
fn ordinary_compiler_help_is_unchanged() {
    let output = Command::new(env!("CARGO_BIN_EXE_vastitas"))
        .args([OsStr::new("check"), OsStr::new("--help")])
        .output()
        .expect("run Vastitas check help");
    assert!(output.status.success());
    assert!(String::from_utf8_lossy(&output.stdout).contains("vastitas check INPUT.vast"));
}
