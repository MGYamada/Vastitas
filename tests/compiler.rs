//! End-to-end tests require `lake -d lean-kernel build vastitas-kernel` first.
use serde_json::{Value, json};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static SERIAL: AtomicU64 = AtomicU64::new(0);

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "vastitas tests {} {}",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn source(&self, text: &str) -> PathBuf {
        let file = self.0.join("input file.vast");
        fs::write(&file, text).unwrap();
        file
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}
fn cli() -> Command {
    Command::new(env!("CARGO_BIN_EXE_vastitas"))
}
fn assert_success(output: &Output) {
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
fn check(source: &str) -> Output {
    let scratch = Scratch::new();
    cli()
        .arg("check")
        .arg(scratch.source(source))
        .output()
        .unwrap()
}
fn reject(source: &str, expected: &str) {
    let result = check(source);
    assert!(
        !result.status.success(),
        "accepted invalid source: {source}"
    );
    let message = String::from_utf8_lossy(&result.stderr);
    assert!(
        message.contains(expected),
        "expected {expected:?}: {message}"
    );
    assert!(
        message.contains("input file.vast:"),
        "missing source location: {message}"
    );
}
fn native(source: &str, expected: &str) {
    let scratch = Scratch::new();
    let file = scratch.source(source);
    let output = scratch.0.join("native program");
    let result = cli()
        .arg("build")
        .arg(file)
        .arg("-o")
        .arg(&output)
        .output()
        .unwrap();
    assert_success(&result);
    let result = Command::new(&output).output().unwrap();
    assert_success(&result);
    assert_eq!(
        String::from_utf8(result.stdout).unwrap(),
        format!("{expected}\n")
    );
}
fn kernel(request: Value, mode: &str) -> Value {
    let path = root().join("lean-kernel/.lake/build/bin/vastitas-kernel");
    assert!(
        path.is_file(),
        "Build backend first: lake -d lean-kernel build vastitas-kernel"
    );
    let mut child = Command::new(path)
        .arg(mode)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(serde_json::to_string(&request).unwrap().as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "invalid response: {error}; {}",
            String::from_utf8_lossy(&output.stderr)
        )
    })
}
fn request(source: &str) -> Value {
    serde_json::to_value(vastitas::frontend::parse(source, "forged.vast").unwrap()).unwrap()
}
fn assert_rejected(value: Value) {
    let result = kernel(value, "emit");
    assert_eq!(result["ok"], false, "backend accepted forged IR: {result}");
    assert!(result.get("lean_source").is_none());
    assert!(!result["diagnostics"].as_array().unwrap().is_empty());
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
        "E_",
    );
}

#[test]
fn mixed_settings_and_wrong_test_objects_are_rejected() {
    reject(
        "fn main() -> Int { let X: Scheme = Affine(CInfReal, 2); 0 }",
        "E_",
    );
    reject(
        "fn main() -> Int { let X = Affine(QQ, 2); let S = Affine(QQ, 0); let p: Point<X, S> = origin(X); 0 }",
        "E_",
    );
    reject(
        "fn main() -> Int { let X = Affine(QQ, 2); let p: Point<X, Base(CInfReal)> = origin(X); 0 }",
        "E_",
    );
}

#[test]
fn dependent_arguments_are_substituted() {
    reject(
        "fn keep(X: Scheme, p: Point<X, Base(QQ)>) -> Point<X, Base(QQ)> { p } fn main() -> Int { let A = Affine(QQ, 2); let B = Affine(QQ, 2); let p = keep(A, origin(B)); 0 }",
        "E_",
    );
    assert_success(&check(
        "fn keep(X: Scheme, p: Point<X, Base(QQ)>) -> Point<X, Base(QQ)> { p } fn main() -> Int { let A = Affine(QQ, 2); let p: Point<A, Base(QQ)> = keep(A, origin(A)); 0 }",
    ));
}

#[test]
fn mismatched_morphism_endpoints_are_rejected() {
    reject(
        "fn main() -> Int { let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let f = compose(id(X), id(Y)); 0 }",
        "E_",
    );
    reject(
        "fn main() -> Int { let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let p = apply(id(X), origin(Y)); 0 }",
        "E_",
    );
}

#[test]
fn package_cannot_lie_about_its_point_or_base() {
    reject(
        "fn make() -> Pointed<Scheme, QQ> { let X = Affine(QQ, 2); let Y = Affine(QQ, 2); pack { scheme: X, point: origin(Y) } }",
        "E_",
    );
    reject(
        "fn make() -> Pointed<Scheme, CInfReal> { let X = Affine(QQ, 2); pack { scheme: X, point: origin(X) } }",
        "E_",
    );
}

#[test]
fn unsealed_local_point_cannot_escape_a_block() {
    reject(
        "fn main() -> Int { let p = { let X = Affine(QQ, 2); origin(X) }; 0 }",
        "E_",
    );
}

#[test]
fn independent_openings_do_not_share_a_nominal_identity() {
    reject(
        "fn main() -> Int { let X = Affine(QQ, 2); let q = pack { scheme: X, point: origin(X) }; unpack q as { scheme: A, point: a }; unpack q as { scheme: B, point: b }; let p: Point<A, Base(QQ)> = b; 0 }",
        "E_",
    );
}

#[test]
fn scalar_coercions_and_geometry_equality_are_rejected() {
    reject("fn main() -> Int { let n: Nat = 1; n }", "E_");
    reject(
        "fn main() -> Int { let X = Affine(QQ, 1); if X == X { 1 } else { 0 } }",
        "E_",
    );
}

#[test]
fn library_check_does_not_require_an_entrypoint_but_build_does() {
    let source = "fn f(x: Int) -> Int { x + 1 }";
    assert_success(&check(source));
    assert_rejected(request(source));
}

#[test]
fn malformed_ir_version_type_binding_and_literal_are_rejected() {
    let original = request("fn main() -> Int { 1 }");
    let mut value = original.clone();
    value["version"] = json!(2);
    assert_rejected(value);
    let mut value = original.clone();
    value["functions"][0]["return_type"] = json!({"kind":"named", "name":"Bool"});
    assert_rejected(value);
    let mut value = original.clone();
    value["functions"][0]["body"]["result"]["kind"] = json!("variable");
    value["functions"][0]["body"]["result"]["name"] = json!("forged");
    assert_rejected(value);
    let mut value = original.clone();
    value["functions"][0]["body"]["result"]["value"] = json!("1); IO.println 99");
    assert_rejected(value);
    let mut value = original;
    value["functions"][0]["body"]["result"]["kind"] = json!("unsupported_operation");
    assert_rejected(value);
}

#[test]
fn backend_checks_forged_endpoint_annotations_and_recursion() {
    let mut value = request(
        "fn main() -> Int { let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let p: Point<X, Base(QQ)> = origin(X); 0 }",
    );
    value["functions"][0]["body"]["statements"][2]["annotation"]["target"]["name"] = json!("Y");
    assert_rejected(value);
    let mut value = request("fn main() -> Int { 1 }");
    value["functions"][0]["body"]["result"] = json!({"kind":"call", "callee":"main", "args":[], "span":{"start":0,"end":1,"line":1,"column":1}});
    assert_rejected(value);
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
