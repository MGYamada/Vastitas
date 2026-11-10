//! Shared process and filesystem harness. Each integration binary uses its own
//! subset; source names and package layouts are configured by its tests.
#![allow(dead_code)]
use serde_json::Value;
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

static SERIAL: AtomicU64 = AtomicU64::new(0);
pub struct Scratch(pub PathBuf);
impl Scratch {
    pub fn empty(prefix: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "vastitas {prefix} {} {}",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    pub fn write(&self, name: &str, source: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, source).unwrap();
        path
    }
    /// Writes package `name` as `<name>/Vastitas.toml` with root `main.vast`.
    pub fn write_package(&self, name: &str, source: &str, dependencies: &str) {
        self.write(
            &format!("{name}/Vastitas.toml"),
            &format!(
                "[package]\nname='{name}'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\n{dependencies}\n"
            ),
        );
        self.write(&format!("{name}/main.vast"), source);
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

pub fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}
pub fn prepare_stdlib_package() {
    static BUILD: std::sync::Once = std::sync::Once::new();
    BUILD.call_once(|| {
        success(
            &Command::new("python3")
                .arg(root().join("scripts/build_stdlib_package.py"))
                .output()
                .unwrap(),
        );
    });
}
pub fn cli() -> Command {
    Command::new(env!("CARGO_BIN_EXE_vastitas"))
}
pub fn success(output: &Output) {
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
pub fn kernel_path() -> PathBuf {
    root().join("lean-kernel/.lake/build/bin/vastitas-kernel")
}
/// The driver's own list of the files that a native build verifies in the
/// selected kernel root.
#[path = "../../src/runtime_inputs.rs"]
pub mod runtime_inputs;
/// Copies into `kernel_root` the runtime inputs that a native build verifies:
/// those of the kernel package and, when selected, of the storage (`native`)
/// and numerical packages. A scratch kernel root needs them even under a
/// mocked Lake. The caller writes `lean-toolchain`, which has its own check.
pub fn copy_runtime_inputs(kernel_root: &Path, storage: bool, numerical: bool) {
    use runtime_inputs::{ABSENT, KERNEL, NUMERICAL, STORAGE, inputs};
    let packages = [
        (&KERNEL, true),
        (&STORAGE, storage),
        (&NUMERICAL, numerical),
    ];
    for (package, _) in packages.iter().filter(|(_, selected)| *selected) {
        let source = package.directory_in(&root().join("lean-kernel"));
        let destination = package.directory_in(kernel_root);
        for (relative, digest) in inputs(&source, package).unwrap() {
            if digest != ABSENT {
                let target = destination.join(&relative);
                fs::create_dir_all(target.parent().unwrap()).unwrap();
                fs::copy(source.join(&relative), target).unwrap();
            }
        }
    }
}
/// The `kernel` build identity (JSON object text) that the built kernel reports
/// in every response. The driver rejects success responses without it, so mock
/// backends must echo it.
pub fn kernel_identity() -> String {
    static IDENTITY: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    IDENTITY
        .get_or_init(|| {
            let mut child = Command::new(kernel_path())
                .arg("check")
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .spawn()
                .expect("built kernel");
            child.stdin.take().unwrap().write_all(b"{}").unwrap();
            let output = child.wait_with_output().unwrap();
            let response: Value = serde_json::from_slice(&output.stdout).unwrap();
            assert!(response["kernel"].is_object(), "{response}");
            response["kernel"].to_string()
        })
        .clone()
}
pub fn check(source: &str, filename: &str) -> Output {
    let scratch = Scratch::empty("check");
    cli()
        .arg("check")
        .arg(scratch.write(filename, source))
        .output()
        .unwrap()
}
#[track_caller]
pub fn reject(source: &str, code: &str, filename: &str) -> String {
    let output = check(source, filename);
    assert!(
        !output.status.success(),
        "accepted invalid source: {source}"
    );
    let message = expect_code(&output, code);
    assert!(
        message.contains(&format!("{filename}:")),
        "missing source location: {message}"
    );
    message
}
/// The diagnostic codes in rendered compiler or executable output, in order.
/// A diagnostic line is `<path>:<line>:<column>: CODE: message`, `CODE: message`
/// or `<prefix>: CODE: message` (for example Lean's `uncaught exception:`).
/// Each line contributes at most its first code; notes (which may quote other
/// codes), usage text and message continuations contribute none.
pub fn diagnostic_codes(stderr: &str) -> Vec<String> {
    stderr
        .lines()
        .filter(|line| !line.starts_with("note: ") && !line.contains(": note: "))
        .filter_map(|line| {
            let starts = std::iter::once(0).chain(line.match_indices(": ").map(|(at, _)| at + 2));
            starts
                .filter_map(|start| {
                    let rest = &line[start..];
                    let end = rest
                        .find(|c: char| !(c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_'))
                        .unwrap_or(rest.len());
                    let code = &rest[..end];
                    (code.len() > 2 && code.starts_with("E_") && rest[end..].starts_with(": "))
                        .then(|| code.to_string())
                })
                .next()
        })
        .collect()
}
/// Asserts that `output` failed and that its first diagnostic code is exactly
/// `code`. A substring match would let `E_TYPE` accept `E_RESOURCE_TYPE` and an
/// unrelated parse error accept any expected rejection. Returns stderr.
#[track_caller]
pub fn expect_code(output: &Output, code: &str) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        !output.status.success(),
        "expected {code}, but the command succeeded\nstdout:\n{}\nstderr:\n{stderr}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_first_code(&stderr, code);
    stderr
}
/// Asserts that the first diagnostic code in rendered output is exactly `code`.
#[track_caller]
pub fn assert_first_code(stderr: &str, code: &str) {
    let codes = diagnostic_codes(stderr);
    assert_eq!(
        codes.first().map(String::as_str),
        Some(code),
        "expected first diagnostic {code}; found {codes:?}\nstderr:\n{stderr}"
    );
}
/// Like [`expect_code`], for `expected` written as `CODE` or `CODE: message
/// prefix`: the code must match exactly and the whole text must appear.
#[track_caller]
pub fn expect_diagnostic(output: &Output, expected: &str) -> String {
    let code = expected.split(':').next().unwrap();
    let stderr = expect_code(output, code);
    assert!(stderr.contains(expected), "expected {expected:?}: {stderr}");
    stderr
}
/// Asserts that a kernel response is a failure whose first diagnostic has
/// exactly `code` and that no generated Lean source escaped with it.
#[track_caller]
pub fn assert_wire_rejected(response: &Value, code: &str) {
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(response["diagnostics"][0]["code"], code, "{response}");
    assert!(response.get("lean_source").is_none(), "{response}");
}
/// True when `variable=1` asks a golden test to rewrite its fixture. Refused
/// under CI: the test would then compare the fixture only with itself.
pub fn regenerate_fixture(variable: &str) -> bool {
    let requested = std::env::var_os(variable).as_deref() == Some(std::ffi::OsStr::new("1"));
    assert!(
        !(requested && std::env::var_os("CI").is_some()),
        "{variable}=1 is refused under CI; regenerate fixtures locally and commit them"
    );
    requested
}
/// Replaces `from` with `to`, failing if `from` is absent. A silent no-op
/// replacement would turn a mutation or equivalence test vacuous.
#[track_caller]
pub fn checked_replace(source: &str, from: &str, to: &str) -> String {
    assert!(
        source.contains(from),
        "replacement target is absent: {from:?}"
    );
    source.replace(from, to)
}
/// Runs `command` against a capture backend and returns the exact wire request
/// the frontend sent. The stub answers with a protocol-`version` failure and
/// has no acceptance authority; callers mutate the captured wire and submit it
/// to the real kernel. The captured request must use `version`.
#[track_caller]
pub fn captured_wire(mut command: impl std::borrow::BorrowMut<Command>, version: u64) -> Value {
    use std::os::unix::fs::PermissionsExt;
    let capture = Scratch::empty("capture");
    let stub = capture.write(
        "capture",
        &format!(
            "#!/bin/sh\ncat > \"$(dirname \"$0\")/wire.json\"\nprintf '%s\\n' '{{\"version\":{version},\"ok\":false,\"diagnostics\":[{{\"code\":\"E_CAPTURED\",\"message\":\"captured\"}}]}}'\nexit 1\n"
        ),
    );
    fs::set_permissions(&stub, fs::Permissions::from_mode(0o755)).unwrap();
    let output = command
        .borrow_mut()
        .env("VASTITAS_KERNEL", &stub)
        .output()
        .unwrap();
    let stderr = expect_code(&output, "E_CAPTURED");
    assert!(
        !stderr.contains("incompatible backend protocol version"),
        "captured request does not use protocol {version}: {stderr}"
    );
    let wire: Value = serde_json::from_slice(&fs::read(capture.0.join("wire.json")).unwrap())
        .expect("captured wire request");
    assert_eq!(wire["version"], version, "captured protocol version");
    wire
}
pub fn native(source: &str, libraries: &[PathBuf], expected: &str, filename: &str) {
    let scratch = Scratch::empty("native");
    let output_path = scratch.0.join("native program");
    let mut command = cli();
    command
        .arg("build")
        .arg(scratch.write(filename, source))
        .arg("-o")
        .arg(&output_path);
    for library in libraries {
        command.arg("--lib").arg(library);
    }
    success(&command.output().unwrap());
    let output = Command::new(output_path).output().unwrap();
    success(&output);
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        format!("{expected}\n")
    );
}
pub fn request(source: &str, filename: &str) -> Value {
    serde_json::to_value(vastitas::frontend::parse(source, filename).unwrap()).unwrap()
}
/// The definitions of an emitted Lean module in order, as `(name, text)`
/// pairs: each `def` runs to the next one, and the last to the end.
pub fn lean_definitions(source: &str) -> Vec<(&str, &str)> {
    let starts: Vec<usize> = source
        .match_indices("\ndef ")
        .map(|(at, _)| at + 1)
        .collect();
    starts
        .iter()
        .enumerate()
        .map(|(index, &start)| {
            let text = &source[start..starts.get(index + 1).copied().unwrap_or(source.len())];
            let name = text["def ".len()..].split([' ', '\n']).next().unwrap();
            (name, text)
        })
        .collect()
}
/// The id of a generated Lean function `f_<id>`.
pub fn lean_function_id(name: &str) -> Option<usize> {
    name.strip_prefix("f_")?.parse().ok()
}
/// The backward functions that the kernel generates for the reverse sites of
/// an emitted module (#623), given the number of source functions: the
/// definitions `f_<id>` with an id past every source function's. The test
/// fails unless they come first.
#[track_caller]
pub fn generated_reverse_functions(source: &str, functions: usize) -> Vec<(&str, &str)> {
    let definitions = lean_definitions(source);
    let generated = definitions
        .iter()
        .take_while(|(name, _)| lean_function_id(name).is_some_and(|id| id >= functions))
        .count();
    assert!(
        definitions[generated..]
            .iter()
            .all(|(name, _)| lean_function_id(name).is_none_or(|id| id < functions)),
        "generated functions must precede the source functions:\n{source}"
    );
    definitions[..generated].to_vec()
}
pub fn remove_spans(value: &mut Value) {
    match value {
        Value::Object(fields) => {
            fields.remove("span");
            for child in fields.values_mut() {
                remove_spans(child);
            }
        }
        Value::Array(items) => {
            for child in items {
                remove_spans(child);
            }
        }
        _ => {}
    }
}
pub fn assert_rejected(request: Value, code: &str) -> Value {
    let response = kernel(request, "emit");
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(response["diagnostics"][0]["code"], code, "{response}");
    assert!(response.get("lean_source").is_none(), "{response}");
    response
}
pub fn kernel(request: impl std::borrow::Borrow<Value>, mode: &str) -> Value {
    let path = kernel_path();
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
    let input = serde_json::to_vec(request.borrow()).unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let writer = std::thread::spawn(move || stdin.write_all(&input));
    let mut stdout = child.stdout.take().unwrap();
    let reader = std::thread::spawn(move || {
        let mut bytes = Vec::new();
        stdout.read_to_end(&mut bytes).unwrap();
        bytes
    });
    let mut stderr = child.stderr.take().unwrap();
    let errors = std::thread::spawn(move || {
        let mut bytes = Vec::new();
        stderr.read_to_end(&mut bytes).unwrap();
        bytes
    });
    let deadline = Instant::now() + Duration::from_secs(60);
    let timed_out = loop {
        if child.try_wait().unwrap().is_some() {
            break false;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            break true;
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let write_result = writer.join().unwrap();
    let stdout = reader.join().unwrap();
    let stderr = errors.join().unwrap();
    assert!(
        !timed_out,
        "kernel exceeded 60-second regression deadline: {}",
        String::from_utf8_lossy(&stderr)
    );
    write_result.unwrap();
    let response: Value = serde_json::from_slice(&stdout).unwrap_or_else(|error| {
        panic!(
            "invalid response: {error}; {}",
            String::from_utf8_lossy(&stderr)
        )
    });
    assert_eq!(
        child.wait().unwrap().success(),
        response["ok"] == true,
        "{response}"
    );
    response
}
