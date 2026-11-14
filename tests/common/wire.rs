//! Wire requests, the built kernel and the assertions on its responses.
use super::diagnostics::{assert_source_names, expect_code};
use super::process::{Scratch, root};
use super::runtime_inputs;
use serde_json::Value;
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

pub fn kernel_path() -> PathBuf {
    root().join("lean-kernel/.lake/build/bin/vastitas-kernel")
}
/// Copies into `kernel_root` the runtime inputs that a native build verifies:
/// those of the kernel package and, when selected, of the storage (`native`)
/// and numerical packages. A scratch kernel root needs them even under a
/// mocked Lake. The caller writes `lean-toolchain`, which has its own check.
pub fn copy_runtime_inputs(kernel_root: &Path, storage: bool, numerical: bool) {
    use runtime_inputs::{KERNEL, NUMERICAL, STORAGE, required_inputs};
    let packages = [
        (&KERNEL, true),
        (&STORAGE, storage),
        (&NUMERICAL, numerical),
    ];
    for (package, _) in packages.iter().filter(|(_, selected)| *selected) {
        let source = package.directory_in(&root().join("lean-kernel"));
        let destination = package.directory_in(kernel_root);
        for (relative, _) in required_inputs(&source, package).unwrap() {
            let target = destination.join(&relative);
            fs::create_dir_all(target.parent().unwrap()).unwrap();
            fs::copy(source.join(&relative), target).unwrap();
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
            let output = kernel_bytes("check", b"{}".to_vec());
            let response: Value = serde_json::from_slice(&output.stdout).unwrap();
            assert!(response["kernel"].is_object(), "{response}");
            response["kernel"].to_string()
        })
        .clone()
}
/// Asserts that a kernel response is a failure whose first diagnostic has
/// exactly `code` and that no generated Lean source escaped with it.
#[track_caller]
pub fn assert_wire_rejected(response: &Value, code: &str) {
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(response["diagnostics"][0]["code"], code, "{response}");
    assert!(response.get("lean_source").is_none(), "{response}");
    assert_source_names(&response["diagnostics"].to_string());
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
pub fn request(source: &str, filename: &str) -> Value {
    serde_json::to_value(vastitas::frontend::parse(source, filename).unwrap()).unwrap()
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
    assert_wire_rejected(&response, code);
    response
}
/// The response of the built kernel in `mode` to the wire request `request`,
/// whose success must agree with the exit status.
pub fn kernel(request: impl std::borrow::Borrow<Value>, mode: &str) -> Value {
    let output = kernel_bytes(mode, serde_json::to_vec(request.borrow()).unwrap());
    let response: Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "invalid response: {error}; {}",
            String::from_utf8_lossy(&output.stderr)
        )
    });
    assert_eq!(output.status.success(), response["ok"] == true, "{response}");
    response
}
/// Runs the built kernel in `mode` on the bytes `input`, as a tampered or
/// truncated request would arrive, under the 60-second regression deadline.
/// The input must be written whole; returns the exit status and both outputs.
pub fn kernel_bytes(mode: &str, input: Vec<u8>) -> Output {
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
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break Some(status);
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            break None;
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let write_result = writer.join().unwrap();
    let stdout = reader.join().unwrap();
    let stderr = errors.join().unwrap();
    let Some(status) = status else {
        panic!(
            "kernel exceeded 60-second regression deadline: {}",
            String::from_utf8_lossy(&stderr)
        )
    };
    write_result.unwrap();
    Output {
        status,
        stdout,
        stderr,
    }
}
