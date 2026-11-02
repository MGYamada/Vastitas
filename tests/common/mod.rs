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
pub fn check(source: &str, filename: &str) -> Output {
    let scratch = Scratch::empty("check");
    cli()
        .arg("check")
        .arg(scratch.write(filename, source))
        .output()
        .unwrap()
}
pub fn reject(source: &str, code: &str, filename: &str) -> String {
    let output = check(source, filename);
    assert!(
        !output.status.success(),
        "accepted invalid source: {source}"
    );
    let message = String::from_utf8(output.stderr).unwrap();
    assert!(
        message.contains(&format!(": {code}: ")),
        "expected {code}: {message}"
    );
    assert!(
        message.contains(&format!("{filename}:")),
        "missing source location: {message}"
    );
    message
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
