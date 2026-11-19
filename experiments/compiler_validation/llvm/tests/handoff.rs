//! Host-boundary tests. The checked source-to-byte regression runs in the compiler.
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const BACKEND: &str = env!("CARGO_BIN_EXE_vastitas-llvm-qualification");

struct Work(PathBuf);
impl Work {
    fn new() -> Self {
        let root = std::env::temp_dir();
        for n in 0.. {
            let candidate = root.join(format!("vastitas-llvm-handoff-{}-{n}", std::process::id()));
            match fs::create_dir(&candidate) {
                Ok(()) => return Self(candidate),
                Err(err) if err.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(err) => panic!("{err}"),
            }
        }
        unreachable!()
    }
}
impl Drop for Work {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn target_fields() -> (String, String) {
    let result = Command::new(BACKEND).arg("describe").output().unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let text = String::from_utf8(result.stdout).unwrap();
    let field = |key: &str| {
        text.lines()
            .find_map(|v| v.strip_prefix(key))
            .unwrap()
            .to_owned()
    };
    assert_eq!(field("llvm="), "23.1.4");
    (field("triple="), field("layout="))
}

fn module(triple: &str, layout: &str, body: &str) -> Vec<u8> {
    format!("target datalayout = \"{layout}\"\ntarget triple = \"{triple}\"\n\ndefine i32 @main() {{\n{body}\n}}\n").into_bytes()
}

fn emit(dir: &Path, expected: &[u8], disk: &[u8]) -> Output {
    fs::write(dir.join("expected.ll"), expected).unwrap();
    fs::write(dir.join("readback.ll"), disk).unwrap();
    Command::new(BACKEND)
        .current_dir(dir)
        .args(["emit", "expected.ll", "readback.ll", "status.o"])
        .output()
        .unwrap()
}

#[test]
fn pinned_host_object_links_and_runs_and_never_replaces_an_existing_object() {
    let work = Work::new();
    let (triple, layout) = target_fields();
    let text = module(&triple, &layout, "entry:\n  ret i32 37");
    let result = emit(&work.0, &text, &text);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(
        Command::new("cc")
            .current_dir(&work.0)
            .args(["status.o", "-o", "status"])
            .status()
            .unwrap()
            .success()
    );
    assert_eq!(
        Command::new(work.0.join("status")).status().unwrap().code(),
        Some(37)
    );
    fs::write(work.0.join("status.o"), b"reserved").unwrap();
    assert!(!emit(&work.0, &text, &text).status.success());
    assert_eq!(fs::read(work.0.join("status.o")).unwrap(), b"reserved");
}

#[test]
fn malformed_or_changed_bytes_target_layout_and_invalid_ssa_create_no_object() {
    let work = Work::new();
    let (triple, layout) = target_fields();
    let body = "entry:\n  ret i32 37";
    let good = module(&triple, &layout, body);
    let mut changed = good.clone();
    *changed.last_mut().unwrap() = b' ';
    let mut oversized = good.clone();
    oversized.resize(4 * 1024 * 1024, b' ');
    let malformed = b"invalid IR\n";
    let verify_rejection = |expected: &[u8], disk: &[u8], diagnostic: &str| {
        let result = emit(&work.0, expected, disk);
        assert!(!result.status.success());
        let stderr = String::from_utf8(result.stderr).unwrap();
        assert!(stderr.contains(diagnostic), "{stderr}");
        assert!(!work.0.join("status.o").exists());
    };
    verify_rejection(&good, &changed, "complete LLVM byte comparison failed");
    verify_rejection(
        &good,
        &good[..good.len() - 1],
        "complete LLVM byte comparison failed",
    );
    verify_rejection(&good, &oversized, "complete LLVM byte comparison failed");
    verify_rejection(malformed, malformed, "expected top-level entity");
    verify_rejection(b"\0", b"\0", "NUL in LLVM handoff");
    let target = module("unknown-unknown-unknown", &layout, body);
    verify_rejection(
        &target,
        &target,
        "module target does not equal selected target",
    );
    let bad_layout = module(&triple, "e-p:32:32", body);
    verify_rejection(
        &bad_layout,
        &bad_layout,
        "module layout does not equal selected layout",
    );
    let invalid = module(
        &triple,
        &layout,
        "entry:\n  br label %join\njoin:\n  %a = phi i32 [ 2, %join ]\n  ret i32 %a",
    );
    verify_rejection(
        &invalid,
        &invalid,
        "PHI node entries do not match predecessors",
    );
}
