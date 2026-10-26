//! Driver configuration regressions; each child receives its own environment.
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static SERIAL: AtomicU64 = AtomicU64::new(0);
struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "vastitas-driver-{}-{}",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("main.vast"), "fn main() -> Int { 42 }").unwrap();
        Self(path)
    }
    fn cli(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_vastitas"));
        command
            .current_dir(&self.0)
            .env("VASTITAS_KERNEL", kernel());
        command
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn kernel() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("lean-kernel/.lake/build/bin/vastitas-kernel")
}
fn executable(path: &Path, source: &str) {
    fs::write(path, source).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
}

#[test]
fn explicit_kernel_check_does_not_require_a_kernel_root() {
    let scratch = Scratch::new();
    let result = scratch
        .cli()
        .args(["check", "main.vast"])
        .env("VASTITAS_KERNEL_ROOT", scratch.0.join("absent"))
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let result = scratch
        .cli()
        .args(["build", "main.vast", "-o", "program"])
        .env("VASTITAS_KERNEL_ROOT", scratch.0.join("absent"))
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("E_BACKEND:"));
}

#[test]
fn native_project_uses_the_selected_kernel_toolchain() {
    let scratch = Scratch::new();
    let root = scratch.0.join("selected kernel");
    fs::create_dir(&root).unwrap();
    // A sentinel version demonstrates copying from the selected root, without
    // depending on an additional installed Lean toolchain.
    let expected = "leanprover/lean4:v99.98.97\n";
    fs::write(root.join("lean-toolchain"), expected).unwrap();
    let bin = scratch.0.join("bin");
    fs::create_dir(&bin).unwrap();
    executable(
        &bin.join("lake"),
        "#!/bin/sh\nset -eu\ncat lean-toolchain > \"$VASTITAS_TEST_TOOLCHAIN\"\nmkdir -p .lake/build/bin\ncp \"$VASTITAS_TEST_NATIVE\" .lake/build/bin/program\n",
    );
    let native = scratch.0.join("native");
    executable(&native, "#!/bin/sh\nprintf '42\\n'\n");
    let captured = scratch.0.join("captured");
    let mut paths = vec![bin];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let result = scratch
        .cli()
        .args(["build", "main.vast", "-o", "program"])
        .env("VASTITAS_KERNEL_ROOT", &root)
        .env("PATH", std::env::join_paths(paths).unwrap())
        .env("VASTITAS_TEST_TOOLCHAIN", &captured)
        .env("VASTITAS_TEST_NATIVE", &native)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(fs::read_to_string(captured).unwrap(), expected);
    assert_eq!(
        fs::read(scratch.0.join("program")).unwrap(),
        fs::read(native).unwrap()
    );
}

#[test]
fn missing_or_empty_kernel_toolchain_preserves_output() {
    let scratch = Scratch::new();
    let root = scratch.0.join("selected kernel");
    fs::create_dir(&root).unwrap();
    let output = scratch.0.join("program");
    fs::write(&output, b"existing artifact").unwrap();
    for toolchain in [None, Some("")] {
        if let Some(text) = toolchain {
            fs::write(root.join("lean-toolchain"), text).unwrap();
        }
        let result = scratch
            .cli()
            .args(["build", "main.vast", "-o", "program"])
            .env("VASTITAS_KERNEL_ROOT", &root)
            .output()
            .unwrap();
        assert!(!result.status.success());
        let error = String::from_utf8_lossy(&result.stderr);
        assert!(
            error.contains("E_BUILD:") && error.contains("lean-toolchain"),
            "{error}"
        );
        assert_eq!(fs::read(&output).unwrap(), b"existing artifact");
    }
}

#[test]
fn runtime_native_artifacts_are_prebuilt_and_reused() {
    let scratch = Scratch::new();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("lean-kernel");
    let artifacts = [
        root.join(".lake/build/lib/lean/VastitasKernel/Runtime.olean"),
        root.join(".lake/build/ir/VastitasKernel/Runtime.c.o.export"),
    ];
    let before: Vec<_> = artifacts
        .iter()
        .map(|path| {
            fs::metadata(path)
                .unwrap_or_else(|error| {
                    panic!("kernel build must provide {}: {error}", path.display())
                })
                .modified()
                .unwrap()
        })
        .collect();
    let result = scratch
        .cli()
        .args(["build", "main.vast", "-o", "program"])
        .env("VASTITAS_KERNEL_ROOT", &root)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    for (path, timestamp) in artifacts.iter().zip(before) {
        assert_eq!(
            fs::metadata(path).unwrap().modified().unwrap(),
            timestamp,
            "native build recompiled {}",
            path.display()
        );
    }
    let result = Command::new(scratch.0.join("program")).output().unwrap();
    assert!(result.status.success());
    assert_eq!(result.stdout, b"42\n");
}
