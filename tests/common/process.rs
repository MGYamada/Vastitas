//! Scratch directories, the compiler binary and the programs it builds.
use super::diagnostics::expect_code;
use super::wire::captured_wire;
use serde_json::Value;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

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
    /// The compiler, run in this directory.
    pub fn cli(&self) -> Command {
        let mut command = cli();
        command.current_dir(&self.0);
        command
    }
    /// `vastitas <mode> --manifest-path <manifest>`, run in this directory, so
    /// that `manifest` and every path the command prints are relative to it.
    pub fn command(&self, mode: &str, manifest: &str) -> Command {
        let mut command = manifest_command(mode, manifest);
        command.current_dir(&self.0);
        command
    }
    /// Checks the package of `manifest`, relative to this directory.
    pub fn check_manifest(&self, manifest: &str) -> Output {
        self.command("check", manifest).output().unwrap()
    }
    /// The wire request that checking the package of `manifest` sends, which
    /// must use protocol `version` (see [`captured_wire`]).
    #[track_caller]
    pub fn captured(&self, manifest: &str, version: u64) -> Value {
        captured_wire(self.command("check", manifest), version)
    }
    /// Builds the package of `manifest` to `program` in this directory and
    /// runs it. The build must succeed; returns what the program did.
    pub fn build_and_run(&self, manifest: &str) -> Run {
        success(
            &self
                .command("build", manifest)
                .args(["-o", "program"])
                .output()
                .unwrap(),
        );
        ran(&Command::new(self.0.join("program")).output().unwrap())
    }
    /// [`Scratch::build_and_run`] after a successful check of `manifest`.
    pub fn check_build_and_run(&self, manifest: &str) -> Run {
        success(&self.check_manifest(manifest));
        self.build_and_run(manifest)
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
/// The compiler, without the kernel selection of the environment that runs the
/// tests: `VASTITAS_KERNEL` and `VASTITAS_KERNEL_ROOT` are removed, so the
/// compiler uses the built kernel unless a test sets them on the command.
pub fn cli() -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_vastitas"));
    command
        .env_remove("VASTITAS_KERNEL")
        .env_remove("VASTITAS_KERNEL_ROOT");
    command
}
/// `vastitas <mode> --manifest-path <manifest>`, with `manifest` as given:
/// absolute, or relative to the directory that runs the tests.
pub fn manifest_command(mode: &str, manifest: impl AsRef<OsStr>) -> Command {
    let mut command = cli();
    command.args([mode, "--manifest-path"]).arg(manifest);
    command
}
pub fn success(output: &Output) {
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
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
/// The pinned OpenBLAS prefix that the numerical CI jobs name in
/// `VASTITAS_TEST_OPENBLAS_PREFIX`. The tests that need it are ignored
/// elsewhere.
pub fn openblas_prefix() -> String {
    std::env::var("VASTITAS_TEST_OPENBLAS_PREFIX").expect("OpenBLAS prefix")
}
/// `--native-cc` with the native compiler that a numerical CI job names in
/// `VASTITAS_TEST_NATIVE_CC`, or `default_cc` where the job names none; no
/// option when neither names one.
pub fn native_cc_options(default_cc: Option<&str>) -> Vec<String> {
    let cc = std::env::var("VASTITAS_TEST_NATIVE_CC")
        .ok()
        .or_else(|| default_cc.map(str::to_owned));
    cc.map(|cc| vec!["--native-cc".to_owned(), cc])
        .unwrap_or_default()
}
/// The build options of a numerical package in the numerical CI jobs: the
/// pinned OpenBLAS prefix and the native compiler. The compiler is the one
/// that the job names, or `default_cc` where the job names none.
pub fn numerical_build_options(default_cc: Option<&str>) -> Vec<String> {
    let mut options = vec!["--openblas-prefix".to_owned(), openblas_prefix()];
    options.extend(native_cc_options(default_cc));
    options
}
/// What a built program did (#836): its exit status, which is the `Int`
/// result of `main` modulo 256, and what it wrote on standard output, the
/// `label = value` lines of its `show!`. Its standard error is kept for the
/// failure message of a comparison only.
#[derive(Debug)]
pub struct Run {
    pub status: i32,
    pub stdout: String,
    pub stderr: String,
}
impl PartialEq for Run {
    fn eq(&self, other: &Self) -> bool {
        self.status == other.status && self.stdout == other.stdout
    }
}
/// A program that exits with `status` and writes nothing on standard output.
pub fn exits(status: i32) -> Run {
    Run {
        status,
        stdout: String::new(),
        stderr: String::new(),
    }
}
/// A program that exits with 0 and writes `lines` on standard output, each
/// with a line feed: the `label = value` lines of its `show!`.
pub fn shows(lines: &[&str]) -> Run {
    Run {
        status: 0,
        stdout: lines.iter().map(|line| format!("{line}\n")).collect(),
        stderr: String::new(),
    }
}
/// What the program of `output` did. It must have exited, not stopped at a
/// signal.
#[track_caller]
pub fn ran(output: &Output) -> Run {
    let status = output.status.code().unwrap_or_else(|| {
        panic!(
            "program stopped without an exit status: {}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        )
    });
    Run {
        status,
        stdout: String::from_utf8(output.stdout.clone()).unwrap(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    }
}
/// Builds the flat program `source` with `libraries` and runs it; it must do
/// what `expected` says.
#[track_caller]
pub fn native(source: &str, libraries: &[PathBuf], expected: Run, filename: &str) {
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
    assert_eq!(ran(&output), expected, "{source}");
}
