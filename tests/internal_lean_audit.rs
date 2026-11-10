//! `audit-lean` through the `nanoda_bin` shipped with the pinned Lean toolchain.
//! Positive and export-rejection cases run the real toolchain checker (located
//! through `ELAN_HOME` as in CI, or `~/.elan`). Resolution failures use fake
//! elan homes so they never depend on, or modify, the real installation.
use std::ffi::OsStr;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

static NEXT_PATH: AtomicU64 = AtomicU64::new(0);
const TOOLCHAIN_DIRECTORY: &str = "leanprover--lean4---v4.35.0";
const FIXTURE: &str = include_str!("fixtures/lean_audit/id_prop.ndjson");

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/lean_audit/id_prop.ndjson")
}

fn header() -> &'static str {
    FIXTURE.lines().next().unwrap()
}

fn audit_command(path: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_vastitas"));
    command.arg("audit-lean").arg(path);
    command
}

fn run_audit(path: &Path) -> Output {
    audit_command(path)
        .output()
        .expect("run Vastitas audit-lean")
}

fn temporary_path(kind: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!(
        "vastitas-audit-test-{}-{nanos}-{}{kind}",
        std::process::id(),
        // SystemTime resolution can give simultaneous test threads the same
        // timestamp. Their inputs and cleanup must remain independent.
        NEXT_PATH.fetch_add(1, Ordering::Relaxed)
    ))
}

fn temporary_export(contents: &str) -> Output {
    let path = temporary_path(".ndjson");
    fs::write(&path, contents).expect("write temporary Lean export");
    let output = run_audit(&path);
    fs::remove_file(&path).expect("remove temporary Lean export");
    output
}

fn export(lines: &[&str]) -> String {
    let mut lines = lines.to_vec();
    lines.insert(0, header());
    lines.join("\n")
}

fn accepted(output: &Output) -> String {
    assert!(output.status.success(), "unexpected rejection: {output:?}");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    for required in [
        "internal-only conditional Lean audit completed (nanoda_bin 0.4.19 from the Lean 4.35.0 toolchain)",
        "commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc",
        "Result is relative to the supplied environment",
        "NOT authenticated as the standard Lean axioms",
        "nanoda is not the official Lean kernel",
        "NOT official Lean-kernel verification",
        "no Vastitas Core or constitutional acceptance",
    ] {
        assert!(stdout.contains(required), "missing {required:?}: {stdout}");
    }
    for forbidden in ["kernel_verified", "official_kernel_checked", "audit passed"] {
        assert!(!stdout.contains(forbidden), "{stdout}");
    }
    stdout
}

fn rejected(output: &Output) -> String {
    assert!(!output.status.success(), "unexpected success: {output:?}");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        stderr.contains("E_LEAN_AUDIT"),
        "audit rejection did not reach the driver: {stderr}"
    );
    stderr
}

fn checker_rejected(output: &Output) -> String {
    let stderr = rejected(output);
    assert!(
        stderr.contains("E_LEAN_AUDIT: nanoda_bin 0.4.19 rejected"),
        "{stderr}"
    );
    stderr
}

/// The real elan home, as `audit-lean` resolves it without overrides.
fn real_toolchain() -> PathBuf {
    let home = std::env::var_os("ELAN_HOME")
        .filter(|home| !home.is_empty())
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(std::env::var_os("HOME").unwrap()).join(".elan"));
    home.join("toolchains").join(TOOLCHAIN_DIRECTORY)
}

/// A fake elan home whose pinned toolchain contains the given `bin` scripts.
struct FakeElan(PathBuf);

impl FakeElan {
    fn new(scripts: &[(&str, String)]) -> Self {
        Self::at(temporary_path("-elan"), scripts)
    }

    /// A fake elan home at `home`.
    fn at(home: PathBuf, scripts: &[(&str, String)]) -> Self {
        let bin = home
            .join("toolchains")
            .join(TOOLCHAIN_DIRECTORY)
            .join("bin");
        fs::create_dir_all(&bin).unwrap();
        for (name, body) in scripts {
            let path = bin.join(name);
            fs::write(&path, format!("#!/bin/sh\n{body}\n")).unwrap();
            fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
        }
        Self(home)
    }

    fn bin(&self) -> PathBuf {
        self.0
            .join("toolchains")
            .join(TOOLCHAIN_DIRECTORY)
            .join("bin")
    }

    fn audit(&self, path: &Path) -> Output {
        audit_command(path)
            .env("ELAN_HOME", &self.0)
            .output()
            .expect("run Vastitas audit-lean")
    }
}

impl Drop for FakeElan {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Single-quote a path for a POSIX shell script.
fn shell_quote(path: &Path) -> String {
    format!("'{}'", path.to_str().unwrap().replace('\'', "'\\''"))
}

/// A fake `lean` that delegates to the real pinned one, so the toolchain
/// identity check passes and only the checker under test differs.
fn real_lean() -> (&'static str, String) {
    let lean = real_toolchain().join("bin/lean");
    ("lean", format!("exec {} \"$@\"", shell_quote(&lean)))
}

/// A fake checker reporting the pinned identity and otherwise running `body`.
fn identified_checker(body: &str) -> (&'static str, String) {
    (
        "nanoda_bin",
        format!("if [ \"$1\" = --help ]; then echo 'nanoda_bin 0.4.19'; exit 0; fi\n{body}"),
    )
}

#[test]
fn checked_export_returns_conditional_receipt_with_checker_identity() {
    let stdout = accepted(&run_audit(&fixture()));
    assert!(stdout.contains(": 1 declarations in "), "{stdout}");
    let checker = real_toolchain()
        .join("bin/nanoda_bin")
        .canonicalize()
        .unwrap();
    assert!(
        stdout.contains(&format!("Checker: {}", checker.display())),
        "{stdout}"
    );
}

#[test]
fn standard_axiom_names_cannot_authenticate_arbitrary_statements() {
    // Well-typed but inconsistent assumption: propext : forall P : Prop, P.
    // It has an allowed name, but is not Lean's propositional extensionality,
    // and a theorem that every proposition holds checks against it.
    let spoofed = export(&[
        r#"{"in":1,"str":{"pre":0,"str":"propext"}}"#,
        r#"{"in":2,"str":{"pre":0,"str":"P"}}"#,
        r#"{"in":3,"str":{"pre":0,"str":"everything"}}"#,
        r#"{"ie":0,"sort":0}"#,
        r#"{"ie":1,"bvar":0}"#,
        r#"{"ie":2,"forallE":{"binderInfo":"default","body":1,"name":2,"type":0}}"#,
        r#"{"ie":3,"const":{"name":1,"us":[]}}"#,
        r#"{"axiom":{"name":1,"levelParams":[],"type":2,"isUnsafe":false}}"#,
        r#"{"thm":{"name":3,"levelParams":[],"type":2,"value":3}}"#,
    ]);
    let stdout = accepted(&temporary_export(&spoofed));
    assert!(stdout.contains(": 2 declarations in "), "{stdout}");

    // Finding (#539): nanoda compares rendered names, so a single-component
    // name spelled `Classical.choice` also passes the name policy. The result
    // stays conditional because no name is authenticated.
    let dotted = export(&[
        r#"{"in":1,"str":{"pre":0,"str":"Classical.choice"}}"#,
        r#"{"ie":0,"sort":0}"#,
        r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
    ]);
    accepted(&temporary_export(&dotted));
}

#[test]
fn invalid_proof_term_is_rejected_with_the_checker_status() {
    // Replace the identity proof lambda with Prop itself (a wrong type).
    let modified = FIXTURE.replacen(r#""type":4,"value":6}}"#, r#""type":4,"value":0}}"#, 1);
    assert_ne!(FIXTURE, modified);
    let stderr = checker_rejected(&temporary_export(&modified));
    assert!(stderr.contains("exit status: 101"), "{stderr}");
}

#[test]
fn unauthorized_axioms_are_hard_errors_even_if_unused() {
    for name in [
        "NotPermitted",
        "sorryAx",
        "Lean.trustCompiler",
        "Classical.propext",
    ] {
        let input = export(&[
            &format!(r#"{{"in":1,"str":{{"pre":0,"str":"{name}"}}}}"#),
            r#"{"ie":0,"sort":0}"#,
            r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
        ]);
        let stderr = checker_rejected(&temporary_export(&input));
        assert!(stderr.contains("unpermitted axiom"), "{name}: {stderr}");
    }
}

#[test]
fn spoofed_axiom_environments_are_rejected() {
    // An unsafe declaration with an allowed name.
    let unsafe_axiom = export(&[
        r#"{"in":1,"str":{"pre":0,"str":"propext"}}"#,
        r#"{"ie":0,"sort":0}"#,
        r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":true}}"#,
    ]);
    checker_rejected(&temporary_export(&unsafe_axiom));
    // Two declarations of one allowed name.
    let axiom = r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#;
    let duplicate = export(&[
        r#"{"in":1,"str":{"pre":0,"str":"propext"}}"#,
        r#"{"ie":0,"sort":0}"#,
        axiom,
        axiom,
    ]);
    checker_rejected(&temporary_export(&duplicate));
}

#[test]
fn checker_diagnostics_cannot_drive_the_terminal() {
    let input = export(&[
        r#"{"in":1,"str":{"pre":0,"str":"Evil\u001b[2J\u202e"}}"#,
        r#"{"ie":0,"sort":0}"#,
        r#"{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"#,
    ]);
    let output = temporary_export(&input);
    checker_rejected(&output);
    assert!(!output.stderr.contains(&0x1b), "{output:?}");
    assert!(!String::from_utf8_lossy(&output.stderr).contains('\u{202e}'));
}

/// The audit shows the path of the export, and the paths of the toolchain that
/// the environment selects, as the compiler shows every path (#718): it names
/// a control character by its code point. The names are created in the
/// temporary directory only.
#[test]
fn audit_paths_cannot_drive_the_terminal() {
    // Clear the screen, ring the bell, start a forged line, the one-character
    // control sequence introducer, a tab and a right-to-left override.
    const HOSTILE: &str = "x\u{1b}[2J\u{7}\nE_FORGED: \u{9b}2J\t\u{202e}";
    const NAMED: &str = "x<U+001B>[2J<U+0007><U+000A>E_FORGED: <U+009B>2J<U+0009><U+202E>";
    const ABSENT: &str = "No such file or directory (os error 2)";
    let shown = |path: &Path| path.to_str().unwrap().replace(HOSTILE, NAMED);
    // The failed cases. One run reports all of them, so a run without the
    // fix shows that every case depends on it. A stream must start with
    // `start` and hold `lines` lines, and the line feeds that end them must
    // be its only control characters.
    let mut failures = Vec::new();
    let mut case = |name: &str, stream: &[u8], start: String, lines: usize| {
        let text = String::from_utf8_lossy(stream);
        let controls: String = text
            .chars()
            .filter(|ch| (ch.is_control() && *ch != '\n') || *ch == '\u{202e}')
            .collect();
        if !controls.is_empty()
            || !text.ends_with('\n')
            || !text.starts_with(&start)
            || text.lines().count() != lines
        {
            failures.push(format!(
                "{name}: expected {start:?} in {lines} lines, found {text:?}"
            ));
        }
    };

    // The export, as the command line gives it.
    let export = temporary_path(&format!("{HOSTILE}.ndjson"));
    let name = shown(&export);
    let output = run_audit(&export);
    rejected(&output);
    case(
        "export absent",
        &output.stderr,
        format!("E_LEAN_AUDIT: cannot read {name}: {ABSENT}\n"),
        1,
    );
    fs::create_dir(&export).unwrap();
    let output = run_audit(&export);
    fs::remove_dir(&export).unwrap();
    rejected(&output);
    case(
        "export directory",
        &output.stderr,
        format!("E_LEAN_AUDIT: {name} is a directory, not a Lean export\n"),
        1,
    );
    fs::write(&export, FIXTURE).unwrap();
    let rejecting = FakeElan::new(&[real_lean(), identified_checker("exit 3")]);
    let output = rejecting.audit(&export);
    rejected(&output);
    // The checker wrote no diagnostics, so an empty line follows.
    case(
        "export rejected",
        &output.stderr,
        format!("E_LEAN_AUDIT: nanoda_bin 0.4.19 rejected {name} (exit status: 3)\n"),
        2,
    );
    let accepting = FakeElan::new(&[
        real_lean(),
        identified_checker("echo 'Checked 1 declarations with no errors'"),
    ]);
    let output = accepting.audit(&export);
    fs::remove_file(&export).unwrap();
    let stdout = accepted(&output);
    let report = stdout
        .split_once(": 1 declarations in ")
        .map(|parts| parts.1);
    case(
        "export accepted",
        report.unwrap_or_default().as_bytes(),
        format!("{name}\nChecker: "),
        4,
    );

    // The toolchain, under the elan home of the environment.
    let home = |kind: &str| temporary_path(&format!("-{kind}{HOSTILE}"));
    let empty = home("empty");
    fs::create_dir(&empty).unwrap();
    let output = audit_command(&fixture())
        .env("ELAN_HOME", &empty)
        .output()
        .unwrap();
    fs::remove_dir(&empty).unwrap();
    rejected(&output);
    case(
        "toolchain absent",
        &output.stderr,
        format!(
            "E_LEAN_AUDIT_CHECKER: the pinned Lean toolchain leanprover/lean4:v4.35.0 is not installed at {}/toolchains/{TOOLCHAIN_DIRECTORY}: {ABSENT}\n",
            shown(&empty)
        ),
        2,
    );
    let file = home("file");
    fs::create_dir_all(file.join("toolchains")).unwrap();
    fs::write(file.join("toolchains").join(TOOLCHAIN_DIRECTORY), "").unwrap();
    let toolchain = file
        .join("toolchains")
        .join(TOOLCHAIN_DIRECTORY)
        .canonicalize()
        .unwrap();
    let output = audit_command(&fixture())
        .env("ELAN_HOME", &file)
        .output()
        .unwrap();
    fs::remove_dir_all(&file).unwrap();
    rejected(&output);
    case(
        "toolchain file",
        &output.stderr,
        format!(
            "E_LEAN_AUDIT_CHECKER: {} is not a Lean toolchain directory\n",
            shown(&toolchain)
        ),
        1,
    );
    // Each case: the scripts of the toolchain, the start of stderr after the
    // code, and its number of lines. `BIN` stands for the directory of the
    // scripts and `HOME` for the toolchain directory that holds it.
    let other = "echo 'Lean (version 0.0.0)'".to_string();
    for (kind, scripts, start, lines) in [
        (
            "toolchain without lean",
            vec![],
            "the pinned Lean toolchain leanprover/lean4:v4.35.0 at HOME provides no lean: ",
            2,
        ),
        (
            "lean failing",
            vec![("lean", "exit 7".to_string())],
            "BIN/lean --version failed (exit status: 7)\n",
            2,
        ),
        (
            "lean other",
            vec![("lean", other)],
            "BIN/lean is not the official Lean ",
            1,
        ),
        (
            "checker other",
            vec![real_lean(), ("nanoda_bin", "echo other".to_string())],
            "BIN/nanoda_bin does not identify as nanoda_bin 0.4.19, ",
            1,
        ),
    ] {
        let elan = FakeElan::at(home("elan"), &scripts);
        let bin = shown(&elan.bin().canonicalize().unwrap());
        let output = elan.audit(&fixture());
        rejected(&output);
        let start = start
            .replace("BIN", &bin)
            .replace("HOME", bin.strip_suffix("/bin").unwrap());
        case(
            kind,
            &output.stderr,
            format!("E_LEAN_AUDIT_CHECKER: {start}"),
            lines,
        );
    }
    let unusable = FakeElan::at(home("unusable"), &[]);
    fs::write(unusable.bin().join("lean"), "").unwrap();
    let output = unusable.audit(&fixture());
    rejected(&output);
    case(
        "lean not executable",
        &output.stderr,
        format!(
            "E_LEAN_AUDIT_CHECKER: {}/lean is not a regular executable file of the pinned toolchain\n",
            shown(&unusable.bin().canonicalize().unwrap())
        ),
        1,
    );
    assert!(
        failures.is_empty(),
        "{} failed cases:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn malformed_empty_and_missing_exports_are_rejected() {
    checker_rejected(&temporary_export("not-json\n"));
    let truncated = FIXTURE.trim_end().strip_suffix("}}").unwrap();
    checker_rejected(&temporary_export(truncated));
    let stderr = rejected(&temporary_export(header()));
    assert!(stderr.contains("without declarations"), "{stderr}");
    let stderr = rejected(&run_audit(&temporary_path("-missing.ndjson")));
    assert!(stderr.contains("E_LEAN_AUDIT: cannot read"), "{stderr}");
    let stderr = rejected(&run_audit(&std::env::temp_dir()));
    assert!(stderr.contains("is a directory"), "{stderr}");
}

#[test]
fn missing_toolchain_or_checker_fails_closed_without_path_fallback() {
    // An accepting `nanoda_bin` on PATH must never be used.
    let decoy = FakeElan::new(&[identified_checker(
        "echo 'Checked 1 declarations with no errors'",
    )]);
    let path = format!("{}:/usr/bin:/bin", decoy.bin().display());

    let empty = temporary_path("-empty-elan");
    fs::create_dir(&empty).unwrap();
    let output = audit_command(&fixture())
        .env("ELAN_HOME", &empty)
        .env("PATH", &path)
        .output()
        .unwrap();
    fs::remove_dir(&empty).unwrap();
    let stderr = rejected(&output);
    assert!(
        stderr.contains("E_LEAN_AUDIT_CHECKER: the pinned Lean toolchain leanprover/lean4:v4.35.0 is not installed"),
        "{stderr}"
    );

    let without_checker = FakeElan::new(&[real_lean()]);
    let output = audit_command(&fixture())
        .env("ELAN_HOME", &without_checker.0)
        .env("PATH", &path)
        .output()
        .unwrap();
    let stderr = rejected(&output);
    assert!(stderr.contains("provides no nanoda_bin"), "{stderr}");
    assert!(stderr.contains("no fallback checker"), "{stderr}");
}

#[test]
fn mismatched_toolchain_or_checker_identity_fails_closed() {
    let accept = "echo 'Checked 1 declarations with no errors'";
    let newer = FakeElan::new(&[
        real_lean(),
        (
            "nanoda_bin",
            format!("[ \"$1\" = --help ] && echo 'nanoda_bin 0.4.31' && exit 0\n{accept}"),
        ),
    ]);
    let stderr = rejected(&newer.audit(&fixture()));
    assert!(
        stderr.contains("does not identify as nanoda_bin 0.4.19") && stderr.contains("0.4.31"),
        "{stderr}"
    );

    let older_lean = FakeElan::new(&[
        (
            "lean",
            "echo 'Lean (version 4.34.1, arm64-apple-darwin24.6.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)'".into(),
        ),
        identified_checker(accept),
    ]);
    let stderr = rejected(&older_lean.audit(&fixture()));
    assert!(
        stderr.contains("is not the official Lean 4.35.0 release"),
        "{stderr}"
    );

    // The toolchain's own regular file is required, not a link to elsewhere.
    let linked = FakeElan::new(&[real_lean()]);
    std::os::unix::fs::symlink(
        real_toolchain().join("bin/nanoda_bin"),
        linked.bin().join("nanoda_bin"),
    )
    .unwrap();
    let stderr = rejected(&linked.audit(&fixture()));
    assert!(stderr.contains("not a regular executable file"), "{stderr}");
}

#[test]
fn checker_uses_upstream_configuration_and_its_report_is_validated() {
    // Record the configuration the checker receives, then exit with a status
    // or report chosen by the test.
    let record = temporary_path("-config.json");
    let checker = |tail: &str| {
        identified_checker(&format!(
            "cp \"$1\" {} || exit 9\ntest -f nanoda-config.json || exit 8\n{tail}",
            shell_quote(&record)
        ))
    };
    let elan = FakeElan::new(&[real_lean(), checker("exit 3")]);
    let stderr = rejected(&elan.audit(&fixture()));
    assert!(stderr.contains("nanoda_bin 0.4.19 rejected"), "{stderr}");
    assert!(stderr.contains("exit status: 3"), "{stderr}");
    let config: serde_json::Value = serde_json::from_slice(&fs::read(&record).unwrap()).unwrap();
    fs::remove_file(&record).unwrap();
    let mut expected: serde_json::Value =
        serde_json::from_str(include_str!("../config/nanoda-internal-audit.json")).unwrap();
    expected["export_file_path"] = fixture().to_str().unwrap().into();
    assert_eq!(config, expected);

    for (tail, message) in [
        ("exit 0", "unexpected nanoda_bin 0.4.19 success report"),
        (
            "echo 'Checked 1 declarations with no errors, skipping exported but unpermitted axioms [\"x\"]'",
            "unexpected nanoda_bin 0.4.19 success report",
        ),
        (
            "echo 'Checked 1 declarations with no errors'; echo warning >&2",
            "reported diagnostics despite success",
        ),
    ] {
        let elan = FakeElan::new(&[real_lean(), checker(tail)]);
        let stderr = rejected(&elan.audit(&fixture()));
        assert!(stderr.contains(message), "{tail}: {stderr}");
    }
    let _ = fs::remove_file(&record);
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

#[test]
fn interrupted_audit_terminates_and_reaps_the_checker() {
    use nix::errno::Errno;
    use nix::sys::signal::{Signal, kill};
    use nix::sys::stat::Mode;
    use nix::unistd::{Pid, mkfifo};
    use std::os::unix::fs::OpenOptionsExt;
    use std::process::Stdio;
    use std::time::{Duration, Instant};

    for (signal, code) in [(Signal::SIGINT, 130), (Signal::SIGTERM, 143)] {
        let fifo = temporary_path(".fifo");
        mkfifo(&fifo, Mode::S_IRUSR | Mode::S_IWUSR).unwrap();
        let mut child = audit_command(&fifo)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        // Opening a nonblocking writer succeeds only once the toolchain checker
        // is opening the FIFO. Keep it open without bytes so checking cannot
        // finish by itself, and signal only the Vastitas process.
        let deadline = Instant::now() + Duration::from_secs(10);
        let writer = loop {
            match fs::OpenOptions::new()
                .write(true)
                .custom_flags(nix::libc::O_NONBLOCK)
                .open(&fifo)
            {
                Ok(writer) => break writer,
                Err(error) if error.raw_os_error() == Some(Errno::ENXIO as i32) => {
                    assert!(Instant::now() < deadline, "checker did not open input");
                    assert!(child.try_wait().unwrap().is_none());
                    std::thread::sleep(Duration::from_millis(10));
                }
                Err(error) => panic!("open audit input: {error}"),
            }
        };
        kill(Pid::from_raw(child.id() as i32), signal).unwrap();
        let deadline = Instant::now() + Duration::from_secs(5);
        while child.try_wait().unwrap().is_none() {
            if Instant::now() >= deadline {
                drop(writer);
                child.kill().unwrap();
                child.wait().unwrap();
                fs::remove_file(&fifo).unwrap();
                panic!("audit cancellation exceeded watchdog");
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        // No wall-clock bound beyond the watchdog: under load, forwarding and
        // TERM/KILL escalation both finish well inside it. The checker runs no
        // Vastitas code, so #564 (4)'s worker signal dispositions no longer apply.
        let output = child.wait_with_output().unwrap();
        assert_eq!(output.status.code(), Some(code));
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("E_LEAN_AUDIT: audit interrupted")
        );
        // No FIFO reader may survive Vastitas. A leaked checker would make
        // this open succeed even though it emits no output.
        let reopened = fs::OpenOptions::new()
            .write(true)
            .custom_flags(nix::libc::O_NONBLOCK)
            .open(&fifo);
        assert_eq!(
            reopened.unwrap_err().raw_os_error(),
            Some(Errno::ENXIO as i32)
        );
        drop(writer);
        fs::remove_file(&fifo).unwrap();
    }
}
