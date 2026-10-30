use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/lean_audit/id_prop.ndjson")
}

fn run_audit(path: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_vastitas"))
        .arg("audit-lean")
        .arg(path)
        .output()
        .expect("run Vastitas audit-lean")
}

fn temporary_path() -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!(
        "vastitas-nanoda-{}-{nanos}.ndjson",
        std::process::id()
    ))
}

fn temporary_export(contents: &str) -> (PathBuf, Output) {
    let path = temporary_path();
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
    // Replace the identity proof lambda with Prop itself (a wrong type).
    let original = include_str!("fixtures/lean_audit/id_prop.ndjson");
    let modified = original.replacen(r#""type":4,"value":6}}"#, r#""type":4,"value":0}}"#, 1);
    assert_ne!(original, modified);
    rejected(&temporary_export(&modified).1);
}

#[test]
fn undeclared_axiom_is_a_hard_error_even_if_unused() {
    let original = include_str!("fixtures/lean_audit/id_prop.ndjson");
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
    let original = include_str!("fixtures/lean_audit/id_prop.ndjson");
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

#[test]
fn interrupted_audit_terminates_and_reaps_its_worker() {
    use nix::errno::Errno;
    use nix::sys::signal::{Signal, kill};
    use nix::sys::stat::Mode;
    use nix::unistd::{Pid, mkfifo};
    use std::os::unix::fs::OpenOptionsExt;
    use std::process::Stdio;
    use std::time::{Duration, Instant};

    for (signal, code) in [(Signal::SIGINT, 130), (Signal::SIGTERM, 143)] {
        let fifo = temporary_path();
        mkfifo(&fifo, Mode::S_IRUSR | Mode::S_IWUSR).unwrap();
        let mut child = Command::new(env!("CARGO_BIN_EXE_vastitas"))
            .arg("audit-lean")
            .arg(&fifo)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        // Opening a nonblocking writer succeeds only once the actual audit
        // worker is opening the FIFO. Keep it open without bytes so checking
        // cannot finish by itself, and signal only the parent process.
        let deadline = Instant::now() + Duration::from_secs(5);
        let writer = loop {
            match fs::OpenOptions::new()
                .write(true)
                .custom_flags(nix::libc::O_NONBLOCK)
                .open(&fifo)
            {
                Ok(writer) => break writer,
                Err(error) if error.raw_os_error() == Some(Errno::ENXIO as i32) => {
                    assert!(Instant::now() < deadline, "audit worker did not open input");
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
        let output = child.wait_with_output().unwrap();
        assert_eq!(output.status.code(), Some(code));
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("E_LEAN_AUDIT: audit interrupted")
        );
        // No FIFO reader may survive the parent. A leaked checker would make
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
