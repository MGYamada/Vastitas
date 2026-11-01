//! Driver configuration regressions; each child receives its own environment.
mod common;
use common::{Scratch, kernel_path as kernel};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::fs::symlink;
use std::path::Path;
use std::process::{Command, Stdio};

impl Scratch {
    fn new() -> Self {
        let scratch = Self::empty("driver_issues");
        let path = &scratch.0;
        fs::write(path.join("main.vast"), "fn main() -> Int { 42 }").unwrap();
        scratch
    }
    fn cli(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_vastitas"));
        command
            .current_dir(&self.0)
            .env("VASTITAS_KERNEL", kernel());
        command
    }
}
fn executable(path: &Path, source: &str) {
    fs::write(path, source).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
}

#[test]
fn exited_compilers_cannot_leave_pipe_holders_or_silent_descendants() {
    use nix::sys::signal::{Signal, kill};
    use nix::unistd::Pid;
    use std::time::{Duration, Instant};

    for build in [false, true] {
        for detached_pipes in [false, true] {
            let scratch = Scratch::new();
            let bin = scratch.0.join("bin");
            fs::create_dir(&bin).unwrap();
            let worker = scratch.0.join("worker");
            let mock = if build {
                bin.join("lake")
            } else {
                bin.join("kernel")
            };
            let redirection = if detached_pipes {
                " </dev/null >/dev/null 2>&1"
            } else {
                ""
            };
            executable(
                &mock,
                &format!(
                    "#!/bin/sh\nsh -c 'trap \"\" TERM INT; exec sleep 60'{redirection} &\necho $! > \"$WORKER\"\nexit 0\n"
                ),
            );
            let mut paths = vec![bin];
            paths.extend(std::env::split_paths(
                &std::env::var_os("PATH").unwrap_or_default(),
            ));
            fs::write(scratch.0.join("program"), b"existing artifact").unwrap();
            let mut command = scratch.cli();
            if build {
                command.args(["build", "main.vast", "-o", "program"]);
            } else {
                command
                    .args(["check", "main.vast"])
                    .env("VASTITAS_KERNEL", mock);
            }
            let mut child = command
                .env("WORKER", &worker)
                .env("PATH", std::env::join_paths(paths).unwrap())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap();
            let deadline = Instant::now() + Duration::from_secs(12);
            while child.try_wait().unwrap().is_none() {
                if Instant::now() >= deadline {
                    child.kill().unwrap();
                    child.wait().unwrap();
                    if let Ok(pid) = fs::read_to_string(&worker) {
                        let _ = kill(Pid::from_raw(pid.trim().parse().unwrap()), Signal::SIGKILL);
                    }
                    panic!("post-exit cleanup exceeded watchdog");
                }
                std::thread::sleep(Duration::from_millis(20));
            }
            let result = child.wait_with_output().unwrap();
            assert!(!result.status.success());
            let error = String::from_utf8_lossy(&result.stderr);
            assert!(
                error.contains(if build { "E_BUILD" } else { "E_BACKEND" }),
                "{error}"
            );
            assert!(error.contains("forced cleanup"), "{error}");
            assert_eq!(
                fs::read(scratch.0.join("program")).unwrap(),
                b"existing artifact"
            );
            let pid = fs::read_to_string(&worker).unwrap();
            let state = Command::new("ps")
                .args(["-o", "stat=", "-p", pid.trim()])
                .output()
                .unwrap();
            let state = String::from_utf8_lossy(&state.stdout);
            assert!(
                state.trim().is_empty() || state.trim().starts_with('Z'),
                "worker still running: {state}"
            );
        }
    }
}

#[test]
fn output_cannot_replace_any_input_or_alias() {
    let scratch = Scratch::new();
    let original = fs::read(scratch.0.join("main.vast")).unwrap();
    fs::write(scratch.0.join("library.vast"), "fn answer() -> Int { 42 }").unwrap();
    symlink("main.vast", scratch.0.join("alias.vast")).unwrap();
    fs::hard_link(scratch.0.join("main.vast"), scratch.0.join("hard.vast")).unwrap();
    for output in [
        "main.vast",
        "./main.vast",
        "alias.vast",
        "hard.vast",
        "library.vast",
    ] {
        let result = scratch
            .cli()
            .args(["build", "main.vast", "--lib", "library.vast", "-o", output])
            .env("VASTITAS_KERNEL", scratch.0.join("absent-backend"))
            .output()
            .unwrap();
        assert!(!result.status.success());
        assert!(
            String::from_utf8_lossy(&result.stderr)
                .contains("E_OUTPUT: output would overwrite input")
        );
        assert_eq!(fs::read(scratch.0.join("main.vast")).unwrap(), original);
        assert_eq!(
            fs::read_to_string(scratch.0.join("library.vast")).unwrap(),
            "fn answer() -> Int { 42 }"
        );
    }
}

#[test]
fn interrupted_build_reaps_children_and_removes_temporary_files() {
    use nix::sys::signal::{Signal, kill};
    use nix::unistd::Pid;
    use std::time::{Duration, Instant};
    for (signal, code, detached_pipes, manifest) in [
        (Signal::SIGINT, 130, false, false),
        (Signal::SIGTERM, 143, false, false),
        (Signal::SIGTERM, 143, true, false),
        (Signal::SIGTERM, 143, true, true),
        (Signal::SIGHUP, 129, true, true),
        (Signal::SIGQUIT, 131, true, true),
    ] {
        let scratch = Scratch::new();
        let temp = scratch.0.join("tmp");
        let bin = scratch.0.join("bin");
        fs::create_dir(&temp).unwrap();
        fs::create_dir(&bin).unwrap();
        let ready = scratch.0.join("ready");
        let worker = scratch.0.join("worker");
        executable(
            &bin.join("lake"),
            if detached_pipes {
                // This descendant ignores cancellation and closes every pipe.
                // Waiting only for the direct child and I/O would leak it.
                "#!/bin/sh\ntrap 'exit 0' INT TERM HUP QUIT\nsh -c 'trap \"\" INT TERM HUP QUIT; echo ready > \"$READY\"; exec sleep 60' </dev/null >/dev/null 2>&1 &\necho $! > \"$WORKER\"\nwait\n"
            } else {
                "#!/bin/sh\ntrap 'exit 0' INT TERM\nsleep 60 &\necho $! > \"$WORKER\"\necho ready > \"$READY\"\nwait\n"
            },
        );
        fs::write(scratch.0.join("program"), b"existing output").unwrap();
        let mut paths = vec![bin];
        paths.extend(std::env::split_paths(
            &std::env::var_os("PATH").unwrap_or_default(),
        ));
        let input = if manifest {
            fs::write(
                scratch.0.join("Vastitas.toml"),
                "[package]\nname='test'\nversion='0.1.0'\nroot='main.vast'\n",
            )
            .unwrap();
            vec!["--manifest-path", "Vastitas.toml"]
        } else {
            vec!["main.vast"]
        };
        let mut child = scratch
            .cli()
            .arg("build")
            .args(input)
            .args(["-o", "program"])
            .env("TMPDIR", &temp)
            .env("READY", &ready)
            .env("WORKER", &worker)
            .env("PATH", std::env::join_paths(paths).unwrap())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(15);
        while !ready.exists() || !worker.exists() {
            assert!(Instant::now() < deadline, "Lake mock did not start");
            assert!(
                child.try_wait().unwrap().is_none(),
                "build exited before mock readiness"
            );
            std::thread::sleep(Duration::from_millis(10));
        }
        kill(Pid::from_raw(child.id() as i32), signal).unwrap();
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            if Instant::now() >= deadline {
                child.kill().unwrap();
                child.wait().unwrap();
                panic!("interrupted build did not terminate");
            }
            std::thread::sleep(Duration::from_millis(20));
        };
        assert_eq!(status.code(), Some(code));
        let result = child.wait_with_output().unwrap();
        let error = String::from_utf8_lossy(&result.stderr);
        assert!(
            error.contains("E_INTERRUPTED: compilation interrupted"),
            "{error}"
        );
        assert!(!error.contains("cannot start"), "{error}");
        assert!(!error.contains("Build it with"), "{error}");
        assert_eq!(fs::read_dir(&temp).unwrap().count(), 0);
        assert_eq!(
            fs::read(scratch.0.join("program")).unwrap(),
            b"existing output"
        );
        assert!(!fs::read_dir(&scratch.0).unwrap().any(|entry| {
            entry
                .unwrap()
                .file_name()
                .to_string_lossy()
                .contains(".vastitas-")
        }));
        let pid: i32 = fs::read_to_string(worker).unwrap().trim().parse().unwrap();
        // The worker may briefly be a zombie awaiting the host's init reaper.
        let status = Command::new("ps")
            .args(["-o", "stat=", "-p", &pid.to_string()])
            .output()
            .unwrap();
        let state = String::from_utf8_lossy(&status.stdout);
        assert!(
            state.trim().is_empty() || state.trim().starts_with('Z'),
            "worker still running: {state}"
        );
    }
}

#[test]
fn invalid_output_paths_fail_before_starting_the_backend() {
    let scratch = Scratch::new();
    fs::create_dir(scratch.0.join("directory")).unwrap();
    symlink("directory", scratch.0.join("directory-link")).unwrap();
    for path in [
        "",
        ".",
        "..",
        "directory",
        "directory-link",
        "new/",
        "directory/.",
        "directory/..",
        "absent/program",
        "main.vast/program",
    ] {
        let result = scratch
            .cli()
            .args(["build", "main.vast", "-o", path])
            .env("VASTITAS_KERNEL", scratch.0.join("absent-backend"))
            .output()
            .unwrap();
        let error = String::from_utf8_lossy(&result.stderr);
        assert!(!result.status.success(), "accepted {path:?}");
        assert!(error.starts_with("E_OUTPUT:"), "{path:?}: {error}");
        assert!(!error.contains("E_BACKEND"), "{error}");
    }
}

#[test]
fn output_protection_still_precedes_source_parsing() {
    let scratch = Scratch::new();
    fs::write(scratch.0.join("main.vast"), "invalid source").unwrap();
    let result = scratch
        .cli()
        .args(["build", "main.vast", "-o", "main.vast"])
        .output()
        .unwrap();
    let error = String::from_utf8_lossy(&result.stderr);
    assert!(
        error.starts_with("E_OUTPUT: output would overwrite input"),
        "{error}"
    );
}

#[test]
fn subcommand_help_succeeds_without_inputs_or_backend() {
    let scratch = Scratch::new();
    for mode in ["check", "build"] {
        for help in ["--help", "-h"] {
            let result = scratch
                .cli()
                .args([mode, help])
                .env("VASTITAS_KERNEL", scratch.0.join("absent-backend"))
                .output()
                .unwrap();
            assert!(result.status.success());
            assert!(String::from_utf8_lossy(&result.stdout).contains("Usage:"));
            assert!(result.stderr.is_empty());
        }
    }
}

#[test]
fn interrupted_backend_has_no_spawn_failure_or_rebuild_hint() {
    use nix::sys::signal::{Signal, kill};
    use nix::unistd::Pid;
    use std::time::{Duration, Instant};
    for (signal, code) in [(Signal::SIGINT, 130), (Signal::SIGTERM, 143)] {
        let scratch = Scratch::new();
        let ready = scratch.0.join("ready");
        let backend = scratch.0.join("slow-kernel");
        executable(
            &backend,
            "#!/bin/sh\ncat >/dev/null\necho ready > \"$READY\"\nexec sleep 60\n",
        );
        let mut child = scratch
            .cli()
            .args(["check", "main.vast"])
            .env("VASTITAS_KERNEL", &backend)
            .env("READY", &ready)
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(15);
        while !ready.exists() {
            assert!(Instant::now() < deadline, "backend did not start");
            assert!(child.try_wait().unwrap().is_none());
            std::thread::sleep(Duration::from_millis(10));
        }
        kill(Pid::from_raw(child.id() as i32), signal).unwrap();
        while child.try_wait().unwrap().is_none() {
            if Instant::now() >= deadline {
                child.kill().unwrap();
                child.wait().unwrap();
                panic!("backend interruption did not terminate");
            }
            std::thread::sleep(Duration::from_millis(20));
        }
        let result = child.wait_with_output().unwrap();
        assert_eq!(result.status.code(), Some(code));
        let error = String::from_utf8_lossy(&result.stderr);
        assert!(
            error.contains("E_INTERRUPTED: compilation interrupted"),
            "{error}"
        );
        assert!(!error.contains("cannot start"), "{error}");
        assert!(!error.contains("Build it with"), "{error}");
    }
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
        root.join(".lake/build/lib/lean/VastitasKernel/IndexedRuntime.olean"),
        root.join(".lake/build/ir/VastitasKernel/IndexedRuntime.c.o.export"),
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

#[test]
fn mismatched_failure_version_preserves_diagnostics_but_success_is_rejected() {
    let scratch = Scratch::new();
    let backend = scratch.0.join("kernel");
    executable(
        &backend,
        "#!/bin/sh\ncat >/dev/null\nprintf '%s\\n' '{\"version\":3,\"ok\":false,\"diagnostics\":[{\"code\":\"E_SENTINEL\",\"message\":\"original diagnostic\"}]}'\nexit 1\n",
    );
    let output = scratch
        .cli()
        .env("VASTITAS_KERNEL", &backend)
        .args(["check", "main.vast"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let message = String::from_utf8_lossy(&output.stderr);
    assert!(
        message.contains("E_SENTINEL: original diagnostic"),
        "{message}"
    );
    assert!(
        message.contains("note: incompatible backend protocol version"),
        "{message}"
    );
    executable(
        &backend,
        "#!/bin/sh\ncat >/dev/null\nprintf '%s\\n' '{\"version\":3,\"ok\":true}'\n",
    );
    let output = scratch
        .cli()
        .env("VASTITAS_KERNEL", &backend)
        .args(["check", "main.vast"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("E_PROTOCOL: incompatible"));
}
