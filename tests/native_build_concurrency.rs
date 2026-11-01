//! Shared optional Lake packages are build-time resources, not runtime locks.
mod common;
use common::{Scratch, cli, kernel_path, root, success};
use nix::sys::signal::{Signal, kill};
use nix::unistd::Pid;
use std::fs;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::time::{Duration, Instant};

const SOURCE: &str = "resource fn main() -> Int {
    allocate data: F64[1];
    borrow output = write(data, layout(0, 1, 1, 1, false));
    store(output, 0, 0, f64_bits(4631107791820423168));
    release(output);
    borrow input = read(data, layout(0, 1, 1, 1, false));
    expect(input, 0, 0, f64_bits(4631107791820423168));
    release(input);
    drop(data);
    value { 42 }
}";

fn executable(path: &Path, source: &str) {
    fs::write(path, source).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
}

struct Running(Option<Child>);
impl Running {
    fn start(command: &mut Command) -> Self {
        Self(Some(
            command
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap(),
        ))
    }
    fn interrupt(&self) {
        kill(
            Pid::from_raw(self.0.as_ref().unwrap().id() as i32),
            Signal::SIGINT,
        )
        .unwrap();
    }
    fn finish(mut self) -> Output {
        let deadline = Instant::now() + Duration::from_secs(30);
        while self.0.as_mut().unwrap().try_wait().unwrap().is_none() {
            assert!(Instant::now() < deadline, "native build exceeded watchdog");
            std::thread::sleep(Duration::from_millis(10));
        }
        self.0.take().unwrap().wait_with_output().unwrap()
    }
}
impl Drop for Running {
    fn drop(&mut self) {
        if let Some(child) = &mut self.0 {
            let _ = kill(Pid::from_raw(child.id() as i32), Signal::SIGTERM);
            let deadline = Instant::now() + Duration::from_secs(4);
            while child.try_wait().ok().flatten().is_none() && Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(10));
            }
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

fn wait_for(path: &Path) {
    let deadline = Instant::now() + Duration::from_secs(10);
    while !path.exists() {
        assert!(
            Instant::now() < deadline,
            "no handshake at {}",
            path.display()
        );
        std::thread::sleep(Duration::from_millis(10));
    }
}

fn fixture() -> Scratch {
    let s = Scratch::empty("native concurrency");
    s.write(
        "Vastitas.toml",
        "[package]\nname = \"concurrency\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n",
    );
    s.write("main.vast", SOURCE);
    s.write(
        "kernel/lean-toolchain",
        include_str!("../lean-kernel/lean-toolchain"),
    );
    s.write("kernel/native/marker", "");
    s.write("kernel/numerical/marker", "");
    s
}

fn build(s: &Scratch, kernel: &Path, name: &str) -> Command {
    let mut command = cli();
    command
        .args(["build", "--manifest-path"])
        .arg(s.0.join("Vastitas.toml"))
        .arg("-o")
        .arg(s.0.join(name))
        .env("VASTITAS_KERNEL", kernel_path())
        .env("VASTITAS_KERNEL_ROOT", kernel);
    command
}

fn mock_path(s: &Scratch) -> std::ffi::OsString {
    let mut paths = vec![s.0.join("bin")];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    std::env::join_paths(paths).unwrap()
}

fn mocked(s: &Scratch, kernel: &Path, name: &str) -> Command {
    let backend = s.0.join("backend");
    if !backend.exists() {
        executable(
            &backend,
            r#"#!/bin/sh
cat >/dev/null
if [ -n "$BUILD_TEST_READY" ]; then : > "$BUILD_TEST_READY"; fi
printf '%s\n' "{\"version\":8,\"ok\":true,\"lean_source\":\"def main : IO Unit := pure ()\",\"storage_runtime\":true,\"numerical_runtime\":${BUILD_TEST_NUMERICAL:-false}}"
"#,
        );
        let lake = s.write("bin/lake", "");
        executable(
            &lake,
            r#"#!/bin/sh
if [ -n "$BUILD_TEST_ENTERED" ]; then : > "$BUILD_TEST_ENTERED"; fi
if [ -n "$BUILD_TEST_RELEASE" ]; then
  while [ ! -f "$BUILD_TEST_RELEASE" ]; do sleep 0.01; done
fi
if [ -n "$BUILD_TEST_FAIL" ]; then exit 7; fi
mkdir -p .lake/build/bin
printf '#!/bin/sh\nprintf "42\\n"\n' > .lake/build/bin/program
chmod +x .lake/build/bin/program
"#,
        );
    }
    let mut command = build(s, kernel, name);
    command
        .env("VASTITAS_KERNEL", backend)
        .env("PATH", mock_path(s));
    command
}

#[test]
fn same_optional_package_serializes_but_independent_roots_do_not() {
    let s = fixture();
    let kernel = s.0.join("kernel");
    let alias = s.0.join("kernel alias");
    symlink(&kernel, &alias).unwrap();
    let entered = s.0.join("first entered");
    let release = s.0.join("release");
    let first = Running::start(
        mocked(&s, &kernel, "first")
            .env("BUILD_TEST_ENTERED", &entered)
            .env("BUILD_TEST_RELEASE", &release),
    );
    wait_for(&entered);
    let ready = s.0.join("second ready");
    let second_entered = s.0.join("second entered");
    let second = Running::start(
        mocked(&s, &alias, "second")
            .env("BUILD_TEST_READY", &ready)
            .env("BUILD_TEST_ENTERED", &second_entered),
    );
    wait_for(&ready);
    let pure_backend = s.0.join("pure backend");
    executable(
        &pure_backend,
        "#!/bin/sh\ncat >/dev/null\nprintf '%s\\n' '{\"version\":2,\"ok\":true,\"lean_source\":\"def main : IO Unit := pure ()\"}'\n",
    );
    let mut pure = cli();
    pure.arg("build")
        .arg(s.write("pure.vast", "fn main() -> Int { 42 }"))
        .arg("-o")
        .arg(s.0.join("pure"))
        .env("VASTITAS_KERNEL", pure_backend)
        .env("VASTITAS_KERNEL_ROOT", &kernel)
        .env("PATH", mock_path(&s));
    success(&Running::start(&mut pure).finish());
    // This build must finish while the first still owns its package. A global
    // compiler mutex would block it, even though it has no shared dependency.
    let other = fixture();
    success(&Running::start(&mut mocked(&other, &other.0.join("kernel"), "independent")).finish());
    std::thread::sleep(Duration::from_millis(200));
    assert!(
        !second_entered.exists(),
        "aliased native package was built concurrently"
    );
    fs::write(release, "").unwrap();
    success(&first.finish());
    success(&second.finish());
    assert!(second_entered.exists());
}

#[test]
fn waiting_for_either_package_is_interruptible_and_failure_releases_locks() {
    for numerical in [false, true] {
        let s = fixture();
        let kernel = s.0.join("kernel");
        let held =
            fs::File::open(kernel.join(if numerical { "numerical" } else { "native" })).unwrap();
        held.try_lock().unwrap();
        // Another test's concurrently spawned process can briefly inherit this
        // file description before exec closes it. Model that shared ownership.
        let _inherited_held = held.try_clone().unwrap();
        let ready = s.0.join("ready");
        let entered = s.0.join("entered");
        let output = s.write("program", "existing artifact");
        let mut command = mocked(&s, &kernel, "program");
        command
            .env("BUILD_TEST_READY", &ready)
            .env("BUILD_TEST_ENTERED", &entered);
        if numerical {
            command
                .env("BUILD_TEST_NUMERICAL", "true")
                .arg("--openblas-prefix")
                .arg(&s.0);
        }
        let child = Running::start(&mut command);
        wait_for(&ready);
        std::thread::sleep(Duration::from_millis(200));
        assert!(
            !entered.exists(),
            "Lake started before the package became available"
        );
        child.interrupt();
        let result = child.finish();
        assert_eq!(result.status.code(), Some(130));
        assert!(String::from_utf8_lossy(&result.stderr).contains("E_INTERRUPTED"));
        assert_eq!(fs::read(&output).unwrap(), b"existing artifact");
        // Release the fixture's lock even if an inherited descriptor is still
        // open. Dropping only this handle need not release the shared flock.
        held.unlock().unwrap();
        drop(held);
        // Cancellation while holding the earlier lock must release that lock.
        for directory in ["native", "numerical"] {
            fs::File::open(kernel.join(directory))
                .unwrap()
                .try_lock()
                .unwrap();
        }
        command
            .env_remove("BUILD_TEST_READY")
            .env("BUILD_TEST_FAIL", "1");
        let failed = Running::start(&mut command).finish();
        assert!(!failed.status.success());
        assert!(String::from_utf8_lossy(&failed.stderr).contains("native compilation failed"));
        assert_eq!(fs::read(&output).unwrap(), b"existing artifact");
        command.env_remove("BUILD_TEST_FAIL");
        success(&Running::start(&mut command).finish());
    }
}

fn copy_sources(source: &Path, destination: &Path) {
    fs::create_dir_all(destination).unwrap();
    for entry in fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        if entry.file_name() == ".lake" {
            continue;
        }
        let target = destination.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_sources(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), target).unwrap();
        }
    }
}

#[test]
fn simultaneous_cold_resource_builds_execute_and_reuse_native_artifacts() {
    let s = fixture();
    let kernel = s.0.join("kernel");
    s.write(
        "kernel/lakefile.toml",
        "name = \"vastitas_kernel\"\n[[lean_lib]]\nname = \"VastitasKernel\"\n",
    );
    s.write(
        "kernel/VastitasKernel/IndexedRuntime.lean",
        include_str!("../lean-kernel/VastitasKernel/IndexedRuntime.lean"),
    );
    copy_sources(&root().join("lean-kernel/native"), &kernel.join("native"));
    assert!(!kernel.join("native/.lake").exists());
    let alias = s.0.join("kernel alias");
    symlink(&kernel, &alias).unwrap();
    let first = Running::start(&mut build(&s, &kernel, "first"));
    let second = Running::start(&mut build(&s, &alias, "second"));
    success(&first.finish());
    success(&second.finish());
    let artifacts: Vec<PathBuf> = [
        ".lake/build/lib/lean/VastitasStorageNative.olean",
        ".lake/build/storage.o",
    ]
    .into_iter()
    .map(|p| kernel.join("native").join(p))
    .collect();
    let before: Vec<_> = artifacts
        .iter()
        .map(|p| fs::metadata(p).unwrap().modified().unwrap())
        .collect();
    success(&Running::start(&mut build(&s, &kernel, "third")).finish());
    for (path, time) in artifacts.iter().zip(before) {
        assert_eq!(
            fs::metadata(path).unwrap().modified().unwrap(),
            time,
            "rebuilt {}",
            path.display()
        );
    }
    for name in ["first", "second", "third"] {
        let output = Command::new(s.0.join(name)).output().unwrap();
        success(&output);
        assert_eq!(output.stdout, b"42\n");
    }
}
