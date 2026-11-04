//! Host driver. Semantic acceptance always comes from the Lean backend.
use crate::ir::Span;
use crate::sources::Sources;
use serde_json::{Value, json};
use std::ffi::{OsStr, OsString};
use std::fs::{self, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);
const USAGE: &str = "Vastitas Stage 1b\n\nUsage:\n  vastitas check INPUT.vast [--lib LIBRARY.vast]...\n  vastitas build INPUT.vast [--lib LIBRARY.vast]... -o OUTPUT\n  vastitas check --manifest-path Vastitas.toml\n  vastitas build --manifest-path Vastitas.toml -o OUTPUT [--openblas-prefix PREFIX] [--native-cc COMPILER]\n  vastitas audit-lean LEAN4EXPORT.ndjson\n\n--lib adds explicitly selected source libraries to the same checked compilation unit.\nManifest mode accepts local path packages and cannot be mixed with INPUT.vast or --lib.\nNumerical builds require pinned sequential LP64 OpenBLAS 0.3.34 via --openblas-prefix.\n--native-cc explicitly selects the compiler/linker for numerical builds (for example cc on Linux).\nBuild the backend first: lake -d lean-kernel build vastitas-kernel\n";

struct Options {
    mode: &'static str,
    input: Option<PathBuf>,
    manifest: Option<PathBuf>,
    libraries: Vec<PathBuf>,
    output: Option<PathBuf>,
    openblas: Option<PathBuf>,
    native_cc: Option<OsString>,
}

fn options(args: &[OsString]) -> Result<Options, String> {
    let usage = || format!("E_USAGE: invalid arguments\n{USAGE}");
    let mode = match args.first().and_then(|arg| arg.to_str()) {
        Some("check") => "check",
        Some("build") => "emit",
        _ => return Err(usage()),
    };
    let mut input = None;
    let mut output = None;
    let mut libraries = Vec::new();
    let mut manifest = None;
    let mut openblas = None;
    let mut native_cc = None;
    let mut remaining = args.iter().skip(1);
    while let Some(arg) = remaining.next() {
        if arg == "--manifest-path" {
            if manifest.is_some() {
                return Err(usage());
            }
            let path = remaining.next().ok_or_else(usage)?;
            if path.to_string_lossy().starts_with('-') {
                return Err(usage());
            }
            manifest = Some(PathBuf::from(path));
        } else if arg == "--openblas-prefix" || arg == "--native-cc" {
            if mode != "emit" {
                return Err(usage());
            }
            let value = remaining.next().ok_or_else(usage)?;
            if value.is_empty() || value.to_string_lossy().starts_with('-') {
                return Err(usage());
            }
            if arg == "--openblas-prefix" {
                if openblas.replace(PathBuf::from(value)).is_some() {
                    return Err(usage());
                }
            } else if native_cc.replace(value.clone()).is_some() {
                return Err(usage());
            }
        } else if arg == "--lib" {
            let path = remaining.next().ok_or_else(usage)?;
            if path.to_string_lossy().starts_with('-') {
                return Err(usage());
            }
            libraries.push(PathBuf::from(path));
        } else if arg == "-o" {
            if mode != "emit" || output.is_some() {
                return Err(usage());
            }
            let path = remaining.next().ok_or_else(usage)?;
            if path.to_string_lossy().starts_with('-') {
                return Err(usage());
            }
            output = Some(PathBuf::from(path));
        } else if arg.to_string_lossy().starts_with('-') || input.is_some() {
            return Err(usage());
        } else {
            input = Some(PathBuf::from(arg));
        }
    }
    if mode == "emit" && output.is_none() {
        return Err(usage());
    }
    if manifest.is_some() == input.is_some() || (manifest.is_some() && !libraries.is_empty()) {
        return Err(usage());
    }
    Ok(Options {
        mode,
        input,
        manifest,
        libraries,
        output,
        openblas,
        native_cc,
    })
}

pub fn run(args: impl Iterator<Item = OsString>) -> Result<(), String> {
    let args: Vec<_> = args.collect();
    // The isolated audit worker never polls the cancellation flag. It keeps the
    // default signal dispositions, so a forwarded SIGINT/SIGTERM stops it at once.
    if args
        .first()
        .is_some_and(|command| command == crate::internal_lean_audit::WORKER_COMMAND)
    {
        return crate::internal_lean_audit::run_worker(&args[1..]);
    }
    crate::process::install()
        .map_err(|error| format!("E_BACKEND: cannot install signal handlers: {error}"))?;
    let subcommand_help = args.len() == 2
        && (args[0] == "check" || args[0] == "build" || args[0] == "audit-lean")
        && (args[1] == "--help" || args[1] == "-h");
    if args.is_empty() || args == ["--help"] || args == ["-h"] || subcommand_help {
        print!("{USAGE}");
        return Ok(());
    }
    if args == ["--version"] {
        let protocols = crate::packages::PUBLIC_PROTOCOLS.map(|version| version.to_string());
        println!(
            "vastitas {} (wire protocols {})",
            env!("CARGO_PKG_VERSION"),
            protocols.join("/")
        );
        return Ok(());
    }
    if args.first().is_some_and(|command| command == "audit-lean") {
        return crate::internal_lean_audit::run_cli(&args[1..]);
    }
    let Options {
        mode,
        input,
        manifest,
        libraries,
        output,
        openblas,
        native_cc,
    } = options(&args)?;
    if let Some(output) = &output {
        validate_output(output)?;
        probe_output_directory(output)?;
    }
    let display_input = manifest.as_ref().or(input.as_ref()).unwrap().clone();
    let (sources, request, version) = if let Some(manifest) = manifest {
        let (sources, module) = crate::packages::load(&manifest, output.as_deref())?;
        let request = serde_json::to_vec(&module)
            .map_err(|error| format!("E_PROTOCOL: cannot encode packages: {error}"))?;
        (sources, request, module.version)
    } else {
        let sources = Sources::load(input.as_ref().unwrap(), &libraries)?;
        if let Some(output) = &output {
            sources.protect_output(output)?;
        }
        let module = sources.parse()?;
        let request = serde_json::to_vec(&module)
            .map_err(|error| format!("E_PROTOCOL: cannot encode module: {error}"))?;
        (sources, request, module.version)
    };
    let configured_executable = std::env::var_os("VASTITAS_KERNEL").map(PathBuf::from);
    let default_executable = configured_executable.is_none();
    let root = if output.is_some() || default_executable {
        Some(kernel_root()?)
    } else {
        None
    };
    if output.is_some() {
        // Native builds embed the root in a generated Lake manifest.
        manifest_text(
            root.as_ref().expect("native build requires kernel root"),
            "kernel root",
        )?;
    }
    let executable = configured_executable.unwrap_or_else(|| {
        root.as_ref()
            .expect("default executable requires kernel root")
            .join(".lake/build/bin/vastitas-kernel")
    });
    if default_executable && !executable.is_file() {
        let root = root
            .as_deref()
            .expect("default executable requires kernel root");
        return Err(missing_kernel(root, &executable));
    }
    let response = invoke_kernel(
        &executable,
        mode,
        &request,
        &sources,
        version,
        root.as_deref(),
    )?;
    if let Some(output) = output {
        let lean_source = response
            .get("lean_source")
            .and_then(Value::as_str)
            .ok_or_else(|| "E_PROTOCOL: backend omitted generated Lean source".to_string())?;
        let storage_runtime = match response.get("storage_runtime") {
            None => false,
            Some(Value::Bool(required))
                if matches!(
                    version,
                    crate::packages::RESOURCE_PROTOCOL | crate::packages::NAMED_RECIPIENT_PROTOCOL
                ) =>
            {
                *required
            }
            Some(_) => {
                return Err("E_PROTOCOL: invalid optional storage runtime requirement".into());
            }
        };
        let numerical_runtime = match response.get("numerical_runtime") {
            None => false,
            Some(Value::Bool(required))
                if matches!(
                    version,
                    crate::packages::RESOURCE_PROTOCOL | crate::packages::NAMED_RECIPIENT_PROTOCOL
                ) =>
            {
                *required
            }
            Some(_) => {
                return Err("E_PROTOCOL: invalid optional numerical runtime requirement".into());
            }
        };
        if numerical_runtime && !storage_runtime {
            return Err(
                "E_PROTOCOL: numerical runtime requires the checked storage runtime".into(),
            );
        }
        if numerical_runtime && openblas.is_none() {
            return Err("E_BUILD: numerical program requires --openblas-prefix with pinned sequential LP64 OpenBLAS 0.3.34".into());
        }
        if !numerical_runtime && (openblas.is_some() || native_cc.is_some()) {
            return Err("E_USAGE: --openblas-prefix and --native-cc require a program with checked numerical operations".into());
        }
        build_native(
            root.as_ref().expect("native build requires kernel root"),
            lean_source,
            &output,
            &sources,
            storage_runtime,
            openblas.as_deref(),
            native_cc.as_deref(),
        )?;
        println!("built {}", output.display());
    } else {
        println!("checked {}", display_input.display());
    }
    Ok(())
}

pub fn failure_exit_code() -> i32 {
    crate::process::exit_code()
}

fn kernel_root() -> Result<PathBuf, String> {
    let root = std::env::var_os("VASTITAS_KERNEL_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("lean-kernel"));
    root.canonicalize()
        .map_err(|error| format!("E_BACKEND: cannot locate {}: {error}", root.display()))
}

// Build-time identity of the kernel sources next to this driver (see build.rs).
mod expected_kernel {
    include!(concat!(env!("OUT_DIR"), "/kernel_identity.rs"));
}

// Responses may carry generated Lean for the whole program; bound them anyway.
const MAX_BACKEND_RESPONSE: usize = 256 * 1024 * 1024;

/// Every kernel response reports the digest of the Lean sources it was compiled
/// from and its Lean version. Protocol numbers stay fixed across releases, so
/// only this identity ties the checker to this driver and its runtime sources.
fn kernel_identity_problem(response: &Value) -> Option<String> {
    let identity = response.get("kernel");
    let field = |name| {
        identity
            .and_then(|value| value.get(name))
            .and_then(Value::as_str)
    };
    match (field("sources"), field("lean")) {
        (Some(sources), Some(lean))
            if sources == expected_kernel::SOURCES && lean == expected_kernel::LEAN =>
        {
            None
        }
        (Some(sources), Some(lean)) => Some(format!(
            "the kernel was built from kernel sources {sources} with Lean {lean}, but this compiler requires kernel sources {} with Lean {}",
            expected_kernel::SOURCES,
            expected_kernel::LEAN
        )),
        _ => Some("the backend did not report a Vastitas kernel build identity".into()),
    }
}

fn rebuild_advice(root: Option<&Path>) -> String {
    let build = root.map_or_else(
        || "lake -d <kernel root> build vastitas-kernel".to_string(),
        |root| format!("lake -d {} build vastitas-kernel", root.display()),
    );
    format!(
        "Rebuild the kernel from the same Vastitas sources as this compiler: {build}\n\
         VASTITAS_KERNEL_ROOT and VASTITAS_KERNEL must name a kernel of this compiler's version."
    )
}

/// An installed driver falls back to its build-time source directory, which may be
/// Cargo's registry cache; Cargo removes unused extracted sources automatically.
fn missing_kernel(root: &Path, executable: &Path) -> String {
    let build = format!("lake -d {} build vastitas-kernel", root.display());
    let advice = if std::env::var_os("VASTITAS_KERNEL_ROOT").is_some() {
        format!("Build it with: {build}")
    } else {
        format!(
            "VASTITAS_KERNEL_ROOT is not set; the default is this compiler's build-time source directory.\n\
             In a source checkout, build it with: {build}\n\
             After cargo install, that directory is Cargo's registry cache, which Cargo cleans \
             automatically. Extract the matching crate, build its lean-kernel and set \
             VASTITAS_KERNEL_ROOT to that absolute path (README: Install the alpha)."
        )
    };
    format!(
        "E_BACKEND: kernel executable {} is not built\n{advice}",
        executable.display()
    )
}

fn invoke_kernel(
    executable: &Path,
    mode: &str,
    request: &[u8],
    sources: &Sources,
    version: u32,
    root: Option<&Path>,
) -> Result<Value, String> {
    let mut command = Command::new(executable);
    command.arg(mode);
    let retention = crate::process::Retention::Complete(MAX_BACKEND_RESPONSE);
    let output = crate::process::capture(command, Some(request), retention).map_err(|error| {
        subprocess_error(error, "E_BACKEND", &executable.display().to_string(), true)
    })?;
    let response: Value = serde_json::from_slice(&output.stdout).map_err(|error| {
        format!(
            "E_PROTOCOL: invalid backend response: {error}\n{}",
            String::from_utf8_lossy(&output.stderr)
        )
    })?;
    let identity_problem = kernel_identity_problem(&response);
    let version_mismatch = response.get("version") != Some(&json!(version));
    if response.get("ok") == Some(&Value::Bool(false)) {
        let diagnostics = response
            .get("diagnostics")
            .and_then(Value::as_array)
            .filter(|items| !items.is_empty())
            .ok_or_else(|| "E_PROTOCOL: backend failure has no diagnostics".to_string())?;
        let mut rendered = diagnostics
            .iter()
            .map(|item| {
                let code = item
                    .get("code")
                    .and_then(Value::as_str)
                    .unwrap_or("E_BACKEND");
                let message = item
                    .get("message")
                    .and_then(Value::as_str)
                    .unwrap_or("backend rejected input");
                let mut rendered = sources.diagnostic(code, message, response_span(item));
                if let Some(notes) = item.get("notes").and_then(Value::as_array) {
                    for note in notes {
                        if let Some(message) = note.get("message").and_then(Value::as_str) {
                            rendered.push('\n');
                            rendered.push_str(&sources.diagnostic(
                                "note",
                                message,
                                response_span(note),
                            ));
                        }
                    }
                }
                rendered
            })
            .collect::<Vec<_>>()
            .join("\n");
        if version_mismatch {
            rendered.push_str("\nnote: incompatible backend protocol version in failure response");
        }
        if let Some(problem) = identity_problem {
            rendered.push_str(&format!(
                "\nnote: these diagnostics may come from a stale or foreign kernel: {problem}\n{}",
                rebuild_advice(root)
            ));
        }
        return Err(rendered);
    }
    if version_mismatch {
        return Err("E_PROTOCOL: incompatible backend protocol version".into());
    }
    if response.get("ok") != Some(&Value::Bool(true)) || !output.status.success() {
        let note = identity_problem.map_or_else(String::new, |problem| {
            format!("\nnote: {problem}\n{}", rebuild_advice(root))
        });
        return Err(format!(
            "E_BACKEND: backend failed ({})\n{}{note}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    if let Some(problem) = identity_problem {
        return Err(format!(
            "E_BACKEND: incompatible kernel {}: {problem}\n{}",
            executable.display(),
            rebuild_advice(root)
        ));
    }
    Ok(response)
}

fn response_span(item: &Value) -> Span {
    let span = item.get("span");
    let field = |name, default| {
        span.and_then(|value| value.get(name))
            .and_then(Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
            .unwrap_or(default)
    };
    Span {
        start: field("start", 0),
        end: field("end", 0),
        line: field("line", 1),
        column: field("column", 1),
    }
}

struct BuildDirectory(PathBuf);

impl BuildDirectory {
    fn create() -> Result<Self, String> {
        for _ in 0..100 {
            let path = std::env::temp_dir().join(format!(
                "vastitas-{}-{}",
                std::process::id(),
                NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
            ));
            // The name is predictable and Lake executes the generated lakefile,
            // so only the invoking user may enter the directory, whatever the umask.
            match fs::DirBuilder::new().mode(0o700).create(&path) {
                Ok(()) => {
                    let directory = Self(path);
                    fs::set_permissions(&directory.0, fs::Permissions::from_mode(0o700)).map_err(
                        |error| format!("E_BUILD: cannot secure build directory: {error}"),
                    )?;
                    return Ok(directory);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => {
                    return Err(format!("E_BUILD: cannot create build directory: {error}"));
                }
            }
        }
        Err("E_BUILD: cannot allocate a unique build directory".into())
    }
}

impl Drop for BuildDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Name of the fallback lock file for filesystems that cannot lock directories.
const PACKAGE_LOCK_FILE: &str = ".vastitas-build.lock";

/// Errors meaning that this filesystem cannot flock a read-only directory
/// descriptor. Linux NFS emulates flock with byte-range locks, and an exclusive
/// byte-range lock requires a descriptor opened for writing (`EBADF`).
fn directory_lock_unsupported(error: &std::io::Error) -> bool {
    use nix::errno::Errno;
    error.raw_os_error().is_some_and(|code| {
        [
            Errno::EBADF,
            Errno::ENOLCK,
            Errno::EOPNOTSUPP,
            Errno::ENOTSUP,
            Errno::EINVAL,
        ]
        .iter()
        .any(|errno| *errno as i32 == code)
    })
}

fn acquire_lock(file: &fs::File) -> Result<(), std::io::Error> {
    loop {
        crate::process::check()?;
        match file.try_lock() {
            Ok(()) => return Ok(()),
            Err(fs::TryLockError::WouldBlock) => {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            Err(fs::TryLockError::Error(error))
                if error.kind() == std::io::ErrorKind::Interrupted => {}
            Err(fs::TryLockError::Error(error)) => return Err(error),
        }
    }
}

/// Lock one package directory, falling back to a read-write lock file inside it
/// where directory locks are unsupported. Every process on one filesystem takes
/// the same branch, so the fallback still excludes concurrent compiler builds.
fn lock_package(path: &Path) -> Result<fs::File, String> {
    let directory = fs::File::open(path).map_err(|error| {
        format!(
            "E_BUILD: cannot open native package {}: {error}",
            path.display()
        )
    })?;
    match acquire_lock(&directory) {
        Ok(()) => Ok(directory),
        Err(error) if directory_lock_unsupported(&error) => lock_file(path),
        Err(error) => Err(locking_error(error, path)),
    }
}

fn locking_error(error: std::io::Error, lock: &Path) -> String {
    if error.kind() == std::io::ErrorKind::Interrupted {
        "E_INTERRUPTED: compilation interrupted".to_string()
    } else {
        format!(
            "E_BUILD: cannot lock native package {}: {error}",
            lock.display()
        )
    }
}

/// The fallback: an exclusive lock on `PACKAGE_LOCK_FILE`, opened read-write.
fn lock_file(package: &Path) -> Result<fs::File, String> {
    let lock = package.join(PACKAGE_LOCK_FILE);
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o666)
        .open(&lock)
        .map_err(|error| {
            format!(
                "E_BUILD: directory locks are unsupported for native package {} and its lock file {} cannot be opened: {error}",
                package.display(),
                lock.display()
            )
        })?;
    acquire_lock(&file).map_err(|error| locking_error(error, &lock))?;
    Ok(file)
}

// Lake writes setup files and compiled objects inside local dependency packages.
// Coordinate optional-package builds across compiler processes, including path
// aliases. Lock the existing directories so no removable/stale lockfile or write
// permission on a warmed package is needed; filesystems without directory locks
// use a lock file instead (see `lock_package`). The supported Unix hosts use flock;
// direct Lake invocations must still be kept separate from compiler builds.
fn lock_native_packages(kernel_root: &Path, numerical: bool) -> Result<Vec<fs::File>, String> {
    let mut paths = vec![kernel_root.join("native")];
    if numerical {
        paths.push(kernel_root.join("numerical"));
    }
    let mut paths = paths
        .into_iter()
        .map(|path| {
            path.canonicalize().map_err(|error| {
                format!(
                    "E_BUILD: cannot locate native package {}: {error}",
                    path.display()
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    // A fixed order also handles shared packages reached from distinct roots.
    paths.sort();
    paths.dedup();
    let mut locks = Vec::new();
    for path in paths {
        let file = lock_package(&path)?;
        // Lake and its descendants must retain the flock even if the driver is
        // killed without cleanup. These handles are held only during this build.
        use nix::fcntl::{FcntlArg, FdFlag, fcntl};
        let flags = FdFlag::from_bits_truncate(
            fcntl(file.as_raw_fd(), FcntlArg::F_GETFD)
                .map_err(|error| format!("E_BUILD: cannot inspect package lock: {error}"))?,
        );
        fcntl(
            file.as_raw_fd(),
            FcntlArg::F_SETFD(flags & !FdFlag::FD_CLOEXEC),
        )
        .map_err(|error| format!("E_BUILD: cannot preserve package lock for Lake: {error}"))?;
        locks.push(file);
    }
    Ok(locks)
}

/// Path text for a generated Lake manifest. Lake reads TOML and Lean strings,
/// which cannot represent non-UTF-8 bytes, so such paths are rejected by name
/// instead of being replaced lossily.
fn manifest_text<'a>(path: &'a Path, role: &str) -> Result<&'a str, String> {
    path.to_str().ok_or_else(|| {
        format!(
            "E_BUILD: {role} path is not valid UTF-8 and cannot be written to the generated Lake manifest: {}",
            path.display()
        )
    })
}

/// A TOML basic string: escape the quote, the backslash and every control
/// character (TOML forbids raw controls other than tab).
fn toml_string(text: &str) -> String {
    let mut quoted = String::from('"');
    for character in text.chars() {
        match character {
            '"' => quoted.push_str("\\\""),
            '\\' => quoted.push_str("\\\\"),
            control if control.is_control() => {
                quoted.push_str(&format!("\\u{:04X}", control as u32));
            }
            other => quoted.push(other),
        }
    }
    quoted.push('"');
    quoted
}

/// A Lean 4 string literal. After a backslash Lean accepts only `\\ \" \' \n
/// \t \r \xHH \uHHHH` (and gaps), so other controls use four-digit `\u` escapes.
fn lean_string(text: &str) -> String {
    let mut quoted = String::from('"');
    for character in text.chars() {
        match character {
            '"' => quoted.push_str("\\\""),
            '\\' => quoted.push_str("\\\\"),
            '\n' => quoted.push_str("\\n"),
            '\t' => quoted.push_str("\\t"),
            '\r' => quoted.push_str("\\r"),
            control if control.is_control() => {
                quoted.push_str(&format!("\\u{:04X}", control as u32));
            }
            other => quoted.push(other),
        }
    }
    quoted.push('"');
    quoted
}

/// Lake compiles the shared kernel packages with whatever `lean` it resolves.
/// Resolve it the same way (same directory and environment) and require the
/// pinned version, so ELAN_TOOLCHAIN or another Lean on PATH cannot rebuild the
/// kernel artifacts with a different toolchain.
/// The caller has already required `toolchain` to be this compiler's pin, whose
/// version `build.rs` exports as `expected_kernel::LEAN`.
fn check_lean_version(directory: &Path, toolchain: &str) -> Result<(), String> {
    let expected = expected_kernel::LEAN;
    let mut command = Command::new("lean");
    command.current_dir(directory).arg("--version");
    let retention = crate::process::Retention::Complete(64 * 1024);
    let result = crate::process::capture(command, None, retention)
        .map_err(|error| subprocess_error(error, "E_BUILD", "Lean version query", false))?;
    let text = String::from_utf8_lossy(&result.stdout);
    let reported = text
        .split_once("version ")
        .map(|(_, rest)| rest.split([',', ' ', ')']).next().unwrap_or_default());
    if result.status.success() && reported == Some(expected) {
        return Ok(());
    }
    Err(format!(
        "E_BUILD: Lean toolchain mismatch: `lean --version` reports {}, but the kernel pins {}\n\
         help: use elan's lean and lake (first on PATH) without ELAN_TOOLCHAIN, so the pinned toolchain is selected",
        reported.map_or_else(|| format!("{:?}", text.trim()), str::to_string),
        toolchain.trim()
    ))
}

fn build_native(
    kernel_root: &Path,
    source: &str,
    output: &Path,
    sources: &Sources,
    storage_runtime: bool,
    numerical_prefix: Option<&Path>,
    native_cc: Option<&OsStr>,
) -> Result<(), String> {
    let toolchain_path = kernel_root.join("lean-toolchain");
    let toolchain = fs::read_to_string(&toolchain_path)
        .map_err(|error| format!("E_BUILD: cannot read {}: {error}", toolchain_path.display()))?;
    if toolchain.trim().is_empty() {
        return Err(format!(
            "E_BUILD: empty toolchain in {}",
            toolchain_path.display()
        ));
    }
    if toolchain.trim() != expected_kernel::TOOLCHAIN {
        return Err(format!(
            "E_BUILD: kernel root {} pins {}, but this compiler was built for {}\n{}",
            kernel_root.display(),
            toolchain.trim(),
            expected_kernel::TOOLCHAIN,
            rebuild_advice(Some(kernel_root))
        ));
    }
    let root_text = manifest_text(kernel_root, "kernel root")?;
    let native_root = kernel_root.join("native");
    let native_text = manifest_text(&native_root, "native runtime")?;
    let numerical_root = kernel_root.join("numerical");
    let directory = BuildDirectory::create()?;
    let path = &directory.0;
    let optional_storage = if storage_runtime {
        format!(
            "\n[[require]]\nname = \"vastitas_storage_native\"\npath = {}\n",
            toml_string(native_text)
        )
    } else {
        String::new()
    };
    let (manifest_name, manifest) = if let Some(prefix) = numerical_prefix {
        let prefix = prefix.canonicalize().map_err(|error| {
            format!(
                "E_BUILD: cannot locate OpenBLAS prefix {}: {error}",
                prefix.display()
            )
        })?;
        let prefix = lean_string(manifest_text(&prefix, "OpenBLAS prefix")?);
        let numerical = lean_string(manifest_text(&numerical_root, "numerical runtime")?);
        let package_options = if native_cc.is_some() {
            // Select host libc while retaining the pinned Lean C++ support
            // libraries. Do not add Lean's portable lib/glibc to this path.
            let mut command = Command::new("lean");
            command.current_dir(kernel_root).arg("--print-prefix");
            let retention = crate::process::Retention::Complete(64 * 1024);
            let result = crate::process::capture(command, None, retention)
                .map_err(|error| subprocess_error(error, "E_BUILD", "Lean prefix query", false))?;
            if !result.status.success() {
                return Err("E_BUILD: cannot query the pinned Lean installation".into());
            }
            let lean_prefix = std::str::from_utf8(&result.stdout)
                .map_err(|_| "E_BUILD: invalid Lean installation path".to_string())?
                .trim();
            if lean_prefix.is_empty() {
                return Err("E_BUILD: empty Lean installation path".into());
            }
            let library = Path::new(lean_prefix).join("lib");
            let library_path = lean_string(manifest_text(&library, "Lean library")?);
            format!(" where\n  moreLinkArgs := #[\"-L\", {library_path}]")
        } else {
            String::new()
        };
        let dependency_path = lean_string(root_text);
        (
            "lakefile.lean",
            format!(
                "import Lake\nopen Lake DSL\npackage vastitas_program{package_options}\n\nrequire vastitas_kernel from {dependency_path}\nrequire vastitas_gemm_native from {numerical} with\n  NameMap.empty.insert `openblas {prefix}\n\n@[default_target]\nlean_exe program where root := `Main\n"
            ),
        )
    } else {
        let dependency_path = toml_string(root_text);
        (
            "lakefile.toml",
            format!(
                "name = \"vastitas_program\"\nversion = \"0.1.0\"\ndefaultTargets = [\"program\"]\n\n[[require]]\nname = \"vastitas_kernel\"\npath = {dependency_path}\n{optional_storage}\n[[lean_exe]]\nname = \"program\"\nroot = \"Main\"\n"
            ),
        )
    };
    for (name, contents) in [
        (manifest_name, manifest.as_str()),
        ("lean-toolchain", toolchain.as_str()),
        ("Main.lean", source),
    ] {
        fs::write(path.join(name), contents)
            .map_err(|error| format!("E_BUILD: cannot write {name}: {error}"))?;
    }
    check_lean_version(path, &toolchain)?;
    let _native_locks = if storage_runtime {
        lock_native_packages(kernel_root, numerical_prefix.is_some())?
    } else {
        Vec::new()
    };
    let mut command = Command::new("lake");
    command.current_dir(path).args(["build", "program"]);
    if let Some(compiler) = native_cc {
        command.env("LEAN_CC", compiler);
    }
    // Lake's output only explains failures; keep a bounded tail of it.
    let retention = crate::process::Retention::Tail(crate::process::DIAGNOSTIC_TAIL);
    let result = crate::process::capture(command, None, retention)
        .map_err(|error| subprocess_error(error, "E_BUILD", "Lake", false))?;
    if !result.status.success() {
        let hint = if cfg!(target_os = "linux") && numerical_prefix.is_some() && native_cc.is_none()
        {
            "\nhelp: on Linux, pass --native-cc cc to link with the host libc used to build OpenBLAS\n"
        } else {
            ""
        };
        return Err(format!(
            "E_BUILD: native compilation failed ({})\n{}{}{hint}",
            result.status,
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        ));
    }
    install_output(&path.join(".lake/build/bin/program"), output, sources)
}

struct StagingFile(PathBuf);
impl Drop for StagingFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn subprocess_error(
    error: crate::process::CaptureError,
    code: &str,
    program: &str,
    backend_hint: bool,
) -> String {
    use crate::process::CaptureError;
    match error {
        CaptureError::Interrupted => "E_INTERRUPTED: compilation interrupted".into(),
        CaptureError::Spawn(error) => {
            let hint = if backend_hint {
                "\nBuild it with: lake -d lean-kernel build vastitas-kernel"
            } else {
                ""
            };
            format!("{code}: cannot start {program}: {error}{hint}")
        }
        CaptureError::Wait(error) => format!("{code}: waiting for {program} failed: {error}"),
        CaptureError::Io(error) => format!("{code}: {program} I/O failed: {error}"),
        CaptureError::OutputLimit(limit) => format!(
            "{code}: {program} wrote more than {} MiB to standard output",
            limit / (1024 * 1024)
        ),
    }
}

fn validate_output(output: &Path) -> Result<(), String> {
    // Path::file_name normalizes trailing separators and `/.`; inspect the
    // original spelling as well so a directory request cannot become a file.
    let last = output
        .as_os_str()
        .as_bytes()
        .rsplit(|byte| *byte == b'/')
        .next();
    if output.file_name().is_none() || matches!(last, Some(b"" | b"." | b"..")) {
        return Err("E_OUTPUT: output must name a file".into());
    }
    let parent = output
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let metadata = fs::metadata(parent).map_err(|error| {
        format!(
            "E_OUTPUT: cannot inspect parent {}: {error}",
            parent.display()
        )
    })?;
    if !metadata.is_dir() {
        return Err(format!(
            "E_OUTPUT: parent is not a directory: {}",
            parent.display()
        ));
    }
    match fs::symlink_metadata(output) {
        Ok(metadata) if metadata.is_file() => Ok(()),
        Ok(metadata)
            if metadata.is_symlink()
                && fs::metadata(output).is_ok_and(|target| target.is_file()) =>
        {
            Ok(())
        }
        Ok(_) => Err(format!(
            "E_OUTPUT: output must name a regular file: {}",
            output.display()
        )),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!(
            "E_OUTPUT: cannot inspect {}: {error}",
            output.display()
        )),
    }
}

fn parent_directory(path: &Path) -> &Path {
    path.parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."))
}

/// The file that `-o OUTPUT` replaces. A symlink to a regular file is written
/// through: the binary is staged beside the link's final target and renamed
/// onto it, so the link survives. Input protection compares canonical targets,
/// so it refuses exactly the outputs whose installation would replace an input.
fn install_target(output: &Path) -> Result<PathBuf, String> {
    match fs::symlink_metadata(output) {
        Ok(metadata) if metadata.is_symlink() => output.canonicalize().map_err(|error| {
            format!(
                "E_OUTPUT: cannot resolve symlink {}: {error}",
                output.display()
            )
        }),
        Ok(_) => Ok(output.to_path_buf()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(output.to_path_buf()),
        Err(error) => Err(format!(
            "E_OUTPUT: cannot inspect {}: {error}",
            output.display()
        )),
    }
}

/// Create a new staging file beside `target`. Names are retried, so a file
/// left by a killed run whose PID was reused cannot block later builds.
fn create_staging(target: &Path) -> std::io::Result<(PathBuf, fs::File)> {
    let parent = parent_directory(target);
    for _ in 0..100 {
        let staging = parent.join(format!(
            ".vastitas-{}-{}.tmp",
            std::process::id(),
            NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
        ));
        match OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&staging)
        {
            Ok(file) => return Ok((staging, file)),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    Err(std::io::Error::new(
        std::io::ErrorKind::AlreadyExists,
        "cannot allocate a unique staging file",
    ))
}

/// Before any backend or Lake work, prove that the installation directory
/// accepts a staging file.
fn probe_output_directory(output: &Path) -> Result<(), String> {
    let target = install_target(output)?;
    let (staging, file) = create_staging(&target).map_err(|error| {
        format!(
            "E_OUTPUT: cannot write to output directory {}: {error}",
            parent_directory(&target).display()
        )
    })?;
    drop(file);
    fs::remove_file(&staging).map_err(|error| {
        format!(
            "E_OUTPUT: cannot remove probe {}: {error}",
            staging.display()
        )
    })
}

fn install_output(binary: &Path, output: &Path, sources: &Sources) -> Result<(), String> {
    validate_output(output)?;
    sources.protect_output(output)?;
    let target = install_target(output)?;
    let (staging, mut file) = create_staging(&target)
        .map_err(|error| format!("E_OUTPUT: cannot stage {}: {error}", output.display()))?;
    let _staging_guard = StagingFile(staging.clone());
    let result = (|| {
        let mut compiled = fs::File::open(binary)?;
        let mut buffer = [0u8; 65536];
        loop {
            crate::process::check()?;
            let count = compiled.read(&mut buffer)?;
            if count == 0 {
                break;
            }
            file.write_all(&buffer[..count])?;
        }
        file.set_permissions(compiled.metadata()?.permissions())?;
        file.sync_all()?;
        crate::process::check()?;
        validate_output(output).map_err(std::io::Error::other)?;
        sources
            .protect_output(output)
            .map_err(std::io::Error::other)?;
        if install_target(output).map_err(std::io::Error::other)? != target {
            return Err(std::io::Error::other(
                "the output symlink changed during the build",
            ));
        }
        fs::rename(&staging, &target)
    })();
    if let Err(error) = result {
        let _ = fs::remove_file(&staging);
        if error.kind() == std::io::ErrorKind::Interrupted {
            return Err("E_INTERRUPTED: compilation interrupted".into());
        }
        return Err(format!(
            "E_OUTPUT: cannot install {}: {error}",
            output.display()
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn manifest_strings_use_their_own_syntax() {
        let text = "a\u{8}b\u{c}c\"d\\e\nf\tg\u{7f}h\u{1b}é";
        assert_eq!(
            toml_string(text),
            "\"a\\u0008b\\u000Cc\\\"d\\\\e\\u000Af\\u0009g\\u007Fh\\u001Bé\""
        );
        assert_eq!(
            lean_string(text),
            "\"a\\u0008b\\u000Cc\\\"d\\\\e\\nf\\tg\\u007Fh\\u001Bé\""
        );
        let parsed: toml::Value = toml::from_str(&format!("path = {}", toml_string(text))).unwrap();
        assert_eq!(parsed["path"].as_str(), Some(text));
    }

    #[test]
    fn non_utf8_manifest_paths_are_named() {
        let path = Path::new(OsStr::from_bytes(b"/tmp/root\xff"));
        let error = manifest_text(path, "kernel root").unwrap_err();
        assert!(error.starts_with("E_BUILD: kernel root path is not valid UTF-8"));
        assert!(error.contains("/tmp/root"));
    }

    #[test]
    fn package_lock_falls_back_to_an_exclusive_lock_file() {
        use nix::errno::Errno;
        for errno in [Errno::EBADF, Errno::ENOLCK, Errno::EOPNOTSUPP] {
            assert!(directory_lock_unsupported(
                &std::io::Error::from_raw_os_error(errno as i32)
            ));
        }
        assert!(!directory_lock_unsupported(
            &std::io::Error::from_raw_os_error(Errno::EACCES as i32)
        ));
        let package = std::env::temp_dir().join(format!(
            "vastitas-lock-test-{}-{}",
            std::process::id(),
            NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&package).unwrap();
        let held = lock_file(&package).unwrap();
        let other = OpenOptions::new()
            .read(true)
            .write(true)
            .open(package.join(PACKAGE_LOCK_FILE))
            .unwrap();
        assert!(matches!(
            other.try_lock(),
            Err(fs::TryLockError::WouldBlock)
        ));
        drop(held);
        assert!(other.try_lock().is_ok());
        drop(other);
        // The lock file is reusable rather than a stale exclusive marker.
        drop(lock_file(&package).unwrap());
        fs::remove_dir_all(&package).unwrap();
    }
}
