//! Host driver. Semantic acceptance always comes from the Lean backend.
use crate::ir::Span;
use crate::runtime_inputs::{self, Package};
use crate::sources::{Sources, shown, shown_text};
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
const USAGE: &str = concat!(
    "vastitas ",
    env!("CARGO_PKG_VERSION"),
    "\n\nUsage:\n  vastitas check INPUT.vast [--lib LIBRARY.vast]...\n  vastitas build INPUT.vast [--lib LIBRARY.vast]... -o OUTPUT\n  vastitas check --manifest-path Vastitas.toml\n  vastitas build --manifest-path Vastitas.toml -o OUTPUT [--openblas-prefix PREFIX] [--native-cc COMPILER]\n  vastitas audit-lean LEAN4EXPORT.ndjson\n\n--lib adds explicitly selected source libraries to the same checked compilation unit.\nManifest mode accepts local path packages and cannot be mixed with INPUT.vast or --lib.\nNumerical builds require pinned sequential LP64 OpenBLAS 0.3.34 via --openblas-prefix.\n--native-cc explicitly selects the compiler/linker for numerical builds (for example cc on Linux).\nBuild the backend first: lake -d lean-kernel build vastitas-kernel\n"
);

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
        let request = kernel_request(&module, &sources, "packages")?;
        (sources, request, module.version)
    } else {
        let sources = Sources::load(input.as_ref().unwrap(), &libraries)?;
        if let Some(output) = &output {
            sources.protect_output(output)?;
        }
        let module = sources.parse()?;
        let request = kernel_request(&module, &sources, "module")?;
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
        println!("built {}", shown(&output));
    } else {
        println!("checked {}", shown(&display_input));
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
        .map_err(|error| format!("E_BACKEND: cannot locate {}: {error}", shown(&root)))
}

// Build-time identity of the kernel sources next to this driver (see build.rs).
mod expected_kernel {
    include!(concat!(env!("OUT_DIR"), "/kernel_identity.rs"));
}

// Responses may carry generated Lean for the whole program; bound them anyway.
const MAX_BACKEND_RESPONSE: usize = 256 * 1024 * 1024;

/// Every kernel response reports the digest of the Lean sources and of the
/// compiler limits it was built from, and its Lean version. Protocol numbers
/// stay fixed across releases, so only this identity ties the checker to this
/// driver. It says nothing about the root that a native build compiles; see
/// `verify_runtime_inputs`.
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
        |root| format!("lake -d {} build vastitas-kernel", shown(root)),
    );
    format!(
        "Rebuild the kernel from the same Vastitas sources as this compiler: {build}\n\
         VASTITAS_KERNEL_ROOT and VASTITAS_KERNEL must name a kernel of this compiler's version."
    )
}

/// An installed driver falls back to its build-time source directory, which may be
/// Cargo's registry cache; Cargo removes unused extracted sources automatically.
fn missing_kernel(root: &Path, executable: &Path) -> String {
    let build = format!("lake -d {} build vastitas-kernel", shown(root));
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
        shown(executable)
    )
}

/// The request of a program, or the limit on the size of a request. The
/// kernel refuses a request beyond `requestBytes` of the compiler limits
/// before it parses it; a program within the limits on its inputs can make
/// one (#740). The frontend reports the limit of the program instead, at the
/// start of the first input like the other limits of a whole program.
fn kernel_request(
    value: &impl serde::Serialize,
    sources: &Sources,
    what: &str,
) -> Result<Vec<u8>, String> {
    use crate::limits::MAX_REQUEST_BYTES;
    match bounded_json(value, MAX_REQUEST_BYTES) {
        Ok(Some(request)) => Ok(request),
        Ok(None) => Err(sources.diagnostic(
            "E_LIMIT",
            &format!(
                "the request of the program exceeds {MAX_REQUEST_BYTES} bytes, the largest request that the kernel reads"
            ),
            Span {
                start: 0,
                end: 0,
                line: 1,
                column: 1,
            },
        )),
        Err(error) => Err(format!("E_PROTOCOL: cannot encode {what}: {error}")),
    }
}

/// The JSON text of `value`, or `None` when it is longer than `bound` bytes.
/// A first pass counts the bytes without keeping them and stops at the bound,
/// so a text beyond it is never held. A second pass writes the text into a
/// buffer of its exact size.
fn bounded_json(
    value: &impl serde::Serialize,
    bound: usize,
) -> Result<Option<Vec<u8>>, serde_json::Error> {
    struct Counter {
        bytes: usize,
        bound: usize,
    }
    impl Write for Counter {
        fn write(&mut self, buffer: &[u8]) -> std::io::Result<usize> {
            self.bytes = self.bytes.saturating_add(buffer.len());
            if self.bytes > self.bound {
                return Err(std::io::Error::other("the text exceeds its bound"));
            }
            Ok(buffer.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    let mut counter = Counter { bytes: 0, bound };
    match serde_json::to_writer(&mut counter, value) {
        Ok(()) => {}
        Err(_) if counter.bytes > bound => return Ok(None),
        Err(error) => return Err(error),
    }
    let mut text = Vec::with_capacity(counter.bytes);
    serde_json::to_writer(&mut text, value)?;
    debug_assert_eq!(text.len(), counter.bytes);
    Ok(Some(text))
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
    let output = crate::process::capture(command, Some(request), retention)
        .map_err(|error| subprocess_error(error, "E_BACKEND", &shown(executable), true))?;
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
            shown(executable),
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

/// A private temporary directory, removed when dropped.
pub(crate) struct PrivateDirectory(pub(crate) PathBuf);

impl PrivateDirectory {
    /// Create one with errors labelled `code` and describing the `purpose`.
    pub(crate) fn create(code: &str, purpose: &str) -> Result<Self, String> {
        for _ in 0..100 {
            let path = std::env::temp_dir().join(format!(
                "vastitas-{}-{}",
                std::process::id(),
                NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
            ));
            // The name is predictable and child processes trust its contents
            // (Lake executes a generated lakefile; nanoda reads its configuration),
            // so only the invoking user may enter the directory, whatever the umask.
            match fs::DirBuilder::new().mode(0o700).create(&path) {
                Ok(()) => {
                    let directory = Self(path);
                    fs::set_permissions(&directory.0, fs::Permissions::from_mode(0o700))
                        .map_err(|error| format!("{code}: cannot secure {purpose}: {error}"))?;
                    return Ok(directory);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => {
                    return Err(format!("{code}: cannot create {purpose}: {error}"));
                }
            }
        }
        Err(format!("{code}: cannot allocate a unique {purpose}"))
    }
}

impl Drop for PrivateDirectory {
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
            shown(path)
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
            shown(lock)
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
                shown(package),
                shown(&lock)
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
                    shown(&path)
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
            shown(path)
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

/// Generated programs import only the runtime modules of the selected
/// packages, so `verify_runtime_inputs` covers every module that Lake compiles
/// for them. A response that imports any other module is refused. The name of
/// that module is text of the response, so it is shown like a path.
fn check_generated_imports(
    source: &str,
    selected: &[(&Package, &[(&str, &str)])],
) -> Result<(), String> {
    for module in runtime_inputs::header_imports(source) {
        if !selected
            .iter()
            .any(|(package, _)| package.modules.contains(&module.as_str()))
        {
            return Err(format!(
                "E_PROTOCOL: the generated program imports {}, which is not a runtime module that this compiler verifies for this build",
                shown_text(&module)
            ));
        }
    }
    Ok(())
}

/// The identity check ties the kernel executable to this compiler, but Lake
/// compiles the runtime from the files of the selected root. A stale
/// executable in a changed tree passes that check, and so does `VASTITAS_KERNEL`
/// with another root. Digest the files that Lake reads for `package` and
/// compare them with the ones this compiler was built from (the `build.rs`
/// table), never with a value that the root states about itself. The table
/// holds only files that exist in the compiler's sources. A forbidden name of
/// the package, the other name of its Lake configuration, is refused by rule,
/// whatever the table holds.
fn verify_runtime_inputs(
    kernel_root: &Path,
    package: &Package,
    expected: &[(&str, &str)],
) -> Result<(), String> {
    let directory = package.directory_in(kernel_root);
    let name = package.name;
    let found = runtime_inputs::inputs(&directory, package).map_err(|error| {
        format!(
            "E_BUILD: cannot read the {name} inputs in {}: {error}",
            shown(&directory)
        )
    })?;
    let found: Vec<(&str, &str)> = found
        .iter()
        .map(|(path, digest)| (path.as_str(), digest.as_str()))
        .collect();
    let forbidden: Vec<&str> = found
        .iter()
        .map(|(path, _)| *path)
        .filter(|path| package.forbidden.contains(path))
        .collect();
    if found == expected && forbidden.is_empty() {
        return Ok(());
    }
    fn digest_in<'a>(inputs: &[(&str, &'a str)], path: &str) -> Option<&'a str> {
        inputs
            .iter()
            .find(|(name, _)| *name == path)
            .map(|(_, digest)| *digest)
    }
    let mut paths: Vec<&str> = found
        .iter()
        .chain(expected)
        .map(|(path, _)| *path)
        .collect();
    paths.sort_unstable();
    paths.dedup();
    // The file of a module is named after an import in a source of the root,
    // which can spell any character, so each input is shown like a path.
    let mut other_differences = false;
    let differing: Vec<String> = paths
        .into_iter()
        .filter_map(|path| {
            let state = if forbidden.contains(&path) {
                "unexpected"
            } else {
                let state = match (digest_in(&found, path), digest_in(expected, path)) {
                    (found, expected) if found == expected => return None,
                    (None, _) => "missing",
                    (_, None) => "unexpected",
                    _ => "changed",
                };
                other_differences = true;
                state
            };
            Some(format!("{} ({state})", shown_text(path)))
        })
        .collect();
    const LISTED: usize = 6;
    let more = differing.len().saturating_sub(LISTED);
    let mut list = differing[..differing.len() - more].join(", ");
    if more > 0 {
        list.push_str(&format!(" and {more} more"));
    }
    let mut message = format!(
        "E_BUILD: kernel root {} provides {name} inputs {}, but this compiler requires {name} inputs {}\n\
         note: differing inputs in {}: {list}",
        shown(kernel_root),
        runtime_inputs::summary(found.iter().copied()),
        runtime_inputs::summary(expected.iter().copied()),
        shown(&directory)
    );
    // No build of the compiler accepts a forbidden name, so the advice to
    // rebuild is given only for a difference that a rebuild can resolve.
    for path in &forbidden {
        message.push_str(&format!(
            "\nnote: {} must not exist in {}: it is the other name of the package's Lake configuration, \
             and a rebuilt compiler rejects it as well. Remove it.",
            shown_text(path),
            shown(&directory)
        ));
    }
    if other_differences {
        message.push_str(
            "\nLake would compile the generated program against files other than the ones this compiler and its kernel were built with.\n\
             Set VASTITAS_KERNEL_ROOT to the unmodified lean-kernel directory of this compiler's Vastitas sources, \
             or rebuild this compiler and the kernel from the sources in that directory.",
        );
    }
    Err(message)
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
        .map_err(|error| format!("E_BUILD: cannot read {}: {error}", shown(&toolchain_path)))?;
    if toolchain.trim().is_empty() {
        return Err(format!(
            "E_BUILD: empty toolchain in {}",
            shown(&toolchain_path)
        ));
    }
    if toolchain.trim() != expected_kernel::TOOLCHAIN {
        return Err(format!(
            "E_BUILD: kernel root {} pins {}, but this compiler was built for {}\n{}",
            shown(kernel_root),
            // The pin is text of a file of the root.
            shown_text(toolchain.trim()),
            expected_kernel::TOOLCHAIN,
            rebuild_advice(Some(kernel_root))
        ));
    }
    // Before anything is generated, built or installed: the selected root must
    // hold the runtime that this compiler and its checked kernel were built with.
    let mut selected = vec![(&runtime_inputs::KERNEL, expected_kernel::KERNEL_RUNTIME)];
    if storage_runtime || numerical_prefix.is_some() {
        selected.push((&runtime_inputs::STORAGE, expected_kernel::STORAGE_RUNTIME));
    }
    if numerical_prefix.is_some() {
        selected.push((
            &runtime_inputs::NUMERICAL,
            expected_kernel::NUMERICAL_RUNTIME,
        ));
    }
    check_generated_imports(source, &selected)?;
    for (package, expected) in &selected {
        verify_runtime_inputs(kernel_root, package, expected)?;
    }
    let root_text = manifest_text(kernel_root, "kernel root")?;
    let native_root = kernel_root.join("native");
    let native_text = manifest_text(&native_root, "native runtime")?;
    let numerical_root = kernel_root.join("numerical");
    let directory = PrivateDirectory::create("E_BUILD", "build directory")?;
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
                shown(prefix)
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
    let metadata = fs::metadata(parent)
        .map_err(|error| format!("E_OUTPUT: cannot inspect parent {}: {error}", shown(parent)))?;
    if !metadata.is_dir() {
        return Err(format!(
            "E_OUTPUT: parent is not a directory: {}",
            shown(parent)
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
            shown(output)
        )),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!(
            "E_OUTPUT: cannot inspect {}: {error}",
            shown(output)
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
                shown(output)
            )
        }),
        Ok(_) => Ok(output.to_path_buf()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(output.to_path_buf()),
        Err(error) => Err(format!(
            "E_OUTPUT: cannot inspect {}: {error}",
            shown(output)
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
            shown(parent_directory(&target))
        )
    })?;
    drop(file);
    fs::remove_file(&staging)
        .map_err(|error| format!("E_OUTPUT: cannot remove probe {}: {error}", shown(&staging)))
}

fn install_output(binary: &Path, output: &Path, sources: &Sources) -> Result<(), String> {
    validate_output(output)?;
    sources.protect_output(output)?;
    let target = install_target(output)?;
    let (staging, mut file) = create_staging(&target)
        .map_err(|error| format!("E_OUTPUT: cannot stage {}: {error}", shown(output)))?;
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
            shown(output)
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    // #740: the frontend bounds the request that it writes. A source program
    // within the limits on its inputs needs about a gigabyte of request to
    // reach the bound, so this test gives the counter a small bound; the
    // ignored test `request_bound_is_a_limit_of_the_program` in
    // `tests/input_safety.rs` checks the program of the issue.
    #[test]
    fn bounded_json_stops_at_its_bound() {
        let value = json!({"version": 2, "names": ["a", "b", "c"]});
        let text = serde_json::to_vec(&value).unwrap();
        // A text of exactly the bound is within it, and the second pass
        // writes the same text as an unbounded encoding.
        assert_eq!(
            bounded_json(&value, text.len()).unwrap(),
            Some(text.clone())
        );
        assert_eq!(
            bounded_json(&value, usize::MAX).unwrap(),
            Some(text.clone())
        );
        assert_eq!(bounded_json(&value, text.len() - 1).unwrap(), None);
        assert_eq!(bounded_json(&value, 0).unwrap(), None);
        // The real bound is the kernel's: `requestBytes` of the limits file.
        let limits: Value =
            serde_json::from_str(include_str!("../lean-kernel/compiler-limits.json")).unwrap();
        assert_eq!(
            limits["requestBytes"].as_u64(),
            Some(crate::limits::MAX_REQUEST_BYTES as u64)
        );
    }

    // An error of the encoding is no limit: it stays `E_PROTOCOL`.
    #[test]
    fn bounded_json_reports_an_encoding_error() {
        struct Failing;
        impl serde::Serialize for Failing {
            fn serialize<S: serde::Serializer>(&self, _: S) -> Result<S::Ok, S::Error> {
                Err(serde::ser::Error::custom("not encodable"))
            }
        }
        let error = bounded_json(&Failing, usize::MAX).unwrap_err();
        assert!(error.to_string().contains("not encodable"), "{error}");
    }

    // The tables that `build.rs` embedded hold a digest for each input that
    // the lists name and for nothing else. They record no absence and no
    // forbidden name, so the creation of a file cannot make an entry stale.
    // They also equal the sources as they are when the test runs.
    #[test]
    fn embedded_runtime_tables_hold_only_inputs_that_exist() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("lean-kernel");
        for (package, table) in [
            (&runtime_inputs::KERNEL, expected_kernel::KERNEL_RUNTIME),
            (&runtime_inputs::STORAGE, expected_kernel::STORAGE_RUNTIME),
            (
                &runtime_inputs::NUMERICAL,
                expected_kernel::NUMERICAL_RUNTIME,
            ),
        ] {
            let name = package.name;
            for (path, digest) in table {
                assert!(
                    digest.len() == 16 && digest.bytes().all(|byte| byte.is_ascii_hexdigit()),
                    "{name}: {path} is recorded as {digest}"
                );
                assert!(!package.forbidden.contains(path), "{name}: {path}");
            }
            for file in package.files {
                assert!(
                    table.iter().any(|(path, _)| path == file),
                    "{name}: no entry for {file}"
                );
            }
            let directory = package.directory_in(&root);
            let current = runtime_inputs::required_inputs(&directory, package)
                .unwrap_or_else(|error| panic!("{name}: {error}"));
            let current: Vec<(&str, &str)> = current
                .iter()
                .map(|(path, digest)| (path.as_str(), digest.as_str()))
                .collect();
            assert_eq!(current, table, "{name}");
        }
    }

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
        // Model a child that another test of this binary spawns at this moment.
        // Between fork and exec it owns a copy of every descriptor, which
        // `FD_CLOEXEC` closes only at exec.
        let inherited = held.try_clone().unwrap();
        let exec = std::thread::spawn(move || {
            std::thread::sleep(std::time::Duration::from_millis(50));
            drop(inherited);
        });
        drop(held);
        // The flock belongs to the open file description, so dropping `held`
        // releases it only once such a copy is closed too. Asserting at once
        // failed under a concurrent spawn (#677), so wait for the release.
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        loop {
            match other.try_lock() {
                Ok(()) => break,
                Err(fs::TryLockError::WouldBlock) if std::time::Instant::now() < deadline => {
                    std::thread::sleep(std::time::Duration::from_millis(10));
                }
                error => panic!("the dropped package lock was not released: {error:?}"),
            }
        }
        exec.join().unwrap();
        drop(other);
        // The lock file is reusable rather than a stale exclusive marker.
        drop(lock_file(&package).unwrap());
        fs::remove_dir_all(&package).unwrap();
    }
}
