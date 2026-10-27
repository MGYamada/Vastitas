//! Host driver. Semantic acceptance always comes from the Lean backend.
use crate::ir::{PROTOCOL_VERSION, Span};
use crate::sources::Sources;
use serde_json::{Value, json};
use std::ffi::OsString;
use std::fs::{self, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::ffi::OsStrExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);
const USAGE: &str = "Vastitas Stage 1b\n\nUsage:\n  vastitas check INPUT.vast [--lib LIBRARY.vast]...\n  vastitas build INPUT.vast [--lib LIBRARY.vast]... -o OUTPUT\n  vastitas check --manifest-path Vastitas.toml\n  vastitas build --manifest-path Vastitas.toml -o OUTPUT\n\n--lib adds explicitly selected source libraries to the same checked compilation unit.\nManifest mode accepts local path packages and cannot be mixed with INPUT.vast or --lib.\nBuild the backend first: lake -d lean-kernel build vastitas-kernel\n";

struct Options {
    mode: &'static str,
    input: Option<PathBuf>,
    manifest: Option<PathBuf>,
    libraries: Vec<PathBuf>,
    output: Option<PathBuf>,
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
    })
}

pub fn run(args: impl Iterator<Item = OsString>) -> Result<(), String> {
    crate::process::install()
        .map_err(|error| format!("E_BACKEND: cannot install signal handlers: {error}"))?;
    let args: Vec<_> = args.collect();
    let subcommand_help = args.len() == 2
        && (args[0] == "check" || args[0] == "build")
        && (args[1] == "--help" || args[1] == "-h");
    if args.is_empty() || args == ["--help"] || args == ["-h"] || subcommand_help {
        print!("{USAGE}");
        return Ok(());
    }
    if args == ["--version"] {
        println!(
            "vastitas {} (Stage 1b + packages + abstract selectors, protocols {PROTOCOL_VERSION}/3/4)",
            env!("CARGO_PKG_VERSION")
        );
        return Ok(());
    }
    let Options {
        mode,
        input,
        manifest,
        libraries,
        output,
    } = options(&args)?;
    if let Some(output) = &output {
        validate_output(output)?;
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
    let root = if output.is_some() || configured_executable.is_none() {
        Some(kernel_root()?)
    } else {
        None
    };
    let executable = configured_executable.unwrap_or_else(|| {
        root.as_ref()
            .expect("default executable requires kernel root")
            .join(".lake/build/bin/vastitas-kernel")
    });
    let response = invoke_kernel(&executable, mode, &request, &sources, version)?;
    if let Some(output) = output {
        let lean_source = response
            .get("lean_source")
            .and_then(Value::as_str)
            .ok_or_else(|| "E_PROTOCOL: backend omitted generated Lean source".to_string())?;
        build_native(
            root.as_ref().expect("native build requires kernel root"),
            lean_source,
            &output,
            &sources,
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

fn invoke_kernel(
    executable: &Path,
    mode: &str,
    request: &[u8],
    sources: &Sources,
    version: u32,
) -> Result<Value, String> {
    let mut command = Command::new(executable);
    command.arg(mode);
    let output = crate::process::capture(command, Some(request)).map_err(|error| {
        subprocess_error(error, "E_BACKEND", &executable.display().to_string(), true)
    })?;
    let response: Value = serde_json::from_slice(&output.stdout).map_err(|error| {
        format!(
            "E_PROTOCOL: invalid backend response: {error}\n{}",
            String::from_utf8_lossy(&output.stderr)
        )
    })?;
    if response.get("version") != Some(&json!(version)) {
        return Err("E_PROTOCOL: incompatible backend protocol version".into());
    }
    if response.get("ok") == Some(&Value::Bool(false)) {
        let diagnostics = response
            .get("diagnostics")
            .and_then(Value::as_array)
            .filter(|items| !items.is_empty())
            .ok_or_else(|| "E_PROTOCOL: backend failure has no diagnostics".to_string())?;
        return Err(diagnostics
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
            .join("\n"));
    }
    if response.get("ok") != Some(&Value::Bool(true)) || !output.status.success() {
        return Err(format!(
            "E_BACKEND: backend failed ({})\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
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
            match fs::create_dir(&path) {
                Ok(()) => return Ok(Self(path)),
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

fn build_native(
    kernel_root: &Path,
    source: &str,
    output: &Path,
    sources: &Sources,
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
    let directory = BuildDirectory::create()?;
    let path = &directory.0;
    let dependency_path = serde_json::to_string(&kernel_root.to_string_lossy())
        .map_err(|error| format!("E_BUILD: invalid kernel path: {error}"))?;
    let manifest = format!(
        "name = \"vastitas_program\"\nversion = \"0.1.0\"\ndefaultTargets = [\"program\"]\n\n[[require]]\nname = \"vastitas_kernel\"\npath = {dependency_path}\n\n[[lean_exe]]\nname = \"program\"\nroot = \"Main\"\n"
    );
    for (name, contents) in [
        ("lakefile.toml", manifest.as_str()),
        ("lean-toolchain", toolchain.as_str()),
        ("Main.lean", source),
    ] {
        fs::write(path.join(name), contents)
            .map_err(|error| format!("E_BUILD: cannot write {name}: {error}"))?;
    }
    let mut command = Command::new("lake");
    command.current_dir(path).args(["build", "program"]);
    let result = crate::process::capture(command, None)
        .map_err(|error| subprocess_error(error, "E_BUILD", "Lake", false))?;
    if !result.status.success() {
        return Err(format!(
            "E_BUILD: native compilation failed ({})\n{}{}",
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
    match fs::metadata(output) {
        Ok(metadata) if metadata.is_dir() => Err("E_OUTPUT: output must name a file".into()),
        Ok(_) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!(
            "E_OUTPUT: cannot inspect {}: {error}",
            output.display()
        )),
    }
}

fn install_output(binary: &Path, output: &Path, sources: &Sources) -> Result<(), String> {
    validate_output(output)?;
    sources.protect_output(output)?;
    let parent = output
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let name = output
        .file_name()
        .ok_or_else(|| "E_OUTPUT: output must name a file".to_string())?;
    let mut staging_name = OsString::from(".");
    staging_name.push(name);
    staging_name.push(format!(
        ".vastitas-{}-{}.tmp",
        std::process::id(),
        NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
    ));
    let staging = parent.join(staging_name);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&staging)
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
        sources
            .protect_output(output)
            .map_err(std::io::Error::other)?;
        fs::rename(&staging, output)
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
