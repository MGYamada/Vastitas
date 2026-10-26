//! Host driver. Semantic acceptance always comes from the Lean backend.
use crate::ir::Span;
use crate::sources::Sources;
use serde_json::{Value, json};
use std::ffi::OsString;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);
const USAGE: &str = "Vastitas Stage 0\n\nUsage:\n  vastitas check INPUT.vast [--lib LIBRARY.vast]...\n  vastitas build INPUT.vast [--lib LIBRARY.vast]... -o OUTPUT\n\n--lib adds explicitly selected source libraries to the same checked compilation unit.\nBuild the backend first: lake -d lean-kernel build vastitas-kernel\n";

struct Options {
    mode: &'static str,
    input: PathBuf,
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
    let mut remaining = args.iter().skip(1);
    while let Some(arg) = remaining.next() {
        if arg == "--lib" {
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
    Ok(Options {
        mode,
        input: input.ok_or_else(usage)?,
        libraries,
        output,
    })
}

pub fn run(args: impl Iterator<Item = OsString>) -> Result<(), String> {
    let args: Vec<_> = args.collect();
    if args.is_empty() || args == ["--help"] || args == ["-h"] {
        print!("{USAGE}");
        return Ok(());
    }
    if args == ["--version"] {
        println!(
            "vastitas {} (Stage 0, protocol 1)",
            env!("CARGO_PKG_VERSION")
        );
        return Ok(());
    }
    let Options {
        mode,
        input,
        libraries,
        output,
    } = options(&args)?;
    let sources = Sources::load(&input, &libraries)?;
    let module = sources.parse()?;
    let request = serde_json::to_vec(&module)
        .map_err(|error| format!("E_PROTOCOL: cannot encode module: {error}"))?;
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
    let response = invoke_kernel(&executable, mode, &request, &sources)?;
    if let Some(output) = output {
        let lean_source = response
            .get("lean_source")
            .and_then(Value::as_str)
            .ok_or_else(|| "E_PROTOCOL: backend omitted generated Lean source".to_string())?;
        build_native(
            root.as_ref().expect("native build requires kernel root"),
            lean_source,
            &output,
        )?;
        println!("built {}", output.display());
    } else {
        println!("checked {}", input.display());
    }
    Ok(())
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
) -> Result<Value, String> {
    let mut child = Command::new(executable)
        .arg(mode)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| {
            format!(
                "E_BACKEND: cannot start {}: {error}\nBuild it with: lake -d lean-kernel build vastitas-kernel",
                executable.display()
            )
        })?;
    let mut stdin = child.stdin.take().expect("piped stdin");
    // Send while wait_with_output drains stdout/stderr, avoiding pipe deadlocks.
    let request = request.to_vec();
    let writer = std::thread::spawn(move || stdin.write_all(&request));
    let output = child
        .wait_with_output()
        .map_err(|error| format!("E_BACKEND: cannot wait for backend: {error}"))?;
    let write_result = writer
        .join()
        .map_err(|_| "E_BACKEND: request writer failed".to_string())?;
    let response: Value = serde_json::from_slice(&output.stdout).map_err(|error| {
        format!(
            "E_PROTOCOL: invalid backend response: {error}\n{}",
            String::from_utf8_lossy(&output.stderr)
        )
    })?;
    if response.get("version") != Some(&json!(1)) {
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
    write_result.map_err(|error| format!("E_BACKEND: cannot send IR: {error}"))?;
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

fn build_native(kernel_root: &Path, source: &str, output: &Path) -> Result<(), String> {
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
    let result = Command::new("lake")
        .current_dir(path)
        .args(["build", "program"])
        .output()
        .map_err(|error| format!("E_BUILD: cannot start Lake: {error}"))?;
    if !result.status.success() {
        return Err(format!(
            "E_BUILD: native compilation failed ({})\n{}{}",
            result.status,
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        ));
    }
    install_output(&path.join(".lake/build/bin/program"), output)
}

fn install_output(binary: &Path, output: &Path) -> Result<(), String> {
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
    let result = (|| {
        let mut compiled = fs::File::open(binary)?;
        std::io::copy(&mut compiled, &mut file)?;
        file.set_permissions(compiled.metadata()?.permissions())?;
        file.sync_all()?;
        fs::rename(&staging, output)
    })();
    if let Err(error) = result {
        let _ = fs::remove_file(&staging);
        return Err(format!(
            "E_OUTPUT: cannot install {}: {error}",
            output.display()
        ));
    }
    Ok(())
}
