//! `vastitas audit-lean`: a non-authoritative recheck of a supplied Lean export
//! by the `nanoda_bin` checker that the pinned official Lean toolchain ships
//! (#539). The checker runs out of process under `crate::process`. nanoda is not
//! the official Lean kernel, and no result here confers Vastitas acceptance.
use serde_json::{Map, Value};
use std::ffi::OsString;
use std::fs;
use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

/// Upstream nanoda configuration, completed with `export_file_path` at run time.
const POLICY: &str = include_str!("../config/nanoda-internal-audit.json");

/// The pinned official Lean toolchain, its release identity, and the checker
/// version that release distributes. A toolchain bump updates all four together;
/// a unit test compares the name with every checked-in `lean-toolchain` file.
const LEAN_TOOLCHAIN: &str = "leanprover/lean4:v4.35.0";
const LEAN_VERSION: &str = "4.35.0";
const LEAN_COMMIT: &str = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc";
const NANODA_IDENTITY: &str = "nanoda_bin 0.4.19";

const PERMITTED_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];
/// Every key the reviewed policy may set. nanoda 0.4.19 ignores unknown keys,
/// so an unlisted (for example misspelled) option is rejected here instead.
const POLICY_KEYS: [&str; 9] = [
    "use_stdin",
    "permitted_axioms",
    "unpermitted_axiom_hard_error",
    "unsafe_permit_all_axioms",
    "nat_extension",
    "string_extension",
    "num_threads",
    "print_axioms",
    "print_success_message",
];
/// Checker diagnostics shown to the user, in characters.
const DIAGNOSTIC_CHARS: usize = 2000;

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

fn export_path(args: &[OsString]) -> Result<PathBuf, String> {
    if args.len() != 1 || args[0] == "--help" || args[0] == "-h" {
        return Err("E_USAGE: expected vastitas audit-lean LEAN4EXPORT.ndjson".into());
    }
    Ok(PathBuf::from(args[0].clone()))
}

/// The checked-in policy as an upstream configuration object. It must allow
/// exactly the three reviewed axiom names, reject any other exported axiom even
/// when unused, forbid permit-all, read a file, and report a success message.
fn policy() -> Result<Map<String, Value>, String> {
    let invalid = |reason: &str| format!("E_LEAN_AUDIT_POLICY: invalid internal policy: {reason}");
    let Value::Object(config) =
        serde_json::from_str(POLICY).map_err(|error| invalid(&error.to_string()))?
    else {
        return Err(invalid("expected a JSON object"));
    };
    let mut keys = config.keys().map(String::as_str).collect::<Vec<_>>();
    let mut expected = POLICY_KEYS.to_vec();
    keys.sort_unstable();
    expected.sort_unstable();
    if keys != expected {
        return Err(invalid(&format!(
            "expected exactly the keys {POLICY_KEYS:?}"
        )));
    }
    let axioms = config["permitted_axioms"]
        .as_array()
        .map(|axioms| axioms.iter().map(Value::as_str).collect::<Option<Vec<_>>>());
    if axioms != Some(Some(PERMITTED_AXIOMS.to_vec()))
        || config["unpermitted_axiom_hard_error"] != Value::Bool(true)
        || config["unsafe_permit_all_axioms"] != Value::Bool(false)
        || config["use_stdin"] != Value::Bool(false)
        || config["print_success_message"] != Value::Bool(true)
        // Its default (true) turns into a pretty-printer error on success.
        || config["print_axioms"] != Value::Bool(false)
    {
        return Err("E_LEAN_AUDIT_POLICY: internal policy must allow exactly the three configured axiom names, fail on any other name, forbid permit-all, read the export file and report success".into());
    }
    if !config["nat_extension"].is_boolean()
        || !config["string_extension"].is_boolean()
        || config["num_threads"].as_u64().is_none()
    {
        return Err(invalid(
            "extension flags and the thread count have the wrong types",
        ));
    }
    Ok(config)
}

fn configuration(export: &Path) -> Result<String, String> {
    let mut config = policy()?;
    let export = export.to_str().ok_or(
        "E_USAGE: the export path must be valid UTF-8 to be passed in nanoda's JSON configuration",
    )?;
    config.insert("export_file_path".into(), Value::String(export.into()));
    serde_json::to_string(&Value::Object(config))
        .map_err(|error| format!("E_LEAN_AUDIT_POLICY: cannot encode configuration: {error}"))
}

/// The platform part of `lean --version` for each Lean release platform that
/// ships `nanoda_bin`.
fn lean_platform() -> Result<&'static str, String> {
    match (std::env::consts::OS, std::env::consts::ARCH) {
        ("macos", "aarch64") => Ok("arm64-apple-darwin"),
        ("macos", "x86_64") => Ok("x86_64-apple-darwin"),
        ("linux", "x86_64") => Ok("x86_64-unknown-linux-gnu"),
        ("linux", "aarch64") => Ok("aarch64-unknown-linux-gnu"),
        (os, arch) => Err(format!(
            "E_LEAN_AUDIT_CHECKER: Lean {LEAN_VERSION} distributes no nanoda_bin for {os}/{arch}"
        )),
    }
}

/// The elan directory of the pinned toolchain. This is the toolchain selected by
/// the checked-in `lean-toolchain` files, never whichever Lean is on `PATH`.
fn toolchain_directory() -> Result<PathBuf, String> {
    let home = match std::env::var_os("ELAN_HOME").filter(|home| !home.is_empty()) {
        Some(home) => PathBuf::from(home),
        None => std::env::var_os("HOME")
            .filter(|home| !home.is_empty())
            .map(|home| PathBuf::from(home).join(".elan"))
            .ok_or("E_LEAN_AUDIT_CHECKER: neither ELAN_HOME nor HOME is set, so the pinned Lean toolchain cannot be located")?,
    };
    // elan names toolchain directories by replacing `/` with `--` and `:` with `---`.
    let name = LEAN_TOOLCHAIN.replace('/', "--").replace(':', "---");
    let directory = home.join("toolchains").join(name);
    let canonical = directory.canonicalize().map_err(|error| {
        format!(
            "E_LEAN_AUDIT_CHECKER: the pinned Lean toolchain {LEAN_TOOLCHAIN} is not installed at {}: {error}\nhelp: elan toolchain install {LEAN_TOOLCHAIN}",
            directory.display()
        )
    })?;
    if !canonical.is_dir() {
        return Err(format!(
            "E_LEAN_AUDIT_CHECKER: {} is not a Lean toolchain directory",
            canonical.display()
        ));
    }
    Ok(canonical)
}

/// A toolchain-owned executable: a regular file in the toolchain's own `bin`.
fn toolchain_executable(directory: &Path, name: &str) -> Result<PathBuf, String> {
    let path = directory.join("bin").join(name);
    let metadata = fs::symlink_metadata(&path).map_err(|error| {
        format!(
            "E_LEAN_AUDIT_CHECKER: the pinned Lean toolchain {LEAN_TOOLCHAIN} at {} provides no {name}: {error}\nVastitas has no fallback checker; reinstall the official toolchain.",
            directory.display()
        )
    })?;
    if !metadata.file_type().is_file() || metadata.permissions().mode() & 0o111 == 0 {
        return Err(format!(
            "E_LEAN_AUDIT_CHECKER: {} is not a regular executable file of the pinned toolchain",
            path.display()
        ));
    }
    Ok(path)
}

fn run(command: Command, program: &str) -> Result<Output, String> {
    use crate::process::CaptureError;
    crate::process::capture(command, None).map_err(|error| match error {
        CaptureError::Interrupted => "E_LEAN_AUDIT: audit interrupted".into(),
        CaptureError::Spawn(error) => {
            format!("E_LEAN_AUDIT_CHECKER: cannot start {program}: {error}")
        }
        CaptureError::Wait(error) => format!("E_LEAN_AUDIT: waiting for {program} failed: {error}"),
        CaptureError::Io(error) => format!("E_LEAN_AUDIT: {program} I/O failed: {error}"),
    })
}

/// Run an identity probe and return its standard output.
fn probe(program: &Path, argument: &str) -> Result<String, String> {
    let mut command = Command::new(program);
    command.arg(argument);
    let name = program.display().to_string();
    let output = run(command, &name)?;
    if !output.status.success() {
        return Err(format!(
            "E_LEAN_AUDIT_CHECKER: {name} {argument} failed ({})\n{}",
            output.status,
            diagnostics(&output.stderr)
        ));
    }
    String::from_utf8(output.stdout)
        .map_err(|_| format!("E_LEAN_AUDIT_CHECKER: {name} {argument} printed invalid UTF-8"))
}

/// Accept exactly `Lean (version V, PLATFORM…, commit C, Release)` for the pinned
/// release on this platform.
fn lean_identity_matches(version: &str, platform: &str) -> bool {
    let Some(fields) = version
        .strip_suffix('\n')
        .unwrap_or(version)
        .strip_prefix("Lean (version ")
        .and_then(|line| line.strip_suffix(", Release)"))
    else {
        return false;
    };
    let fields = fields.split(", ").collect::<Vec<_>>();
    let commit = format!("commit {LEAN_COMMIT}");
    !version.trim_end_matches('\n').contains('\n')
        && fields.len() == 3
        && fields[0] == LEAN_VERSION
        && fields[1].starts_with(platform)
        && fields[2] == commit
}

/// The toolchain's `nanoda_bin`, after checking that it belongs to the pinned
/// Lean release for this platform and reports the checker version that release
/// ships. These checks catch missing, stale, foreign-platform and mismatched
/// installations. They do not authenticate the files against local tampering:
/// the installed toolchain is trusted exactly as the official kernel path is.
fn resolve_checker() -> Result<PathBuf, String> {
    let platform = lean_platform()?;
    let directory = toolchain_directory()?;
    let lean = toolchain_executable(&directory, "lean")?;
    let version = probe(&lean, "--version")?;
    if !lean_identity_matches(&version, platform) {
        return Err(format!(
            "E_LEAN_AUDIT_CHECKER: {} is not the official Lean {LEAN_VERSION} release for {platform} (commit {LEAN_COMMIT}); it reports: {}",
            lean.display(),
            diagnostics(version.as_bytes())
        ));
    }
    let nanoda = toolchain_executable(&directory, "nanoda_bin")?;
    let help = probe(&nanoda, "--help")?;
    if help.lines().next() != Some(NANODA_IDENTITY) {
        return Err(format!(
            "E_LEAN_AUDIT_CHECKER: {} does not identify as {NANODA_IDENTITY}, the checker Lean {LEAN_VERSION} ships; it reports: {}",
            nanoda.display(),
            diagnostics(help.lines().next().unwrap_or_default().as_bytes())
        ));
    }
    Ok(nanoda)
}

/// A private directory for the configuration file, removed on every return.
struct ConfigDirectory(PathBuf);

impl ConfigDirectory {
    fn create() -> Result<Self, String> {
        for _ in 0..100 {
            let path = std::env::temp_dir().join(format!(
                "vastitas-lean-audit-{}-{}",
                std::process::id(),
                NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::DirBuilder::new().mode(0o700).create(&path) {
                Ok(()) => return Ok(Self(path)),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => {
                    return Err(format!(
                        "E_LEAN_AUDIT: cannot create a configuration directory: {error}"
                    ));
                }
            }
        }
        Err("E_LEAN_AUDIT: cannot allocate a unique configuration directory".into())
    }
}

impl Drop for ConfigDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// A bounded, terminal-safe rendering of checker output. Export-controlled names
/// can reach panic messages, so control and bidirectional formatting characters
/// are shown as escapes.
fn diagnostics(bytes: &[u8]) -> String {
    let text = String::from_utf8_lossy(bytes);
    let mut rendered = String::new();
    for character in text.trim().chars().take(DIAGNOSTIC_CHARS) {
        let bidi = matches!(character, '\u{200e}' | '\u{200f}' | '\u{202a}'..='\u{202e}' | '\u{2066}'..='\u{2069}');
        if character == '\n' || character == '\t' || !(character.is_control() || bidi) {
            rendered.push(character);
        } else {
            rendered.extend(character.escape_unicode());
        }
    }
    rendered
}

/// The declaration count from nanoda's exact success message.
fn checked_declarations(stdout: &[u8]) -> Option<u64> {
    let count = std::str::from_utf8(stdout)
        .ok()?
        .strip_prefix("Checked ")?
        .strip_suffix(" declarations with no errors\n")?;
    if count.is_empty() || !count.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    count.parse().ok()
}

/// An opt-in, non-authoritative cross-check. The official Lean kernel remains
/// the only authority for CI proofs, kernel compilation, and the Constitution.
pub fn run_cli(args: &[OsString]) -> Result<(), String> {
    let path = export_path(args)?;
    let export = std::path::absolute(&path)
        .map_err(|error| format!("E_LEAN_AUDIT: cannot resolve {}: {error}", path.display()))?;
    // Check the policy before starting any process.
    let config = configuration(&export)?;
    // `metadata` never opens the export, so FIFOs remain unread until nanoda runs.
    let metadata = fs::metadata(&export)
        .map_err(|error| format!("E_LEAN_AUDIT: cannot read {}: {error}", path.display()))?;
    if metadata.is_dir() {
        return Err(format!(
            "E_LEAN_AUDIT: {} is a directory, not a Lean export",
            path.display()
        ));
    }
    let nanoda = resolve_checker()?;
    let directory = ConfigDirectory::create()?;
    let config_path = directory.0.join("nanoda-config.json");
    fs::write(&config_path, config)
        .map_err(|error| format!("E_LEAN_AUDIT: cannot write the nanoda configuration: {error}"))?;
    let mut command = Command::new(&nanoda);
    // Like Lake's external-checker runner, pass only the configuration path and
    // run outside the caller's directory.
    command.arg(&config_path).current_dir(&directory.0);
    let output = run(command, NANODA_IDENTITY)?;
    if !output.status.success() {
        return Err(format!(
            "E_LEAN_AUDIT: {NANODA_IDENTITY} rejected {} ({})\n{}",
            path.display(),
            output.status,
            diagnostics(&output.stderr)
        ));
    }
    let Some(checked) = checked_declarations(&output.stdout) else {
        return Err(format!(
            "E_LEAN_AUDIT: unexpected {NANODA_IDENTITY} success report: {}",
            diagnostics(&output.stdout)
        ));
    };
    if checked == 0 {
        return Err("E_LEAN_AUDIT: an export without declarations is not an accepted audit".into());
    }
    if !output.stderr.is_empty() {
        return Err(format!(
            "E_LEAN_AUDIT: {NANODA_IDENTITY} reported diagnostics despite success:\n{}",
            diagnostics(&output.stderr)
        ));
    }
    println!(
        "internal-only conditional Lean audit completed ({NANODA_IDENTITY} from the Lean {LEAN_VERSION} toolchain): {checked} declarations in {}\nChecker: {} (toolchain {LEAN_TOOLCHAIN}, commit {LEAN_COMMIT})\nResult is relative to the supplied environment. Axioms named {} are admitted by name only; their statements and dependencies are NOT authenticated as the standard Lean axioms.\nnanoda is not the official Lean kernel. This is NOT official Lean-kernel verification and confers no Vastitas Core or constitutional acceptance.",
        path.display(),
        nanoda.display(),
        PERMITTED_AXIOMS.join(", ")
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checked_in_policy_is_strict() {
        let config = policy().unwrap();
        assert_eq!(
            config["permitted_axioms"],
            serde_json::json!(PERMITTED_AXIOMS)
        );
        assert_eq!(config["unpermitted_axiom_hard_error"], true);
        assert_eq!(config["unsafe_permit_all_axioms"], false);
        let written: Value =
            serde_json::from_str(&configuration(Path::new("/tmp/export.ndjson")).unwrap()).unwrap();
        assert_eq!(written["export_file_path"], "/tmp/export.ndjson");
        assert_eq!(written["use_stdin"], false);
    }

    #[test]
    fn identity_matches_every_checked_in_toolchain_pin() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        for file in [
            "lean-toolchain",
            "lean-kernel/lean-toolchain",
            "lean/lean-toolchain",
        ] {
            let pin = fs::read_to_string(root.join(file)).unwrap();
            assert_eq!(pin.trim(), LEAN_TOOLCHAIN, "{file}");
        }
        assert_eq!(
            LEAN_TOOLCHAIN.strip_prefix("leanprover/lean4:v"),
            Some(LEAN_VERSION)
        );
    }

    #[test]
    fn lean_identity_requires_the_exact_release() {
        let platform = "arm64-apple-darwin";
        let line = |version: &str, commit: &str, kind: &str| {
            format!("Lean (version {version}, arm64-apple-darwin24.6.0, commit {commit}, {kind})\n")
        };
        assert!(lean_identity_matches(
            &line(LEAN_VERSION, LEAN_COMMIT, "Release"),
            platform
        ));
        assert!(!lean_identity_matches(
            &line("4.34.1", LEAN_COMMIT, "Release"),
            platform
        ));
        assert!(!lean_identity_matches(
            &line(LEAN_VERSION, "0000", "Release"),
            platform
        ));
        assert!(!lean_identity_matches(
            &line(LEAN_VERSION, LEAN_COMMIT, "Debug"),
            platform
        ));
        assert!(!lean_identity_matches(
            &line(LEAN_VERSION, LEAN_COMMIT, "Release"),
            "x86_64-unknown-linux-gnu"
        ));
        let extra = format!("{}extra\n", line(LEAN_VERSION, LEAN_COMMIT, "Release"));
        assert!(!lean_identity_matches(&extra, platform));
    }

    #[test]
    fn success_report_is_parsed_exactly() {
        assert_eq!(
            checked_declarations(b"Checked 12 declarations with no errors\n"),
            Some(12)
        );
        assert_eq!(
            checked_declarations(b"Checked 0 declarations with no errors\n"),
            Some(0)
        );
        for report in [
            &b""[..],
            b"Checked 1 declarations with no errors",
            b"Checked +1 declarations with no errors\n",
            b"Checked 1 declarations with no errors\nmore\n",
            b"Checked 1 declarations with no errors, skipping exported but unpermitted axioms [\"x\"]\n",
        ] {
            assert_eq!(checked_declarations(report), None, "{report:?}");
        }
    }

    #[test]
    fn diagnostics_escape_terminal_controls() {
        let rendered = diagnostics("bad \u{1b}[2J name\u{202e}\nnext".as_bytes());
        assert_eq!(rendered, "bad \\u{1b}[2J name\\u{202e}\nnext");
        assert_eq!(
            diagnostics("x".repeat(5000).as_bytes()).len(),
            DIAGNOSTIC_CHARS
        );
    }
}
