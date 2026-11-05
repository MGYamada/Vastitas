//! Driver and process-handling regressions from the v0.1.0-alpha review
//! (#519, #522, #550, #564). Process-group signaling (#520) and package-lock
//! fallback classification are unit-tested next to their implementations.
mod common;
use common::{Scratch, kernel_identity, kernel_path};
use std::ffi::OsString;
use std::fs;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{Duration, Instant};

const PINNED: &str = include_str!("../lean-kernel/lean-toolchain");
const RESOURCE_MAIN: &str = "resource fn main() -> Int {
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
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, source).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
}

fn fixture() -> Scratch {
    let s = Scratch::empty("driver_hardening");
    s.write("main.vast", "fn main() -> Int { 42 }");
    s
}

/// The mock directory `bin` comes first on PATH; real `lean` stays reachable.
fn mock_path(s: &Scratch) -> OsString {
    let mut paths = vec![s.0.join("bin")];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    std::env::join_paths(paths).unwrap()
}

/// A Lake mock that installs a shell "binary" printing `$NATIVE_TEXT`.
fn successful_lake(s: &Scratch) {
    executable(
        &s.0.join("bin/lake"),
        "#!/bin/sh\nset -eu\nmkdir -p .lake/build/bin\nprintf '#!/bin/sh\\necho %s\\n' \"$NATIVE_TEXT\" > .lake/build/bin/program\nchmod +x .lake/build/bin/program\n",
    );
}

fn cli(s: &Scratch) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_vastitas"));
    command
        .current_dir(&s.0)
        .env("VASTITAS_KERNEL", kernel_path())
        .env("PATH", mock_path(s));
    command
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn leftovers(directory: &Path) -> Vec<String> {
    fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .filter(|name| name.starts_with(".vastitas-"))
        .collect()
}

fn running_as_root() -> bool {
    // SAFETY: geteuid has no preconditions and cannot fail.
    unsafe { nix::libc::geteuid() == 0 }
}

// #519: a symlink to a regular file is written through, and protection agrees.
#[test]
fn output_symlink_is_written_through_to_its_target() {
    let s = fixture();
    successful_lake(&s);
    fs::create_dir_all(s.0.join("dist")).unwrap();
    fs::create_dir_all(s.0.join("bin-links")).unwrap();
    fs::write(s.0.join("dist/app"), "old contents\n").unwrap();
    symlink("../dist/app", s.0.join("bin-links/app")).unwrap();
    // A chain of links resolves to the same final target.
    symlink("app", s.0.join("bin-links/chain")).unwrap();
    for (output, text) in [("bin-links/app", "first"), ("bin-links/chain", "second")] {
        let result = cli(&s)
            .args(["build", "main.vast", "-o", output])
            .env("NATIVE_TEXT", text)
            .output()
            .unwrap();
        assert!(result.status.success(), "{}", stderr(&result));
        let link = fs::symlink_metadata(s.0.join(output)).unwrap();
        assert!(link.file_type().is_symlink(), "{output} was replaced");
        let ran = Command::new(s.0.join("dist/app")).output().unwrap();
        assert_eq!(String::from_utf8_lossy(&ran.stdout).trim(), text);
    }
    assert_eq!(
        fs::read_link(s.0.join("bin-links/app")).unwrap(),
        Path::new("../dist/app")
    );
    assert!(leftovers(&s.0.join("dist")).is_empty());
    assert!(leftovers(&s.0.join("bin-links")).is_empty());

    // Writing through `alias.vast` would replace the input it names, so the
    // refusal matches what installation would do.
    symlink("main.vast", s.0.join("alias.vast")).unwrap();
    let result = cli(&s)
        .args(["build", "main.vast", "-o", "alias.vast"])
        .env("NATIVE_TEXT", "never")
        .output()
        .unwrap();
    assert!(
        stderr(&result).starts_with("E_OUTPUT: output would overwrite input file main.vast"),
        "{}",
        stderr(&result)
    );
    assert_eq!(
        fs::read_to_string(s.0.join("main.vast")).unwrap(),
        "fn main() -> Int { 42 }"
    );
    assert!(
        fs::symlink_metadata(s.0.join("alias.vast"))
            .unwrap()
            .file_type()
            .is_symlink()
    );
}

// #564 (1): the generated Lake project is private regardless of the umask.
#[test]
fn build_directory_is_private_under_a_permissive_umask() {
    let s = fixture();
    let modes = s.0.join("modes");
    executable(
        &s.0.join("bin/lake"),
        "#!/bin/sh\npython3 -c 'import os, stat; print(oct(stat.S_IMODE(os.stat(\".\").st_mode)))' > \"$MODES\"\nexit 3\n",
    );
    let temp = s.0.join("tmp");
    fs::create_dir(&temp).unwrap();
    // Command cannot set a umask; start the driver from a shell that does.
    let result = Command::new("sh")
        .current_dir(&s.0)
        .args(["-c", "umask 000; exec \"$0\" build main.vast -o program"])
        .arg(env!("CARGO_BIN_EXE_vastitas"))
        .env("VASTITAS_KERNEL", kernel_path())
        .env("PATH", mock_path(&s))
        .env("TMPDIR", &temp)
        .env("MODES", &modes)
        .output()
        .unwrap();
    common::expect_code(&result, "E_BUILD");
    assert_eq!(fs::read_to_string(&modes).unwrap().trim(), "0o700");
    assert_eq!(fs::read_dir(&temp).unwrap().count(), 0);
}

// #564 (2): leftover staging names from a killed run with a reused PID are
// skipped, and an unwritable output directory fails before any build work.
#[test]
fn staging_names_are_retried_and_output_directory_is_probed_first() {
    let s = fixture();
    let out = s.0.join("out");
    fs::create_dir(&out).unwrap();
    // The mock's parent is the driver: leave names that its counter will reach.
    executable(
        &s.0.join("bin/lake"),
        "#!/bin/sh\nset -eu\ni=0\nwhile [ $i -lt 50 ]; do : > \"$OUT/.vastitas-$PPID-$i.tmp\"; i=$((i + 1)); done\nmkdir -p .lake/build/bin\nprintf '#!/bin/sh\\necho staged\\n' > .lake/build/bin/program\nchmod +x .lake/build/bin/program\n",
    );
    let result = cli(&s)
        .args(["build", "main.vast", "-o", "out/program"])
        .env("OUT", &out)
        .output()
        .unwrap();
    assert!(result.status.success(), "{}", stderr(&result));
    let ran = Command::new(out.join("program")).output().unwrap();
    assert_eq!(String::from_utf8_lossy(&ran.stdout).trim(), "staged");
    assert_eq!(leftovers(&out).len(), 50, "stale files must be left alone");

    if running_as_root() {
        eprintln!("skipping unwritable-directory case: root bypasses permissions");
        return;
    }
    let locked = s.0.join("locked");
    fs::create_dir(&locked).unwrap();
    fs::set_permissions(&locked, fs::Permissions::from_mode(0o555)).unwrap();
    let result = cli(&s)
        .args(["build", "main.vast", "-o", "locked/program"])
        .env("VASTITAS_KERNEL", s.0.join("absent-backend"))
        .output()
        .unwrap();
    fs::set_permissions(&locked, fs::Permissions::from_mode(0o755)).unwrap();
    let error = stderr(&result);
    assert!(
        error.starts_with("E_OUTPUT: cannot write to output directory locked"),
        "{error}"
    );
    assert!(!error.contains("E_BACKEND"), "{error}");
}

// #564 (3): diagnostics keep a bounded tail; backend JSON has a hard limit.
#[test]
fn subprocess_output_is_bounded() {
    let s = fixture();
    executable(
        &s.0.join("bin/lake"),
        "#!/bin/sh\nhead -c 40000000 /dev/zero | tr '\\0' x\nhead -c 40000000 /dev/zero | tr '\\0' y >&2\necho last-lake-line >&2\nexit 9\n",
    );
    let result = cli(&s)
        .args(["build", "main.vast", "-o", "program"])
        .output()
        .unwrap();
    let error = stderr(&result);
    assert!(error.starts_with("E_BUILD: native compilation failed"));
    assert!(error.len() < 3 * 1024 * 1024, "{} bytes", error.len());
    assert!(error.contains("earlier bytes omitted]"));
    assert!(error.trim_end().ends_with("last-lake-line"));

    let backend = s.0.join("flooding-backend");
    executable(&backend, "#!/bin/sh\ncat >/dev/null\nexec yes\n");
    let start = Instant::now();
    let result = cli(&s)
        .args(["check", "main.vast"])
        .env("VASTITAS_KERNEL", &backend)
        .output()
        .unwrap();
    let error = stderr(&result);
    assert!(
        error.starts_with("E_BACKEND:") && error.contains("wrote more than 256 MiB"),
        "{error}"
    );
    assert!(start.elapsed() < Duration::from_secs(60));
}

// #564 (6): module names are matched byte for byte, also on case-insensitive
// filesystems. These are source → diagnostic-code cases.
#[test]
fn module_files_must_match_module_names_exactly() {
    for (root, files) in [
        (
            "mod Math; fn main() -> Int { 0 }",
            &[("src/math.vast", "")][..],
        ),
        (
            "mod a; mod A; fn main() -> Int { 0 }",
            &[("src/a.vast", "")][..],
        ),
        (
            "mod geo; fn main() -> Int { 0 }",
            &[("src/Geo/mod.vast", "")][..],
        ),
        (
            "mod geo; fn main() -> Int { 0 }",
            &[
                ("src/geo/mod.vast", "mod Shape;"),
                ("src/geo/shape.vast", ""),
            ][..],
        ),
    ] {
        let s = Scratch::empty("driver_hardening modules");
        s.write(
            "app/Vastitas.toml",
            "[package]\nname = 'app'\nversion = '0.1.0'\nroot = 'src/main.vast'\n",
        );
        s.write("app/src/main.vast", root);
        for (path, source) in files {
            s.write(&format!("app/{path}"), source);
        }
        let result = Command::new(env!("CARGO_BIN_EXE_vastitas"))
            .args(["check", "--manifest-path"])
            .arg(s.0.join("app/Vastitas.toml"))
            .env("VASTITAS_KERNEL", kernel_path())
            .output()
            .unwrap();
        let error = stderr(&result);
        assert!(!result.status.success(), "accepted {root} with {files:?}");
        common::assert_first_code(&error, "E_INPUT");
    }
    // The exact spelling still loads.
    let s = Scratch::empty("driver_hardening modules");
    s.write(
        "app/Vastitas.toml",
        "[package]\nname = 'app'\nversion = '0.1.0'\nroot = 'src/main.vast'\n",
    );
    s.write("app/src/main.vast", "mod Geo; fn main() -> Int { 0 }");
    s.write("app/src/Geo/mod.vast", "mod Shape;");
    s.write("app/src/Geo/Shape.vast", "");
    let result = Command::new(env!("CARGO_BIN_EXE_vastitas"))
        .args(["check", "--manifest-path"])
        .arg(s.0.join("app/Vastitas.toml"))
        .env("VASTITAS_KERNEL", kernel_path())
        .output()
        .unwrap();
    assert!(result.status.success(), "{}", stderr(&result));
}

/// A kernel root (only the files a mocked Lake build reads) named `name`.
fn kernel_root(s: &Scratch, name: &str) -> PathBuf {
    let root = s.0.join(name);
    fs::create_dir_all(root.join("native")).unwrap();
    fs::create_dir_all(root.join("numerical")).unwrap();
    fs::write(root.join("lean-toolchain"), PINNED).unwrap();
    root
}

fn capturing_lake(s: &Scratch) -> PathBuf {
    let capture = s.0.join("capture");
    fs::create_dir_all(&capture).unwrap();
    executable(
        &s.0.join("bin/lake"),
        "#!/bin/sh\ncp lakefile.* \"$CAPTURE/\"\nexit 1\n",
    );
    capture
}

/// Evaluate a Lean string literal with the pinned toolchain.
fn lean_literal(s: &Scratch, literal: &str) -> String {
    let directory = s.0.join("literal");
    fs::create_dir_all(&directory).unwrap();
    fs::write(directory.join("lean-toolchain"), PINNED).unwrap();
    fs::write(
        directory.join("Literal.lean"),
        format!("def main : IO Unit := IO.print {literal}\n"),
    )
    .unwrap();
    let result = Command::new("lean")
        .current_dir(&directory)
        .args(["--run", "Literal.lean"])
        .output()
        .unwrap();
    assert!(result.status.success(), "{}", stderr(&result));
    String::from_utf8(result.stdout).unwrap()
}

// #522: manifests use TOML or Lean string escaping, never JSON escaping.
#[test]
fn generated_manifests_escape_paths_for_their_own_syntax() {
    let s = fixture();
    let capture = capturing_lake(&s);
    let name = "root\u{8}bs \"quote\" back\\slash\u{c}feed\ttab";
    let root = kernel_root(&s, name).canonicalize().unwrap();
    let root_text = root.to_str().unwrap();
    let result = cli(&s)
        .args(["build", "main.vast", "-o", "program"])
        .env("VASTITAS_KERNEL_ROOT", &root)
        .env("CAPTURE", &capture)
        .output()
        .unwrap();
    common::expect_code(&result, "E_BUILD");
    let manifest: toml::Value =
        toml::from_str(&fs::read_to_string(capture.join("lakefile.toml")).unwrap()).unwrap();
    assert_eq!(manifest["require"][0]["path"].as_str(), Some(root_text));

    // Numerical builds use lakefile.lean: a mocked protocol-8 backend asks for
    // both optional runtimes.
    s.write(
        "pkg/Vastitas.toml",
        "[package]\nname = 'numeric'\nversion = '0.1.0'\nroot = 'main.vast'\n",
    );
    s.write("pkg/main.vast", RESOURCE_MAIN);
    let backend = s.0.join("numerical-backend");
    executable(
        &backend,
        &format!(
            "#!/bin/sh\ncat >/dev/null\nprintf '%s\\n' '{{\"version\":8,\"ok\":true,\"kernel\":{},\"lean_source\":\"def main : IO Unit := pure ()\",\"storage_runtime\":true,\"numerical_runtime\":true}}'\n",
            kernel_identity()
        ),
    );
    let prefix = s.0.join("openblas \"prefix\"\u{8}");
    fs::create_dir_all(&prefix).unwrap();
    let result = cli(&s)
        .args([
            "build",
            "--manifest-path",
            "pkg/Vastitas.toml",
            "-o",
            "numeric",
        ])
        .arg("--openblas-prefix")
        .arg(&prefix)
        .env("VASTITAS_KERNEL", &backend)
        .env("VASTITAS_KERNEL_ROOT", &root)
        .env("CAPTURE", &capture)
        .output()
        .unwrap();
    common::expect_code(&result, "E_BUILD");
    let lakefile = fs::read_to_string(capture.join("lakefile.lean")).unwrap();
    assert!(
        !lakefile.contains("\\b") && !lakefile.contains("\\f"),
        "{lakefile}"
    );
    let literal = |marker: &str| {
        let start = lakefile.find(marker).unwrap() + marker.len();
        let line = lakefile[start..].lines().next().unwrap();
        line.trim_end_matches(" with").to_string()
    };
    assert_eq!(
        lean_literal(&s, &literal("require vastitas_kernel from ")),
        root_text
    );
    assert_eq!(
        lean_literal(&s, &literal("require vastitas_gemm_native from ")),
        root.join("numerical").to_str().unwrap()
    );
    assert_eq!(
        lean_literal(&s, &literal("insert `openblas ")),
        prefix.canonicalize().unwrap().to_str().unwrap()
    );
}

// #522: a non-UTF-8 kernel root is named and rejected before the backend runs.
#[test]
fn non_utf8_kernel_root_is_rejected_before_the_backend() {
    use std::os::unix::ffi::OsStrExt;
    let s = fixture();
    let root = s.0.join(std::ffi::OsStr::from_bytes(b"root\xfflatin1"));
    if let Err(error) = fs::create_dir(&root) {
        // APFS and other UTF-8-only filesystems cannot express the case.
        eprintln!("skipping: cannot create a non-UTF-8 directory name: {error}");
        return;
    }
    fs::write(root.join("lean-toolchain"), PINNED).unwrap();
    let result = cli(&s)
        .args(["build", "main.vast", "-o", "program"])
        .env("VASTITAS_KERNEL", s.0.join("absent-backend"))
        .env("VASTITAS_KERNEL_ROOT", &root)
        .output()
        .unwrap();
    let error = stderr(&result);
    assert!(
        error.starts_with("E_BUILD: kernel root path is not valid UTF-8")
            && error.contains("latin1"),
        "{error}"
    );
    assert!(!error.contains("E_BACKEND"), "{error}");
}

// #550: only a kernel built from this compiler's kernel sources is accepted.
#[test]
fn kernel_build_identity_fails_closed() {
    let s = fixture();
    let identity = kernel_identity();
    let stale = identity.replace(
        &serde_json::from_str::<serde_json::Value>(&identity).unwrap()["sources"]
            .as_str()
            .unwrap()
            .to_string(),
        "0123456789abcdef",
    );
    let backend = s.0.join("kernel");
    for (response, problem) in [
        (
            r#"{"version":2,"ok":true}"#.to_string(),
            "did not report a Vastitas kernel build identity",
        ),
        (
            format!(r#"{{"version":2,"ok":true,"kernel":{stale}}}"#),
            "built from kernel sources 0123456789abcdef",
        ),
        (
            format!(
                r#"{{"version":2,"ok":true,"kernel":{}}}"#,
                identity.replace("\"lean\":\"", "\"lean\":\"0.")
            ),
            "with Lean 0.",
        ),
    ] {
        executable(
            &backend,
            &format!("#!/bin/sh\ncat >/dev/null\nprintf '%s\\n' '{response}'\n"),
        );
        let result = cli(&s)
            .args(["check", "main.vast"])
            .env("VASTITAS_KERNEL", &backend)
            .output()
            .unwrap();
        let error = stderr(&result);
        assert!(!result.status.success(), "accepted {response}");
        assert!(
            error.starts_with("E_BACKEND: incompatible kernel") && error.contains(problem),
            "{error}"
        );
        assert!(error.contains("Rebuild the kernel"), "{error}");
    }
    // A stale kernel's rejection is shown, with a note about its identity.
    executable(
        &backend,
        &format!(
            "#!/bin/sh\ncat >/dev/null\nprintf '%s\\n' '{{\"version\":2,\"ok\":false,\"kernel\":{stale},\"diagnostics\":[{{\"code\":\"E_SENTINEL\",\"message\":\"stale rejection\"}}]}}'\nexit 1\n"
        ),
    );
    let result = cli(&s)
        .args(["check", "main.vast"])
        .env("VASTITAS_KERNEL", &backend)
        .output()
        .unwrap();
    let error = stderr(&result);
    assert!(error.contains("E_SENTINEL: stale rejection"), "{error}");
    assert!(
        error.contains("note: these diagnostics may come from a stale or foreign kernel"),
        "{error}"
    );
    // The real kernel reports exactly the identity this driver was built for.
    let result = cli(&s).args(["check", "main.vast"]).output().unwrap();
    assert!(result.status.success(), "{}", stderr(&result));
}

// #550: Lake must not run with a Lean other than the pinned toolchain.
#[test]
fn lean_toolchain_mismatch_fails_before_lake() {
    let s = fixture();
    let ran = s.0.join("lake-ran");
    executable(&s.0.join("bin/lake"), "#!/bin/sh\n: > \"$RAN\"\nexit 1\n");
    executable(
        &s.0.join("bin/lean"),
        "#!/bin/sh\necho 'Lean (version 4.0.0, x86_64-unknown-linux-gnu, commit 0, Release)'\n",
    );
    fs::write(s.0.join("program"), "existing").unwrap();
    let result = cli(&s)
        .args(["build", "main.vast", "-o", "program"])
        .env("RAN", &ran)
        .output()
        .unwrap();
    let error = stderr(&result);
    assert!(
        error.starts_with("E_BUILD: Lean toolchain mismatch: `lean --version` reports 4.0.0")
            && error.contains(PINNED.trim()),
        "{error}"
    );
    assert!(!ran.exists(), "Lake ran with a mismatched toolchain");
    assert_eq!(fs::read_to_string(s.0.join("program")).unwrap(), "existing");
}

// #557: building over an existing regular output replaces its bytes and mode
// and leaves no staging file behind.
#[test]
fn existing_output_is_replaced_with_new_bytes_and_mode() {
    let s = fixture();
    successful_lake(&s);
    let output = s.0.join("program");
    fs::write(&output, "previous output\n").unwrap();
    fs::set_permissions(&output, fs::Permissions::from_mode(0o600)).unwrap();
    for text in ["first", "second"] {
        let result = cli(&s)
            .args(["build", "main.vast", "-o", "program"])
            .env("NATIVE_TEXT", text)
            .output()
            .unwrap();
        assert!(result.status.success(), "{}", stderr(&result));
        let metadata = fs::symlink_metadata(&output).unwrap();
        assert!(metadata.file_type().is_file());
        assert_eq!(
            metadata.permissions().mode() & 0o100,
            0o100,
            "not executable"
        );
        assert_eq!(
            fs::read_to_string(&output).unwrap(),
            format!("#!/bin/sh\necho {text}\n")
        );
        let ran = Command::new(&output).output().unwrap();
        assert_eq!(String::from_utf8_lossy(&ran.stdout).trim(), text);
        assert!(leftovers(&s.0).is_empty(), "{:?}", leftovers(&s.0));
    }
}

// #557: native-runtime options are refused for a program without checked
// numerical operations, before Lake runs and without touching the output.
#[test]
fn native_options_require_a_numerical_program() {
    let s = fixture();
    let lake_ran = s.0.join("lake-ran");
    executable(
        &s.0.join("bin/lake"),
        &format!("#!/bin/sh\n: > '{}'\nexit 1\n", lake_ran.display()),
    );
    s.write("program", "previous output");
    for options in [
        vec!["--openblas-prefix", "openblas"],
        vec!["--native-cc", "cc"],
    ] {
        let result = cli(&s)
            .args(["build", "main.vast", "-o", "program"])
            .args(&options)
            .output()
            .unwrap();
        let error = common::expect_code(&result, "E_USAGE");
        assert!(
            error.contains("require a program with checked numerical operations"),
            "{options:?}: {error}"
        );
        assert!(!lake_ran.exists(), "{options:?} reached Lake");
        assert_eq!(fs::read(s.0.join("program")).unwrap(), b"previous output");
    }
}

// #557: only protocols 8 and 9 may ask for the optional native runtimes; an
// older success response that carries either flag is a protocol error.
#[test]
fn optional_runtime_flags_are_refused_for_protocols_before_eight() {
    let s = fixture();
    successful_lake(&s);
    s.write(
        "pkg/Vastitas.toml",
        "[package]\nname = 'plain'\nversion = '0.1.0'\nroot = 'main.vast'\n",
    );
    s.write("pkg/main.vast", "fn main() -> Int { 42 }");
    let indexed = common::root().join("examples/packages/geometry/indexed/Vastitas.toml");
    let backend = s.0.join("old-backend");
    // Echo the request's own protocol version, so only the flags are wrong.
    executable(
        &backend,
        &format!(
            "#!/bin/sh\nrequest=$(cat)\nversion=$(printf '%s' \"$request\" | sed -n 's/^{{\"version\":\\([0-9]*\\),.*/\\1/p')\nprintf '{{\"version\":%s,\"ok\":true,\"kernel\":{},\"lean_source\":\"def main : IO Unit := pure ()\",%s}}\\n' \"$version\" \"$FLAGS\"\n",
            kernel_identity()
        ),
    );
    for (inputs, version) in [
        (vec!["main.vast".to_string()], 2),
        (
            vec!["--manifest-path".into(), "pkg/Vastitas.toml".into()],
            3,
        ),
        (
            vec!["--manifest-path".into(), indexed.display().to_string()],
            7,
        ),
    ] {
        let wire = common::captured_wire(cli(&s).arg("check").args(&inputs), version);
        assert_eq!(wire["version"], version);
        for (flags, message) in [
            (
                "\"storage_runtime\":true",
                "invalid optional storage runtime requirement",
            ),
            (
                "\"storage_runtime\":false",
                "invalid optional storage runtime requirement",
            ),
            (
                "\"numerical_runtime\":true",
                "invalid optional numerical runtime requirement",
            ),
        ] {
            let result = cli(&s)
                .arg("build")
                .args(&inputs)
                .args(["-o", "program"])
                .env("VASTITAS_KERNEL", &backend)
                .env("FLAGS", flags)
                .env("NATIVE_TEXT", "never")
                .output()
                .unwrap();
            let error = common::expect_code(&result, "E_PROTOCOL");
            assert!(error.contains(message), "v{version} {flags}: {error}");
            assert!(
                !s.0.join("program").exists(),
                "v{version} {flags} installed"
            );
        }
    }
}
