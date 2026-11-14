//! Reject blocking/special inputs and bounded expansion before invoking Lean.
mod common;
use common::{Scratch, cli};
use nix::sys::stat::Mode;
use nix::unistd::mkfifo;
use std::fs;
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt, symlink};
use std::os::unix::net::UnixListener;
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

fn bounded(command: &mut Command) -> Output {
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(30);
    while child.try_wait().unwrap().is_none() {
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("input/output validation blocked");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    child.wait_with_output().unwrap()
}

#[track_caller]
fn reject(s: &Scratch, args: &[&str], expected: &str) -> String {
    let output = bounded(
        cli()
            .current_dir(&s.0)
            .args(args)
            .env("VASTITAS_KERNEL", s.0.join("absent backend")),
    );
    let error = common::expect_diagnostic(&output, expected);
    assert!(
        !error.contains("E_BACKEND"),
        "validation reached the backend: {error}"
    );
    error
}

#[test]
fn blocking_and_device_sources_are_rejected_without_reading() {
    let s = Scratch::empty("special inputs");
    mkfifo(&s.0.join("pipe.vast"), Mode::S_IRUSR | Mode::S_IWUSR).unwrap();
    symlink("/dev/zero", s.0.join("device.vast")).unwrap();
    fs::create_dir(s.0.join("directory.vast")).unwrap();
    for path in ["pipe.vast", "device.vast", "directory.vast"] {
        reject(
            &s,
            &["check", path],
            "E_INPUT: input must be a regular file",
        );
    }
    s.write("main.vast", "fn main() -> Int { 0 }");
    reject(
        &s,
        &["check", "main.vast", "--lib", "pipe.vast"],
        "E_INPUT: input must be a regular file",
    );
    mkfifo(&s.0.join("Vastitas.toml"), Mode::S_IRUSR | Mode::S_IWUSR).unwrap();
    reject(
        &s,
        &["check", "--manifest-path", "Vastitas.toml"],
        "E_INPUT: input must be a regular file",
    );
    fs::remove_file(s.0.join("Vastitas.toml")).unwrap();
    s.write(
        "Vastitas.toml",
        "[package]\nname='special'\nversion='0.1.0'\nroot='main.vast'\n",
    );
    s.write("main.vast", "mod pipe; fn main() -> Int { 0 }");
    reject(
        &s,
        &["check", "--manifest-path", "Vastitas.toml"],
        "E_INPUT: input must be a regular file",
    );
}

#[test]
fn special_outputs_and_their_symlinks_are_preserved() {
    let s = Scratch::empty("special outputs");
    s.write("main.vast", "fn main() -> Int { 0 }");
    mkfifo(&s.0.join("pipe"), Mode::S_IRUSR | Mode::S_IWUSR).unwrap();
    symlink("pipe", s.0.join("pipe-link")).unwrap();
    symlink("/dev/null", s.0.join("device-link")).unwrap();
    symlink("missing", s.0.join("dangling-link")).unwrap();
    let _socket = UnixListener::bind(s.0.join("socket")).unwrap();
    for path in [
        "pipe",
        "pipe-link",
        "device-link",
        "dangling-link",
        "socket",
        "/dev/null",
    ] {
        let file = s.0.join(path);
        let before = fs::symlink_metadata(&file).unwrap();
        reject(
            &s,
            &["build", "main.vast", "-o", path],
            "E_OUTPUT: output must name a regular file",
        );
        let after = fs::symlink_metadata(&file).unwrap();
        assert_eq!(
            (before.dev(), before.ino(), before.mode()),
            (after.dev(), after.ino(), after.mode())
        );
    }
    assert!(
        fs::metadata(s.0.join("pipe"))
            .unwrap()
            .file_type()
            .is_fifo()
    );
}

#[test]
fn oversized_regular_input_is_rejected_before_parsing() {
    let s = Scratch::empty("input size");
    fs::File::create(s.0.join("large.vast"))
        .unwrap()
        .set_len(16 * 1024 * 1024 + 1)
        .unwrap();
    reject(&s, &["check", "large.vast"], "E_LIMIT: input");
}

/// #740: a source file of 11.9 MB, within the limits on inputs, makes a
/// request of 1.14 GB, beyond the largest request that the kernel reads. The
/// frontend reports the limit of the program before it starts the kernel,
/// and it never holds the request. Ignored because the frontend still builds
/// the whole program and counts its request: about 3 GB of memory and 30
/// seconds in a debug build. The unit tests of `bounded_json` in
/// `src/driver.rs` check the bound with a small one.
#[test]
#[ignore = "builds a request of more than 1 GiB"]
fn request_bound_is_a_limit_of_the_program() {
    let s = Scratch::empty("request size");
    let sum = vec!["0"; 120].join("+");
    let mut source = String::from("fn main() -> Int {\n");
    for index in 0..47_000 {
        source.push_str(&format!("let x{index} = {sum};\n"));
    }
    source.push_str("0\n}\n");
    assert!(source.len() < 16 * 1024 * 1024);
    s.write("big.vast", &source);
    let output = cli()
        .current_dir(&s.0)
        .args(["check", "big.vast"])
        .env("VASTITAS_KERNEL", s.0.join("absent backend"))
        .output()
        .unwrap();
    let error = common::expect_code(&output, "E_LIMIT");
    assert!(
        error
            .contains("big.vast:1:1: E_LIMIT: the request of the program exceeds 1073741824 bytes"),
        "{error}"
    );
    assert!(!error.contains("E_BACKEND"), "{error}");
}

#[test]
fn reused_source_bytes_are_charged_for_each_logical_module() {
    let s = Scratch::empty("total input size");
    s.write(
        "Vastitas.toml",
        "[package]\nname='large'\nversion='0.1.0'\nroot='main.vast'\n",
    );
    s.write("main.vast", "mod a; mod b; mod c; mod d;");
    let text = format!("//{}", "x".repeat(16 * 1024 * 1024 - 2));
    s.write("a.vast", &text);
    for name in ["b.vast", "c.vast", "d.vast"] {
        symlink("a.vast", s.0.join(name)).unwrap();
    }
    let error = reject(
        &s,
        &["check", "--manifest-path", "Vastitas.toml"],
        "E_LIMIT",
    );
    assert!(error.contains("64 MiB compilation input budget"), "{error}");
}

#[test]
fn symlink_module_fanout_is_bounded_across_the_package_closure() {
    let s = Scratch::empty("module fanout");
    s.write(
        "Vastitas.toml",
        "[package]\nname='fanout'\nversion='0.1.0'\nroot='L0/mod.vast'\n",
    );
    for depth in 0..14 {
        s.write(
            &format!("L{depth}/mod.vast"),
            if depth == 13 { "" } else { "mod a; mod b;" },
        );
        if depth < 13 {
            for name in ["a", "b"] {
                symlink(
                    format!("../L{}", depth + 1),
                    s.0.join(format!("L{depth}/{name}")),
                )
                .unwrap();
            }
        }
    }
    reject(
        &s,
        &["check", "--manifest-path", "Vastitas.toml"],
        "E_LIMIT: package closure exceeds 4096 logical modules",
    );
}

// #557: the 8,192-input-file bound is exact and is enforced before the backend.
#[test]
fn input_file_count_is_bounded_before_the_backend() {
    let s = Scratch::empty("input count");
    s.write("main.vast", "fn main() -> Int { 42 }");
    for index in 0..8192 {
        s.write(&format!("libs/l{index}.vast"), "");
    }
    let arguments = |libraries: usize| {
        let mut arguments = vec!["check".to_string(), "main.vast".to_string()];
        for index in 0..libraries {
            arguments.push("--lib".into());
            arguments.push(format!("libs/l{index}.vast"));
        }
        arguments
    };
    // main.vast plus 8,191 libraries is exactly the bound.
    let accepted = bounded(cli().current_dir(&s.0).args(arguments(8191)));
    common::success(&accepted);
    let over = arguments(8192);
    let over: Vec<&str> = over.iter().map(String::as_str).collect();
    let error = reject(&s, &over, "E_LIMIT");
    assert!(
        error.contains("compilation inputs exceed 8192 files"),
        "{error}"
    );
}

/// A manifest chooses its root and dependency paths, and TOML escapes can
/// spell any character in them (#680). An `E_INPUT` error names a control
/// character by its code point: the path stays readable, and neither a
/// terminal control nor a forged line reaches stderr.
#[test]
fn manifest_paths_in_errors_carry_no_terminal_controls() {
    let s = Scratch::empty("manifest controls");
    // As TOML escapes: clear the screen, home the cursor, ring the bell, start
    // a line, and the one-character control sequence introducer.
    let hostile = r"x\u001b[2J\u001b[H\u0007\nE_FORGED: \u009b2J";
    let named = "x<U+001B>[2J<U+001B>[H<U+0007><U+000A>E_FORGED: <U+009B>2J";
    let package = |name: &str, body: String| {
        s.write(&format!("{name}/main.vast"), "fn main() -> Int { 0 }");
        s.write(
            &format!("{name}/Vastitas.toml"),
            &format!("[package]\nname = \"probe\"\nversion = \"0.1.0\"\n{body}\n"),
        );
    };
    package("root", format!("root = \"{hostile}.vast\""));
    package(
        "dependency",
        format!("root = \"main.vast\"\n[dependencies]\ndep = {{ path = \"{hostile}\" }}"),
    );
    // A root that exists, under a name with a control character.
    package("existing", r#"root = "x\u001b[2J.txt""#.to_string());
    s.write("existing/x\u{1b}[2J.txt", "");
    const MISSING: &str = "E_INPUT: cannot read ";
    const EXTENSION: &str = "E_INPUT: module filename must have the .vast extension: ";
    for (name, start, path) in [
        (
            "root",
            MISSING,
            format!("/root/{named}.vast: No such file or directory"),
        ),
        (
            "dependency",
            MISSING,
            format!("/dependency/{named}/Vastitas.toml: No such file or directory"),
        ),
        (
            "existing",
            EXTENSION,
            "/existing/x<U+001B>[2J.txt\n".to_string(),
        ),
    ] {
        let output = bounded(
            cli()
                .current_dir(&s.0)
                .args(["check", "--manifest-path"])
                .arg(format!("{name}/Vastitas.toml"))
                .env("VASTITAS_KERNEL", s.0.join("absent backend")),
        );
        let stderr = common::expect_code(&output, "E_INPUT");
        assert!(stderr.starts_with(start), "{stderr:?}");
        assert!(stderr.contains(&path), "{stderr:?}");
        // The scratch directory's own name, spaces included, is not rewritten.
        let scratch = s.0.file_name().unwrap().to_str().unwrap();
        assert!(stderr.contains(scratch), "{stderr:?}");
        // The only control byte or character is the newline that ends the line.
        let controls: Vec<u8> = output
            .stderr
            .iter()
            .copied()
            .filter(u8::is_ascii_control)
            .collect();
        assert_eq!(controls, b"\n", "{stderr:?}");
        assert!(output.stderr.ends_with(b"\n"), "{stderr:?}");
        assert_eq!(stderr.chars().filter(|ch| ch.is_control()).count(), 1);
    }
}

/// A file name that a terminal would obey (#718): clear the screen, ring the
/// bell, start a forged diagnostic line, the one-character control sequence
/// introducer, a tab and a right-to-left override. Files under such names are
/// created in the scratch directory of a test only.
const HOSTILE: &str = "x\u{1b}[2J\u{7}\nE_FORGED: \u{9b}2J\t\u{202e}";
/// `HOSTILE` as a TOML basic string spells it.
const SPELLED: &str = "x\\u001b[2J\\u0007\\nE_FORGED: \\u009b2J\\t\\u202e";
/// `HOSTILE` as the compiler shows it.
const NAMED: &str = "x<U+001B>[2J<U+0007><U+000A>E_FORGED: <U+009B>2J<U+0009><U+202E>";

/// What a stream of the compiler must hold: all of its text, or its start,
/// its number of lines and parts that it contains.
struct Expected {
    start: String,
    whole: bool,
    lines: usize,
    parts: Vec<String>,
}

fn whole(text: impl Into<String>) -> Expected {
    let start = text.into();
    Expected {
        lines: start.lines().count(),
        start,
        whole: true,
        parts: Vec::new(),
    }
}

fn start(text: impl Into<String>, lines: usize) -> Expected {
    Expected {
        start: text.into(),
        whole: false,
        lines,
        parts: Vec::new(),
    }
}

impl Expected {
    fn with(mut self, part: impl Into<String>) -> Self {
        self.parts.push(part.into());
        self
    }

    /// How `stream` differs. Whatever is expected, the line feeds that end
    /// the lines of `stream` must be its only control characters, and it
    /// must hold no right-to-left override.
    fn difference(&self, stream: &[u8]) -> Option<String> {
        let text = String::from_utf8_lossy(stream);
        let controls: String = text
            .chars()
            .filter(|ch| (ch.is_control() && *ch != '\n') || *ch == '\u{202e}')
            .collect();
        if !controls.is_empty() {
            return Some(format!("the characters {controls:?} in {text:?}"));
        }
        if !(text.is_empty() || text.ends_with('\n')) {
            return Some(format!("an open last line in {text:?}"));
        }
        let missing = self.parts.iter().find(|part| !text.contains(part.as_str()));
        if (self.whole && *text != self.start)
            || !text.starts_with(&self.start)
            || text.lines().count() != self.lines
            || missing.is_some()
        {
            return Some(format!(
                "expected {:?} with {:?} in {} lines, found {text:?}",
                self.start, self.parts, self.lines
            ));
        }
        None
    }
}

/// The failed cases of a test. One run reports all of them, so a run without
/// the fix shows that every case depends on it.
#[derive(Default)]
struct Cases(Vec<String>);

impl Cases {
    /// The command must fail with `code` as its first diagnostic code and
    /// with `expected` as its stderr.
    fn rejected(&mut self, name: &str, output: &Output, code: &str, expected: Expected) {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let codes = common::diagnostic_codes(&stderr);
        let problem = if output.status.success() {
            Some("the command succeeded".to_string())
        } else if codes.first().map(String::as_str) != Some(code) {
            Some(format!("expected {code} first in {stderr:?}"))
        } else {
            expected.difference(&output.stderr)
        };
        self.0
            .extend(problem.map(|problem| format!("{name}: {problem}")));
    }

    /// The command must succeed with `expected` as its stdout and nothing on
    /// stderr.
    fn accepted(&mut self, name: &str, output: &Output, expected: Expected) {
        let problem = if !output.status.success() || !output.stderr.is_empty() {
            Some(format!(
                "the command failed or wrote {:?}",
                String::from_utf8_lossy(&output.stderr)
            ))
        } else {
            expected.difference(&output.stdout)
        };
        self.0
            .extend(problem.map(|problem| format!("{name}: {problem}")));
    }

    #[track_caller]
    fn finish(self) {
        assert!(
            self.0.is_empty(),
            "{} failed cases:\n{}",
            self.0.len(),
            self.0.join("\n")
        );
    }
}

/// The canonical path of the scratch directory, as diagnostics print it.
fn canonical(s: &Scratch) -> String {
    fs::canonicalize(&s.0)
        .unwrap()
        .into_os_string()
        .into_string()
        .unwrap()
}

/// Checks the package in directory `package` of the scratch directory. No
/// backend is reachable: the rejection comes from the driver.
fn manifest_mode(s: &Scratch, package: &str) -> Output {
    bounded(
        s.command("check", &format!("{package}/Vastitas.toml"))
            .env("VASTITAS_KERNEL", s.0.join("absent backend")),
    )
}

/// A TOML error quotes the offending line of the manifest, and its message can
/// quote a key that TOML escapes spell (#718). Both name a control character
/// by its code point. The carets stay under the place that toml marks: they
/// move right by what the names ahead of it add and widen by what the names
/// in it add.
#[test]
fn manifest_text_in_toml_errors_carries_no_terminal_controls() {
    let s = Scratch::empty("toml controls");
    let root = canonical(&s);
    let mut cases = Cases::default();
    const HEAD: &str = "[package]\nname = \"probe\"\nversion = \"0.1.0\"\n";
    for (name, manifest, expected) in [
        (
            // Raw controls in a comment. toml marks the first of them.
            "comment",
            format!("{HEAD}root = \"main.vast\" # \u{1b}[2J\u{1b}[H\n"),
            concat!(
                "TOML parse error at line 4, column 22\n",
                "  |\n",
                "4 | root = \"main.vast\" # <U+001B>[2J<U+001B>[H\n",
                "  |                      ^^^^^^^^\n",
                "expected newline, `#`\n",
            ),
        ),
        (
            // A tab and a right-to-left override ahead of the place, which
            // is the `x`.
            "ahead",
            format!("{HEAD}\troot = \"a\u{202e}b.vast\" x\n"),
            concat!(
                "TOML parse error at line 4, column 20\n",
                "  |\n",
                "4 | <U+0009>root = \"a<U+202E>b.vast\" x\n",
                "  |                                  ^\n",
                "expected newline, `#`\n",
            ),
        ),
        (
            // The message quotes the key as TOML decodes it: with an escape
            // character and a line feed that starts a forged line.
            "key",
            format!("{HEAD}root = \"main.vast\"\n\"k\\u001b[2J\\nE_FORGED: x\" = 1\n"),
            concat!(
                "TOML parse error at line 5, column 1\n",
                "  |\n",
                "5 | \"k\\u001b[2J\\nE_FORGED: x\" = 1\n",
                "  | ^^^^^^^^^^^^^^^^^^^^^^^^^\n",
                "unknown field `k<U+001B>[2J<U+000A>E_FORGED: x`, ",
                "expected one of `name`, `version`, `root`\n",
            ),
        ),
        (
            "duplicate",
            format!("{HEAD}root = \"main.vast\"\n\"k\\u001b[2J\" = 1\n\"k\\u001b[2J\" = 2\n"),
            concat!(
                "TOML parse error at line 6, column 1\n",
                "  |\n",
                "6 | \"k\\u001b[2J\" = 2\n",
                "  | ^\n",
                "duplicate key `k<U+001B>[2J` in table `package`\n",
            ),
        ),
        (
            // The carriage return of a CR LF line end is no part of the
            // quoted line. The two lines of the message stay two lines.
            "crlf",
            "[package]\r\nname = \"probe\"\r\nversion = \r\nroot = \"main.vast\"\r\n".to_string(),
            concat!(
                "TOML parse error at line 3, column 11\n",
                "  |\n",
                "3 | version = \n",
                "  |           ^\n",
                "invalid string\n",
                "expected `\"`, `'`\n",
            ),
        ),
    ] {
        s.write(&format!("{name}/Vastitas.toml"), &manifest);
        // toml ends its rendering with a line feed, and the driver ends the
        // error with another.
        cases.rejected(
            name,
            &manifest_mode(&s, name),
            "E_MANIFEST",
            whole(format!(
                "{root}/{name}/Vastitas.toml: E_MANIFEST: {expected}\n"
            )),
        );
    }
    cases.finish();
}

/// A package ships its files under names of its choice and names them in its
/// manifest (#718). Every diagnostic for such a file names the control
/// characters of its path: the `FILE:LINE:COLUMN:` and `MANIFEST:` prefixes,
/// the paths of `E_CYCLE` and of the input and output errors, and the module
/// files that a message lists.
#[test]
fn package_paths_in_diagnostics_carry_no_terminal_controls() {
    let s = Scratch::empty("package controls");
    let root = canonical(&s);
    let mut cases = Cases::default();
    let manifest = |root: &str, rest: &str| {
        format!("[package]\nname = \"probe\"\nversion = \"0.1.0\"\nroot = \"{root}\"\n{rest}")
    };

    // The prefix of a source diagnostic, for a root file under a hostile name.
    s.write(
        "prefix/Vastitas.toml",
        &manifest(&format!("{SPELLED}.vast"), ""),
    );
    s.write(
        &format!("prefix/{HOSTILE}.vast"),
        "fn main() -> Int { 0 } }",
    );
    cases.rejected(
        "prefix",
        &manifest_mode(&s, "prefix"),
        "E_PARSE",
        start(format!("{root}/prefix/{NAMED}.vast:1:24: E_PARSE: "), 1),
    );

    // The manifest of a dependency in a hostile directory: the prefix of
    // each `E_MANIFEST` error, and the path of a dependency cycle. `PATH`
    // stands for the path of that manifest.
    let dependency = format!("[dependencies]\ndep = {{ path = \"{SPELLED}\" }}\n");
    const DEP: &str = "[package]\nname = \"dep\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n";
    for (name, body, code, expected) in [
        (
            "empty-name",
            DEP.replace("dep", ""),
            "E_MANIFEST",
            whole("PATH: E_MANIFEST: package name must not be empty\n"),
        ),
        (
            "version",
            DEP.replace("0.1.0", "1"),
            "E_MANIFEST",
            start("PATH: E_MANIFEST: invalid SemVer: ", 1),
        ),
        (
            "alias",
            format!("{DEP}[dependencies]\n\"a-b\" = {{ path = \".\" }}\n"),
            "E_MANIFEST",
            whole("PATH: E_MANIFEST: dependency alias must be an ASCII identifier\n"),
        ),
        (
            "reserved",
            format!("{DEP}[dependencies]\nmod = {{ path = \".\" }}\n"),
            "E_MANIFEST",
            whole("PATH: E_MANIFEST: dependency alias 'mod' is reserved\n"),
        ),
        (
            "syntax",
            "[package]\nname = \n".to_string(),
            "E_MANIFEST",
            start(
                "PATH: E_MANIFEST: TOML parse error at line 2, column 8\n",
                7,
            ),
        ),
        (
            "cycle",
            format!("{DEP}[dependencies]\nback = {{ path = \".\" }}\n"),
            "E_CYCLE",
            whole("E_CYCLE: cyclic package dependency at PATH\n"),
        ),
    ] {
        s.write(
            &format!("{name}/Vastitas.toml"),
            &manifest("main.vast", &dependency),
        );
        s.write(&format!("{name}/main.vast"), "fn main() -> Int { 0 }");
        s.write(&format!("{name}/{HOSTILE}/Vastitas.toml"), &body);
        s.write(&format!("{name}/{HOSTILE}/main.vast"), "");
        let path = format!("{root}/{name}/{NAMED}/Vastitas.toml");
        let expected = Expected {
            start: expected.start.replace("PATH", &path),
            ..expected
        };
        cases.rejected(name, &manifest_mode(&s, name), code, expected);
    }

    // Module files of a root in a hostile directory.
    let module = |name: &str| {
        s.write(
            &format!("{name}/Vastitas.toml"),
            &manifest(&format!("{SPELLED}/main.vast"), ""),
        );
        s.write(
            &format!("{name}/{HOSTILE}/main.vast"),
            "mod a;\nfn main() -> Int { 0 }",
        );
        format!("{root}/{name}/{NAMED}")
    };
    let directory = module("module-cycle");
    symlink(
        "main.vast",
        s.0.join(format!("module-cycle/{HOSTILE}/a.vast")),
    )
    .unwrap();
    cases.rejected(
        "module-cycle",
        &manifest_mode(&s, "module-cycle"),
        "E_CYCLE",
        whole(format!(
            "E_CYCLE: cyclic module loading: {directory}/main.vast\n"
        )),
    );
    let directory = module("missing");
    cases.rejected(
        "missing",
        &manifest_mode(&s, "missing"),
        "E_INPUT",
        whole(format!(
            "{directory}/main.vast:1:1: E_INPUT: module requires {directory}/a.vast or {directory}/a/mod.vast\n"
        )),
    );
    let directory = module("ambiguous");
    s.write(&format!("ambiguous/{HOSTILE}/a.vast"), "");
    s.write(&format!("ambiguous/{HOSTILE}/a/mod.vast"), "");
    cases.rejected(
        "ambiguous",
        &manifest_mode(&s, "ambiguous"),
        "E_INPUT",
        whole(format!(
            "{directory}/main.vast:1:1: E_INPUT: ambiguous module: both {directory}/a.vast and {directory}/a/mod.vast exist\n"
        )),
    );
    // `A.vast` for `mod a;` is a case mismatch on a case-insensitive
    // filesystem and a missing module on any other.
    let directory = module("case");
    s.write(&format!("case/{HOSTILE}/A.vast"), "");
    cases.rejected(
        "case",
        &manifest_mode(&s, "case"),
        "E_INPUT",
        start(format!("{directory}/main.vast:1:1: E_INPUT: module "), 1)
            .with(format!("{directory}/a.vast")),
    );

    // A root that is no readable source file, under a hostile name.
    for name in ["directory", "encoding", "size", "overwrite"] {
        s.write(
            &format!("{name}/Vastitas.toml"),
            &manifest(&format!("{SPELLED}.vast"), ""),
        );
    }
    fs::create_dir(s.0.join(format!("directory/{HOSTILE}.vast"))).unwrap();
    cases.rejected(
        "directory",
        &manifest_mode(&s, "directory"),
        "E_INPUT",
        whole(format!(
            "E_INPUT: input must be a regular file: {root}/directory/{NAMED}.vast\n"
        )),
    );
    fs::write(s.0.join(format!("encoding/{HOSTILE}.vast")), b"// \xff\n").unwrap();
    cases.rejected(
        "encoding",
        &manifest_mode(&s, "encoding"),
        "E_INPUT",
        start(
            format!("E_INPUT: cannot read {root}/encoding/{NAMED}.vast: "),
            1,
        ),
    );
    fs::File::create(s.0.join(format!("size/{HOSTILE}.vast")))
        .unwrap()
        .set_len(16 * 1024 * 1024 + 1)
        .unwrap();
    cases.rejected(
        "size",
        &manifest_mode(&s, "size"),
        "E_LIMIT",
        whole(format!(
            "E_LIMIT: input {root}/size/{NAMED}.vast exceeds the 16 MiB file or 64 MiB compilation input budget\n"
        )),
    );
    s.write(
        &format!("overwrite/{HOSTILE}.vast"),
        "fn main() -> Int { 0 }",
    );
    let output = bounded(
        cli()
            .current_dir(&s.0)
            .args(["build", "--manifest-path", "overwrite/Vastitas.toml", "-o"])
            .arg(format!("overwrite/{HOSTILE}.vast"))
            .env("VASTITAS_KERNEL", s.0.join("absent backend")),
    );
    cases.rejected(
        "overwrite",
        &output,
        "E_OUTPUT",
        whole(format!(
            "E_OUTPUT: output would overwrite input file {root}/overwrite/{NAMED}.vast\n"
        )),
    );
    cases.finish();
}

/// The output of a command whose backend is a script that the test wrote. A
/// child that another test spawned while the script was written holds it
/// open for writing until its exec, and the script cannot start before that.
fn settled(mut command: impl FnMut() -> Output) -> Output {
    loop {
        let output = command();
        if !String::from_utf8_lossy(&output.stderr).contains("Text file busy") {
            return output;
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

/// The toolchain that this compiler pins.
const PINNED: &str = include_str!("../lean-kernel/lean-toolchain");

/// The compiler shows a path from the command line or from the environment
/// like a path that a package chose (#718): the same file name reaches it
/// through a shell glob. A native build shows the names that it reads from
/// the selected kernel root and from the generated program the same way.
#[test]
fn command_line_and_environment_paths_carry_no_terminal_controls() {
    let s = Scratch::empty("argument controls");
    let root = canonical(&s);
    // A path from the environment is printed as it was given.
    let given = s.0.to_str().unwrap().to_string();
    let mut cases = Cases::default();
    let run = |arguments: &[&str]| {
        bounded(
            cli()
                .current_dir(&s.0)
                .args(arguments)
                .env("VASTITAS_KERNEL", s.0.join("absent backend")),
        )
    };
    const ABSENT: &str = "No such file or directory (os error 2)";
    let source = format!("{HOSTILE}.vast");
    s.write(&source, "fn main() -> Int { 0 } }");
    s.write("main.vast", "fn main() -> Int { 0 }");

    // Inputs of flat mode.
    cases.rejected(
        "input prefix",
        &run(&["check", &source]),
        "E_PARSE",
        start(format!("{NAMED}.vast:1:24: E_PARSE: "), 1),
    );
    cases.rejected(
        "input absent",
        &run(&["check", &format!("absent {source}")]),
        "E_INPUT",
        whole(format!(
            "E_INPUT: cannot read absent {NAMED}.vast: {ABSENT}\n"
        )),
    );
    cases.rejected(
        "input extension",
        &run(&["check", HOSTILE]),
        "E_INPUT",
        whole(format!(
            "E_INPUT: source filename must have the .vast extension: {NAMED}\n"
        )),
    );
    cases.rejected(
        "input twice",
        &run(&["check", &source, "--lib", &source]),
        "E_INPUT",
        whole(format!(
            "E_INPUT: source file supplied more than once: {NAMED}.vast\n"
        )),
    );
    let directory = format!("directory {source}");
    fs::create_dir(s.0.join(&directory)).unwrap();
    cases.rejected(
        "input directory",
        &run(&["check", &directory]),
        "E_INPUT",
        whole(format!(
            "E_INPUT: input must be a regular file: directory {NAMED}.vast\n"
        )),
    );

    // Outputs.
    cases.rejected(
        "output directory",
        &run(&["build", "main.vast", "-o", &directory]),
        "E_OUTPUT",
        whole(format!(
            "E_OUTPUT: output must name a regular file: directory {NAMED}.vast\n"
        )),
    );
    cases.rejected(
        "output parent absent",
        &run(&["build", "main.vast", "-o", &format!("{HOSTILE}/out")]),
        "E_OUTPUT",
        whole(format!(
            "E_OUTPUT: cannot inspect parent {NAMED}: {ABSENT}\n"
        )),
    );
    cases.rejected(
        "output parent file",
        &run(&["build", "main.vast", "-o", &format!("{source}/out")]),
        "E_OUTPUT",
        whole(format!(
            "E_OUTPUT: parent is not a directory: {NAMED}.vast\n"
        )),
    );
    cases.rejected(
        "output input",
        &run(&["build", &source, "-o", &source]),
        "E_OUTPUT",
        whole(format!(
            "E_OUTPUT: output would overwrite input file {NAMED}.vast\n"
        )),
    );
    // A name longer than a file name may be: an error other than a missing file.
    let long = format!("{HOSTILE}{}", "a".repeat(300));
    cases.rejected(
        "output long",
        &run(&["build", "main.vast", "-o", &long]),
        "E_OUTPUT",
        start(format!("E_OUTPUT: cannot inspect {NAMED}aaa"), 1),
    );
    let locked = format!("locked {HOSTILE}");
    fs::create_dir(s.0.join(&locked)).unwrap();
    fs::set_permissions(s.0.join(&locked), fs::Permissions::from_mode(0o555)).unwrap();
    let output = run(&["build", "main.vast", "-o", &format!("{locked}/out")]);
    fs::set_permissions(s.0.join(&locked), fs::Permissions::from_mode(0o755)).unwrap();
    cases.rejected(
        "output locked",
        &output,
        "E_OUTPUT",
        whole(format!(
            "E_OUTPUT: cannot write to output directory locked {NAMED}: Permission denied (os error 13)\n"
        )),
    );

    // The kernel that the environment selects.
    let kernel_root = s.0.join(format!("root {HOSTILE}"));
    let with_root = || {
        bounded(
            cli()
                .current_dir(&s.0)
                .args(["check", "main.vast"])
                .env_remove("VASTITAS_KERNEL")
                .env("VASTITAS_KERNEL_ROOT", &kernel_root),
        )
    };
    cases.rejected(
        "kernel root absent",
        &with_root(),
        "E_BACKEND",
        whole(format!(
            "E_BACKEND: cannot locate {given}/root {NAMED}: {ABSENT}\n"
        )),
    );
    fs::create_dir(&kernel_root).unwrap();
    cases.rejected(
        "kernel not built",
        &with_root(),
        "E_BACKEND",
        whole(format!(
            "E_BACKEND: kernel executable {root}/root {NAMED}/.lake/build/bin/vastitas-kernel is not built\n\
             Build it with: lake -d {root}/root {NAMED} build vastitas-kernel\n"
        )),
    );
    let with_kernel = |kernel: &std::path::Path| {
        bounded(
            cli()
                .current_dir(&s.0)
                .args(["check", "main.vast"])
                .env("VASTITAS_KERNEL", kernel),
        )
    };
    cases.rejected(
        "kernel absent",
        &with_kernel(&s.0.join(format!("kernel {HOSTILE}"))),
        "E_BACKEND",
        start(
            format!("E_BACKEND: cannot start {given}/kernel {NAMED}: {ABSENT}\n"),
            2,
        ),
    );
    // A backend that reports no build identity.
    let backend = s.0.join(format!("backend {HOSTILE}"));
    fs::write(
        &backend,
        "#!/bin/sh\ncat >/dev/null\necho '{\"version\":2,\"ok\":true}'\n",
    )
    .unwrap();
    fs::set_permissions(&backend, fs::Permissions::from_mode(0o755)).unwrap();
    let output = settled(|| with_kernel(&backend));
    cases.rejected(
        "kernel identity",
        &output,
        "E_BACKEND",
        start(
            format!("E_BACKEND: incompatible kernel {given}/backend {NAMED}: "),
            3,
        ),
    );

    // The kernel root of a native build, with the built kernel as the backend.
    let build = || {
        bounded(
            cli()
                .current_dir(&s.0)
                .args(["build", "main.vast", "-o", "program"])
                .env("VASTITAS_KERNEL", common::kernel_path())
                .env("VASTITAS_KERNEL_ROOT", &kernel_root),
        )
    };
    let toolchain = format!("{root}/root {NAMED}/lean-toolchain");
    cases.rejected(
        "toolchain absent",
        &build(),
        "E_BUILD",
        whole(format!("E_BUILD: cannot read {toolchain}: {ABSENT}\n")),
    );
    fs::write(kernel_root.join("lean-toolchain"), "\n").unwrap();
    cases.rejected(
        "toolchain empty",
        &build(),
        "E_BUILD",
        whole(format!("E_BUILD: empty toolchain in {toolchain}\n")),
    );
    // The pin is text of a file of the root.
    fs::write(kernel_root.join("lean-toolchain"), format!("{HOSTILE}\n")).unwrap();
    cases.rejected(
        "toolchain other",
        &build(),
        "E_BUILD",
        start(
            format!("E_BUILD: kernel root {root}/root {NAMED} pins {NAMED}, "),
            3,
        )
        .with(format!(
            ": lake -d {root}/root {NAMED} build vastitas-kernel\n"
        )),
    );

    // The runtime inputs of the root, which a native build compares with the
    // ones of this compiler. A root with the pin alone has none of them.
    fs::write(kernel_root.join("lean-toolchain"), PINNED).unwrap();
    let differing =
        format!("E_BUILD: kernel root {root}/root {NAMED} provides kernel runtime inputs ");
    let listed = format!("\nnote: differing inputs in {root}/root {NAMED}: ");
    cases.rejected(
        "runtime inputs absent",
        &build(),
        "E_BUILD",
        start(differing.as_str(), 4).with(listed.as_str()),
    );
    // With the inputs of this compiler and one more: a module that a runtime
    // source imports, whose file the root holds. The name of a module holds
    // no white space, so it leaves out the line feed and the tab.
    const MODULE: &str = "x\u{1b}[2J\u{7}\u{9b}2J\u{202e}";
    const MODULE_NAMED: &str = "x<U+001B>[2J<U+0007><U+009B>2J<U+202E>";
    common::copy_runtime_inputs(&kernel_root, false, false);
    let runtime = kernel_root.join("VastitasKernel/IndexedRuntime.lean");
    let source = fs::read_to_string(&runtime).unwrap();
    fs::write(
        &runtime,
        format!("import VastitasKernel.{MODULE}\n{source}"),
    )
    .unwrap();
    fs::write(
        kernel_root.join(format!("VastitasKernel/{MODULE}.lean")),
        "",
    )
    .unwrap();
    cases.rejected(
        "runtime input name",
        &build(),
        "E_BUILD",
        start(differing.as_str(), 4).with(format!(
            "{listed}VastitasKernel/IndexedRuntime.lean (changed), VastitasKernel/{MODULE_NAMED}.lean (unexpected)\n"
        )),
    );
    // An input that cannot be read, where the user may not read every file.
    // SAFETY: geteuid has no preconditions and cannot fail.
    if unsafe { nix::libc::geteuid() } != 0 {
        fs::set_permissions(&runtime, fs::Permissions::from_mode(0o000)).unwrap();
        let output = build();
        fs::set_permissions(&runtime, fs::Permissions::from_mode(0o644)).unwrap();
        cases.rejected(
            "runtime input unreadable",
            &output,
            "E_BUILD",
            whole(format!(
                "E_BUILD: cannot read the kernel runtime inputs in {root}/root {NAMED}: Permission denied (os error 13)\n"
            )),
        );
    }
    // A backend whose generated program imports a module under such a name.
    // The driver refuses the import ahead of the runtime inputs.
    let identity: serde_json::Value = serde_json::from_str(&common::kernel_identity()).unwrap();
    let response = serde_json::json!({
        "version": 2,
        "ok": true,
        "kernel": identity,
        "lean_source": format!("import {MODULE}\ndef main : IO Unit := pure ()\n"),
    });
    s.write("response.json", &response.to_string());
    let importing = s.0.join("importing backend");
    fs::write(
        &importing,
        "#!/bin/sh\ncat >/dev/null\ncat \"$(dirname \"$0\")/response.json\"\n",
    )
    .unwrap();
    fs::set_permissions(&importing, fs::Permissions::from_mode(0o755)).unwrap();
    let output = settled(|| {
        bounded(
            cli()
                .current_dir(&s.0)
                .args(["build", "main.vast", "-o", "program"])
                .env("VASTITAS_KERNEL", &importing)
                .env("VASTITAS_KERNEL_ROOT", &kernel_root),
        )
    });
    cases.rejected(
        "generated import",
        &output,
        "E_PROTOCOL",
        whole(format!(
            "E_PROTOCOL: the generated program imports {MODULE_NAMED}, which is not a runtime module that this compiler verifies for this build\n"
        )),
    );
    cases.finish();
}

/// A manifest names its package with any string, and a kernel diagnostic
/// names a declaration by the path that starts with that name (#718). The
/// driver names the control characters of the message like those of the path
/// in front of it.
#[test]
fn package_names_in_kernel_diagnostics_carry_no_terminal_controls() {
    let s = Scratch::empty("kernel controls");
    let root = canonical(&s);
    let mut cases = Cases::default();
    // A hostile file name with a plain package name, and the reverse: the
    // prefix of a kernel diagnostic, and its message.
    for (name, package, file, spelled) in [
        (
            "path",
            "probe",
            format!("{HOSTILE}.vast"),
            format!("{SPELLED}.vast"),
        ),
        (
            "message",
            SPELLED,
            "main.vast".to_string(),
            "main.vast".to_string(),
        ),
    ] {
        s.write(
            &format!("{name}/Vastitas.toml"),
            &format!(
                "[package]\nname = \"{package}\"\nversion = \"0.1.0\"\nroot = \"{spelled}\"\n"
            ),
        );
        s.write(
            &format!("{name}/{file}"),
            "fn a() -> Int { b() }\nfn b() -> Int { a() }\nfn main() -> Int { a() }",
        );
    }
    let check = |name: &str| {
        bounded(
            cli()
                .current_dir(&s.0)
                .args(["check", "--manifest-path"])
                .arg(format!("{name}/Vastitas.toml")),
        )
    };
    cases.rejected(
        "path",
        &check("path"),
        "E_RECURSION",
        start(format!("{root}/path/{NAMED}.vast:1:1: E_RECURSION: "), 1).with("`probe::a`"),
    );
    cases.rejected(
        "message",
        &check("message"),
        "E_RECURSION",
        start(format!("{root}/message/main.vast:1:1: E_RECURSION: "), 1)
            .with(format!("`{NAMED}::a`")),
    );
    cases.finish();

    // Diagnostics alone name the characters. The request to the kernel
    // carries the name of a package and the location of a manifest as they
    // are.
    s.write(
        "wire/Vastitas.toml",
        &format!(
            "[package]\nname = \"{SPELLED}\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n[dependencies]\ndep = {{ path = \"{SPELLED}\" }}\n"
        ),
    );
    s.write("wire/main.vast", "fn main() -> Int { 0 }");
    s.write(
        &format!("wire/{HOSTILE}/Vastitas.toml"),
        "[package]\nname = \"dep\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n",
    );
    s.write(&format!("wire/{HOSTILE}/main.vast"), "");
    let wire = common::captured_wire(
        cli()
            .current_dir(&s.0)
            .args(["check", "--manifest-path", "wire/Vastitas.toml"]),
        3,
    );
    let packages = wire["packages"].as_array().unwrap();
    let location = format!("{root}/wire/{HOSTILE}/Vastitas.toml");
    assert!(
        packages.iter().any(|package| package["name"] == HOSTILE),
        "{wire}"
    );
    assert!(
        packages.iter().any(|package| package["source"] == location),
        "{wire}"
    );
}

/// The line that reports a checked input on stdout shows its path like a
/// diagnostic does (#718).
#[test]
fn status_lines_carry_no_terminal_controls() {
    let s = Scratch::empty("status controls");
    let mut cases = Cases::default();
    let source = format!("{HOSTILE}.vast");
    s.write(&source, "fn main() -> Int { 0 }");
    cases.accepted(
        "checked",
        &bounded(cli().current_dir(&s.0).args(["check", &source])),
        whole(format!("checked {NAMED}.vast\n")),
    );
    cases.finish();

    // The request to the kernel names the file as it is.
    let wire = common::captured_wire(cli().current_dir(&s.0).args(["check", &source]), 2);
    assert_eq!(wire["file"], source);
}
