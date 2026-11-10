//! Reject blocking/special inputs and bounded expansion before invoking Lean.
mod common;
use common::{Scratch, cli};
use nix::sys::stat::Mode;
use nix::unistd::mkfifo;
use std::fs;
use std::os::unix::fs::{FileTypeExt, MetadataExt, symlink};
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
