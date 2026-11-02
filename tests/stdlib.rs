//! Standard-library inclusion is source composition, with independent checking.
mod common;
use common::{Scratch, cli, success};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

impl Scratch {
    fn new() -> Self {
        Self::empty("stdlib")
    }
}

fn library(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("stdlib/src/arithmetic")
        .join(name)
}

fn failure(output: &Output, expected: &str) -> String {
    assert!(
        !output.status.success(),
        "unexpected successful compilation"
    );
    let error = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(error.contains(expected), "expected {expected:?}: {error}");
    error
}

#[test]
fn generated_package_preserves_comment_boundaries_in_native_programs() {
    let scratch = Scratch::new();
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    fs::create_dir_all(scratch.0.join("scripts")).unwrap();
    fs::copy(
        root.join("scripts/build_stdlib_package.py"),
        scratch.0.join("scripts/build_stdlib_package.py"),
    )
    .unwrap();
    let sources = scratch.0.join("stdlib/src/arithmetic");
    fs::create_dir_all(&sources).unwrap();
    for name in ["int", "nat", "generic"] {
        fs::copy(
            library(&format!("{name}.vast")),
            sources.join(format!("{name}.vast")),
        )
        .unwrap();
    }
    let original = fs::read_to_string(sources.join("int.vast")).unwrap();
    // These separators are line boundaries to Python. The generator must keep
    // their bytes so that the lexer rejects them instead of exposing code.
    let comments = [
        '\r', '\u{b}', '\u{c}', '\u{1c}', '\u{1d}', '\u{1e}', '\u{85}', '\u{2028}', '\u{2029}',
    ]
    .iter()
    .map(|separator| format!("    // ignored{separator} + 100\n"))
    .collect::<String>();
    let changed = original.replacen("left + right", &format!("left\n{comments}    + right"), 1);
    assert_ne!(changed, original);
    fs::write(sources.join("int.vast"), changed).unwrap();
    fs::write(
        scratch.0.join("stdlib/Vastitas.toml"),
        format!("[package]\nname='stdlib'\nversion='0.1.0'\nroot='target/package/lib.vast'\n[dependencies]\ngeometry_library={{path='{}'}}\n", root.join("stdlib/src/geometry").display()),
    )
    .unwrap();
    scratch.write("Vastitas.toml", "[package]\nname='app'\nversion='0.1.0'\nroot='package.vast'\n[dependencies]\nstd={path='stdlib'}\n");
    scratch.write("flat.vast", "fn main() -> Int { add(2, 3) }");
    scratch.write(
        "package.vast",
        "use std::arithmetic::generic::add;\nfn main() -> Int { add(2, 3) }",
    );
    for args in [vec![], vec!["--check"]] {
        success(
            &Command::new("python3")
                .arg(scratch.0.join("scripts/build_stdlib_package.py"))
                .args(args)
                .output()
                .unwrap(),
        );
    }
    let generated = fs::read_to_string(
        scratch
            .0
            .join("stdlib/target/package/arithmetic/integers.vast"),
    )
    .unwrap();
    assert!(generated.contains(&comments));
    for args in [
        vec!["flat.vast", "--lib"],
        vec!["--manifest-path", "Vastitas.toml"],
    ] {
        let mut command = cli();
        command.current_dir(&scratch.0).arg("check").args(&args);
        if args[0] == "flat.vast" {
            command.arg(sources.join("int.vast"));
        }
        failure(
            &command.output().unwrap(),
            "E_LEX: unsupported line separator",
        );
    }
    // CRLF and ordinary Unicode comment text remain supported in both forms.
    fs::write(
        sources.join("int.vast"),
        original.replacen(
            "left + right",
            "left\r\n    // 日本語 + 100\r\n    + right",
            1,
        ),
    )
    .unwrap();
    success(
        &Command::new("python3")
            .arg(scratch.0.join("scripts/build_stdlib_package.py"))
            .output()
            .unwrap(),
    );
    for package in [false, true] {
        for mode in ["check", "build"] {
            let mut command = cli();
            command.current_dir(&scratch.0).arg(mode);
            if package {
                command.args(["--manifest-path", "Vastitas.toml"]);
            } else {
                command.arg("flat.vast");
                for name in ["int", "nat", "generic"] {
                    command
                        .arg("--lib")
                        .arg(sources.join(format!("{name}.vast")));
                }
            }
            if mode == "build" {
                command.args(["-o", "program"]);
            }
            success(&command.output().unwrap());
            if mode == "build" {
                let output = Command::new(scratch.0.join("program")).output().unwrap();
                success(&output);
                assert_eq!(output.stdout, b"5\n");
            }
        }
    }
}

#[test]
fn native_standard_arithmetic_handles_integer_and_natural_boundaries() {
    let scratch = Scratch::new();
    let source = scratch.write(
        "arithmetic app.vast",
        r#"
fn main() -> Int {
    let negative: Int = -123456789012345678901234567890;
    let integers_ok =
        int_abs(negative) == 123456789012345678901234567890 &&
        int_neg(negative) == 123456789012345678901234567890 &&
        int_abs(0) == 0 && int_neg(0) == 0 && int_abs(17) == 17 &&
        int_add(negative, 123456789012345678901234567890) == 0 &&
        int_sub(2, 5) == -3 && int_mul(-7, 6) == -42 &&
        int_mul(negative, 0) == 0 &&
        int_min(-4, 9) == -4 && int_min(9, -4) == -4 &&
        int_max(-4, 9) == 9 && int_max(9, -4) == 9 &&
        int_min(-4, -4) == -4 && int_max(0, 0) == 0;
    let naturals_ok =
        nat_add(20, 22) == 42 && nat_add(0, 0) == 0 &&
        nat_sub(2, 5) == 0 && nat_sub(5, 2) == 3 &&
        nat_sub(0, 0) == 0 && nat_sub(5, 5) == 0 &&
        nat_mul(7, 6) == 42 && nat_mul(123456789012345678901234567890, 0) == 0 &&
        nat_min(2, 5) == 2 && nat_min(5, 2) == 2 && nat_min(3, 3) == 3 &&
        nat_max(2, 5) == 5 && nat_max(5, 2) == 5 && nat_max(0, 0) == 0;
    if integers_ok && naturals_ok { int_add(40, 2) } else { -1 }
}
"#,
    );
    let result = cli()
        .arg("check")
        .arg("--lib")
        .arg(library("nat.vast"))
        .arg(&source)
        .arg("--lib")
        .arg(library("int.vast"))
        .output()
        .unwrap();
    success(&result);

    let output = scratch.0.join("arithmetic program");
    let result = cli()
        .arg("build")
        .arg("--lib")
        .arg(library("int.vast"))
        .arg("-o")
        .arg(&output)
        .arg(&source)
        .arg("--lib")
        .arg(library("nat.vast"))
        .output()
        .unwrap();
    success(&result);
    let result = Command::new(&output).output().unwrap();
    success(&result);
    assert_eq!(String::from_utf8(result.stdout).unwrap(), "42\n");
}

#[test]
fn libraries_are_explicit_and_individually_checkable() {
    for filename in ["int.vast", "nat.vast"] {
        success(&cli().arg("check").arg(library(filename)).output().unwrap());
    }
    let scratch = Scratch::new();
    let source = scratch.write("main.vast", "fn main() -> Int { int_add(20, 22) }");
    let result = cli().arg("check").arg(&source).output().unwrap();
    failure(&result, "int_add");
    success(
        &cli()
            .arg("check")
            .arg(source)
            .arg("--lib")
            .arg(library("int.vast"))
            .output()
            .unwrap(),
    );
}

#[test]
fn repeated_files_and_conflicting_definitions_are_rejected() {
    let scratch = Scratch::new();
    let source = scratch.write("main.vast", "fn main() -> Int { 0 }");
    let alias = library("../arithmetic/int.vast");
    let repeated = cli()
        .arg("check")
        .arg(&source)
        .arg("--lib")
        .arg(library("int.vast"))
        .arg("--lib")
        .arg(alias)
        .output()
        .unwrap();
    failure(&repeated, "E_INPUT");

    let first = scratch.write("first.vast", "fn repeated() -> Int { 1 }");
    let second = scratch.write("second.vast", "fn repeated() -> Int { 2 }");
    let result = cli()
        .arg("check")
        .arg(source)
        .arg("--lib")
        .arg(first)
        .arg("--lib")
        .arg(second)
        .output()
        .unwrap();
    failure(&result, "E_DUPLICATE");
}

#[test]
fn library_inputs_must_exist_and_have_vast_extension() {
    let scratch = Scratch::new();
    let source = scratch.write("main.vast", "fn main() -> Int { 0 }");
    let wrong_extension = scratch.write("library.txt", "fn helper() -> Int { 0 }");
    for library in [scratch.0.join("missing.vast"), wrong_extension] {
        let result = cli()
            .arg("check")
            .arg(&source)
            .arg("--lib")
            .arg(&library)
            .output()
            .unwrap();
        failure(&result, "E_INPUT");
    }
}

#[test]
fn library_syntax_and_type_diagnostics_retain_their_own_file_and_line() {
    let scratch = Scratch::new();
    let source = scratch.write(
        "main.vast",
        "// application\n\n\n\n\nfn main() -> Int { helper() }\n",
    );
    for (name, body) in [
        (
            "syntax.vast",
            "// library\nfn helper() -> Int {\n    @\n}\n",
        ),
        (
            "types.vast",
            "// library\nfn helper() -> Int {\n    true\n}\n",
        ),
    ] {
        let library = scratch.write(name, body);
        let result = cli()
            .arg("check")
            .arg(&source)
            .arg("--lib")
            .arg(&library)
            .output()
            .unwrap();
        let error = failure(&result, &format!("{}:3:", library.display()));
        assert!(
            !error.starts_with(&format!("{}:", source.display())),
            "library error mislabeled as application error: {error}"
        );
    }
}

#[test]
fn library_cannot_supply_the_application_entrypoint() {
    let scratch = Scratch::new();
    let source = scratch.write("application.vast", "fn helper() -> Int { 0 }");
    let library = scratch.write("entrypoint.vast", "fn main() -> Int { helper() }");
    let result = cli()
        .arg("check")
        .arg(source)
        .arg("--lib")
        .arg(library)
        .output()
        .unwrap();
    failure(&result, "E_LIBRARY");
}

#[test]
fn missing_flag_values_and_duplicate_outputs_are_usage_errors() {
    let scratch = Scratch::new();
    let source = scratch.write("main.vast", "fn main() -> Int { 0 }");
    let output = scratch.0.join("program");
    for tail in [vec!["--lib"], vec!["--lib", "-o"], vec!["-o"]] {
        let result = cli().arg("build").arg(&source).args(tail).output().unwrap();
        failure(&result, "E_USAGE");
    }
    let result = cli()
        .arg("build")
        .arg(source)
        .arg("-o")
        .arg(&output)
        .arg("-o")
        .arg(output)
        .output()
        .unwrap();
    failure(&result, "E_USAGE");
}

#[test]
fn invalid_library_does_not_overwrite_existing_native_artifact() {
    let scratch = Scratch::new();
    let source = scratch.write("main.vast", "fn main() -> Int { 42 }");
    let library = scratch.write("invalid.vast", "fn invalid() -> Int { false }");
    let output = scratch.write("program", "previous artifact");
    let result = cli()
        .arg("build")
        .arg(source)
        .arg("--lib")
        .arg(library)
        .arg("-o")
        .arg(&output)
        .output()
        .unwrap();
    failure(&result, "E_TYPE");
    assert_eq!(fs::read(output).unwrap(), b"previous artifact");
}

#[test]
fn source_files_cannot_complete_each_others_syntax() {
    let scratch = Scratch::new();
    let source = scratch.write("main.vast", "fn main() -> Int { partial() }");
    let first = scratch.write("first.vast", "fn partial() -> Int {");
    let second = scratch.write("second.vast", "42 }");
    let result = cli()
        .arg("check")
        .arg(source)
        .arg("--lib")
        .arg(&first)
        .arg("--lib")
        .arg(second)
        .output()
        .unwrap();
    failure(&result, &format!("{}:", first.display()));
}
