//! Documented examples run with the commands their documentation gives and
//! print the documented output (docs/development/documentation.md, step 3).
//! Examples that other tests already exercise end to end are not repeated.
mod common;
use common::{Scratch, cli, root, success};
use std::collections::BTreeSet;
use std::path::Path;
use std::process::Command;

const INT: &str = "stdlib/src/arithmetic/int.vast";
const NAT: &str = "stdlib/src/arithmetic/nat.vast";
const GENERIC: &str = "stdlib/src/arithmetic/generic.vast";

/// `check`, then `build` (with any build-only options) and run, with
/// repository-relative input arguments.
fn documented_build(inputs: &[&str], build_options: &[&str], expected: &str) {
    let scratch = Scratch::empty("documented example");
    let program = scratch.0.join("program");
    let mut check = cli();
    check.current_dir(root()).arg("check").args(inputs);
    success(&check.output().unwrap());
    let mut build = cli();
    build
        .current_dir(root())
        .arg("build")
        .args(inputs)
        .args(build_options)
        .arg("-o")
        .arg(&program);
    success(&build.output().unwrap());
    let output = Command::new(&program).output().unwrap();
    success(&output);
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        format!("{expected}\n")
    );
}

fn documented(inputs: &[&str], expected: &str) {
    documented_build(inputs, &[], expected);
}

/// The complete programs that the book includes, with their `--lib` inputs
/// and the output of the built executable. Every program under
/// `examples/book/` must be listed (docs/development/documentation.md,
/// Examples).
const BOOK_PROGRAMS: &[(&str, &[&str], &str)] = &[
    ("examples/book/programs/hello.vast", &[], "42"),
    ("examples/book/statements/bindings.vast", &[], "42"),
    ("examples/book/expressions/operators.vast", &[], "42"),
    (
        "examples/book/expressions/saturating-subtraction.vast",
        &[],
        "-42",
    ),
    ("examples/book/functions/function-values.vast", &[], "42"),
    (
        "examples/book/geometric-types/pointed-origin.vast",
        &[],
        "42",
    ),
    (
        "examples/arithmetic.vast",
        &[],
        "1234567890123456789012345678900",
    ),
    ("examples/pointed.vast", &[], "42"),
    ("examples/pairs.vast", &[], "42"),
    (
        "examples/dispatch-arithmetic.vast",
        &[INT, NAT, GENERIC],
        "42",
    ),
    ("examples/abstract-contracts.vast", &[], "42"),
    ("examples/functions.vast", &[], "42"),
    ("examples/smooth.vast", &[], "2"),
];

/// The package programs that the book includes, by manifest, with the output
/// of the built executable. Packages that other tests in this file run are
/// not repeated.
const BOOK_PACKAGES: &[(&str, &str)] = &[
    ("examples/packages/inline-module/Vastitas.toml", "42"),
    ("examples/packages/indexed/Vastitas.toml", "42"),
    ("examples/packages/stdlib-geometry/Vastitas.toml", "42"),
    ("examples/packages/storage/app/Vastitas.toml", "42"),
    ("examples/packages/vector-cells/Vastitas.toml", "42"),
];

/// The rejected programs that the book includes from `examples/reject/`, with
/// their `--lib` inputs. `vastitas check`, run from the repository root, must
/// fail and print exactly the lines of the program's sibling `.stderr` file.
/// Every program under `examples/reject/` must be listed.
const BOOK_REJECTIONS: &[(&str, &[&str])] = &[
    ("examples/reject/types/bool-result.vast", &[]),
    ("examples/reject/functions/mutual-recursion.vast", &[]),
    ("examples/reject/statements/nested-rebinding.vast", &[]),
    ("examples/reject/expressions/chained-comparison.vast", &[]),
    ("examples/reject/expressions/mixed-integers.vast", &[]),
    ("examples/reject/diagnostics/several-names.vast", &[]),
    ("examples/reject/limits/nested-parentheses.vast", &[]),
    ("examples/reject/limits/seven-parameters.vast", &[]),
    ("examples/reject/geometric-types/wrong-endpoint.vast", &[]),
    ("examples/reject/geometric-types/escaping-point.vast", &[]),
    ("examples/reject/dispatch/incomparable-methods.vast", &[]),
    ("examples/reject/function-values/capture.vast", &[]),
    ("examples/reject/function-values/two-targets.vast", &[]),
];

/// The rejected packages that the book includes from `examples/reject/packages/`,
/// by directory. `vastitas check --manifest-path <directory>/Vastitas.toml`,
/// run from the repository root, must fail and print exactly the lines of
/// `<directory>.stderr`, with the repository root removed from file names.
const BOOK_REJECTED_PACKAGES: &[&str] = &[
    "examples/reject/packages/private-function",
    "examples/reject/packages/entry-signature",
    "examples/reject/packages/unknown-manifest-key",
    "examples/reject/packages/uninitialized-read",
    "examples/reject/packages/other-basis",
    "examples/reject/packages/other-space",
];

fn with_libs<'a>(path: &'a str, libs: &[&'a str]) -> Vec<&'a str> {
    let mut inputs = vec![path];
    for lib in libs {
        inputs.extend(["--lib", lib]);
    }
    inputs
}

#[test]
fn book_programs_print_their_output() {
    // stdlib-geometry depends on the generated standard-library package.
    common::prepare_stdlib_package();
    for (path, libs, expected) in BOOK_PROGRAMS {
        documented(&with_libs(path, libs), expected);
    }
    for (manifest, expected) in BOOK_PACKAGES {
        documented(&["--manifest-path", manifest], expected);
    }
}

#[test]
fn book_rejections_print_their_diagnostics() {
    for (path, libs) in BOOK_REJECTIONS {
        let output = cli()
            .current_dir(root())
            .arg("check")
            .args(with_libs(path, libs))
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{path} must be rejected");
        let expected = std::fs::read_to_string(root().join(path).with_extension("stderr")).unwrap();
        assert_eq!(
            String::from_utf8(output.stderr).unwrap(),
            expected,
            "{path}"
        );
        common::assert_source_names(&expected);
        assert!(output.stdout.is_empty(), "{path}: no output on stdout");
    }
}

#[test]
fn book_rejected_packages_print_their_diagnostics() {
    for directory in BOOK_REJECTED_PACKAGES {
        let manifest = format!("{directory}/Vastitas.toml");
        let output = cli()
            .current_dir(root())
            .args(["check", "--manifest-path", &manifest])
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(1),
            "{directory} must be rejected"
        );
        assert!(output.stdout.is_empty(), "{directory}: no output on stdout");
        // The driver prints canonical paths, so remove both spellings of the
        // root: a checkout reached through a symbolic link differs.
        let mut stderr = String::from_utf8(output.stderr).unwrap();
        for prefix in [root().to_path_buf(), root().canonicalize().unwrap()] {
            stderr = stderr.replace(&format!("{}/", prefix.display()), "");
        }
        let expected = std::fs::read_to_string(root().join(format!("{directory}.stderr"))).unwrap();
        assert_eq!(stderr, expected, "{directory}");
        common::assert_source_names(&expected);
    }
}

fn files_under(directory: &Path, found: &mut Vec<String>) {
    for entry in std::fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        // Hidden files, such as a desktop's folder metadata, are not examples.
        if path.file_name().unwrap().to_str().unwrap().starts_with('.') {
            continue;
        }
        if path.is_dir() {
            files_under(&path, found);
        } else {
            let relative = path.strip_prefix(root()).unwrap();
            found.push(relative.to_str().unwrap().replace('\\', "/"));
        }
    }
}

// The book's example directories hold only the listed programs and the
// expected diagnostics of the rejected ones, so no program goes untested.
#[test]
fn book_examples_are_registered() {
    let programs: BTreeSet<&str> = BOOK_PROGRAMS.iter().map(|(path, _, _)| *path).collect();
    let rejections: BTreeSet<&str> = BOOK_REJECTIONS.iter().map(|(path, _)| *path).collect();
    let mut expected = BTreeSet::new();
    for path in programs
        .iter()
        .filter(|path| path.starts_with("examples/book/"))
    {
        expected.insert(path.to_string());
    }
    for path in &rejections {
        assert!(path.starts_with("examples/reject/"), "{path}");
        expected.insert(path.to_string());
        expected.insert(path.replace(".vast", ".stderr"));
    }
    for directory in BOOK_REJECTED_PACKAGES {
        assert!(
            directory.starts_with("examples/reject/packages/"),
            "{directory}"
        );
        let mut files = Vec::new();
        files_under(&root().join(directory), &mut files);
        expected.extend(files);
        expected.insert(format!("{directory}.stderr"));
    }
    let mut found = Vec::new();
    files_under(&root().join("examples/book"), &mut found);
    files_under(&root().join("examples/reject"), &mut found);
    let found: BTreeSet<String> = found.into_iter().collect();
    assert_eq!(
        found, expected,
        "files under examples/book/ and examples/reject/"
    );
    for (path, _, _) in BOOK_PROGRAMS {
        assert!(root().join(path).is_file(), "{path}");
    }
    for (manifest, _) in BOOK_PACKAGES {
        assert!(root().join(manifest).is_file(), "{manifest}");
    }
}

// docs/stage1a.md: abstract selectors.
#[test]
fn abstract_selectors() {
    documented(&["examples/abstract-selectors.vast"], "42");
}

// stdlib/README.md: the flat example with the three explicit libraries.
#[test]
fn flat_promotion() {
    documented(
        &[
            "examples/promotion.vast",
            "--lib",
            INT,
            "--lib",
            NAT,
            "--lib",
            GENERIC,
        ],
        "42",
    );
}

// docs/guide/stdlib.md and stdlib/README.md.
#[test]
fn stdlib_arithmetic() {
    documented(
        &[
            "examples/stdlib-arithmetic.vast",
            "--lib",
            INT,
            "--lib",
            NAT,
        ],
        "42",
    );
}

// docs/packages.md (Commands): `demo` builds against the `arithmetic` library package,
// which has no entry point and is checked on its own.
#[test]
fn arithmetic_and_demo_packages() {
    success(
        &cli()
            .current_dir(root())
            .args([
                "check",
                "--manifest-path",
                "examples/packages/arithmetic/Vastitas.toml",
            ])
            .output()
            .unwrap(),
    );
    documented(
        &["--manifest-path", "examples/packages/demo/Vastitas.toml"],
        "42",
    );
}

// docs/language/edit-authority.md: grants, contributions and assemblies.
#[test]
fn edit_borrow_package() {
    documented(
        &[
            "--manifest-path",
            "examples/packages/edit-borrow/app/Vastitas.toml",
        ],
        "42",
    );
}

// docs/language/edit-authority.md: delegations and transfers.
#[test]
fn edit_authority_package() {
    documented(
        &[
            "--manifest-path",
            "examples/packages/edit-authority/app/Vastitas.toml",
        ],
        "44",
    );
}

// stdlib/README.md: package use after build_stdlib_package.py.
#[test]
fn promotion_package() {
    common::prepare_stdlib_package();
    documented(
        &[
            "--manifest-path",
            "examples/packages/promotion/Vastitas.toml",
        ],
        "42",
    );
}

// The Stage 3 acceptance program (#604), checked, built and run in place with
// the commands of its acceptance checklist. tests/smooth_differential.rs runs
// copies of it, mutated and tampered.
#[test]
fn smooth_differential_package() {
    documented(
        &[
            "--manifest-path",
            "examples/packages/smooth-differential/Vastitas.toml",
        ],
        "42",
    );
}

// stdlib/src/geometry/README.md: the smooth affine profile from the standard
// library, run in place. tests/stdlib_differential.rs runs copies of it,
// mutated.
#[test]
fn stdlib_differential_package() {
    common::prepare_stdlib_package();
    documented(
        &[
            "--manifest-path",
            "examples/packages/stdlib-differential/Vastitas.toml",
        ],
        "42",
    );
}

// docs/storage/resource-programs.md: the scalar-flow example.
#[test]
fn resource_values_package() {
    documented(
        &[
            "--manifest-path",
            "examples/packages/resource-values/Vastitas.toml",
        ],
        "42",
    );
}

// docs/storage/resource-programs.md: `check` needs no BLAS.
#[test]
fn runtime_shapes_package_checks_without_blas() {
    success(
        &cli()
            .current_dir(root())
            .args([
                "check",
                "--manifest-path",
                "examples/packages/runtime-shapes/Vastitas.toml",
            ])
            .output()
            .unwrap(),
    );
}

// The native build additionally requires the pinned OpenBLAS prefix. The
// program checks its GEMM results itself and prints 0.
#[test]
#[ignore = "requires pinned sequential LP64 OpenBLAS"]
fn runtime_shapes_package_runs_with_openblas() {
    let prefix = std::env::var("VASTITAS_TEST_OPENBLAS_PREFIX").expect("OpenBLAS prefix");
    let cc = std::env::var("VASTITAS_TEST_NATIVE_CC").unwrap_or_else(|_| "cc".into());
    documented_build(
        &[
            "--manifest-path",
            "examples/packages/runtime-shapes/Vastitas.toml",
        ],
        &["--openblas-prefix", &prefix, "--native-cc", &cc],
        "0",
    );
}
