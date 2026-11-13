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

/// The build options of a numerical package in the numerical CI jobs: the
/// pinned OpenBLAS prefix and the native compiler. The compiler is the one
/// that the job names, or `default_cc` where the job names none.
fn numerical_build_options(default_cc: Option<&str>) -> Vec<String> {
    let prefix = std::env::var("VASTITAS_TEST_OPENBLAS_PREFIX").expect("OpenBLAS prefix");
    let mut options = vec!["--openblas-prefix".to_owned(), prefix];
    let cc = std::env::var("VASTITAS_TEST_NATIVE_CC")
        .ok()
        .or_else(|| default_cc.map(str::to_owned));
    if let Some(cc) = cc {
        options.extend(["--native-cc".to_owned(), cc]);
    }
    options
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
    ("examples/book/programs/flat-library.vast", &[INT], "42"),
    ("examples/book/functions/calls.vast", &[], "42"),
    (
        "examples/book/expressions/unbounded-integers.vast",
        &[],
        "15241578753238836750495351562536198787501905199875019052101",
    ),
    (
        "examples/book/expressions/natural-subtraction.vast",
        &[],
        "42",
    ),
    ("examples/book/types/pair-result.vast", &[], "42"),
    ("examples/book/statements/bindings.vast", &[], "42"),
    ("examples/book/expressions/operators.vast", &[], "42"),
    ("examples/book/expressions/sign.vast", &[], "42"),
    ("examples/book/lexical-structure/comment.vast", &[], "42"),
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
    ("examples/book/geometric-types/objects.vast", &[], "42"),
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
    ("examples/book/dispatch/methods.vast", &[], "42"),
    ("examples/book/dispatch/selectors.vast", &[], "42"),
    ("examples/book/dispatch/capabilities.vast", &[], "42"),
    ("examples/functions.vast", &[], "42"),
    ("examples/book/function-values/signatures.vast", &[], "42"),
    (
        "examples/book/function-values/explicit-parameter.vast",
        &[],
        "42",
    ),
    (
        "examples/book/function-values/static-targets.vast",
        &[],
        "42",
    ),
    ("examples/book/function-values/wrapper.vast", &[], "42"),
    ("examples/smooth.vast", &[], "2"),
];

/// The package programs that the book includes, by manifest, with the output
/// of the built executable. Packages that other tests in this file run are
/// not repeated.
const BOOK_PACKAGES: &[(&str, &str)] = &[
    ("examples/packages/hello/Vastitas.toml", "42"),
    ("examples/packages/dependency/ask/Vastitas.toml", "42"),
    ("examples/packages/stdlib-arithmetic/Vastitas.toml", "42"),
    ("examples/packages/inline-module/Vastitas.toml", "42"),
    ("examples/packages/module-paths/Vastitas.toml", "42"),
    ("examples/packages/module-names/Vastitas.toml", "42"),
    ("examples/packages/indexed/Vastitas.toml", "42"),
    ("examples/packages/indexed-objects/Vastitas.toml", "42"),
    ("examples/packages/geometry-compat/Vastitas.toml", "42"),
    ("examples/packages/stdlib-geometry/Vastitas.toml", "42"),
    ("examples/packages/affine-geometry/Vastitas.toml", "42"),
    ("examples/packages/stdlib-affine/Vastitas.toml", "42"),
    ("examples/packages/smooth-geometry/Vastitas.toml", "42"),
    ("examples/packages/frames/Vastitas.toml", "42"),
    ("examples/packages/physical-dimensions/Vastitas.toml", "42"),
    ("examples/packages/stdlib-frames/Vastitas.toml", "42"),
    ("examples/packages/storage/app/Vastitas.toml", "42"),
    ("examples/packages/vector-cells/Vastitas.toml", "42"),
    ("examples/packages/runtime-extents/Vastitas.toml", "42"),
    ("examples/packages/payloads/Vastitas.toml", "42"),
];

/// The package programs of the book whose build links OpenBLAS, by manifest,
/// with the output of the built executable.
/// `book_numerical_packages_print_their_output` builds and runs them where the
/// pinned OpenBLAS is available.
const BOOK_NUMERICAL_PACKAGES: &[(&str, &str)] = &[
    ("examples/packages/numerical/Vastitas.toml", "42"),
    ("examples/packages/linear-transforms/Vastitas.toml", "42"),
    ("examples/packages/finite_network/Vastitas.toml", "42"),
    ("examples/packages/gemm-coefficients/Vastitas.toml", "42"),
];

/// The packages of the book whose executable stops with a run-time
/// diagnostic, by directory. The package must build. Its executable must exit
/// with status 1, write nothing to standard output and write exactly the
/// lines of `<directory>.stderr` to standard error.
const BOOK_RUNTIME_FAILURES: &[&str] = &["examples/packages/failed-expect"];

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
    ("examples/reject/expressions/if-without-else.vast", &[]),
    ("examples/reject/types/pair-literals.vast", &[]),
    ("examples/reject/diagnostics/several-names.vast", &[]),
    ("examples/reject/limits/nested-parentheses.vast", &[]),
    ("examples/reject/limits/seven-parameters.vast", &[]),
    ("examples/reject/geometric-types/wrong-endpoint.vast", &[]),
    ("examples/reject/geometric-types/escaping-point.vast", &[]),
    ("examples/reject/dispatch/incomparable-methods.vast", &[]),
    ("examples/reject/dispatch/crossed-selectors.vast", &[]),
    ("examples/reject/dispatch/unused-key.vast", &[]),
    ("examples/reject/dispatch/literal-key.vast", &[]),
    ("examples/reject/abstract-types/value-type.vast", &[]),
    ("examples/reject/abstract-types/same-members.vast", &[]),
    ("examples/reject/abstract-types/contract-result.vast", &[]),
    ("examples/reject/function-values/capture.vast", &[]),
    ("examples/reject/function-values/generic-value.vast", &[]),
    ("examples/reject/function-values/two-targets.vast", &[]),
];

/// The rejected packages that the book includes from `examples/reject/packages/`,
/// by directory. `vastitas check --manifest-path <directory>/Vastitas.toml`,
/// run from the repository root, must fail and print exactly the lines of
/// `<directory>.stderr`, with the repository root removed from file names.
const BOOK_REJECTED_PACKAGES: &[&str] = &[
    "examples/reject/packages/private-function",
    "examples/reject/packages/import-collision",
    "examples/reject/packages/geometric-use",
    "examples/reject/packages/geometric-function",
    "examples/reject/packages/foreign-method",
    "examples/reject/packages/outside-region",
    "examples/reject/packages/private-dependency",
    "examples/reject/packages/entry-signature",
    "examples/reject/packages/unknown-manifest-key",
    "examples/reject/packages/uninitialized-read",
    "examples/reject/packages/moved-owner",
    "examples/reject/packages/overlapping-writers",
    "examples/reject/packages/inexact-payload",
    "examples/reject/packages/other-basis",
    "examples/reject/packages/other-space",
    "examples/reject/packages/missing-capability",
    "examples/reject/packages/lost-capability",
    "examples/reject/packages/other-witness",
    "examples/reject/packages/second-opening",
    "examples/reject/packages/copied-profile",
    "examples/reject/packages/smooth-parameter-object",
    "examples/reject/packages/smooth-coordinate-count",
    "examples/reject/packages/smooth-degree",
    "examples/reject/packages/smooth-target-coordinate",
    "examples/reject/packages/smooth-point-object",
    "examples/reject/packages/smooth-pairing-order",
    "examples/reject/packages/smooth-pullback-mode",
    "examples/reject/packages/smooth-asymmetric-metric",
    "examples/reject/packages/smooth-indefinite-metric",
    "examples/reject/packages/smooth-singular-metric",
    "examples/reject/packages/smooth-default-metric",
    "examples/reject/packages/smooth-seed-object",
    "examples/reject/packages/smooth-other-line",
    "examples/reject/packages/frame-constant-inverse",
    "examples/reject/packages/frame-missing-inverse",
    "examples/reject/packages/frame-encode-variance",
    "examples/reject/packages/frame-transition-objects",
    "examples/reject/packages/frame-apply-frame",
    "examples/reject/packages/frame-component-bound",
    "examples/reject/packages/dimension-length-time",
    "examples/reject/packages/dimension-reading-coordinate",
    "examples/reject/packages/dimension-scale-magnitude",
    "examples/reject/packages/dimension-gram-magnitude",
    "examples/reject/packages/dimension-declared-value",
    "examples/reject/packages/dimension-torque-scale",
    "examples/reject/packages/dimension-module-import",
    "examples/reject/packages/affine-off-chain",
    "examples/reject/packages/affine-missing-image",
    "examples/reject/packages/affine-relation",
    "examples/reject/packages/affine-selector",
    "examples/reject/packages/affine-not-inverse",
    "examples/reject/packages/affine-separate-bases",
    "examples/reject/packages/affine-square",
    "examples/reject/packages/affine-not-preimage",
    "examples/reject/packages/affine-other-object",
    "examples/reject/packages/callee-region",
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
    // The affine packages depend on the generated standard-library package.
    common::prepare_stdlib_package();
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

#[test]
fn book_runtime_failures_print_their_diagnostics() {
    for directory in BOOK_RUNTIME_FAILURES {
        let scratch = Scratch::empty("run-time failure");
        let program = scratch.0.join("program");
        let manifest = format!("{directory}/Vastitas.toml");
        let mut build = cli();
        build
            .current_dir(root())
            .args(["build", "--manifest-path", &manifest, "-o"])
            .arg(&program);
        success(&build.output().unwrap());
        let output = Command::new(&program).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some(1),
            "{directory} must stop when it runs"
        );
        assert!(output.stdout.is_empty(), "{directory}: no output on stdout");
        let expected = std::fs::read_to_string(root().join(format!("{directory}.stderr"))).unwrap();
        assert_eq!(
            String::from_utf8(output.stderr).unwrap(),
            expected,
            "{directory}"
        );
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
    for (manifest, _) in BOOK_PACKAGES.iter().chain(BOOK_NUMERICAL_PACKAGES) {
        assert!(root().join(manifest).is_file(), "{manifest}");
    }
    for directory in BOOK_RUNTIME_FAILURES {
        let manifest = format!("{directory}/Vastitas.toml");
        assert!(root().join(&manifest).is_file(), "{manifest}");
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

// docs/language/programs.md (Flat mode) and stdlib/README.md.
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

// docs/guide/creating-a-package.md: a library package has no entry point, so
// `check` accepts it and `build` reports the missing entry point.
#[test]
fn library_package_checks_and_does_not_build() {
    let manifest = "examples/packages/dependency/answers/Vastitas.toml";
    success(
        &cli()
            .current_dir(root())
            .args(["check", "--manifest-path", manifest])
            .output()
            .unwrap(),
    );
    let scratch = Scratch::empty("library package");
    let output = cli()
        .current_dir(root())
        .args(["build", "--manifest-path", manifest, "-o"])
        .arg(scratch.0.join("program"))
        .output()
        .unwrap();
    common::expect_code(&output, "E_MAIN");
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
    // As tests/runtime_shape_source.rs builds runtime shapes: with `cc` named.
    let options = numerical_build_options(Some("cc"));
    let options: Vec<&str> = options.iter().map(String::as_str).collect();
    documented_build(
        &[
            "--manifest-path",
            "examples/packages/runtime-shapes/Vastitas.toml",
        ],
        &options,
        "0",
    );
}

// docs/guide/numerical.md: the numerical packages of the book, built in place
// with the pinned OpenBLAS prefix. tests/numerical_source.rs builds and runs
// copies of their sources in the numerical CI jobs.
#[test]
#[ignore = "requires pinned sequential LP64 OpenBLAS"]
fn book_numerical_packages_print_their_output() {
    // As tests/numerical_source.rs builds the same sources.
    let options = numerical_build_options(None);
    let options: Vec<&str> = options.iter().map(String::as_str).collect();
    for (manifest, expected) in BOOK_NUMERICAL_PACKAGES {
        documented_build(&["--manifest-path", manifest], &options, expected);
    }
}
