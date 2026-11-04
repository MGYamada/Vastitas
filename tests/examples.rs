//! Documented examples run with the commands their documentation gives and
//! print the documented output (docs/development/documentation.md, step 3).
//! Examples that other tests already exercise end to end are not repeated.
mod common;
use common::{Scratch, cli, root, success};
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

// docs/packages.md: `demo` builds against the `arithmetic` library package,
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

// docs/packages.md: edit borrowing.
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

// docs/packages.md: edit authority.
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
