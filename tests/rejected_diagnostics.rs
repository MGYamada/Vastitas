//! The packages under `tests/emit_corpus/rejected/` pass the frontend and are
//! rejected by the kernel. This test runs `vastitas check` on each one with the
//! built kernel and pins the exit code, standard output and standard error
//! (code, message and notes) in `tests/fixtures/rejected/<package>.txt`. The
//! format is the `cli.txt` that `scripts/capture_emit.py` writes, with the
//! checkout root written as `<ROOT>`. A diagnostic change is intentional only
//! when the expectations are regenerated with
//! `VASTITAS_UPDATE_REJECTED_FIXTURES=1 cargo test --test rejected_diagnostics`
//! and their diff is reviewed.
mod common;
use common::{
    Scratch, assert_first_code, cli, diagnostic_codes, kernel_path, regenerate_fixture, root,
};
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

const CORPUS: &str = "tests/emit_corpus/rejected";
const EXPECTED: &str = "tests/fixtures/rejected";

/// The checkout root written as `<ROOT>`, as `normalize` in
/// `scripts/capture_emit.py` does. The driver reports canonical paths, so the
/// canonical root is replaced before the root as Cargo spells it.
fn normalize(bytes: &[u8]) -> String {
    let canonical = root().canonicalize().unwrap();
    String::from_utf8_lossy(bytes)
        .replace(canonical.to_str().unwrap(), "<ROOT>")
        .replace(root().to_str().unwrap(), "<ROOT>")
}

/// The names in `directory` of the entries that `keep` selects, sorted.
fn names(directory: &Path, keep: impl Fn(&Path) -> Option<String>) -> BTreeSet<String> {
    fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", directory.display()))
        .filter_map(|entry| keep(&entry.unwrap().path()))
        .collect()
}

#[test]
fn rejected_primitive_calls_keep_their_diagnostics() {
    assert!(
        kernel_path().is_file(),
        "Build backend first: lake -d lean-kernel build vastitas-kernel"
    );
    let regenerate = regenerate_fixture("VASTITAS_UPDATE_REJECTED_FIXTURES");
    let packages = names(&root().join(CORPUS), |path| {
        path.join("Vastitas.toml")
            .is_file()
            .then(|| path.file_name().unwrap().to_str().unwrap().to_owned())
    });
    assert!(!packages.is_empty(), "no package under {CORPUS}");
    let mut failures = Vec::new();
    for name in &packages {
        let manifest = root().join(CORPUS).join(name).join("Vastitas.toml");
        // The frontend accepts the package: with no executable at the
        // configured kernel path, `check` fails only when it starts the kernel.
        let absent = Scratch::empty("rejected backend");
        let output = cli()
            .args(["check", "--manifest-path"])
            .arg(&manifest)
            .env("VASTITAS_KERNEL", absent.0.join("no kernel"))
            .output()
            .unwrap();
        assert_first_code(&String::from_utf8_lossy(&output.stderr), "E_BACKEND");
        let output = cli()
            .args(["check", "--manifest-path"])
            .arg(&manifest)
            .env("VASTITAS_KERNEL", kernel_path())
            .output()
            .unwrap();
        let stderr = normalize(&output.stderr);
        assert!(
            !output.status.success() && !diagnostic_codes(&stderr).is_empty(),
            "{name}: the kernel must reject the package with a diagnostic\n{stderr}"
        );
        let code = output
            .status
            .code()
            .unwrap_or_else(|| panic!("{name}: check ended by a signal"));
        let actual = format!(
            "exit {code}\n--- stdout ---\n{}--- stderr ---\n{stderr}",
            normalize(&output.stdout)
        );
        let path = root().join(EXPECTED).join(format!("{name}.txt"));
        if regenerate {
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(&path, &actual).unwrap();
        }
        let expected = fs::read_to_string(&path).unwrap_or_else(|_| {
            panic!("{name}: regenerate the expectations as documented in this test")
        });
        if actual != expected {
            failures.push(format!(
                "{name}: `check` output differs from {EXPECTED}/{name}.txt\n\
                 expected:\n{expected}actual:\n{actual}"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // An expectation without a package would pin nothing.
    let expectations = names(&root().join(EXPECTED), |path| {
        (path.extension().and_then(|extension| extension.to_str()) == Some("txt"))
            .then(|| path.file_stem().unwrap().to_str().unwrap().to_owned())
    });
    assert_eq!(
        expectations, packages,
        "{EXPECTED} must hold one expectation for each package under {CORPUS}"
    );
}
