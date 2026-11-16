//! The Stage 6 acceptance program (#841), `examples/packages/two-level/`, as
//! an application of copies of the standard library and of `nature`: it
//! checks, builds and shows the exact prediction of its model at each data
//! point; a changed calibration makes its comparison stale (C9), the std
//! code stays the same without its `nature` declarations, and the
//! comparison recorded again is accepted; and each mutation of a value that
//! `main` expects, of the verdict or of a measured value is caught.
mod common;
use common::{Run, Scratch, expect_code, kernel, root};

const EXAMPLE: &str = "examples/packages/two-level/src/main.vast";
const MANIFEST: &str = "[package]\nname = \"two_level\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n\n[dependencies]\nstd = { path = \"../stdlib\" }\nnature = { path = \"../nature\" }\n";
/// The fingerprint that the example records for its calibration.
const FINGERPRINT: &str = "fnv1a64:fd1f7edd812db49f";
/// The values that `main` expects, as it writes them, and the line that it
/// shows for each: the average Ω²/(2(Δ² + Ω²)) at Ω = 5/2, which is
/// 25/(8Δ² + 50), for Δ = 0, 1, 2, −1 and 5/2.
const EXPECTED: [(&str, &str); 5] = [
    ("reads(resonance, 1, 2)", "avg(at(0, 5)) = (1, 2)"),
    ("reads(one, 25, 58)", "avg(at(2, 5)) = (25, 58)"),
    ("reads(two, 25, 82)", "avg(at(4, 5)) = (25, 82)"),
    ("reads(minus_one, 25, 58)", "avg(at(-2, 5)) = (25, 58)"),
    ("reads(five_halves, 1, 4)", "avg(at(5, 5)) = (1, 4)"),
];

fn source() -> String {
    std::fs::read_to_string(root().join(EXAMPLE)).unwrap()
}

/// The application `main` in `app/`, with copies of the stdlib and of
/// `nature`, as in the repository.
fn app(main: &str) -> Scratch {
    let s = common::stdlib_app("two level", MANIFEST, main, &[]);
    s.copy_nature();
    s
}

fn check(s: &Scratch) -> std::process::Output {
    s.check_manifest("app/Vastitas.toml")
}

fn shown() -> Run {
    common::shows(&EXPECTED.map(|(_, line)| line))
}

/// The Lean that the kernel generates for the application.
fn generated(main: &str) -> String {
    generated_in(&app(main))
}

/// The Lean that the kernel generates for the application of `s`.
fn generated_in(s: &Scratch) -> String {
    let wire = s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    let emitted = kernel(wire, "emit");
    assert_eq!(emitted["ok"], true, "{emitted}");
    emitted["lean_source"].as_str().unwrap().to_owned()
}

/// The text from the line that begins with `start` through the next line
/// that ends with `;`: one declaration of the example.
fn declaration(source: &str, start: &str) -> String {
    let from = source.find(start).unwrap_or_else(|| panic!("no `{start}`"));
    let to = from + source[from..].find(";\n").unwrap() + 2;
    source[from..to].to_owned()
}

/// The fingerprint that `E_STALE` names as the current one.
fn current_fingerprint(stderr: &str) -> String {
    let marker = "its current fingerprint is `";
    let start = stderr.find(marker).unwrap_or_else(|| panic!("{stderr}")) + marker.len();
    let end = stderr[start..].find('`').unwrap() + start;
    stderr[start..end].to_owned()
}

#[test]
fn the_acceptance_program_checks_builds_and_shows_the_exact_predictions() {
    let main = source();
    assert!(main.contains(&format!("fingerprint = \"{FINGERPRINT}\"")));
    assert_eq!(app(&main).check_build_and_run("app/Vastitas.toml"), shown());
}

/// C9 end to end. A changed calibration makes the recorded comparison stale,
/// and the diagnostic names the current fingerprint. Without the comparison
/// the program is accepted, and the generated code is byte identical with
/// the example's and with that of the program without any `nature`
/// declaration: the model and the data change no std code. Recorded again
/// with the current fingerprint, the comparison is accepted.
#[test]
fn a_changed_calibration_is_stale_and_changes_no_std_code() {
    let main = source();
    let changed = common::checked_replace(
        &main,
        "measured(frac(5, 2), u = frac(1, 20))",
        "measured(frac(5, 2), u = frac(1, 25))",
    );
    let stderr = expect_code(&check(&app(&changed)), "E_STALE");
    let current = current_fingerprint(&stderr);
    assert_ne!(current, FINGERPRINT);
    assert!(
        stderr.contains(&format!(
            "the comparison `two_level::C` records the fingerprint `{FINGERPRINT}` of the calibration \
             `two_level::K`, but its current fingerprint is `{current}`"
        )),
        "{stderr}"
    );
    let comparison = declaration(&changed, "indexed comparison C");
    let without_comparison = common::checked_replace(&changed, &comparison, "");
    common::success(&check(&app(&without_comparison)));
    // The application without its nature declarations and imports.
    let mut std_only = main.clone();
    for start in [
        "indexed quantity Frequency",
        "indexed reading r",
        "indexed convention c",
        "indexed model M",
        "indexed calibration K",
        "indexed dataset D",
        "indexed comparison C",
    ] {
        let text = declaration(&std_only, start);
        std_only = common::checked_replace(&std_only, &text, "");
    }
    for import in [
        "use nature::dimension::Reading;\n",
        "use nature::dimension::T;\n",
        "use nature::model::Model;\n",
        "use nature::errorbar::Calibration;\n",
        "use nature::errorbar::Dataset;\n",
        "use nature::errorbar::Comparison;\n",
    ] {
        std_only = common::checked_replace(&std_only, import, "");
    }
    assert!(!std_only.contains("nature::"));
    let example = generated(&main);
    assert_eq!(generated(&without_comparison), example);
    assert_eq!(generated(&std_only), example);
    // Without the dependency on `nature` too.
    let alone = app(&std_only);
    alone.write(
        "app/Vastitas.toml",
        &common::checked_replace(MANIFEST, "nature = { path = \"../nature\" }\n", ""),
    );
    assert_eq!(generated_in(&alone), example);
    assert_eq!(
        app(&std_only).check_build_and_run("app/Vastitas.toml"),
        shown()
    );
    let recorded = common::checked_replace(
        &changed,
        &format!("fingerprint = \"{FINGERPRINT}\""),
        &format!("fingerprint = \"{current}\""),
    );
    assert_eq!(
        app(&recorded).check_build_and_run("app/Vastitas.toml"),
        shown()
    );
}

/// Each mutation is caught. A wrong expected value makes `main` exit with
/// status 1 after it shows the same lines. The recorded verdict
/// `inconsistent` is `E_ERRORBAR`. A measured value moved outside its
/// coverage interval makes the verdict `consistent` wrong (`E_ERRORBAR`) and
/// `inconsistent` right, under the same fingerprint, since the dataset is
/// not part of the calibration.
#[test]
fn each_mutation_of_an_expected_value_or_the_verdict_is_caught() {
    let main = source();
    let program = app(&main);
    let run = program.check_build_and_run("app/Vastitas.toml");
    assert_eq!(run, shown());
    for (check_text, _) in EXPECTED {
        let wrong = check_text.replacen(", ", ", 1 + ", 1);
        program.write(
            "app/main.vast",
            &common::checked_replace(&main, check_text, &wrong),
        );
        let mutated = program.check_build_and_run("app/Vastitas.toml");
        assert_eq!(mutated.status, 1, "{wrong}");
        assert_eq!(mutated.stdout, run.stdout, "{wrong}");
    }
    let verdict = common::checked_replace(&main, "verdict = consistent", "verdict = inconsistent");
    let stderr = expect_code(&check(&app(&verdict)), "E_ERRORBAR");
    assert!(
        stderr.contains("records the verdict `inconsistent`, but every point of the dataset `two_level::D` is consistent"),
        "{stderr}"
    );
    // At resonance the prediction is 1/2; 3/5 lies outside 1/2 ± 2·(1/50)
    // and the propagated uncertainty of omega, which is 0 there.
    let outlier = common::checked_replace(
        &main,
        "(delta = 0, value = measured(frac(1, 2), u = frac(1, 50)))",
        "(delta = 0, value = measured(frac(3, 5), u = frac(1, 50)))",
    );
    expect_code(&check(&app(&outlier)), "E_ERRORBAR");
    let recorded =
        common::checked_replace(&outlier, "verdict = consistent", "verdict = inconsistent");
    common::success(&check(&app(&recorded)));
}
