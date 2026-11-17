//! The Stage 6 (#841) source forms through the public source path:
//! the transition average of `std::linalg::spectral` and its observation
//! `average_at`, the convention and the model of `nature::model`, and the
//! calibration, the dataset and the comparison of `nature::errorbar`. The
//! frontend parses each form into the wire record that the kernel decodes;
//! these tests capture the wire, check its records, submit it to the kernel
//! and forge it, and check, build and run the two-level model of the plan:
//! H = (Δ/2)σz + (Ω/2)σx on
//! Affine(2)[delta, omega], prepared in g and observed in e, with the
//! average Ω²/(2(Δ² + Ω²)), calibrated at Ω = 5/2 ± 1/20 and compared with
//! two points.
mod common;
use common::{Scratch, assert_wire_rejected, expect_code, kernel, remove_spans, success};
use serde_json::{Value, json};

const MANIFEST: &str =
    "[package]\nname = \"two_level\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n";

/// The objects, the families and the `std` declarations of the model.
const STD: &str = "// The two-level field of Stage 6 (#841).
indexed marker CInfReal;
indexed implementation SmoothR(CInfReal, smooth_affine) capabilities();
indexed classification CInfAffine { parents(); domain(SmoothR); };
indexed family Smooth(object(CInfAffine), object(CInfAffine))
    = smooth constraints(canonical(0), canonical(1));
indexed family FreeModule(object(CInfAffine)) = free_module constraints(canonical(0));
indexed family Endomorphism(object(CInfAffine)) = endomorphism constraints(canonical(0));
indexed family Spectrum(object(CInfAffine)) = spectrum constraints(canonical(0));
indexed family Branch(object(CInfAffine)) = branch constraints(canonical(0));
indexed family TransitionAverage(object(CInfAffine)) = transition_average constraints(canonical(0));
indexed family Reading(object(CInfAffine)) = reading constraints(canonical(0));
indexed family Model(object(CInfAffine)) = model constraints(canonical(0));
indexed family Calibration(object(CInfAffine)) = calibration constraints(canonical(0));
indexed family Dataset(object(CInfAffine)) = dataset constraints(canonical(0));
indexed family Comparison(object(CInfAffine)) = comparison constraints(canonical(0));
indexed affine Pt(SmoothR) = Affine(0)[];
indexed affine Line(SmoothR) = Affine(1)[s];
indexed affine P(SmoothR) = Affine(2)[delta, omega];

indexed free_module V: FreeModule<P> = basis(g, e);
indexed endomorphism H: Endomorphism<P> =
    rows((frac(1, 2) * delta, frac(1, 2) * omega), (frac(1, 2) * omega, -frac(1, 2) * delta)) of V symmetric;
indexed spectrum S: Spectrum<P> = eigen(H, t);
indexed branch B: Branch<P> = simple(S, localize = delta^2 + omega^2, witness = 2 * t, exponent = 1);
indexed average A: TransitionAverage<P> = transition_average(B, from = g, to = e) = ratio(frac(1, 2) * omega^2, delta^2 + omega^2);
indexed primitive plane_at = smooth_int_point(Smooth, P, Pt);
indexed primitive avg = average_at(Smooth, Line, average = A);
";

/// The declarations of `nature`: the reading, the convention, the model, the
/// calibration, the dataset and the comparison, whose fingerprint is
/// `FINGERPRINT`.
const NATURE: &str = r#"
indexed base_dimension T;
indexed quantity Frequency = T^-1;
indexed reading r: Reading<P> = (delta: Frequency, omega: Frequency);
indexed convention c = hbar_one;
indexed model M: Model<P> = model(hamiltonian = H, reading = r, convention = c, prepare = g, observe = e,
    predicts = A, regime = assume("rotating-wave approximation, drive far below the transition frequency"));
indexed calibration K: Calibration<P> = calibrate(omega = measured(frac(5, 2), u = frac(1, 20)),
    method = type_b, reference = "JCGM 100:2008", revision = "rev-1");
indexed dataset D: Dataset<P> = measure(model = M, calibration = K, coverage = 2,
    points = [(delta = 0, value = measured(frac(1, 2), u = frac(1, 50))),
              (delta = 1, value = measured(frac(9, 20), u = frac(1, 50)))]);
indexed comparison C: Comparison<P> = compare(D, calibration = K, fingerprint = "FINGERPRINT", verdict = consistent);
"#;

/// The entry point: the exact average at (1, 2), at resonance (0, 5) and at
/// the origin, which is off the chart.
const MAIN: &str = "
fn main() -> Int {
    let near = show!(avg(plane_at(1, 2)));
    let resonance = show!(avg(plane_at(0, 5)));
    let off = show!(avg(plane_at(0, 0)));
    0
}
";

/// What `MAIN` shows.
fn shown() -> common::Run {
    common::shows(&[
        "avg(plane_at(1, 2)) = (2, 5)",
        "avg(plane_at(0, 5)) = (1, 2)",
        "avg(plane_at(0, 0)) = (0, 0)",
    ])
}

fn package(main: &str) -> Scratch {
    let s = Scratch::empty("physical models");
    s.write("Vastitas.toml", MANIFEST);
    s.write("main.vast", main);
    s
}

fn check(s: &Scratch) -> std::process::Output {
    s.check_manifest("Vastitas.toml")
}

/// The program with `nature` as given and `fingerprint` recorded.
fn program(nature: &str, fingerprint: &str) -> String {
    format!(
        "{STD}{}{MAIN}",
        common::checked_replace(nature, "FINGERPRINT", fingerprint)
    )
}

/// The current fingerprint of the calibration of `nature`, which the
/// kernel names in the `E_STALE` of a comparison that records another one.
fn fingerprint(nature: &str) -> String {
    let stderr = expect_code(&check(&package(&program(nature, "stale"))), "E_STALE");
    let start = stderr
        .find("its current fingerprint is `")
        .unwrap_or_else(|| panic!("{stderr}"))
        + "its current fingerprint is `".len();
    let end = stderr[start..].find('`').unwrap() + start;
    stderr[start..end].to_owned()
}

/// The accepted program, with the current fingerprint.
fn accepted() -> String {
    program(NATURE, &fingerprint(NATURE))
}

/// The declaration `name` of the one module of a captured request.
fn declaration<'a>(wire: &'a Value, name: &str) -> &'a Value {
    wire["packages"][0]["modules"][0]["indexed_declarations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|d| d["name"] == name)
        .unwrap_or_else(|| panic!("no declaration {name}"))
}

fn without_spans(value: &Value) -> Value {
    let mut value = value.clone();
    remove_spans(&mut value);
    value
}

fn p(name: &str) -> Value {
    json!({ "path": [name] })
}

fn n(value: &str) -> Value {
    json!({ "op": "natural", "value": value })
}

fn frac(numerator: &str, denominator: &str) -> Value {
    json!({ "op": "fraction", "numerator": numerator, "denominator": denominator })
}

fn pow(name: &str) -> Value {
    json!({ "op": "pow", "base": { "op": "coordinate", "name": name }, "exponent": "2" })
}

/// A program with a Stage 6 form is a request of the one wire protocol, as
/// every request is (#533): a convention alone, which is no algebraic form,
/// is accepted. Every form serializes to the record that the kernel decodes.
#[test]
fn the_stage6_forms_serialize_to_their_records() {
    let alone = package("indexed convention c = hbar_one;\nfn main() -> Int { 0 }\n");
    let wire = alone.captured("Vastitas.toml", common::CURRENT_PROTOCOL);
    assert_eq!(wire["version"], common::CURRENT_PROTOCOL);
    assert_eq!(declaration(&wire, "c")["kind"], "convention");
    assert_eq!(declaration(&wire, "c")["value"], "hbar_one");
    assert_eq!(kernel(&wire, "check")["ok"], true);
    let source = accepted();
    let fingerprint = fingerprint(NATURE);
    let wire = package(&source).captured("Vastitas.toml", common::CURRENT_PROTOCOL);
    let record = |name: &str| {
        let mut record = without_spans(declaration(&wire, name));
        let object = record.as_object_mut().unwrap();
        object.remove("name");
        object.remove("public");
        record
    };
    assert_eq!(
        record("A"),
        json!({ "kind": "transition_average", "family": p("TransitionAverage"), "indices": [p("P")],
            "branch": p("B"), "from": "g", "to": "e",
            "numerator": { "op": "product", "factors": [frac("1", "2"), pow("omega")] },
            "denominator": { "op": "sum", "terms": [pow("delta"), pow("omega")] } })
    );
    assert_eq!(
        record("avg"),
        json!({ "kind": "primitive", "binding": { "op": "average_at", "map_family": p("Smooth"),
            "line": p("Line"), "average": p("A") } })
    );
    assert_eq!(
        record("M"),
        json!({ "kind": "model", "family": p("Model"), "indices": [p("P")], "hamiltonian": p("H"),
            "reading": p("r"), "convention": p("c"), "prepare": "g", "observe": "e", "predicts": p("A"),
            "regime": "rotating-wave approximation, drive far below the transition frequency" })
    );
    assert_eq!(
        record("K"),
        json!({ "kind": "calibration", "family": p("Calibration"), "indices": [p("P")],
            "parameters": [{ "coordinate": "omega", "value": frac("5", "2"), "uncertainty": frac("1", "20") }],
            "method": "type_b", "reference": "JCGM 100:2008", "revision": "rev-1" })
    );
    assert_eq!(
        record("D"),
        json!({ "kind": "dataset", "family": p("Dataset"), "indices": [p("P")], "model": p("M"),
            "calibration": p("K"), "coverage": n("2"), "points": [
                { "coordinates": [{ "coordinate": "delta", "value": n("0") }], "value": frac("1", "2"),
                    "uncertainty": frac("1", "50") },
                { "coordinates": [{ "coordinate": "delta", "value": n("1") }], "value": frac("9", "20"),
                    "uncertainty": frac("1", "50") }] })
    );
    assert_eq!(
        record("C"),
        json!({ "kind": "comparison", "family": p("Comparison"), "indices": [p("P")], "dataset": p("D"),
            "calibration": p("K"), "fingerprint": fingerprint, "verdict": "consistent" })
    );
    assert_eq!(kernel(&wire, "check")["ok"], true);
}

/// The two-level model is accepted, and its program shows the exact average
/// on the chart and the failure value off it.
#[test]
fn the_two_level_model_checks_builds_and_runs() {
    let fingerprint = fingerprint(NATURE);
    assert!(fingerprint.starts_with("fnv1a64:"), "{fingerprint}");
    assert_eq!(fingerprint.len(), "fnv1a64:".len() + 16, "{fingerprint}");
    assert_eq!(
        package(&accepted()).check_build_and_run("Vastitas.toml"),
        shown()
    );
}

/// C9: a changed calibration makes the recorded comparison stale, and the
/// diagnostic names the current fingerprint; without the comparison the
/// program is accepted, and its generated code is that of the program
/// without any `nature` declaration; recorded again it is accepted.
#[test]
fn a_changed_calibration_makes_the_comparison_stale() {
    let old = fingerprint(NATURE);
    let changed = common::checked_replace(
        NATURE,
        "measured(frac(5, 2), u = frac(1, 20))",
        "measured(3, u = frac(1, 20))",
    );
    let current = fingerprint(&changed);
    assert_ne!(old, current);
    let stderr = expect_code(&check(&package(&program(&changed, &old))), "E_STALE");
    assert!(
        stderr.contains(&format!(
            "E_STALE: the comparison `two_level::C` records the fingerprint `{old}` of the calibration \
             `two_level::K`, but its current fingerprint is `{current}`"
        )),
        "{stderr}"
    );
    let comparison = changed
        .lines()
        .find(|line| line.starts_with("indexed comparison"))
        .unwrap();
    let without = common::checked_replace(&changed, comparison, "");
    let emitted = |source: &str| {
        let response = kernel(
            package(source).captured("Vastitas.toml", common::CURRENT_PROTOCOL),
            "emit",
        );
        assert_eq!(response["ok"], true, "{response}");
        response["lean_source"].as_str().unwrap().to_owned()
    };
    assert_eq!(
        emitted(&format!("{STD}{without}{MAIN}")),
        emitted(&format!("{STD}{MAIN}"))
    );
    assert_eq!(
        package(&program(&changed, &current)).check_build_and_run("Vastitas.toml"),
        shown()
    );
}

/// The kernel recomputes the verdict: a consistent dataset recorded as
/// inconsistent is `E_ERRORBAR`, and so is an inconsistent point recorded as
/// consistent, which the diagnostic names.
#[test]
fn a_wrong_verdict_is_rejected() {
    let fingerprint = fingerprint(NATURE);
    let inconsistent =
        common::checked_replace(NATURE, "verdict = consistent", "verdict = inconsistent");
    let stderr = expect_code(
        &check(&package(&program(&inconsistent, &fingerprint))),
        "E_ERRORBAR",
    );
    assert!(
        stderr.contains("records the verdict `inconsistent`, but every point of the dataset `two_level::D` is consistent"),
        "{stderr}"
    );
    let far = common::checked_replace(
        NATURE,
        "measured(frac(9, 20), u = frac(1, 50))",
        "measured(frac(3, 5), u = frac(1, 50))",
    );
    let stderr = expect_code(&check(&package(&program(&far, &fingerprint))), "E_ERRORBAR");
    assert!(
        stderr.contains(
            "records the verdict `consistent`, but the point 2 of the dataset `two_level::D`"
        ),
        "{stderr}"
    );
    let recorded = common::checked_replace(&far, "verdict = consistent", "verdict = inconsistent");
    success(&check(&package(&program(&recorded, &fingerprint))));
}

/// A dataset of more than `datasetPoints` points is the frontend's `E_LIMIT`
/// at its points, before the request is written; a forged request beyond
/// the limit is the kernel's `E_LIMIT`.
#[test]
fn the_points_of_a_dataset_are_bounded() {
    let points = |count: usize| {
        vec!["(delta = 0, value = measured(frac(1, 2), u = frac(1, 50)))"; count].join(", ")
    };
    let dataset = |count: usize| {
        format!(
            "{STD}{}{MAIN}",
            common::checked_replace(
                &NATURE.replace("FINGERPRINT", "x"),
                "points = [(delta = 0, value = measured(frac(1, 2), u = frac(1, 50))),\n              (delta = 1, value = measured(frac(9, 20), u = frac(1, 50)))]",
                &format!("points = [{}]", points(count))
            )
        )
    };
    let stderr = expect_code(&check(&package(&dataset(65))), "E_LIMIT");
    assert!(
        stderr.contains("main.vast:")
            && stderr.contains(
                "E_LIMIT: a dataset has at most 64 points (`datasetPoints`), but this one has 65"
            ),
        "{stderr}"
    );
    // At the limit the program is accepted with the current fingerprint of its
    // calibration.
    let at_limit = common::checked_replace(
        NATURE,
        "points = [(delta = 0, value = measured(frac(1, 2), u = frac(1, 50))),\n              (delta = 1, value = measured(frac(9, 20), u = frac(1, 50)))]",
        &format!("points = [{}]", points(64)),
    );
    common::success(&check(&package(&program(
        &at_limit,
        &fingerprint(&at_limit),
    ))));
    // A forged request with one more point is the kernel's limit.
    let wire = package(&dataset(64)).captured("Vastitas.toml", common::CURRENT_PROTOCOL);
    let mut forged = wire.clone();
    let index = wire["packages"][0]["modules"][0]["indexed_declarations"]
        .as_array()
        .unwrap()
        .iter()
        .position(|d| d["name"] == "D")
        .unwrap();
    let points = forged
        .pointer_mut(&format!(
            "/packages/0/modules/0/indexed_declarations/{index}/points"
        ))
        .unwrap()
        .as_array_mut()
        .unwrap();
    points.push(points[0].clone());
    assert_wire_rejected(&kernel(forged, "check"), "E_LIMIT");
}

/// The kernel judges every record of the wire again: a forged fingerprint is
/// stale, a forged verdict and a forged closed form are rejected, a
/// certificate, a trace or an embedded declaration on the wire is an unknown
/// field, and a recorded text that no string literal of the frontend gives is
/// a protocol error.
#[test]
fn forged_stage6_records_are_rejected_by_the_kernel() {
    let wire = package(&accepted()).captured("Vastitas.toml", common::CURRENT_PROTOCOL);
    let index = |name: &str| {
        wire["packages"][0]["modules"][0]["indexed_declarations"]
            .as_array()
            .unwrap()
            .iter()
            .position(|d| d["name"] == name)
            .unwrap()
    };
    let forged = |name: &str, field: &str, value: Value| {
        let mut changed = wire.clone();
        let target = format!("/packages/0/modules/0/indexed_declarations/{}", index(name));
        changed
            .pointer_mut(&target)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .insert(field.into(), value);
        kernel(changed, "check")
    };
    assert_wire_rejected(
        &forged("C", "fingerprint", json!("fnv1a64:0000000000000000")),
        "E_STALE",
    );
    assert_wire_rejected(&forged("C", "verdict", json!("inconsistent")), "E_ERRORBAR");
    assert_wire_rejected(&forged("A", "numerator", pow("omega")), "E_SPECTRAL");
    assert_wire_rejected(&forged("M", "prepare", json!("e")), "E_MODEL");
    assert_wire_rejected(&forged("D", "coverage", n("0")), "E_ERRORBAR");
    for (name, field) in [
        ("A", "certificate"),
        ("A", "trace"),
        ("K", "fingerprint"),
        ("C", "points"),
        ("M", "basis"),
    ] {
        assert_wire_rejected(&forged(name, field, json!([])), "E_PROTOCOL");
    }
    assert_wire_rejected(&forged("C", "verdict", json!("stale")), "E_PROTOCOL");
    // A measured value is a rational literal: a tower of powers of a 64-digit
    // fraction, a few hundred bytes whose value has tens of millions of bits,
    // is rejected before any value is computed, and so is a literal beyond
    // the digit bound.
    let mut tower = frac(
        &format!("1{}1", "0".repeat(62)),
        &format!("{}7", "9".repeat(62)),
    );
    for _ in 0..4 {
        tower = json!({ "op": "pow", "base": tower, "exponent": "16" });
    }
    let started = std::time::Instant::now();
    assert_wire_rejected(
        &forged(
            "K",
            "parameters",
            json!([{ "coordinate": "omega", "value": tower, "uncertainty": frac("1", "20") }]),
        ),
        "E_PROTOCOL",
    );
    assert!(
        started.elapsed() < std::time::Duration::from_secs(2),
        "{:?}",
        started.elapsed()
    );
    let long = json!([{ "coordinate": "omega", "value": n(&"1".repeat(65)), "uncertainty": frac("1", "20") }]);
    assert_wire_rejected(&forged("K", "parameters", long), "E_PROTOCOL");
    assert_wire_rejected(&forged("c", "value", json!("hbar_two")), "E_PROTOCOL");
    let bytes = 256;
    for (name, field, text) in [
        ("C", "fingerprint", "fnv1a64:\\0000000000000000".to_string()),
        ("K", "reference", "JCGM\n100".to_string()),
        ("K", "revision", "\"r\"".to_string()),
        ("M", "regime", "\u{3a9} >> 1".to_string()),
        ("M", "regime", "a".repeat(bytes + 1)),
    ] {
        assert_wire_rejected(&forged(name, field, json!(text)), "E_PROTOCOL");
    }
    let mut at_limit = wire.clone();
    let target = format!(
        "/packages/0/modules/0/indexed_declarations/{}/regime",
        index("M")
    );
    *at_limit.pointer_mut(&target).unwrap() = json!("~".repeat(bytes));
    let response = kernel(at_limit, "check");
    assert_eq!(response["ok"], true, "{response}");
}

/// The syntax errors of the Stage 6 forms are the frontend's, at their place;
/// `/` and `@` keep their errors everywhere, and a recorded text has at most
/// `recordTextBytes` bytes.
#[test]
fn stage6_syntax_errors_are_reported_at_their_place() {
    let long_reference = format!(
        "indexed calibration K: Calibration<P> = calibrate(method = type_a, reference = \"{}\", revision = \"r\");\n",
        "a".repeat(257)
    );
    let cases = [
        (
            "indexed average A: TransitionAverage<P> = transition_average(B, to = e) = ratio(1, 2);\n",
            "main.vast:1:63: E_PARSE: `transition_average` needs an explicit source vector: write `from = …`",
        ),
        (
            "indexed average A: TransitionAverage<P> = transition_average(B, from = g, to = e) = 1;\n",
            "main.vast:1:85: E_PARSE: the closed form of `transition_average` is `ratio(N, D)` of two polynomials",
        ),
        (
            "indexed average A: TransitionAverage<P> = transition_average(B, from = g, to = e) = 1 / 2;\n",
            "main.vast:1:87: E_UNSUPPORTED: division is not supported",
        ),
        (
            "indexed comparison C: Comparison<P> = compare(D, calibration = K, verdict = consistent);\n",
            "main.vast:1:65: E_PARSE: `compare` needs the recorded fingerprint of its calibration: write `fingerprint = …`",
        ),
        (
            "indexed comparison C: Comparison<P> = compare(D, calibration = K @ \"f\", verdict = consistent);\n",
            "main.vast:1:66: E_LEX:",
        ),
        (
            long_reference.as_str(),
            "main.vast:1:80: E_LIMIT: the reference of `calibrate` has at most 256 bytes (`recordTextBytes`), but this one has 257",
        ),
        (
            "indexed convention c = hbar_two;\n",
            "main.vast:1:24: E_TYPE: a convention is `hbar_one`, the one convention of the profile",
        ),
        (
            "fn half(n: Int) -> Int { n / 2 }\n",
            "main.vast:1:28: E_UNSUPPORTED: division is not supported",
        ),
    ];
    for (source, expected) in cases {
        let stderr = String::from_utf8_lossy(
            &check(&package(&format!("{source}fn main() -> Int {{ 0 }}\n"))).stderr,
        )
        .into_owned();
        assert!(stderr.contains(expected), "{source}\n{stderr}");
    }
}

/// With the libraries: the families come from `std::linalg::spectral`,
/// `nature::dimension`, `nature::model` and `nature::errorbar` of copies of
/// the stdlib and of `nature`, and the program checks, builds and runs.
#[test]
fn the_model_uses_the_families_of_the_libraries() {
    let imports = "use std::geometry::smooth::affine::SmoothR;
use std::geometry::smooth::affine::Smooth;
use std::geometry::smooth::affine::Pt;
use std::geometry::smooth::affine::Line;
use std::linalg::spectral::FreeModule;
use std::linalg::spectral::Endomorphism;
use std::linalg::spectral::Spectrum;
use std::linalg::spectral::Branch;
use std::linalg::spectral::TransitionAverage;
use nature::dimension::Reading;
use nature::dimension::T;
use nature::model::Model;
use nature::errorbar::Calibration;
use nature::errorbar::Dataset;
use nature::errorbar::Comparison;
";
    // The program without its own objects and families, which the libraries
    // supply, and without its own base dimension.
    let declarations: String = STD
        .lines()
        .skip_while(|line| !line.starts_with("indexed affine P("))
        .map(|line| format!("{line}\n"))
        .collect();
    let nature = common::checked_replace(NATURE, "indexed base_dimension T;\n", "");
    let manifest = "[package]\nname = \"two_level\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n\n[dependencies]\nstd = { path = \"../stdlib\" }\nnature = { path = \"../nature\" }\n";
    let source = |fingerprint: &str| {
        format!(
            "{imports}{declarations}{}{MAIN}",
            common::checked_replace(&nature, "FINGERPRINT", fingerprint)
        )
    };
    let s = common::stdlib_app("physical models", manifest, &source("stale"), &[]);
    s.copy_nature();
    let stderr = expect_code(&s.check_manifest("app/Vastitas.toml"), "E_STALE");
    let start =
        stderr.find("its current fingerprint is `").unwrap() + "its current fingerprint is `".len();
    let end = stderr[start..].find('`').unwrap() + start;
    s.write("app/main.vast", &source(&stderr[start..end]));
    assert_eq!(s.check_build_and_run("app/Vastitas.toml"), shown());
}
