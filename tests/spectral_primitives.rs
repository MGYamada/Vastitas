//! The spectral primitives of Stage 5 (#806) through the public protocol-9
//! source path, with the emit corpus program
//! `tests/emit_corpus/spectral-primitives`: the invariants `trace_power` and
//! `char_coefficient` as smooth maps, and the observations `annihilates`,
//! `action_entry`, `on_branch`, `branch_differential` and `branch_projector`.
//! The frontend parses each form into the binding that the kernel decodes;
//! these tests capture the wire, check the protocol it selects, submit it to
//! the kernel, which checks the spectral bindings, and build and run the
//! program, whose `main` adds its own power of two for each group of
//! observations that fails.
mod common;
use common::{Scratch, assert_wire_rejected, cli, expect_code, kernel, success};
use serde_json::{Value, json};

const MANIFEST: &str = include_str!("emit_corpus/spectral-primitives/Vastitas.toml");
const MAIN: &str = include_str!("emit_corpus/spectral-primitives/main.vast");

/// The five observations of the table.
const OBSERVATIONS: [&str; 5] = [
    "annihilates",
    "action_entry",
    "on_branch",
    "branch_differential",
    "branch_projector",
];

fn package(main: &str) -> Scratch {
    let s = Scratch::empty("spectral primitives");
    s.write("Vastitas.toml", MANIFEST);
    s.write("main.vast", main);
    s
}

/// The wire that the frontend sends for the program; it must use protocol 9.
fn request(s: &Scratch) -> Value {
    s.captured("Vastitas.toml", 9)
}

/// `MAIN` with the line `from` replaced by `to`.
#[track_caller]
fn replaced(from: &str, to: &str) -> String {
    assert_eq!(
        MAIN.lines().filter(|line| *line == from).count(),
        1,
        "{from}"
    );
    MAIN.lines()
        .map(|line| if line == from { to } else { line })
        .map(|line| format!("{line}\n"))
        .collect()
}

/// `MAIN` with `extra` before `fn verdict`.
fn with(extra: &str) -> String {
    MAIN.replacen("fn verdict", &format!("{extra}\nfn verdict"), 1)
}

/// JSON pointer to the named declaration.
fn pointer(raw: &Value, name: &str) -> String {
    let [module] = raw["packages"][0]["modules"].as_array().unwrap().as_slice() else {
        panic!("one module expected");
    };
    let index = module["indexed_declarations"]
        .as_array()
        .unwrap()
        .iter()
        .position(|d| d["name"] == name)
        .unwrap_or_else(|| panic!("no declaration {name}"));
    format!("/packages/0/modules/0/indexed_declarations/{index}")
}

/// `raw` with the field at `path` below the named declaration set to `value`.
fn forged(raw: &Value, name: &str, path: &str, value: Value) -> Value {
    let mut changed = raw.clone();
    let target = format!("{}{path}", pointer(raw, name));
    let (parent, field) = target.rsplit_once('/').unwrap();
    changed
        .pointer_mut(parent)
        .unwrap_or_else(|| panic!("no {parent}"))
        .as_object_mut()
        .unwrap()
        .insert(field.to_owned(), value);
    changed
}

/// A path on the wire, as the frontend writes it: its segments.
fn p(name: &str) -> Value {
    json!([name])
}

/// The program declares each observation, the kernel accepts it under
/// protocol 9, and protocols 7 and 8 reject it with `E_PROTOCOL`.
#[test]
fn spectral_primitives_select_protocol_nine_and_decode_only_there() {
    let raw = request(&package(MAIN));
    let declared: Vec<&str> = raw["packages"][0]["modules"][0]["indexed_declarations"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|d| d["kind"] == "primitive")
        .filter_map(|d| d["binding"]["op"].as_str())
        .collect();
    for op in OBSERVATIONS {
        assert!(
            vastitas::indexed::primitive_family(op).is_some(),
            "{op} is not in the table"
        );
        assert!(declared.contains(&op), "the program declares no {op}");
    }
    let response = kernel(&raw, "check");
    assert_eq!(response["ok"], true, "{response}");
    for version in [7, 8] {
        let mut older = raw.clone();
        older["version"] = json!(version);
        assert_wire_rejected(&kernel(older, "emit"), "E_PROTOCOL");
    }
}

/// The wire carries no embedded declaration: the kernel fills every
/// endomorphism, spectrum and branch that a binding names from the
/// declarations, and recomputes the image of an invariant. A row, a
/// certificate, a localization or a map on the wire is an unknown field, and
/// each forgery is a protocol error of the kernel's decoder.
#[test]
fn raw_wire_rejects_embedded_spectral_data() {
    let raw = request(&package(MAIN));
    let forgeries = [
        ("ann_j", "/binding/rows", json!([])),
        ("ann_j", "/binding/characteristic", json!([])),
        ("act_j", "/binding/adjugate", json!([])),
        (
            "on",
            "/binding/localize",
            json!({ "op": "natural", "value": "1" }),
        ),
        (
            "dlambda",
            "/binding/witness",
            json!({ "op": "natural", "value": "1" }),
        ),
        ("p12", "/binding/exponent", json!("1")),
        ("p12", "/binding/quotient", json!([])),
        ("tr2", "/definition/map", json!([])),
        ("tr2", "/definition/image", json!([])),
        ("c0", "/definition/characteristic", json!([])),
        // Fields of the wrong kind.
        ("act_j", "/binding/row", json!(0)),
        ("p12", "/binding/column", json!(1)),
        ("ann_j", "/binding/element", json!("t - 2")),
        ("on", "/binding/branch", json!("B")),
    ];
    for (name, path, value) in forgeries {
        let response = kernel(forged(&raw, name, path, value), "emit");
        assert_wire_rejected(&response, "E_PROTOCOL");
    }
}

/// A forged reference on the wire decodes, and the kernel judges it: an
/// observation that names a declaration of the wrong kind is `E_SPECTRAL`,
/// and a family or a line of the wrong kind is the `E_TYPE` of the
/// declaration audit, naming the family or the line.
#[test]
fn raw_wire_forgeries_of_references_are_rejected_by_the_kernel() {
    let raw = request(&package(MAIN));
    let cases = [
        (
            "ann_j",
            "/binding/spectrum/path",
            p("B"),
            "E_SPECTRAL",
            "is not a spectrum declaration",
        ),
        (
            "on",
            "/binding/branch/path",
            p("S"),
            "E_SPECTRAL",
            "is not a branch declaration",
        ),
        (
            "tr2",
            "/definition/endomorphism/path",
            p("S"),
            "E_SPECTRAL",
            "which is not an endomorphism declaration",
        ),
        (
            "c0",
            "/definition/spectrum/path",
            p("H"),
            "E_SPECTRAL",
            "which is not a spectrum declaration",
        ),
        (
            "dlambda",
            "/binding/cotangent/path",
            p("Tangent"),
            "E_TYPE",
            "the family `spectral_primitives::Tangent` of the `branch_differential` primitive `spectral_primitives::dlambda` must have the representation `cotangent`",
        ),
        (
            "on",
            "/binding/line/path",
            p("Plane"),
            "E_TYPE",
            "the line `spectral_primitives::Plane` of the `on_branch` primitive `spectral_primitives::on` must be a smooth object of dimension 1",
        ),
        (
            "p12",
            "/binding/map_family/path",
            p("Cotangent"),
            "E_TYPE",
            "the family `spectral_primitives::Cotangent` of the `branch_projector` primitive `spectral_primitives::p12` must have the representation `smooth`",
        ),
    ];
    for (name, path, value, code, message) in cases {
        let response = kernel(forged(&raw, name, path, value), "check");
        assert_eq!(response["ok"], false, "{name}{path}: {response}");
        assert_eq!(
            response["diagnostics"][0]["code"], code,
            "{name}{path}: {response}"
        );
        let text = response["diagnostics"][0]["message"].as_str().unwrap();
        assert!(text.contains(message), "{name}{path}: {text}");
    }
}

/// The static operands of an observation are checked where it is
/// declared or called: a cotangent family of the wrong variance or a line of
/// the wrong dimension at the declaration, a point of another object or a
/// value in another object than the declared line at the call.
#[test]
fn spectral_operands_are_checked_at_their_declaration_and_call() {
    let dlambda =
        "indexed primitive dlambda = branch_differential(Smooth, Cotangent, Line, branch = B);";
    let on = "indexed primitive on = on_branch(Smooth, Line, branch = B);";
    for (from, to, message) in [
        (
            dlambda,
            "indexed primitive dlambda = branch_differential(Smooth, Tangent, Line, branch = B);",
            "must have the representation `cotangent`",
        ),
        (
            on,
            "indexed primitive on = on_branch(Smooth, Plane, branch = B);",
            "the line `spectral_primitives::Plane` of the `on_branch` primitive `spectral_primitives::on` must be a smooth object of dimension 1",
        ),
    ] {
        let stderr = expect_code(
            &package(&replaced(from, to)).check_manifest("Vastitas.toml"),
            "E_TYPE",
        );
        assert!(stderr.contains(message), "{to}: {stderr}");
    }
    for (body, message) in [
        (
            "ann_zero(plane_at(3, 4))",
            "ann_zero requires a point with target Pt (the spectrum's object), but the supplied point has target Plane",
        ),
        (
            "on(pt_at(), line_at(5))",
            "on requires a point with target Plane (the branch's object), but the supplied point has target Pt",
        ),
        (
            "on(plane_at(3, 4), plane_at(5, 0))",
            "on requires a value with target Line (the primitive's declared line), but the supplied value has target Plane",
        ),
    ] {
        let stderr = expect_code(
            &package(&with(&format!("fn bad() -> Bool {{ {body} }}")))
                .check_manifest("Vastitas.toml"),
            "E_ENDPOINT",
        );
        assert!(stderr.contains(message), "{body}: {stderr}");
    }
}

/// The program checks, builds and exits with 42: each group of observations
/// of `main` adds its own power of two when it fails.
#[test]
fn spectral_program_checks_builds_and_prints_42() {
    let s = package(MAIN);
    success(
        &cli()
            .current_dir(&s.0)
            .args(["check", "--manifest-path", "Vastitas.toml"])
            .output()
            .unwrap(),
    );
    assert_eq!(s.build_and_run("Vastitas.toml"), common::exits(42));
}
