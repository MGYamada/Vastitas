//! The Stage 5 (#806) source forms of `std::linalg::spectral` through the
//! public protocol-9 source path: the spectral families, the free module,
//! endomorphism, spectrum and branch declarations, the invariants
//! `trace_power` and `char_coefficient`, and the five observations. The
//! frontend parses each form into the wire record that the kernel decodes and
//! checks no spectral rule of its own; these tests capture the wire, check the
//! protocol it selects, its records and its round trip, and submit it to the
//! kernel, which decodes it only in protocol 9 and judges it.
mod common;
use common::{Scratch, assert_wire_rejected, expect_code, kernel, remove_spans, success};
use serde_json::{Value, json};

const MANIFEST: &str =
    "[package]\nname = \"spectral_declarations\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n";

/// Every Stage 5 form of the frontend in one module, on the plane of the
/// roadmap: H = rows((x, y), (y, -x)) on V = basis(e1, e2), its spectrum S
/// with fiber coordinate t, and the branch chart D(x² + y²) with witness t/2.
const MAIN: &str = "// The Stage 5 forms of the frontend (#806).
indexed marker CInfReal;
indexed implementation SmoothR(CInfReal, smooth_affine) capabilities();
indexed classification CInfAffine { parents(); domain(SmoothR); };
indexed family Smooth(object(CInfAffine), object(CInfAffine))
    = smooth constraints(canonical(0), canonical(1));
indexed family Cotangent(object(CInfAffine)) = cotangent constraints(canonical(0));
indexed family FreeModule(object(CInfAffine)) = free_module constraints(canonical(0));
indexed family Endomorphism(object(CInfAffine)) = endomorphism constraints(canonical(0));
indexed family Spectrum(object(CInfAffine)) = spectrum constraints(canonical(0));
indexed family Branch(object(CInfAffine)) = branch constraints(canonical(0));
indexed affine Pt(SmoothR) = Affine(0)[];
indexed affine Line(SmoothR) = Affine(1)[s];
indexed affine Plane(SmoothR) = Affine(2)[x, y];

indexed free_module V: FreeModule<Plane> = basis(e1, e2);
indexed endomorphism H: Endomorphism<Plane> = rows((x, y), (y, -x)) of V symmetric;
indexed spectrum S: Spectrum<Plane> = eigen(H, t);
indexed branch B: Branch<Plane> = simple(S, localize = x^2 + y^2, witness = frac(1, 2) * t, exponent = 1);
indexed morphism tr2: Smooth<Plane, Line> = trace_power(H, 2);
indexed morphism c0: Smooth<Plane, Line> = char_coefficient(S, 0);
indexed primitive ann = annihilates(Smooth, spectrum = S, element = t - 2);
indexed primitive act = action_entry(Smooth, spectrum = S, element = t - 2, e1, e2);
indexed primitive on = on_branch(Smooth, Line, branch = B);
indexed primitive dl = branch_differential(Smooth, Cotangent, Line, branch = B);
indexed primitive pr = branch_projector(Smooth, Line, branch = B, e1, e2);

fn main() -> Int { 42 }
";

fn package(main: &str) -> Scratch {
    let s = Scratch::empty("spectral declarations");
    s.write("Vastitas.toml", MANIFEST);
    s.write("main.vast", main);
    s
}

/// The wire that the frontend sends for `main`, which must use `version`.
#[track_caller]
fn request(main: &str, version: u64) -> Value {
    package(main).captured("Vastitas.toml", version)
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

/// The named declaration of the package's only module.
#[track_caller]
fn declaration<'a>(raw: &'a Value, name: &str) -> &'a Value {
    let [module] = raw["packages"][0]["modules"].as_array().unwrap().as_slice() else {
        panic!("one module expected");
    };
    module["indexed_declarations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|d| d["name"] == name)
        .unwrap_or_else(|| panic!("no declaration {name}"))
}

/// The JSON pointer of the named declaration in the package's only module.
#[track_caller]
fn pointer(raw: &Value, name: &str) -> String {
    let index = raw["packages"][0]["modules"][0]["indexed_declarations"]
        .as_array()
        .unwrap()
        .iter()
        .position(|d| d["name"] == name)
        .unwrap_or_else(|| panic!("no declaration {name}"));
    format!("/packages/0/modules/0/indexed_declarations/{index}")
}

fn p(name: &str) -> Value {
    json!({ "path": [name] })
}

fn n(value: &str) -> Value {
    json!({ "op": "natural", "value": value })
}

fn coordinate(name: &str) -> Value {
    json!({ "op": "coordinate", "name": name })
}

/// Checking `main` fails first with the diagnostic `expected`, written
/// `main.vast:<line>:<column>: <code>: <message>`.
#[track_caller]
fn rejected_at(main: &str, expected: &str) {
    let code = expected.split(": ").nth(1).unwrap();
    let stderr = expect_code(&package(main).check_manifest("Vastitas.toml"), code);
    assert!(
        stderr.contains(&format!("/{expected}")),
        "expected {expected:?}: {stderr}"
    );
}

/// The kernel decodes the request: whatever it decides about the program, a
/// decoding failure would be `E_PROTOCOL`.
#[track_caller]
fn decoded(response: &Value) {
    assert_ne!(
        response["diagnostics"][0]["code"], "E_PROTOCOL",
        "{response}"
    );
}

/// Each Stage 5 form alone in a package, with the frontend's only other item
/// `fn main`, and the exact message with which protocols 7 and 8 reject it. Paths
/// are unresolved on the wire; the kernel resolves them. A spectral family of
/// the library's shape is rejected at its constraint `canonical(0)`, a smooth
/// form, before its representation is read, so each representation also
/// appears without parameters and constraints, where the representation
/// decides. A morphism declaration is an algebraic affine form.
const LONE_FORMS: &[(&str, &str)] = &[
    (
        "indexed family FreeModule(object(CInfAffine)) = free_module constraints(canonical(0));",
        "smooth declarations require protocol 9",
    ),
    (
        "indexed family FreeModule() = free_module constraints();",
        "spectral declarations require protocol 9",
    ),
    (
        "indexed family Endomorphism(object(CInfAffine)) = endomorphism constraints(canonical(0));",
        "smooth declarations require protocol 9",
    ),
    (
        "indexed family Endomorphism() = endomorphism constraints();",
        "spectral declarations require protocol 9",
    ),
    (
        "indexed family Spectrum(object(CInfAffine)) = spectrum constraints(canonical(0));",
        "smooth declarations require protocol 9",
    ),
    (
        "indexed family Spectrum() = spectrum constraints();",
        "spectral declarations require protocol 9",
    ),
    (
        "indexed family Branch(object(CInfAffine)) = branch constraints(canonical(0));",
        "smooth declarations require protocol 9",
    ),
    (
        "indexed family Branch() = branch constraints();",
        "spectral declarations require protocol 9",
    ),
    (
        "indexed free_module V: FreeModule<Plane> = basis(e1, e2);",
        "spectral declarations require protocol 9",
    ),
    (
        "indexed endomorphism H: Endomorphism<Plane> = rows((x, y), (y, -x)) of V symmetric;",
        "spectral declarations require protocol 9",
    ),
    (
        "indexed spectrum S: Spectrum<Plane> = eigen(H, t);",
        "spectral declarations require protocol 9",
    ),
    (
        "indexed branch B: Branch<Plane> = simple(S, localize = x^2 + y^2, witness = frac(1, 2) * t, exponent = 1);",
        "spectral declarations require protocol 9",
    ),
    (
        "indexed morphism tr2: Smooth<Plane, Line> = trace_power(H, 2);",
        "algebraic affine declarations require protocol 9",
    ),
    (
        "indexed morphism c0: Smooth<Plane, Line> = char_coefficient(S, 0);",
        "algebraic affine declarations require protocol 9",
    ),
    (
        "indexed primitive ann = annihilates(Smooth, spectrum = S, element = t - 2);",
        "unknown indexed primitive contract",
    ),
    (
        "indexed primitive act = action_entry(Smooth, spectrum = S, element = t - 2, e1, e2);",
        "unknown indexed primitive contract",
    ),
    (
        "indexed primitive on = on_branch(Smooth, Line, branch = B);",
        "unknown indexed primitive contract",
    ),
    (
        "indexed primitive dl = branch_differential(Smooth, Cotangent, Line, branch = B);",
        "unknown indexed primitive contract",
    ),
    (
        "indexed primitive pr = branch_projector(Smooth, Line, branch = B, e1, e2);",
        "unknown indexed primitive contract",
    ),
];

/// A package with a Stage 5 form uses protocol 9, and only there do the
/// records decode: protocols 7 and 8 reject each with `E_PROTOCOL`.
#[test]
fn spectral_forms_select_protocol_nine_only() {
    // Without a Stage 5 form, an indexed package uses protocol 7.
    request("indexed marker M;\nfn main() -> Int { 0 }\n", 7);
    for (form, older_message) in LONE_FORMS {
        let raw = request(&format!("{form}\nfn main() -> Int {{ 0 }}\n"), 9);
        // The record decodes in protocol 9; its unresolved paths are the
        // kernel's next rejection.
        decoded(&kernel(&raw, "check"));
        for version in [7, 8] {
            let mut older = raw.clone();
            older["version"] = json!(version);
            let response = kernel(older, "emit");
            assert_wire_rejected(&response, "E_PROTOCOL");
            assert_eq!(
                response["diagnostics"][0]["message"], *older_message,
                "{form} in protocol {version}: {response}"
            );
        }
    }
}

/// The frontend sends the Stage 5 declarations of `MAIN` as their wire
/// records, with the common fields of every indexed declaration, and each
/// record reads back into the frontend's IR and serializes to itself.
#[test]
fn the_wire_carries_the_spectral_records() {
    let raw = request(MAIN, 9);
    let record = |name: &str| {
        let mut value = declaration(&raw, name).clone();
        assert!(value["span"].is_object(), "{name}");
        // The wire record, without `public`, is the frontend's declaration.
        let mut body = value.clone();
        body.as_object_mut().unwrap().remove("public").unwrap();
        let read: vastitas::indexed::Declaration =
            serde_json::from_value(body.clone()).unwrap_or_else(|error| panic!("{name}: {error}"));
        assert_eq!(serde_json::to_value(&read).unwrap(), body, "{name}");
        remove_spans(&mut value);
        value
    };
    for (name, representation) in [
        ("FreeModule", "free_module"),
        ("Endomorphism", "endomorphism"),
        ("Spectrum", "spectrum"),
        ("Branch", "branch"),
    ] {
        assert_eq!(
            record(name),
            json!({ "kind": "family", "name": name, "public": false,
                "parameters": [{ "kind": "object", "domain": p("CInfAffine") }],
                "constraints": [{ "kind": "canonical", "object": 0 }],
                "representation": representation })
        );
    }
    let x = || coordinate("x");
    let y = || coordinate("y");
    let t = || coordinate("t");
    let neg = |operand: Value| json!({ "op": "neg", "operand": operand });
    let pow = |base: Value| json!({ "op": "pow", "base": base, "exponent": "2" });
    let shifted = || json!({ "op": "sum", "terms": [t(), neg(n("2"))] });
    assert_eq!(
        record("V"),
        json!({ "kind": "free_module", "name": "V", "public": false,
            "family": p("FreeModule"), "indices": [p("Plane")], "basis": ["e1", "e2"] })
    );
    assert_eq!(
        record("H"),
        json!({ "kind": "endomorphism", "name": "H", "public": false,
            "family": p("Endomorphism"), "indices": [p("Plane")], "module": p("V"),
            "rows": [[x(), y()], [y(), neg(x())]], "symmetric": true })
    );
    assert_eq!(
        record("S"),
        json!({ "kind": "spectrum", "name": "S", "public": false,
            "family": p("Spectrum"), "indices": [p("Plane")], "endomorphism": p("H"),
            "fiber": "t" })
    );
    assert_eq!(
        record("B"),
        json!({ "kind": "branch", "name": "B", "public": false,
            "family": p("Branch"), "indices": [p("Plane")], "spectrum": p("S"),
            "localize": { "op": "sum", "terms": [pow(x()), pow(y())] },
            "witness": { "op": "product", "factors": [
                { "op": "fraction", "numerator": "1", "denominator": "2" }, t()] },
            "exponent": "1" })
    );
    let invariant = |name: &str, definition: Value| {
        json!({ "kind": "morphism", "name": name, "public": false, "family": p("Smooth"),
            "indices": [p("Plane"), p("Line")], "definition": definition })
    };
    assert_eq!(
        record("tr2"),
        invariant(
            "tr2",
            json!({ "kind": "trace_power", "endomorphism": p("H"), "power": "2" })
        )
    );
    assert_eq!(
        record("c0"),
        invariant(
            "c0",
            json!({ "kind": "char_coefficient", "spectrum": p("S"), "index": "0" })
        )
    );
    let primitive = |name: &str, binding: Value| json!({ "kind": "primitive", "name": name, "public": false, "binding": binding });
    assert_eq!(
        record("ann"),
        primitive(
            "ann",
            json!({ "op": "annihilates", "map_family": p("Smooth"), "spectrum": p("S"),
                "element": shifted() })
        )
    );
    assert_eq!(
        record("act"),
        primitive(
            "act",
            json!({ "op": "action_entry", "map_family": p("Smooth"), "spectrum": p("S"),
                "element": shifted(), "row": "e1", "column": "e2" })
        )
    );
    assert_eq!(
        record("on"),
        primitive(
            "on",
            json!({ "op": "on_branch", "map_family": p("Smooth"), "line": p("Line"),
                "branch": p("B") })
        )
    );
    assert_eq!(
        record("dl"),
        primitive(
            "dl",
            json!({ "op": "branch_differential", "map_family": p("Smooth"),
                "cotangent": p("Cotangent"), "line": p("Line"), "branch": p("B") })
        )
    );
    assert_eq!(
        record("pr"),
        primitive(
            "pr",
            json!({ "op": "branch_projector", "map_family": p("Smooth"), "line": p("Line"),
                "branch": p("B"), "row": "e1", "column": "e2" })
        )
    );
}

/// The kernel decodes the whole program in protocol 9 and in no older
/// protocol.
#[test]
fn the_kernel_decodes_the_spectral_program_only_in_protocol_nine() {
    let raw = request(MAIN, 9);
    decoded(&kernel(&raw, "check"));
    for version in [7, 8] {
        let mut older = raw.clone();
        older["version"] = json!(version);
        assert_wire_rejected(&kernel(older, "emit"), "E_PROTOCOL");
    }
}

/// The kernel accepts every form of the program in protocol 9: the
/// declarations, the invariants and the observations. The program checks,
/// builds and runs.
#[test]
fn the_spectral_program_checks_and_runs() {
    let response = kernel(request(MAIN, 9), "check");
    assert_eq!(response["ok"], true, "{response}");
    let s = package(MAIN);
    success(&s.check_manifest("Vastitas.toml"));
    assert_eq!(s.build_and_run("Vastitas.toml"), b"42\n");
}

/// The wire carries no certificate: the kernel computes χ, the adjugate and
/// every quotient, so a certificate field is an unknown field. Every field of
/// a spectral record is required and has its one type. Each forgery is a
/// protocol error of the kernel's decoder, whatever the frontend would send.
#[test]
fn raw_wire_rejects_certificates_and_forged_spectral_fields() {
    let raw = request(MAIN, 9);
    let with = |name: &str, path: &str, value: Value| {
        let mut changed = raw.clone();
        let target = format!("{}{path}", pointer(&raw, name));
        let (parent, field) = target.rsplit_once('/').unwrap();
        changed
            .pointer_mut(parent)
            .unwrap_or_else(|| panic!("no {parent}"))
            .as_object_mut()
            .unwrap()
            .insert(field.to_owned(), value);
        changed
    };
    let without = |name: &str, path: &str| {
        let mut changed = raw.clone();
        let target = format!("{}{path}", pointer(&raw, name));
        let (parent, field) = target.rsplit_once('/').unwrap();
        changed
            .pointer_mut(parent)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .remove(field)
            .unwrap_or_else(|| panic!("no {target}"));
        changed
    };
    let empty = || json!([]);
    let forgeries: Vec<(&str, Value)> = vec![
        // Certificates of a spectrum, a branch, an invariant and an
        // observation.
        (
            "spectrum characteristic",
            with("S", "/characteristic", empty()),
        ),
        ("spectrum adjugate", with("S", "/adjugate", empty())),
        ("spectrum idempotence", with("S", "/idempotence", empty())),
        ("branch quotient", with("B", "/quotient", n("0"))),
        ("invariant map", with("tr2", "/definition/map", empty())),
        (
            "observation certificate",
            with("pr", "/binding/certificate", empty()),
        ),
        ("endomorphism transpose", with("H", "/transpose", empty())),
        // Required fields.
        ("no basis", without("V", "/basis")),
        ("no symmetric", without("H", "/symmetric")),
        ("no fiber", without("S", "/fiber")),
        ("no witness", without("B", "/witness")),
        ("no exponent", without("B", "/exponent")),
        ("no power", without("tr2", "/definition/power")),
        ("no index", without("c0", "/definition/index")),
        ("no element", without("ann", "/binding/element")),
        ("no column", without("act", "/binding/column")),
        ("no branch", without("dl", "/binding/branch")),
        // Types: naturals are unsigned decimal strings within the decoder's
        // digit bound, `symmetric` is a boolean, basis names are strings.
        ("symmetric string", with("H", "/symmetric", json!("true"))),
        ("exponent number", with("B", "/exponent", json!(1))),
        ("negative exponent", with("B", "/exponent", json!("-1"))),
        (
            "negative power",
            with("tr2", "/definition/power", json!("-2")),
        ),
        ("empty index", with("c0", "/definition/index", json!(""))),
        (
            "long power",
            with("tr2", "/definition/power", json!("9".repeat(65))),
        ),
        ("numeric row", with("act", "/binding/row", json!(0))),
        ("numeric basis", with("V", "/basis", json!([1, 2]))),
    ];
    for (what, forged) in forgeries {
        let response = kernel(forged, "emit");
        assert_eq!(response["ok"], false, "{what}: {response}");
        assert_eq!(
            response["diagnostics"][0]["code"], "E_PROTOCOL",
            "{what}: {response}"
        );
    }
}

/// The frontend's one duplicated limit on these forms is the decoder's digit
/// bound on a natural (`algebraCoefficientDigits` = 64): a power, an index or
/// an exponent of 64 digits goes to the wire as written and decodes there,
/// and one of 65 digits is the frontend's `E_LIMIT` at the literal, as the
/// kernel's decoder would refuse it.
#[test]
fn natural_digits_are_bounded_as_the_decoder_bounds_them() {
    let widest = "9".repeat(64);
    let long = "9".repeat(65);
    let tr2 = "indexed morphism tr2: Smooth<Plane, Line> = trace_power(H, 2);";
    let c0 = "indexed morphism c0: Smooth<Plane, Line> = char_coefficient(S, 0);";
    let b = "indexed branch B: Branch<Plane> = simple(S, localize = x^2 + y^2, witness = frac(1, 2) * t, exponent = 1);";
    let cases = [
        (
            tr2,
            "trace_power(H, 2)",
            "trace_power(H, {})",
            "tr2",
            "/definition/power",
        ),
        (
            c0,
            "char_coefficient(S, 0)",
            "char_coefficient(S, {})",
            "c0",
            "/definition/index",
        ),
        (b, "exponent = 1", "exponent = {}", "B", "/exponent"),
    ];
    let messages = [
        "the power of `trace_power` has at most 64 decimal digits",
        "the index of `char_coefficient` has at most 64 decimal digits",
        "the exponent of `simple` has at most 64 decimal digits",
    ];
    for ((line, from, to, name, field), message) in cases.into_iter().zip(messages) {
        let wide = replaced(line, &line.replace(from, &to.replace("{}", &widest)));
        let raw = request(&wide, 9);
        let path = format!("{}{field}", pointer(&raw, name));
        assert_eq!(raw.pointer(&path).unwrap(), &json!(widest), "{name}");
        decoded(&kernel(&raw, "check"));
        let source = replaced(line, &line.replace(from, &to.replace("{}", &long)));
        let row = source.lines().position(|l| l.contains(&long)).unwrap() + 1;
        let column = source.lines().nth(row - 1).unwrap().find(&long).unwrap() + 1;
        rejected_at(
            &source,
            &format!("main.vast:{row}:{column}: E_LIMIT: {message}"),
        );
    }
}

/// The frontend checks no spectral rule: a repeated basis name, a rank beyond
/// `spectralRank`, an unknown basis name, ragged rows, a false `symmetric`
/// claim, a fiber name that clashes with a coordinate or a basis name, a
/// localization in the fiber coordinate, an exponent or a power beyond
/// `spectralPower`, a second object, and families in the wrong places all go
/// to the wire as written. The kernel decodes each and rejects it with its
/// own code and exact message.
#[test]
fn the_frontend_leaves_spectral_rules_to_the_kernel() {
    let v = "indexed free_module V: FreeModule<Plane> = basis(e1, e2);";
    let h = "indexed endomorphism H: Endomorphism<Plane> = rows((x, y), (y, -x)) of V symmetric;";
    let s = "indexed spectrum S: Spectrum<Plane> = eigen(H, t);";
    let b = "indexed branch B: Branch<Plane> = simple(S, localize = x^2 + y^2, witness = frac(1, 2) * t, exponent = 1);";
    let tr2 = "indexed morphism tr2: Smooth<Plane, Line> = trace_power(H, 2);";
    let act =
        "indexed primitive act = action_entry(Smooth, spectrum = S, element = t - 2, e1, e2);";
    let dl = "indexed primitive dl = branch_differential(Smooth, Cotangent, Line, branch = B);";
    let v_name = "`spectral_declarations::V`";
    let h_name = "`spectral_declarations::H`";
    let s_name = "`spectral_declarations::S`";
    let b_name = "`spectral_declarations::B`";
    let tr2_name = "`spectral_declarations::tr2`";
    // (line, replacement, field, wire value, code, message)
    let cases: Vec<(&str, &str, &str, Value, &str, String)> = vec![
        (
            v,
            "indexed free_module V: FreeModule<Plane> = basis(e1, e1);",
            "V/basis",
            json!(["e1", "e1"]),
            "E_SPECTRAL",
            format!("the free module {v_name} names the basis vector `e1` twice"),
        ),
        (
            v,
            "indexed free_module V: FreeModule<Plane> = basis(e1, e2, e3, e4, e5);",
            "V/basis",
            json!(["e1", "e2", "e3", "e4", "e5"]),
            "E_LIMIT",
            format!("the free module {v_name} has rank 5, beyond the limit of 4 (`spectralRank`)"),
        ),
        (
            v,
            "indexed free_module V: FreeModule<Plane, Pt> = basis(e1, e2);",
            "V/indices",
            json!([p("Plane"), p("Pt")]),
            "E_SPECTRAL",
            "a free module names one object, as in `FreeModule<X>`, but 2 are given".into(),
        ),
        (
            h,
            "indexed endomorphism H: Endomorphism<Plane> = rows((x, y, 1), (y)) of V;",
            "H/rows",
            json!([
                [coordinate("x"), coordinate("y"), n("1")],
                [coordinate("y")]
            ]),
            "E_SPECTRAL",
            format!(
                "the endomorphism {h_name} of the free module {v_name} of rank 2 needs 2 entries \
                 in each row, but row 1 has 3"
            ),
        ),
        (
            h,
            "indexed endomorphism H: Endomorphism<Plane> = rows((x, y), (x, y)) of V symmetric;",
            "H/rows",
            json!([
                [coordinate("x"), coordinate("y")],
                [coordinate("x"), coordinate("y")]
            ]),
            "E_SPECTRAL",
            format!(
                "the endomorphism {h_name} is declared `symmetric`, but its entry (e1, e2) differs \
                 from its entry (e2, e1)"
            ),
        ),
        (
            s,
            "indexed spectrum S: Spectrum<Plane> = eigen(H, x);",
            "S/fiber",
            json!("x"),
            "E_SPECTRAL",
            format!(
                "the fiber coordinate `x` of the spectrum {s_name} is a coordinate of \
                 `spectral_declarations::Plane`; `eigen(H, t)` needs a new name for the fiber coordinate"
            ),
        ),
        (
            s,
            "indexed spectrum S: Spectrum<Plane> = eigen(H, e1);",
            "S/fiber",
            json!("e1"),
            "E_SPECTRAL",
            format!(
                "the fiber coordinate `e1` of the spectrum {s_name} is a basis vector of the free \
                 module {v_name}; `eigen(H, t)` needs a new name for the fiber coordinate"
            ),
        ),
        (
            b,
            "indexed branch B: Branch<Plane> = simple(S, localize = t, witness = frac(1, 2) * t, exponent = 1);",
            "B/localize",
            coordinate("t"),
            "E_SPECTRAL",
            format!(
                "the localization of the branch {b_name} contains the fiber coordinate `t`; it is a \
                 polynomial in the coordinates of `spectral_declarations::Plane`"
            ),
        ),
        (
            b,
            "indexed branch B: Branch<Plane> = simple(S, localize = x^2 + y^2, witness = frac(1, 2) * t, exponent = 9);",
            "B/exponent",
            json!("9"),
            "E_LIMIT",
            format!(
                "the branch {b_name} has the exponent 9, beyond the limit of 8 (`spectralPower`)"
            ),
        ),
        (
            tr2,
            "indexed morphism tr2: Smooth<Plane, Line> = trace_power(H, 9);",
            "tr2/definition/power",
            json!("9"),
            "E_LIMIT",
            format!(
                "the `trace_power` declaration {tr2_name} takes the power 9, beyond the limit of 8 \
                 (`spectralPower`)"
            ),
        ),
        (
            tr2,
            "indexed morphism tr2: Smooth<Plane, Line> = trace_power(H, 0);",
            "tr2/definition/power",
            json!("0"),
            "E_SPECTRAL",
            format!(
                "the `trace_power` declaration {tr2_name} takes the power 0; `trace_power(H, k)` needs \
                 1 ≤ k ≤ 8"
            ),
        ),
        (
            act,
            "indexed primitive act = action_entry(Smooth, spectrum = S, element = t - 2, e3, e1);",
            "act/binding/row",
            json!("e3"),
            "E_SPECTRAL",
            format!(
                "`e3` is not a basis vector of the free module {v_name} of `action_entry`, whose basis \
                 is e1, e2"
            ),
        ),
        // The positional families are taken in wire order and never
        // reordered: with the line before the cotangent family, each lands
        // in the other's field.
        (
            dl,
            "indexed primitive dl = branch_differential(Smooth, Line, Cotangent, branch = B);",
            "dl/binding",
            json!({ "op": "branch_differential", "map_family": p("Smooth"),
                "cotangent": p("Line"), "line": p("Cotangent"), "branch": p("B") }),
            "E_TYPE",
            "the family `spectral_declarations::Line` of the `branch_differential` primitive \
             `spectral_declarations::dl` must have the representation `cotangent`"
                .into(),
        ),
    ];
    for (from, to, field, expected, code, message) in cases {
        let raw = request(&replaced(from, to), 9);
        let (name, rest) = field.split_once('/').unwrap();
        let path = format!("{}/{rest}", pointer(&raw, name));
        let mut sent = raw.pointer(&path).unwrap().clone();
        remove_spans(&mut sent);
        assert_eq!(sent, expected, "{to}");
        let response = kernel(&raw, "check");
        assert_eq!(response["ok"], false, "{to}: {response}");
        decoded(&response);
        let diagnostic = &response["diagnostics"][0];
        assert_eq!(diagnostic["code"], code, "{to}: {response}");
        assert_eq!(diagnostic["message"], message.as_str(), "{to}: {response}");
    }
}

/// Malformed Stage 5 sources are the frontend's `E_PARSE` at the offending
/// token, before any kernel check: the place is the line and column of the
/// first character of `context` in the changed line.
#[test]
fn malformed_spectral_sources_are_rejected_at_their_place() {
    let cases: &[(&str, &str, &str, &str)] = &[
        (
            "indexed primitive on = on_branch(Smooth, Line, branch = B);",
            "indexed primitive on = on_branch(Smooth, Line, B);",
            ", B)",
            "`on_branch` needs an explicit branch: write `branch = …`",
        ),
        (
            "indexed primitive ann = annihilates(Smooth, spectrum = S, element = t - 2);",
            "indexed primitive ann = annihilates(Smooth, spectrum = S);",
            ");",
            "`annihilates` needs an explicit element: write `element = …`",
        ),
        (
            "indexed primitive act = action_entry(Smooth, spectrum = S, element = t - 2, e1, e2);",
            "indexed primitive act = action_entry(Smooth, spectrum = S, element = t - 2, 0, 1);",
            "0, 1",
            "the row of `action_entry` is a basis name, as in `e1`",
        ),
        (
            "indexed branch B: Branch<Plane> = simple(S, localize = x^2 + y^2, witness = frac(1, 2) * t, exponent = 1);",
            "indexed branch B: Branch<Plane> = simple(S, localize = x^2 + y^2, witness = frac(1, 2) * t);",
            ");",
            "`simple` needs an explicit exponent: write `exponent = …`",
        ),
        (
            "indexed endomorphism H: Endomorphism<Plane> = rows((x, y), (y, -x)) of V symmetric;",
            "indexed endomorphism H: Endomorphism<Plane> = rows(x, y) of V symmetric;",
            "x, y",
            "an endomorphism row is a parenthesized tuple of entries, as in `rows((x, y), (y, -x))`",
        ),
        (
            "indexed spectrum S: Spectrum<Plane> = eigen(H, t);",
            "indexed spectrum S: Spectrum<Plane> = eigen(H, Plane::t);",
            "::t",
            "expected `)`, found `::`",
        ),
        (
            "indexed morphism tr2: Smooth<Plane, Line> = trace_power(H, 2);",
            "indexed morphism tr2: Smooth<Plane, Line> = trace_power(H, k);",
            "k)",
            "the power of `trace_power` is a natural literal, written as an unsigned integer",
        ),
    ];
    for (from, to, context, message) in cases {
        let source = replaced(from, to);
        assert_eq!(to.matches(context).count(), 1, "{to}: {context}");
        let row = source.lines().position(|line| line == *to).unwrap() + 1;
        let column = to.find(context).unwrap() + 1;
        rejected_at(
            &source,
            &format!("main.vast:{row}:{column}: E_PARSE: {message}"),
        );
    }
}

/// The Stage 5 words are reserved nowhere: programs that use them as names of
/// functions, parameters and bindings check as before.
#[test]
fn stage5_words_remain_names_through_the_kernel() {
    const WORDS: [&str; 20] = [
        "free_module",
        "endomorphism",
        "spectrum",
        "branch",
        "basis",
        "rows",
        "symmetric",
        "eigen",
        "simple",
        "localize",
        "witness",
        "exponent",
        "element",
        "trace_power",
        "char_coefficient",
        "annihilates",
        "action_entry",
        "on_branch",
        "branch_differential",
        "branch_projector",
    ];
    let functions: String = WORDS
        .iter()
        .map(|w| format!("fn {w}(n: Int) -> Int {{ n }}\n"))
        .collect();
    let calls: Vec<String> = WORDS.iter().map(|w| format!("{w}(1)")).collect();
    let named = format!("{functions}fn main() -> Int {{ {} }}\n", calls.join(" + "));
    let parameters: Vec<String> = WORDS.iter().map(|w| format!("{w}: Int")).collect();
    let lets: String = WORDS.iter().map(|w| format!("let {w} = 1; ")).collect();
    let bound = format!(
        "fn all({}) -> Int {{ {} }}\nfn main() -> Int {{ {lets}all({}) }}\n",
        parameters.join(", "),
        WORDS.join(" + "),
        WORDS.join(", ")
    );
    for source in [named, bound] {
        success(&common::check(&source, "names.vast"));
    }
}

/// The fiber coordinate of a spectrum is an identifier of the source grammar,
/// which excludes the strict keywords (#831). A protocol-9 request that names
/// a strict keyword as the fiber coordinate, which the frontend never sends,
/// is the kernel's `E_SPECTRAL`; the source is the frontend's `E_PARSE`. An
/// ordinary identifier, and a word that is a keyword only where a construct
/// spells it, are fiber coordinates in both.
#[test]
fn strict_keywords_are_no_fiber_coordinates() {
    // The module without the declarations that read the fiber coordinate `t`.
    let main: String = MAIN
        .lines()
        .filter(|line| {
            !line.starts_with("indexed branch") && !line.starts_with("indexed primitive")
        })
        .map(|line| format!("{line}\n"))
        .collect();
    let spectrum = "indexed spectrum S: Spectrum<Plane> = eigen(H, t);";
    let raw = request(&main, 9);
    let fiber = format!("{}/fiber", pointer(&raw, "S"));
    assert_eq!(raw.pointer(&fiber), Some(&json!("t")));
    let with_fiber = |name: &str| {
        let mut tampered = raw.clone();
        *tampered.pointer_mut(&fiber).unwrap() = json!(name);
        kernel(&tampered, "check")
    };
    for keyword in [
        "if", "fn", "let", "as", "true", "while", "return", "generic", "domain", "type", "subtype",
    ] {
        let response = with_fiber(keyword);
        assert_eq!(response["ok"], false, "{keyword}: {response}");
        decoded(&response);
        let diagnostic = &response["diagnostics"][0];
        assert_eq!(diagnostic["code"], "E_SPECTRAL", "{keyword}: {response}");
        assert_eq!(
            diagnostic["message"],
            format!(
                "the fiber coordinate `{keyword}` of the spectrum `spectral_declarations::S` is a strict \
                 keyword, not an identifier; `eigen(H, t)` names the fiber coordinate with a new identifier"
            ),
            "{keyword}: {response}"
        );
    }
    for name in ["lambda", "_t", "witness", "indexed", "eigen", "Ifs"] {
        let response = with_fiber(name);
        assert_eq!(response["ok"], true, "{name}: {response}");
    }
    // The source: a strict keyword is no name, and the other words are.
    let at = |to: &str| {
        let source: String = main
            .lines()
            .map(|line| if line == spectrum { to } else { line })
            .map(|line| format!("{line}\n"))
            .collect();
        let row = source.lines().position(|line| line == to).unwrap() + 1;
        (source, row)
    };
    let (source, row) = at("indexed spectrum S: Spectrum<Plane> = eigen(H, if);");
    rejected_at(
        &source,
        &format!("main.vast:{row}:48: E_PARSE: expected an identifier"),
    );
    for name in ["lambda", "witness"] {
        let (source, _) = at(&format!(
            "indexed spectrum S: Spectrum<Plane> = eigen(H, {name});"
        ));
        success(&package(&source).check_manifest("Vastitas.toml"));
    }
}

/// A failed gap identity shows a term of the remainder of W·χ′ − gᵉ modulo χ
/// that the kernel computed, with the names of the coordinates and the fiber
/// coordinate (#833). For H = diag(t, −t) with the fiber coordinate z,
/// χ = z² − t², and the witness z/2 gives W·χ′ − (t² + 1) = χ − 1: the
/// remainder is the constant −1. The localization t² is certified by the same
/// witness, and the witness z/2 + t leaves the remainder 2tz.
#[test]
fn a_failed_gap_identity_shows_a_term_of_its_remainder() {
    let header: String = MAIN
        .lines()
        .take_while(|line| !line.starts_with("indexed free_module"))
        .map(|line| format!("{line}\n"))
        .collect();
    let branch = |localize: &str, witness: &str| {
        format!(
            "{header}indexed affine T(SmoothR) = Affine(1)[t];\n\
             indexed free_module VT: FreeModule<T> = basis(e1, e2);\n\
             indexed endomorphism D: Endomorphism<T> = rows((t, 0), (0, -t)) of VT symmetric;\n\
             indexed spectrum SD: Spectrum<T> = eigen(D, z);\n\
             indexed branch BD: Branch<T> = simple(SD, localize = {localize}, witness = {witness}, exponent = 1);\n\
             fn main() -> Int {{ 42 }}\n"
        )
    };
    let row = |source: &str| {
        source
            .lines()
            .position(|line| line.starts_with("indexed branch BD"))
            .unwrap()
            + 1
    };
    let failure = "E_SPECTRAL: the witness of the branch `spectral_declarations::BD` does not certify the \
                   gap: W·χ′ − g^e is not a multiple of the characteristic polynomial χ; its remainder \
                   modulo χ";
    let constant = branch("t^2 + 1", "frac(1, 2) * z");
    rejected_at(
        &constant,
        &format!("main.vast:{}:1: {failure} is `-1`", row(&constant)),
    );
    let linear = branch("t^2", "frac(1, 2) * z + t");
    rejected_at(
        &linear,
        &format!("main.vast:{}:1: {failure} is `2 * t * z`", row(&linear)),
    );
    success(&package(&branch("t^2", "frac(1, 2) * z")).check_manifest("Vastitas.toml"));
}
