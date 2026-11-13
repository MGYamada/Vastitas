//! Stage 4 (#759) frame and `nature::dimension` declarations through the
//! public protocol-9 source path. The frontend parses each form into the wire
//! record that the kernel decodes; these tests capture the wire, check the
//! protocol it selects and submit it to the kernel, which checks them.
mod common;
use common::{Scratch, assert_wire_rejected, cli, kernel, remove_spans, success};
use serde_json::{Value, json};

const MANIFEST: &str = include_str!("fixtures/frame-dimension-declarations/Vastitas.toml");
const MAIN: &str = include_str!("fixtures/frame-dimension-declarations/main.vast");

fn package(main: &str) -> Scratch {
    let s = Scratch::empty("frame dimension declarations");
    s.write("Vastitas.toml", MANIFEST);
    s.write("main.vast", main);
    s
}

fn check(s: &Scratch) -> std::process::Output {
    cli()
        .current_dir(&s.0)
        .args(["check", "--manifest-path", "Vastitas.toml"])
        .output()
        .unwrap()
}

/// The wire that the frontend sends for `s`, which must use `version`.
#[track_caller]
fn request(s: &Scratch, version: u64) -> Value {
    let mut command = cli();
    command
        .current_dir(&s.0)
        .args(["check", "--manifest-path", "Vastitas.toml"]);
    common::captured_wire(command, version)
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

fn p(name: &str) -> Value {
    json!({ "path": [name] })
}

/// The kernel decodes the whole request and accepts the valid program.
#[track_caller]
fn decoded(response: &Value) {
    assert!(response["ok"] == true, "{response}");
}

/// Each declaration form alone in a package, with the frontend's only other
/// item `fn main`. Paths are unresolved on the wire; the kernel resolves them.
const LONE_FORMS: &[&str] = &[
    "indexed family Frame(object(CInfAffine)) = frame constraints(canonical(0));",
    "indexed family Coords(frame(Frame)) = frame_vector;",
    "indexed family CoCoords(frame(Frame)) = frame_covector;",
    "indexed family FrameMap(frame(Frame), frame(Frame)) = frame_map;",
    // A frame parameter alone makes a family a Stage 4 form.
    "indexed family Tokens(frame(Frame)) = token constraints();",
    "indexed family Reading(object(CInfAffine)) = reading constraints(canonical(0));",
    "indexed family PhysicalMetric(object(CInfAffine)) = physical_metric constraints(canonical(0));",
    "indexed frame b: Frame<X> = columns((1, 0), (1, 2));",
    "indexed frame e: Frame<X> = coordinates;",
    "indexed base_dimension L;",
    "indexed quantity Ratio = 1;",
    "indexed reading phys: Reading<C> = (x: Length, t: Time);",
    "indexed scale l0 = 3 of Length;",
    "indexed physical PE: PhysicalMetric<C> = interpret(E, reading = phys, euclidean);",
];

/// A package with a frame or nature declaration uses protocol 9, and only
/// there do the records decode: protocols 7 and 8 reject them.
#[test]
fn frame_and_nature_declarations_select_protocol_nine_only() {
    // Without a Stage 4 declaration, an indexed package uses protocol 7.
    request(&package("indexed marker M;\nfn main() -> Int { 0 }\n"), 7);
    for form in LONE_FORMS {
        let raw = request(&package(&format!("{form}\nfn main() -> Int {{ 0 }}\n")), 9);
        // The record decodes in protocol 9; its unresolved paths are the
        // kernel's next rejection.
        let response = kernel(&raw, "check");
        assert_ne!(
            response["diagnostics"][0]["code"], "E_PROTOCOL",
            "{form}: {response}"
        );
        for version in [7, 8] {
            let mut older = raw.clone();
            older["version"] = json!(version);
            assert_wire_rejected(&kernel(older, "emit"), "E_PROTOCOL");
        }
    }
}

/// The frontend sends the declarations of the fixture as their documented
/// wire records, with the common fields of every indexed declaration.
#[test]
fn the_fixture_wire_carries_the_frame_and_nature_records() {
    let raw = request(&package(MAIN), 9);
    let n = |value: &str| json!({ "op": "natural", "value": value });
    let record = |name: &str| {
        let mut value = declaration(&raw, name).clone();
        assert!(value["span"].is_object(), "{name}");
        remove_spans(&mut value);
        value
    };
    assert_eq!(
        record("Coords"),
        json!({ "kind": "family", "name": "Coords", "public": false,
            "parameters": [{ "kind": "frame", "family": p("Frame") }],
            "constraints": [], "representation": "frame_vector" })
    );
    assert_eq!(
        record("r"),
        json!({ "kind": "frame", "name": "r", "public": false,
            "family": p("Frame"), "indices": [p("Plane")],
            "columns": { "kind": "columns", "columns": [
                [n("1"), n("0")], [{ "op": "coordinate", "name": "x" }, n("2")]] },
            "inverse": { "kind": "columns", "columns": [
                [n("1"), n("0")],
                [{ "op": "product", "factors": [
                    { "op": "fraction", "numerator": "-1", "denominator": "2" },
                    { "op": "coordinate", "name": "x" }] },
                 { "op": "fraction", "numerator": "1", "denominator": "2" }]] } })
    );
    assert_eq!(
        record("z"),
        json!({ "kind": "frame", "name": "z", "public": false,
            "family": p("Frame"), "indices": [p("Pt")],
            "columns": { "kind": "columns", "columns": [] }, "inverse": null })
    );
    assert_eq!(record("e")["columns"], json!({ "kind": "coordinates" }));
    assert_eq!(
        record("L"),
        json!({ "kind": "base_dimension", "name": "L", "public": false })
    );
    assert_eq!(
        record("Speed")["dimension"],
        json!([{ "base": p("L"), "exponent": "1" }, { "base": p("T"), "exponent": "-1" }])
    );
    assert_eq!(record("Ratio")["dimension"], json!([]));
    assert_eq!(
        record("phys"),
        json!({ "kind": "reading", "name": "phys", "public": false,
            "family": p("Reading"), "indices": [p("Chart")],
            "quantities": [{ "coordinate": "x", "quantity": p("Length") },
                { "coordinate": "t", "quantity": p("Time") }] })
    );
    assert_eq!(
        record("h"),
        json!({ "kind": "scale", "name": "h", "public": false, "quantity": p("Length"),
            "magnitude": { "op": "fraction", "numerator": "1", "denominator": "2" } })
    );
    let one = json!({ "coefficient": n("1"), "factors": [] });
    let zero = json!({ "coefficient": n("0"), "factors": [] });
    assert_eq!(
        record("PM"),
        json!({ "kind": "physical_metric", "name": "PM", "public": false,
            "family": p("PhysicalMetric"), "indices": [p("Chart")],
            "metric": p("M"), "reading": p("phys"),
            "value": [{ "base": p("L"), "exponent": "2" }],
            "entries": { "kind": "gram", "rows": [
                [one, zero],
                [zero, { "coefficient": { "op": "neg", "operand": n("1") },
                    "factors": [{ "scale": p("c"), "exponent": "2" }] }]] } })
    );
    assert_eq!(record("PN")["value"], json!([]));
    assert_eq!(
        record("PN")["entries"],
        json!({ "kind": "normalized", "scales": [
            { "coordinate": "x", "scale": p("l0") }, { "coordinate": "t", "scale": p("t0") }] })
    );
    assert_eq!(record("PE")["entries"], json!({ "kind": "euclidean" }));
}

/// The kernel decodes and accepts the whole fixture, and also the fixture
/// without its frames.
#[test]
fn the_kernel_decodes_the_frame_and_nature_records() {
    let raw = request(&package(MAIN), 9);
    decoded(&kernel(&raw, "check"));
    let frameless: String = MAIN
        .lines()
        .filter(|line| !line.starts_with("indexed frame "))
        .map(|line| format!("{line}\n"))
        .collect();
    assert_eq!(MAIN.lines().count() - frameless.lines().count(), 4);
    decoded(&kernel(request(&package(&frameless), 9), "check"));
}

/// The kernel checks frame and nature declarations, and the fixture is a valid
/// program.
#[test]
fn the_fixture_checks_once_the_kernel_checks_frames_and_dimensions() {
    success(&check(&package(MAIN)));
}

/// The Stage 4 words are reserved nowhere: programs that use them as names of
/// functions, parameters and bindings check as before.
#[test]
fn stage4_words_remain_names_through_the_kernel() {
    const WORDS: [&str; 14] = [
        "frame",
        "quantity",
        "reading",
        "scale",
        "physical",
        "base_dimension",
        "columns",
        "coordinates",
        "inverse",
        "interpret",
        "normalized",
        "euclidean",
        "of",
        "value",
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
