//! Adversarial schema mutations at the public kernel boundary.
mod common;

use common::{kernel, request};
use serde_json::{Value, json};
use std::collections::BTreeMap;

/// The fewest record shapes that the sweeps of the flat requests and of the
/// captured package requests exercise: a little below the 97 and 694 that
/// they reach, so that a sweep that loses its records fails.
const MIN_FLAT_SHAPES: usize = 90;
const MIN_CAPTURED_SHAPES: usize = 650;

/// The shape of a record: its keys and its `kind` and `op` tags.
fn shape(fields: &serde_json::Map<String, Value>) -> String {
    format!(
        "{:?}:{:?}:{:?}",
        fields.keys().collect::<Vec<_>>(),
        fields.get("kind"),
        fields.get("op")
    )
}

// Select a representative of every distinct record shape/tag. This avoids
// rerunning identical span mutations for every scalar leaf in a source file.
fn record_paths(value: &Value, path: &str, records: &mut BTreeMap<String, String>) {
    match value {
        Value::Object(fields) => {
            records
                .entry(shape(fields))
                .or_insert_with(|| path.to_string());
            for (name, child) in fields {
                let escaped = name.replace('~', "~0").replace('/', "~1");
                record_paths(child, &format!("{path}/{escaped}"), records);
            }
        }
        Value::Array(items) => {
            for (index, child) in items.iter().enumerate() {
                record_paths(child, &format!("{path}/{index}"), records);
            }
        }
        _ => {}
    }
}

/// The sweep over the requests that the frontend writes for flat units: the
/// examples with their observations, a program with the legacy geometry, a
/// dispatch program and the abstract contracts. Every record shape rejects
/// an unknown field, the top-level envelope included.
#[test]
fn flat_requests_reject_unknown_fields_in_every_nested_record_shape() {
    let geometric = format!(
        "{}\nfn preserve_map(X: Scheme, f: Morphism<X, X>) -> Morphism<X, X> {{ f }}",
        include_str!("../examples/pointed.vast")
    );
    let mut cases = Vec::new();
    for source in [
        include_str!("../examples/functions.vast").to_string(),
        include_str!("../examples/pairs.vast").to_string(),
        geometric,
        "fn empty() -> Unit { { () } } generic f(x) { domain (Int); } method f(x: Int) -> Int { x } fn main() -> Int { f(0) }".to_string(),
        include_str!("../examples/abstract-contracts.vast").to_string(),
    ] {
        cases.push(request(&source, "shape.vast"));
    }
    let mut mutated = 0;
    for raw in cases {
        let baseline = kernel(&raw, "check");
        assert_eq!(baseline["ok"], true, "{baseline}\n{raw}");
        let mut records = BTreeMap::new();
        record_paths(&raw, "", &mut records);
        for path in records.values() {
            let mut changed = raw.clone();
            changed.pointer_mut(path).unwrap()["forged_authority"] = json!("untrusted");
            let response = kernel(changed, "emit");
            assert_eq!(response["version"], raw["version"], "{response}");
            assert_eq!(response["ok"], false, "accepted {path}: {response}");
            common::assert_wire_rejected(&response, "E_PROTOCOL");
            assert!(
                response["diagnostics"][0]["message"]
                    .as_str()
                    .unwrap()
                    .contains("forged_authority")
            );
            assert!(response.get("lean_source").is_none());
            mutated += 1;
        }
    }
    assert!(
        mutated >= MIN_FLAT_SHAPES,
        "only {mutated} record shapes were exercised"
    );
}

// #557: the same sweep over the public decoder, using wires the actual
// frontend sends for indexed, resource, numerical, tree, network, storage and
// named-recipient edit programs.
#[test]
fn public_decoder_rejects_unknown_fields_in_every_captured_record_shape() {
    // The promotion example depends on the generated stdlib package.
    common::prepare_stdlib_package();
    let examples = common::root().join("examples/packages");
    let mut cases: Vec<(String, Value)> = Vec::new();
    for package in [
        "indexed",
        // Its stdlib dependency declares Stage 2 presented affine geometry.
        "promotion",
        "resource-values",
        "numerical",
        "runtime-shapes",
        "tensor-packing",
        "contraction-tree",
        "finite_network",
        "storage/app",
        "edit-borrow/app",
        "edit-authority/app",
        "smooth-objects",
        "smooth-cotangent",
        "smooth-metric",
        "smooth-differential",
    ] {
        let mut command = common::cli();
        command
            .args(["check", "--manifest-path"])
            .arg(examples.join(package).join("Vastitas.toml"));
        let wire = common::captured_wire(command, common::CURRENT_PROTOCOL);
        cases.push((package.to_string(), wire));
    }
    let recipients: Value =
        serde_json::from_str(include_str!("fixtures/edit-recipients.json")).unwrap();
    assert_eq!(recipients["version"], common::CURRENT_PROTOCOL);
    cases.push(("edit-recipients fixture".into(), recipients));
    let mut forgeries = Vec::new();
    for (name, raw) in &cases {
        let baseline = kernel(raw, "check");
        assert_eq!(baseline["ok"], true, "{name}: {baseline}");
        let mut records = BTreeMap::new();
        record_paths(raw, "", &mut records);
        for path in records.into_values() {
            let mut changed = raw.clone();
            changed.pointer_mut(&path).unwrap()["forged_authority"] = json!("untrusted");
            forgeries.push((name.as_str(), raw["version"].clone(), path, changed));
        }
    }
    assert!(
        forgeries.len() >= MIN_CAPTURED_SHAPES,
        "only {} record shapes were exercised",
        forgeries.len()
    );
    // The kernel runs are independent; share them across a few threads.
    let workers = std::thread::available_parallelism().map_or(4, |n| n.get().min(8));
    let chunk = forgeries.len().div_ceil(workers);
    std::thread::scope(|scope| {
        for part in forgeries.chunks(chunk) {
            scope.spawn(move || {
                for (name, version, path, changed) in part {
                    let response = kernel(changed, "emit");
                    assert_eq!(&response["version"], version, "{name} {path}: {response}");
                    common::assert_wire_rejected(&response, "E_PROTOCOL");
                    let message = response["diagnostics"][0]["message"].as_str().unwrap();
                    // A one-key tagged union reports the extra key as a second tag.
                    let tagged = path.ends_with("/representation")
                        && message == "expected exactly one concrete representation";
                    assert!(
                        message.contains("forged_authority") || tagged,
                        "{name} {path}: {response}"
                    );
                }
            });
        }
    });
}

// #759: the frame and `nature::dimension` records, in the wire
// that the frontend sends for `tests/fixtures/frame-dimension-declarations`.
// Records of one shape can have different decoders (the Gram matrix of a
// metric and of a physical metric), so the sweep also keeps one
// representative per shape and declaration kind. The kernel accepts the
// baseline; every forged field is a decoder rejection.
#[test]
fn frame_and_nature_records_reject_unknown_fields() {
    let mut command = common::cli();
    command
        .args(["check", "--manifest-path"])
        .arg(common::root().join("tests/fixtures/frame-dimension-declarations/Vastitas.toml"));
    let raw = common::captured_wire(command, common::CURRENT_PROTOCOL);
    let baseline = kernel(&raw, "check");
    assert!(baseline["ok"] == true, "{baseline}");
    let mut records = BTreeMap::new();
    record_paths(&raw, "", &mut records);
    let base = "/packages/0/modules/0/indexed_declarations";
    for (index, declaration) in raw
        .pointer(base)
        .unwrap()
        .as_array()
        .unwrap()
        .iter()
        .enumerate()
    {
        let mut own = BTreeMap::new();
        record_paths(declaration, &format!("{base}/{index}"), &mut own);
        for (record, path) in own {
            records
                .entry(format!("{}/{record}", declaration["kind"]))
                .or_insert(path);
        }
    }
    // Each Stage 4 record shape, under the declaration kind that holds it.
    let header = json!({"kind": null, "name": null, "public": null, "span": null});
    let declaration = |kind: &str, fields: &[&str]| {
        let mut record = header.as_object().unwrap().clone();
        record.insert("kind".into(), json!(kind));
        for field in fields {
            record.insert((*field).into(), Value::Null);
        }
        format!("{:?}/{}", kind, shape(&record))
    };
    let nested =
        |kind: &str, record: Value| format!("{kind:?}/{}", shape(record.as_object().unwrap()));
    for expected in [
        declaration("family", &["parameters", "constraints", "representation"]),
        nested("family", json!({"kind": "frame", "family": null})),
        declaration("frame", &["family", "indices", "columns", "inverse"]),
        nested("frame", json!({"kind": "columns", "columns": null})),
        nested("frame", json!({"kind": "coordinates"})),
        declaration("base_dimension", &[]),
        declaration("quantity", &["dimension"]),
        nested("quantity", json!({"base": null, "exponent": null})),
        declaration("reading", &["family", "indices", "quantities"]),
        nested("reading", json!({"coordinate": null, "quantity": null})),
        declaration("scale", &["quantity", "magnitude"]),
        nested(
            "scale",
            json!({"op": "fraction", "numerator": null, "denominator": null}),
        ),
        declaration(
            "physical_metric",
            &["family", "indices", "metric", "reading", "value", "entries"],
        ),
        nested("physical_metric", json!({"kind": "euclidean"})),
        nested("physical_metric", json!({"kind": "gram", "rows": null})),
        nested(
            "physical_metric",
            json!({"kind": "normalized", "scales": null}),
        ),
        nested(
            "physical_metric",
            json!({"coefficient": null, "factors": null}),
        ),
        nested("physical_metric", json!({"scale": null, "exponent": null})),
        nested(
            "physical_metric",
            json!({"coordinate": null, "scale": null}),
        ),
        nested("physical_metric", json!({"base": null, "exponent": null})),
        nested("physical_metric", json!({"op": "neg", "operand": null})),
    ] {
        assert!(records.contains_key(&expected), "no record {expected}");
    }
    let paths: std::collections::BTreeSet<String> = records.into_values().collect();
    for path in &paths {
        let mut changed = raw.clone();
        changed.pointer_mut(path).unwrap()["forged_authority"] = json!("untrusted");
        let response = kernel(changed, "emit");
        assert_eq!(
            response["version"],
            common::CURRENT_PROTOCOL,
            "{path}: {response}"
        );
        common::assert_wire_rejected(&response, "E_PROTOCOL");
        let message = response["diagnostics"][0]["message"].as_str().unwrap();
        let tagged = path.ends_with("/representation")
            && message == "expected exactly one concrete representation";
        assert!(
            message.contains("forged_authority") || tagged,
            "{path}: {response}"
        );
    }
}

/// The envelope admits no unknown field, also at the top level of a flat
/// unit's request, and the kernel checks the scalar of a subtype before its
/// authority analysis.
#[test]
fn the_envelope_admits_no_hint_and_checks_membership_scalars() {
    let mut raw = request("fn main() -> Int { 0 }", "shape.vast");
    assert_eq!(kernel(&raw, "check")["ok"], true);
    raw["untrusted_hint"] = json!({"owner":"forged", "checked":true});
    let response = kernel(raw, "check");
    common::assert_wire_rejected(&response, "E_PROTOCOL");
    assert_eq!(
        response["diagnostics"][0]["message"],
        "unknown protocol field 'untrusted_hint'"
    );
    let mut raw = request(
        "abstract type B; subtype Int <: B; fn main() -> Int { 0 }",
        "shape.vast",
    );
    common::flat_module(&mut raw)["subtypes"][0]["scalar"] = json!("Float");
    let response = kernel(raw, "check");
    common::assert_wire_rejected(&response, "E_TYPE");
    assert!(
        response["diagnostics"][0]["message"]
            .as_str()
            .unwrap()
            .contains("Nat, Int, Bool, or Unit")
    );
}

#[test]
fn malformed_versions_and_non_utf8_input_return_protocol_json() {
    for version in [
        Value::Null,
        json!("6"),
        json!(-1),
        json!(1.5),
        json!({}),
        json!([]),
    ] {
        let response = kernel(json!({"version":version}), "check");
        assert_eq!(response["version"], common::CURRENT_PROTOCOL, "{response}");
        common::assert_wire_rejected(&response, "E_PROTOCOL");
        assert!(
            response["diagnostics"][0]["message"]
                .as_str()
                .unwrap()
                .contains("version must be a natural number")
        );
    }
    common::assert_wire_rejected(&kernel(json!({}), "check"), "E_PROTOCOL");
    for mode in ["check", "emit"] {
        let mut input =
            format!("{{\"version\":{},\"file\":\"", common::CURRENT_PROTOCOL).into_bytes();
        input.extend_from_slice(b"\xff\"}");
        let result = common::kernel_bytes(mode, input);
        assert!(!result.status.success());
        assert!(result.stderr.is_empty(), "{result:?}");
        let response: Value = serde_json::from_slice(&result.stdout).unwrap();
        assert_eq!(response["version"], common::CURRENT_PROTOCOL);
        common::assert_wire_rejected(&response, "E_PROTOCOL");
    }
}

/// The package requests that carry `legacy_geometry: true`, with which the
/// kernel appends the compatibility profile of the legacy geometry (#533),
/// are exactly those without a record of the indexed envelope. No other
/// program carries the field, no request carries `input`, and the kernel
/// accepts every request.
#[test]
fn package_requests_carry_legacy_geometry_exactly_without_indexed_records() {
    common::prepare_stdlib_package();
    let s = common::Scratch::empty("legacy geometry field");
    let packages = [
        // Programs without a record of the indexed envelope, the last one
        // with the legacy geometry.
        ("plain", "fn main() -> Int { 0 }", "", true),
        (
            "abstract",
            "pub abstract type Numeric;\nsubtype Int <: Numeric;\ngeneric f(x) { domain (Int); }\nmethod f(x: Numeric) -> Int { 0 }\nfn main() -> Int { f(1) }",
            "",
            true,
        ),
        (
            "assembled",
            "pub generic g(x) { domain (Int); }\ncontribution c : g { method g(x: Int) -> Int { x } }\nassembly {\n  apply c;\n  seal g;\n}\nfn main() -> Int { g(42) }",
            "",
            true,
        ),
        (
            "legacy",
            "fn main() -> Int {\n    let X = Affine(QQ, 2);\n    int(dim(X)) - 2\n}",
            "",
            true,
        ),
        // Programs with a record of the indexed envelopes.
        (
            "observed",
            "fn main() -> Int { let x = show!(1); x - 1 }",
            "",
            false,
        ),
        (
            "resource",
            "resource fn main() -> Int { value { 0 } }",
            "",
            false,
        ),
        (
            "app",
            "pub generic g(x) { domain (Int); }\npub grant spare : g to app::a { domain (Int); }\npub mod a {}\ncontribution c : g { method g(x: Int) -> Int { x } }\nassembly {\n  apply c;\n  seal g;\n}\nfn main() -> Int { g(42) }",
            "",
            false,
        ),
        (
            "indexed",
            "pub indexed marker Tag;\nfn main() -> Int { 0 }",
            "",
            false,
        ),
        (
            "library",
            "fn main() -> Int {\n    let X = Affine(QQ, 2);\n    int(dim(X)) - 2\n}",
            "std = { path = '../stdlib' }",
            false,
        ),
    ];
    s.copy_stdlib(&common::STDLIB_PACKAGES, &[]);
    for (name, source, dependencies, flagged) in packages {
        s.write_package(name, source, dependencies);
        let wire = s.captured(&format!("{name}/Vastitas.toml"), common::CURRENT_PROTOCOL);
        assert!(wire.get("input").is_none(), "{name}: {wire}");
        if flagged {
            assert_eq!(wire["legacy_geometry"], true, "{name}: {wire}");
        } else {
            assert!(wire.get("legacy_geometry").is_none(), "{name}: {wire}");
        }
        let response = kernel(&wire, "check");
        assert_eq!(response["ok"], true, "{name}: {response}");
    }
}

/// The driver writes every flat unit, also with a `--lib` input and with
/// `show!`, as one package with `legacy_geometry: true` (#533), and the kernel
/// accepts it.
#[test]
fn flat_requests_carry_legacy_geometry() {
    let s = common::Scratch::empty("legacy geometry flat");
    s.write("lib.vast", "fn one() -> Int { 1 }");
    for (file, source, libraries) in [
        ("flat.vast", "fn main() -> Int { 0 }", &[][..]),
        (
            "with_lib.vast",
            "fn main() -> Int { one() - 1 }",
            &["lib.vast"][..],
        ),
        (
            "shown.vast",
            "fn main() -> Int { let X = Affine(QQ, 2); let d = show!(dim(X)); int(d) - 2 }",
            &[][..],
        ),
    ] {
        s.write(file, source);
        let mut command = s.cli();
        command.args(["check", file]);
        for library in libraries {
            command.args(["--lib", library]);
        }
        let wire = common::captured_wire(command, common::CURRENT_PROTOCOL);
        assert!(wire.get("input").is_none(), "{file}: {wire}");
        assert_eq!(wire["root"], "vastitas:compat:flat", "{file}: {wire}");
        assert_eq!(wire["legacy_geometry"], true, "{file}: {wire}");
        let response = kernel(&wire, "check");
        assert_eq!(response["ok"], true, "{file}: {response}");
    }
}
