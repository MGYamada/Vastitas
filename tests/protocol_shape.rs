//! Adversarial schema mutations at the actual legacy/public kernel boundary.
mod common;

use common::{kernel, request};
use serde_json::{Value, json};
use std::collections::BTreeMap;

fn package(flat: &Value, version: u64) -> Value {
    let mut module = json!({
        "path": [], "public": true,
        "span": {"start":0,"end":1,"line":1,"column":1}, "imports": [],
        "functions":flat["functions"], "generics":flat["generics"], "methods":flat["methods"]
    });
    for kind in ["functions", "generics"] {
        for declaration in module[kind].as_array_mut().unwrap() {
            declaration["public"] = json!(false);
        }
    }
    if version >= 4 {
        for kind in ["abstract_types", "subtypes", "abstract_methods"] {
            module[kind] = flat.get(kind).cloned().unwrap_or_else(|| json!([]));
        }
        for declaration in module["abstract_types"].as_array_mut().unwrap() {
            declaration["public"] = json!(false);
        }
    }
    if version >= 5 {
        module["grants"] = json!([]);
        module["contributions"] = json!([]);
        module["assembly"] = json!({"events":[],"span":module["span"]});
    }
    if version >= 6 {
        module["delegations"] = json!([]);
        module["transfers"] = json!([]);
    }
    let mut raw = json!({"version":version,"file":"shape.vast","root":"/shape/Vastitas.toml",
        "packages":[{"source":"/shape/Vastitas.toml","name":"shape","version":"0.1.0",
            "dependencies":[],"modules":[module]}]});
    if version >= 4 {
        raw["input"] = json!("package");
    }
    raw
}

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

// old-route(#533): sweeps the legacy decoders of protocols 2 to 6.
#[test]
fn legacy_decoders_reject_unknown_fields_in_every_nested_record_shape() {
    let geometric = format!(
        "{}\nfn preserve_map(X: Scheme, f: Morphism<X, X>) -> Morphism<X, X> {{ f }}",
        include_str!("../examples/pointed.vast")
    );
    // The examples observe values with `show!`, which only protocol 9 carries
    // (#836); without the observations they are flat requests of protocols 2
    // and 4.
    let flat_example = |source: &str| common::checked_replace(source, "show!(", "(");
    let mut cases = Vec::new();
    for source in [
        flat_example(include_str!("../examples/functions.vast")),
        flat_example(include_str!("../examples/pairs.vast")),
        geometric,
        "fn empty() -> Unit { { () } } generic f(x) { domain (Int); } method f(x: Int) -> Int { x } fn main() -> Int { f(0) }".to_string(),
        flat_example(include_str!("../examples/abstract-contracts.vast")),
    ] {
        let flat = request(&source, "shape.vast");
        cases.push(flat.clone());
        for version in 3..=6 {
            if version == 3 && flat["version"] == 4 {
                continue;
            }
            cases.push(package(&flat, version));
        }
    }
    let mut mutated = 0;
    for raw in cases {
        let baseline = kernel(&raw, "check");
        assert_eq!(baseline["ok"], true, "{baseline}\n{raw}");
        let mut records = BTreeMap::new();
        record_paths(&raw, "", &mut records);
        for path in records.values() {
            if path.is_empty() && raw["version"] == 2 {
                continue; // Only v2's top-level hint tolerance is intentional.
            }
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
        mutated >= 300,
        "only {mutated} record shapes were exercised"
    );
}

// old-route(#533): keeps a protocol-7 (`Indexed.Wire`) request in the sweep.
/// The promotion example against a copy of the stdlib without its Stage 2
/// `scheme::affine` module, its Stage 3 `smooth::affine` and `metric`
/// modules and `differential` package, its Stage 4 `frame` module and its
/// Stage 5 `linalg` package. That
/// closure still uses protocol 7, so the Indexed.Wire sweep keeps the
/// geometry-compatibility, dependency and function-body records that only the
/// stdlib supplies.
fn promotion_without_affine() -> Value {
    let root = common::root();
    let stdlib = root.join("stdlib");
    let s = common::Scratch::empty("protocol seven stdlib");
    // Remove the line `line` of the copied file `path`, which must have it.
    let strip = |path: &str, line: &str| {
        let text = std::fs::read_to_string(stdlib.join(path)).unwrap();
        assert!(text.contains(line), "{path} lacks {line:?}");
        s.write(&format!("stdlib/{path}"), &text.replace(line, ""));
    };
    // Copy the generated package and every geometry source except the Stage 2
    // and Stage 3 modules, so new stdlib modules are picked up without editing
    // this list.
    s.copy_stdlib(
        &["target/package", "src/geometry"],
        &[
            "src/geometry/scheme/affine",
            "src/geometry/smooth/affine",
            "src/geometry/metric",
            "src/geometry/frame",
        ],
    );
    strip(
        "Vastitas.toml",
        "differential_library = { path = \"src/differential\" }\nlinalg_library = { path = \"src/linalg\" }\n",
    );
    strip("src/geometry/scheme/mod.vast", "pub mod affine;\n");
    strip("src/geometry/smooth/mod.vast", "pub mod affine;\n");
    strip("src/geometry/mod.vast", "pub mod metric;\npub mod frame;\n");
    strip(
        "target/package/lib.vast",
        "pub use differential_library as differential;\npub use linalg_library as linalg;\n",
    );
    let example = root.join("examples/packages/promotion");
    s.write(
        "app/Vastitas.toml",
        &std::fs::read_to_string(example.join("Vastitas.toml"))
            .unwrap()
            .replace("../../../stdlib", "../stdlib"),
    );
    // Without its observation (#836), which only protocol 9 carries.
    s.write(
        "app/main.vast",
        &common::checked_replace(
            &std::fs::read_to_string(example.join("main.vast")).unwrap(),
            "show!(",
            "(",
        ),
    );
    common::captured_wire(
        common::manifest_command("check", s.0.join("app/Vastitas.toml")),
        7,
    )
}

// #557: the same sweep over the public Indexed.Wire (7) and ResourceSource.Wire
// (8/9) decoders, using wires the actual frontend sends for indexed, resource,
// numerical, tree, network, storage and named-recipient edit programs.
#[test]
fn public_decoders_reject_unknown_fields_in_every_captured_v7_to_v9_record_shape() {
    // The promotion example depends on the generated stdlib package.
    common::prepare_stdlib_package();
    let examples = common::root().join("examples/packages");
    // The indexed example observes its result with `show!`, which only
    // protocol 9 carries (#836); without the observation it is the protocol-7
    // fixture.
    let indexed = common::Scratch::empty("protocol seven indexed");
    indexed.copy_sources(&examples.join("indexed"), "", &[]);
    indexed.write(
        "main.vast",
        &common::checked_replace(
            &std::fs::read_to_string(indexed.0.join("main.vast")).unwrap(),
            "show!(",
            "(",
        ),
    );
    let mut cases: Vec<(String, Value)> = Vec::new();
    // Each package with the protocol that the frontend writes for it and, for
    // a program that the frontend wrote as protocol 8 before #533 round 1, a
    // copy at that protocol.
    // old-route(#533): the copies at protocol 8 retire at the cutover.
    for (package, version, old) in [
        ("indexed", 7, None),
        // Its stdlib dependency declares Stage 2 presented affine geometry.
        ("promotion", common::CURRENT_PROTOCOL, None),
        ("resource-values", common::CURRENT_PROTOCOL, Some(8)),
        ("numerical", common::CURRENT_PROTOCOL, Some(8)),
        ("runtime-shapes", common::CURRENT_PROTOCOL, Some(8)),
        ("tensor-packing", common::CURRENT_PROTOCOL, Some(8)),
        ("contraction-tree", common::CURRENT_PROTOCOL, Some(8)),
        ("finite_network", common::CURRENT_PROTOCOL, Some(8)),
        ("storage/app", common::CURRENT_PROTOCOL, Some(8)),
        ("edit-borrow/app", common::CURRENT_PROTOCOL, None),
        ("edit-authority/app", common::CURRENT_PROTOCOL, None),
        ("smooth-objects", common::CURRENT_PROTOCOL, None),
        ("smooth-cotangent", common::CURRENT_PROTOCOL, None),
        ("smooth-metric", common::CURRENT_PROTOCOL, None),
        ("smooth-differential", common::CURRENT_PROTOCOL, None),
    ] {
        let manifest = if package == "indexed" {
            indexed.0.join("Vastitas.toml")
        } else {
            examples.join(package).join("Vastitas.toml")
        };
        let mut command = common::cli();
        command.args(["check", "--manifest-path"]).arg(manifest);
        let wire = common::captured_wire(command, version);
        if let Some(old) = old {
            let mut copy = wire.clone();
            copy["version"] = json!(old);
            cases.push((format!("{package} on protocol {old}"), copy));
        }
        cases.push((package.to_string(), wire));
    }
    cases.push(("promotion on protocol 7".into(), promotion_without_affine()));
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
        forgeries.len() >= 400,
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

// #759: the frame and `nature::dimension` records of protocol 9, in the wire
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

#[test]
fn legacy_hint_tolerance_is_limited_to_the_v2_envelope() {
    let mut raw = request("fn main() -> Int { 0 }", "shape.vast");
    raw["untrusted_hint"] = json!({"owner":"forged", "checked":true});
    assert_eq!(kernel(&raw, "check")["ok"], true);
    raw["functions"][0]["public"] = json!(true);
    common::assert_wire_rejected(&kernel(raw, "check"), "E_PROTOCOL");
}

// old-route(#533): legacy package envelopes of protocols 4 to 6.
#[test]
fn invalid_membership_scalar_is_rejected_before_authority_analysis() {
    let flat = request(
        "abstract type B; subtype Int <: B; fn main() -> Int { 0 }",
        "shape.vast",
    );
    for version in 4..=6 {
        let mut raw = package(&flat, version);
        raw["packages"][0]["modules"][0]["subtypes"][0]["scalar"] = json!("Float");
        let response = kernel(raw, "check");
        common::assert_wire_rejected(&response, "E_TYPE");
        assert!(
            response["diagnostics"][0]["message"]
                .as_str()
                .unwrap()
                .contains("Nat, Int, Bool, or Unit")
        );
    }
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
        assert_eq!(response["version"], 2, "{response}");
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
        let result = common::kernel_bytes(mode, b"{\"version\":6,\"file\":\"\xff\"}".to_vec());
        assert!(!result.status.success());
        assert!(result.stderr.is_empty(), "{result:?}");
        let response: Value = serde_json::from_slice(&result.stdout).unwrap();
        assert_eq!(response["version"], 2);
        common::assert_wire_rejected(&response, "E_PROTOCOL");
    }
}
