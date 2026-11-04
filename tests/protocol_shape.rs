//! Adversarial schema mutations at the actual legacy/public kernel boundary.
mod common;

use common::{kernel, request};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::io::Write;
use std::process::{Command, Stdio};

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

// Select a representative of every distinct record shape/tag. This avoids
// rerunning identical span mutations for every scalar leaf in a source file.
fn record_paths(value: &Value, path: &str, records: &mut BTreeMap<String, String>) {
    match value {
        Value::Object(fields) => {
            let shape = format!(
                "{:?}:{:?}:{:?}",
                fields.keys().collect::<Vec<_>>(),
                fields.get("kind"),
                fields.get("op")
            );
            records.entry(shape).or_insert_with(|| path.to_string());
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

#[test]
fn legacy_decoders_reject_unknown_fields_in_every_nested_record_shape() {
    let geometric = format!(
        "{}\nfn preserve_map(X: Scheme, f: Morphism<X, X>) -> Morphism<X, X> {{ f }}",
        include_str!("../examples/pointed.vast")
    );
    let mut cases = Vec::new();
    for source in [
        include_str!("../examples/functions.vast"),
        include_str!("../examples/pairs.vast"),
        &geometric,
        "fn empty() -> Unit { { () } } generic f(x) { domain (Int); } method f(x: Int) -> Int { x } fn main() -> Int { f(0) }",
        include_str!("../examples/abstract-contracts.vast"),
    ] {
        let flat = request(source, "shape.vast");
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
            assert_eq!(
                response["diagnostics"][0]["code"], "E_PROTOCOL",
                "{path}: {response}"
            );
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

/// The promotion example against a copy of the stdlib without its Stage 2
/// `scheme::affine` module. That closure still uses protocol 7, so the
/// Indexed.Wire sweep keeps the geometry-compatibility, dependency and
/// function-body records that only the stdlib supplies.
fn promotion_without_affine() -> Value {
    let root = common::root();
    let stdlib = root.join("stdlib");
    let s = common::Scratch::empty("protocol seven stdlib");
    let copy = |from: &str, to: &str| {
        s.write(to, &std::fs::read_to_string(stdlib.join(from)).unwrap());
    };
    copy("Vastitas.toml", "stdlib/Vastitas.toml");
    // Copy the generated package and every geometry source except the Stage 2
    // module, so new stdlib modules are picked up without editing this list.
    for directory in ["target/package", "src/geometry"] {
        let mut stack = vec![stdlib.join(directory)];
        while let Some(path) = stack.pop() {
            if path.ends_with("src/geometry/scheme/affine") {
                continue;
            }
            for entry in std::fs::read_dir(&path).unwrap() {
                let entry = entry.unwrap().path();
                if entry.is_dir() {
                    stack.push(entry);
                } else if entry
                    .extension()
                    .is_some_and(|extension| extension == "vast" || extension == "toml")
                {
                    let relative = entry
                        .strip_prefix(&stdlib)
                        .unwrap()
                        .to_str()
                        .unwrap()
                        .to_owned();
                    copy(&relative, &format!("stdlib/{relative}"));
                }
            }
        }
    }
    let scheme = std::fs::read_to_string(stdlib.join("src/geometry/scheme/mod.vast")).unwrap();
    assert!(scheme.contains("pub mod affine;\n"));
    s.write(
        "stdlib/src/geometry/scheme/mod.vast",
        &scheme.replace("pub mod affine;\n", ""),
    );
    let example = root.join("examples/packages/promotion");
    s.write(
        "app/Vastitas.toml",
        &std::fs::read_to_string(example.join("Vastitas.toml"))
            .unwrap()
            .replace("../../../stdlib", "../stdlib"),
    );
    s.write(
        "app/main.vast",
        &std::fs::read_to_string(example.join("main.vast")).unwrap(),
    );
    let mut command = common::cli();
    command
        .args(["check", "--manifest-path"])
        .arg(s.0.join("app/Vastitas.toml"));
    common::captured_wire(command, 7)
}

// #557: the same sweep over the public Indexed.Wire (7) and ResourceSource.Wire
// (8/9) decoders, using wires the actual frontend sends for indexed, resource,
// numerical, tree, network, storage and named-recipient edit programs.
#[test]
fn public_decoders_reject_unknown_fields_in_every_captured_v7_to_v9_record_shape() {
    // The promotion example depends on the generated stdlib package.
    common::prepare_stdlib_package();
    let examples = common::root().join("examples/packages");
    let mut cases = Vec::new();
    for (package, version) in [
        ("indexed", 7),
        // Its stdlib dependency declares Stage 2 presented affine geometry.
        ("promotion", 9),
        ("resource-values", 8),
        ("numerical", 8),
        ("runtime-shapes", 8),
        ("tensor-packing", 8),
        ("contraction-tree", 8),
        ("finite_network", 8),
        ("storage/app", 8),
        ("edit-borrow/app", 9),
        ("edit-authority/app", 9),
        ("smooth-objects", 9),
        ("smooth-cotangent", 9),
        ("smooth-metric", 9),
        ("smooth-differential", 9),
    ] {
        let manifest = examples.join(package).join("Vastitas.toml");
        let mut command = common::cli();
        command.args(["check", "--manifest-path"]).arg(manifest);
        cases.push((package, common::captured_wire(command, version)));
    }
    cases.push(("promotion on protocol 7", promotion_without_affine()));
    let recipients: Value =
        serde_json::from_str(include_str!("fixtures/edit-recipients.json")).unwrap();
    assert_eq!(recipients["version"], 9);
    cases.push(("edit-recipients fixture", recipients));
    let mut forgeries = Vec::new();
    for (name, raw) in &cases {
        let baseline = kernel(raw, "check");
        assert_eq!(baseline["ok"], true, "{name}: {baseline}");
        let mut records = BTreeMap::new();
        record_paths(raw, "", &mut records);
        for path in records.into_values() {
            let mut changed = raw.clone();
            changed.pointer_mut(&path).unwrap()["forged_authority"] = json!("untrusted");
            forgeries.push((*name, raw["version"].clone(), path, changed));
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

#[test]
fn legacy_hint_tolerance_is_limited_to_the_v2_envelope() {
    let mut raw = request("fn main() -> Int { 0 }", "shape.vast");
    raw["untrusted_hint"] = json!({"owner":"forged", "checked":true});
    assert_eq!(kernel(&raw, "check")["ok"], true);
    raw["functions"][0]["public"] = json!(true);
    assert_eq!(kernel(raw, "check")["diagnostics"][0]["code"], "E_PROTOCOL");
}

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
        assert_eq!(response["ok"], false, "{response}");
        assert_eq!(response["diagnostics"][0]["code"], "E_TYPE", "{response}");
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
        assert_eq!(response["diagnostics"][0]["code"], "E_PROTOCOL");
        assert!(
            response["diagnostics"][0]["message"]
                .as_str()
                .unwrap()
                .contains("version must be a natural number")
        );
    }
    assert_eq!(
        kernel(json!({}), "check")["diagnostics"][0]["code"],
        "E_PROTOCOL"
    );
    for mode in ["check", "emit"] {
        let mut child = Command::new(common::kernel_path())
            .arg(mode)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(b"{\"version\":6,\"file\":\"\xff\"}")
            .unwrap();
        let result = child.wait_with_output().unwrap();
        assert!(!result.status.success());
        assert!(result.stderr.is_empty(), "{result:?}");
        let response: Value = serde_json::from_slice(&result.stdout).unwrap();
        assert_eq!(response["version"], 2);
        assert_eq!(response["diagnostics"][0]["code"], "E_PROTOCOL");
        assert!(response.get("lean_source").is_none());
    }
}
