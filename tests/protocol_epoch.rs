//! The single wire schema epoch (#533, #521). The frontend writes only
//! `ir::PROTOCOL`, the kernel accepts only its `currentProtocol`, and
//! `--version` reports that one number. Every other version fails closed by
//! its version alone with the matching-binaries `E_PROTOCOL`: the retired
//! protocols 2 to 9 in the shape they had, and in the shape of the current
//! envelope, and the never-public 0, 1 and the next number. Nothing falls back
//! to an older decoder. Within the epoch, the names that only old envelopes
//! had are unknown fields: the top-level `input`, a flat module, and the
//! spelling `dimension` of the `dim` op, capability and `geometry_compat` slot.
mod common;

use common::{
    CURRENT_PROTOCOL, assert_wire_rejected, captured_wire, flat_module, kernel, kernel_protocol,
    manifest_command, other_protocol_message, request, root,
};
use serde_json::{Value, json};

const PROGRAM: &str = "fn main() -> Int { 42 }";

/// The frontend's request of a package with indexed declarations, a
/// `geometry_compat` export and the `dim` op and capability: the
/// `geometry-compat` example with its standard library.
fn geometry_request() -> Value {
    captured_wire(
        manifest_command(
            "check",
            root().join("examples/packages/geometry/geometry-compat/Vastitas.toml"),
        ),
        CURRENT_PROTOCOL,
    )
}

/// The kernel's answer to `request` at `version`, in `mode`: `E_PROTOCOL` with
/// the matching-binaries message, the request's own version and no source.
#[track_caller]
fn assert_fails_by_version(request: &Value, version: u64, mode: &str) {
    let response = kernel(request, mode);
    assert_wire_rejected(&response, "E_PROTOCOL");
    assert_eq!(
        response["diagnostics"][0]["message"],
        other_protocol_message(version),
        "{response}"
    );
    assert_eq!(response["version"], version, "{response}");
    assert_eq!(
        response["diagnostics"].as_array().unwrap().len(),
        1,
        "{response}"
    );
}

#[test]
fn the_frontend_the_kernel_and_version_share_one_epoch() {
    assert_eq!(CURRENT_PROTOCOL, kernel_protocol());
    let output = common::cli().arg("--version").output().unwrap();
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        format!(
            "vastitas {} (wire protocol {})",
            env!("CARGO_PKG_VERSION"),
            kernel_protocol()
        )
    );
    for raw in [request(PROGRAM, "epoch.vast"), geometry_request()] {
        assert_eq!(raw["version"], kernel_protocol());
        assert!(raw.get("input").is_none(), "{raw}");
        for mode in ["check", "emit"] {
            let response = kernel(&raw, mode);
            assert_eq!(response["ok"], true, "{response}");
            assert_eq!(response["version"], kernel_protocol(), "{response}");
        }
        let mut nine = raw.clone();
        nine["version"] = json!(9);
        assert_fails_by_version(&nine, 9, "check");
    }
}

/// The request at `version` in the shape that protocol had, for the flat
/// unit of `flat` and for the package request `package` of the same
/// program: the flat module of 2 and 4, the package request without `input`
/// of 3, and with `"input": "package"` of 4 to 9.
fn retired_shapes(version: u64, flat: &Value, package: &Value) -> Vec<Value> {
    let mut module = flat_module(&mut flat.clone()).take();
    let mut shapes = Vec::new();
    if version == 2 || version == 4 {
        for record in ["functions", "generics", "abstract_types"] {
            for item in module[record].as_array_mut().into_iter().flatten() {
                item.as_object_mut().unwrap().remove("public");
            }
        }
        let mut old = json!({
            "version": version,
            "file": flat["file"],
            "functions": module["functions"],
            "generics": module["generics"],
            "methods": module["methods"],
        });
        if version == 4 {
            old["input"] = json!("flat");
        }
        shapes.push(old);
    }
    if (3..=9).contains(&version) {
        let mut old = package.clone();
        old["version"] = json!(version);
        old.as_object_mut().unwrap().remove("legacy_geometry");
        if version >= 4 {
            old["input"] = json!("package");
        }
        shapes.push(old);
    }
    shapes
}

/// Every shape of the request at `version`, in `check` and in `emit`, fails
/// closed by its version alone: the request of the epoch relabelled, and for 2
/// to 9 the shape that the version had.
fn fails_closed(version: u64) {
    let flat = request(PROGRAM, "epoch.vast");
    let package = geometry_request();
    let mut shapes = vec![flat.clone(), package.clone()];
    for shape in &mut shapes {
        shape["version"] = json!(version);
    }
    shapes.extend(retired_shapes(version, &flat, &package));
    for shape in &shapes {
        for mode in ["check", "emit"] {
            assert_fails_by_version(shape, version, mode);
        }
    }
}

/// The retired protocols and the numbers that were never public: every
/// version below the epoch, so that a later epoch tests this one as retired.
#[test]
fn every_version_below_the_epoch_fails_closed() {
    let versions: Vec<u64> = (0..CURRENT_PROTOCOL).collect();
    assert!(
        versions.len() >= 10 && versions.contains(&9),
        "{versions:?}"
    );
    for version in versions {
        fails_closed(version);
    }
}

#[test]
fn the_next_protocol_fails_closed() {
    fails_closed(CURRENT_PROTOCOL + 1);
}

/// A kernel of another epoch answers a request of this one with the
/// matching-binaries `E_PROTOCOL` at the request's version; the CLI shows that
/// diagnostic and fails.
#[test]
fn a_kernel_of_another_epoch_is_reported_as_a_mismatched_build() {
    use std::os::unix::fs::PermissionsExt;
    let scratch = common::Scratch::empty("epoch mismatch");
    scratch.write("main.vast", PROGRAM);
    let message = format!(
        "IR protocol version {CURRENT_PROTOCOL} is not protocol {} of this kernel; \
         the compiler and the kernel must come from the same Vastitas build: rebuild them together",
        CURRENT_PROTOCOL + 1
    );
    let answer = json!({"version": CURRENT_PROTOCOL, "ok": false,
        "diagnostics": [{"code": "E_PROTOCOL", "message": message}]});
    let backend = scratch.write(
        "kernel",
        &format!("#!/bin/sh\ncat >/dev/null\nprintf '%s\\n' '{answer}'\nexit 1\n"),
    );
    std::fs::set_permissions(&backend, std::fs::Permissions::from_mode(0o755)).unwrap();
    let output = scratch
        .cli()
        .env("VASTITAS_KERNEL", &backend)
        .args(["check", "main.vast"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(&format!("E_PROTOCOL: {message}")),
        "{stderr}"
    );
}

#[test]
fn a_protocol_nine_envelope_relabelled_as_the_epoch_keeps_input_unknown() {
    for mut raw in [request(PROGRAM, "epoch.vast"), geometry_request()] {
        raw["input"] = json!("package");
        for mode in ["check", "emit"] {
            let response = kernel(&raw, mode);
            assert_wire_rejected(&response, "E_PROTOCOL");
            assert_eq!(
                response["diagnostics"][0]["message"],
                "unknown protocol field 'input'"
            );
            assert_eq!(response["version"], CURRENT_PROTOCOL);
        }
    }
}

#[test]
fn a_flat_module_labelled_as_the_epoch_is_rejected() {
    let mut raw = request(PROGRAM, "epoch.vast");
    let module = flat_module(&mut raw).take();
    let flat = json!({
        "version": CURRENT_PROTOCOL,
        "file": "epoch.vast",
        "functions": module["functions"],
        "generics": module["generics"],
        "methods": module["methods"],
    });
    for mode in ["check", "emit"] {
        let response = kernel(&flat, mode);
        assert_wire_rejected(&response, "E_PROTOCOL");
        assert_eq!(
            response["diagnostics"][0]["message"],
            "unknown protocol field 'functions'"
        );
    }
    let mut both = request(PROGRAM, "epoch.vast");
    both["functions"] = module["functions"].clone();
    assert_wire_rejected(&kernel(&both, "check"), "E_PROTOCOL");
}

/// Applies `edit` at every place of `value`, recursively, and counts the
/// places where it applied.
fn rewrite(value: &mut Value, edit: &impl Fn(&mut Value) -> bool) -> usize {
    let mut count = usize::from(edit(value));
    match value {
        Value::Object(fields) => {
            for child in fields.values_mut() {
                count += rewrite(child, edit);
            }
        }
        Value::Array(items) => {
            for child in items {
                count += rewrite(child, edit);
            }
        }
        _ => {}
    }
    count
}

/// The wire spells the op, the capability and the `geometry_compat` slot of
/// `dim(…)` as `dim`; the spelling `dimension` in each of these places is
/// rejected.
#[test]
fn the_dimension_spelling_of_dim_is_rejected() {
    let original = geometry_request();
    let text = original.to_string();
    assert!(text.contains(r#""op":"dim""#), "{text}");
    assert!(
        text.contains(r#""capabilities":["origin","dim"]"#),
        "{text}"
    );
    let op = |value: &mut Value| {
        let found = value.get("op") == Some(&json!("dim"));
        if found {
            value["op"] = json!("dimension");
        }
        found
    };
    let capability = |value: &mut Value| {
        let found = value == &json!("dim");
        if found {
            *value = json!("dimension");
        }
        found
    };
    let slot = |value: &mut Value| {
        let Some(fields) = value.as_object_mut() else {
            return false;
        };
        let Some(entry) = fields.remove("dim") else {
            return false;
        };
        fields.insert("dimension".into(), entry);
        true
    };
    for (label, edited, message) in [
        (
            "op",
            rewrite_copy(&original, &op),
            "unknown indexed primitive contract",
        ),
        (
            "capability",
            rewrite_capabilities(&original, &capability),
            "unsupported implementation capability",
        ),
        (
            "geometry_compat slot",
            rewrite_geometry(&original, &slot),
            "unknown protocol field 'dimension'",
        ),
    ] {
        let response = kernel(&edited, "check");
        assert_wire_rejected(&response, "E_PROTOCOL");
        assert_eq!(
            response["diagnostics"][0]["message"], message,
            "{label}: {response}"
        );
    }
}

/// A copy of `value` with `edit` applied at every place; at least one applies.
fn rewrite_copy(value: &Value, edit: &impl Fn(&mut Value) -> bool) -> Value {
    let mut copy = value.clone();
    assert!(rewrite(&mut copy, edit) > 0);
    copy
}

/// A copy of `value` with `edit` applied to the entries of every
/// `capabilities` list.
fn rewrite_capabilities(value: &Value, edit: &impl Fn(&mut Value) -> bool) -> Value {
    rewrite_copy(value, &|place: &mut Value| {
        let Some(list) = place.get_mut("capabilities").and_then(Value::as_array_mut) else {
            return false;
        };
        let mut found = false;
        for entry in list {
            found |= edit(entry);
        }
        found
    })
}

/// A copy of `value` with `edit` applied to the settings of every
/// `geometry_compat` export.
fn rewrite_geometry(value: &Value, edit: &impl Fn(&mut Value) -> bool) -> Value {
    rewrite_copy(value, &|place: &mut Value| {
        let Some(profile) = place.get_mut("geometry_compat") else {
            return false;
        };
        let scheme = edit(&mut profile["scheme"]);
        edit(&mut profile["smooth"]) || scheme
    })
}
