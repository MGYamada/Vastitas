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

#[test]
fn implicit_package_roots_match_the_first_physical_token_or_eof() {
    let s = common::Scratch::empty("implicit module roots");
    let prefix = "// 名\r\n\u{2003} ";
    let empty = "// café\r\n\u{a0}\t";
    s.write_package("empty", empty, "");
    s.write_package("other", "pub fn value() -> Int { 7 }", "");
    s.write_package(
        "app",
        &format!("{prefix}{PROGRAM}"),
        "one={path='../empty'}\ntwo={path='../other'}",
    );
    let raw = s.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    let file_offset = |name: &str| {
        let path = s.0.join(name).join("main.vast").canonicalize().unwrap();
        raw["root_source"]["files"]
            .as_array()
            .unwrap()
            .iter()
            .find(|f| f["path"] == path.to_str().unwrap())
            .unwrap()["offset"]
            .as_u64()
            .unwrap()
    };
    let root_pointer = |name: &str| {
        let packages = raw["packages"].as_array().unwrap();
        let p = packages.iter().position(|p| p["name"] == name).unwrap();
        let m = packages[p]["modules"]
            .as_array()
            .unwrap()
            .iter()
            .position(|m| m["path"] == json!([]))
            .unwrap();
        format!("/packages/{p}/modules/{m}")
    };
    let app = root_pointer("app");
    let dep = root_pointer("empty");
    let first = file_offset("app") + prefix.len() as u64;
    let eof = file_offset("empty") + empty.len() as u64;
    let app_span = json!({"start":first, "end":first+2, "line":2, "column":3});
    let eof_span = json!({"start":eof, "end":eof, "line":2, "column":3});
    assert_eq!(raw.pointer(&app).unwrap()["span"], app_span);
    assert_eq!(raw.pointer(&dep).unwrap()["span"], eof_span);
    let triple = "aarch64-apple-darwin";
    let layout = "e-m:o-i64:64-n32:64-S128";
    let accepted = common::kernel_with_args(&raw, &["llvm-check", triple, layout]);
    assert_eq!(accepted["ok"], true, "{accepted}");

    for (field, value) in [
        ("span/start", json!(first + 1)),
        ("span/end", json!(first)),
        ("span/line", json!(1)),
        ("span/column", json!(4)),
        ("public", json!(false)),
    ] {
        let mut changed = raw.clone();
        *changed.pointer_mut(&format!("{app}/{field}")).unwrap() = value;
        let response = kernel(&changed, "check");
        assert_wire_rejected(&response, "E_MODULE_SOURCE");
        assert_eq!(response["diagnostics"][0]["span"], app_span);
    }

    // Both dependencies are unused. A different dependency's genuine span
    // cannot stand in for the EOF token of the empty package.
    let mut changed = raw.clone();
    changed.pointer_mut(&dep).unwrap()["span"] =
        raw.pointer(&root_pointer("other")).unwrap()["span"].clone();
    for route in [
        &["check"][..],
        &["emit"],
        &["function-revision"],
        &["llvm-check", triple, layout],
        &["llvm-build", triple, layout],
    ] {
        let response = common::kernel_with_args(&changed, route);
        assert_wire_rejected(&response, "E_MODULE_SOURCE");
        assert_eq!(response["diagnostics"][0]["span"], eof_span);
        assert!(response.get("llvm").is_none() && response.get("function_revision").is_none());
    }
}

#[test]
fn flat_and_library_inputs_share_the_synthetic_module_origin() {
    let s = common::Scratch::empty("flat module origin");
    let prefix = "// λ\r\n  ";
    s.write("main.vast", &format!("{prefix}{PROGRAM}"));
    s.write("lib.vast", "fn unused() -> Int { 19 }");
    for files in [&["main.vast"][..], &["main.vast", "--lib", "lib.vast"]] {
        let raw = captured_wire(s.cli().arg("check").args(files), CURRENT_PROTOCOL);
        let module = &raw["packages"][0]["modules"][0];
        assert_eq!(
            module["span"],
            json!({"start":0,"end":0,"line":1,"column":1})
        );
        assert_eq!(kernel(&raw, "function-revision")["ok"], true);
        for (lo, hi, line, column) in [
            (prefix.len(), prefix.len() + 2, 2, 3),
            (0, 0, 2, 1),
            (0, 0, 1, 3),
        ] {
            let mut moved = raw.clone();
            moved["packages"][0]["modules"][0]["span"] =
                json!({"start":lo,"end":hi,"line":line,"column":column});
            assert_wire_rejected(&kernel(&moved, "function-revision"), "E_PROTOCOL");
        }
    }
}

#[test]
fn root_source_is_the_physical_package_entry_at_its_global_byte_offset() {
    let s = common::Scratch::empty("root source");
    let entry = "// λ\r\nmod inner {} mod external; fn main() -> Int { dep::answer() }";
    s.write_package("dep", "pub fn answer() -> Int { 42 }", "");
    s.write_package("app", entry, "dep={path='../dep'}");
    s.write("app/external.vast", "pub fn answer() -> Int { 13 }");
    let raw = s.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    let start: u64 = ["app/Vastitas.toml", "dep/Vastitas.toml", "dep/main.vast"]
        .iter()
        .map(|path| std::fs::metadata(s.0.join(path)).unwrap().len() + 1)
        .sum();
    let root = &raw["root_source"];
    assert_eq!(root["offset"], start);
    assert_eq!(root["text"], entry);
    let paths = [
        "app/Vastitas.toml",
        "dep/Vastitas.toml",
        "dep/main.vast",
        "app/main.vast",
        "app/external.vast",
    ];
    let mut next = 0;
    let files = root["files"].as_array().unwrap();
    assert_eq!(files.len(), paths.len());
    for (file, path) in files.iter().zip(paths) {
        let physical = s.0.join(path).canonicalize().unwrap();
        let text = std::fs::read_to_string(&physical).unwrap();
        assert_eq!(file["path"], physical.to_str().unwrap());
        assert_eq!(file["offset"], next);
        if path == "app/main.vast" {
            assert!(file.get("text").is_none());
        } else {
            assert_eq!(file["text"], text);
        }
        next += text.len() + 1;
    }
    assert_eq!(kernel(&raw, "check")["ok"], true);

    for mode in ["check", "function-revision"] {
        let mut missing = raw.clone();
        missing["root_source"]
            .as_object_mut()
            .unwrap()
            .remove("files");
        assert_wire_rejected(&kernel(&missing, mode), "E_PROTOCOL");
        let mut gap = raw.clone();
        gap["root_source"]["files"][1]["offset"] = json!(1);
        assert_wire_rejected(&kernel(&gap, mode), "E_PROTOCOL");
        let mut duplicate = raw.clone();
        duplicate["root_source"]["files"][3]["text"] = json!(entry);
        assert_wire_rejected(&kernel(&duplicate, mode), "E_PROTOCOL");
        let mut foreign = raw.clone();
        foreign["root_source"]["files"][1]["path"] = json!("unrelated/Vastitas.toml");
        assert_wire_rejected(&kernel(&foreign, mode), "E_PROTOCOL");
        let mut renamed = raw.clone();
        renamed["file"] = json!("unrelated.vast");
        assert_wire_rejected(&kernel(&renamed, mode), "E_PROTOCOL");
        for index in [2, 3] {
            let mut repeated = raw.clone();
            repeated["root_source"]["files"][index]["path"] = raw["root"].clone();
            assert_wire_rejected(&kernel(&repeated, mode), "E_PROTOCOL");
        }
        let mut outside = raw.clone();
        let app = outside["packages"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|p| p["source"] == raw["root"])
            .unwrap();
        let module = app["modules"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|m| m["path"] == json!([]))
            .unwrap();
        module["span"]["end"] = json!(start + entry.len() as u64 + 1);
        assert_wire_rejected(&kernel(&outside, mode), "E_PROTOCOL");
        // Keep every physical record and byte in place, but mark the
        // dependency source as the entry instead of the root module.
        let mut wrong_entry = raw.clone();
        let closure = &mut wrong_entry["root_source"];
        closure["files"][3]["text"] = json!(entry);
        closure["offset"] = closure["files"][2]["offset"].clone();
        closure["text"] = closure["files"][2]
            .as_object_mut()
            .unwrap()
            .remove("text")
            .unwrap();
        assert_wire_rejected(&kernel(&wrong_entry, mode), "E_PROTOCOL");
    }
}

#[test]
fn physical_manifest_editions_bind_the_root_and_unused_dependencies() {
    let s = common::Scratch::empty("physical manifest edition");
    s.write_package("dep", "pub fn answer() -> Int { 9 }", "");
    s.write_package("app", PROGRAM, "dep={path='../dep'}");
    let raw = s.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    let target = &[
        "llvm-check",
        "aarch64-apple-darwin",
        "e-m:o-i64:64-n32:64-S128",
    ];
    let build = &["llvm-build", target[1], target[2]];
    let routes = [
        &["check"][..],
        &["emit"],
        &["function-revision"],
        target,
        build,
    ];
    for args in routes {
        let result = common::kernel_with_args(&raw, args);
        assert_eq!(result["ok"], true, "{result}");
    }
    // All following spans stay fixed because each edit preserves the byte count.
    for row in [0, 1] {
        for (old, new) in [
            ("2026", "2025"),
            ("edition =", "missing ="),
            ("\"2026\"", "2026  "),
        ] {
            let mut changed = raw.clone();
            let text = &mut changed["root_source"]["files"][row]["text"];
            *text = common::checked_replace(text.as_str().unwrap(), old, new).into();
            for args in routes {
                let result = common::kernel_with_args(&changed, args);
                assert_wire_rejected(&result, "E_PROTOCOL");
                assert!(
                    result["diagnostics"][0]["message"]
                        .as_str()
                        .unwrap()
                        .contains("package.edition")
                );
                assert!(result.get("llvm").is_none() && result.get("function_revision").is_none());
            }
        }
    }
    let mut detached = raw;
    detached["file"] = json!("main.vast");
    detached["root_source"] = json!({"offset":0,"text":PROGRAM});
    assert_wire_rejected(&kernel(detached, "check"), "E_PROTOCOL");
}

#[test]
fn physical_edition_accepts_equivalent_toml_and_ignores_decoys() {
    let s = common::Scratch::empty("manifest edition syntax");
    s.write("app/main.vast", PROGRAM);
    let manifest = "app/Vastitas.toml";
    for doc in [
        "[package]\nedition='2026'\nname='app'\nversion='0.1.0'\nroot='main.vast'",
        "package={ edition='2026', name='app', version='0.1.0', root='main.vast' }",
        "package.\"ed\\u0069tion\"=\"20\\u00326\"\r\npackage.name='app'\r\npackage.version='0.1.0'\r\npackage.root='main.vast'",
        "[package]\nname='''edition = \"2025\"\n[other]'''\nversion='0.1.0'\nroot='main.vast'\nedition=\"\"\"\n20\\\n 26\"\"\" # edition = '2025'",
    ] {
        s.write(manifest, doc);
        common::success(&s.check_manifest(manifest));
    }
    let doc =
        "[package]\n#dition='2026'\nedition='2026'\nname='app'\nversion='0.1.0'\nroot='main.vast'";
    s.write(manifest, doc);
    let raw = s.captured(manifest, CURRENT_PROTOCOL);
    for (old, new) in [
        ("#dition", "edition"),
        ("\nedition='2026'", "\nedition='2025'"),
    ] {
        let mut changed = raw.clone();
        changed["root_source"]["files"][0]["text"] = common::checked_replace(doc, old, new).into();
        assert_wire_rejected(&kernel(changed, "check"), "E_PROTOCOL");
    }
}

#[test]
fn every_package_carries_the_edition_including_flat_library_inputs() {
    let s = common::Scratch::empty("flat edition");
    let entry = "fn main() -> Int { answer() }";
    s.write("main.vast", entry);
    s.write("library.vast", "fn answer() -> Int { 42 }");
    let with_library = captured_wire(
        s.cli()
            .args(["check", "main.vast", "--lib", "library.vast"]),
        CURRENT_PROTOCOL,
    );
    assert_eq!(with_library["root"], "vastitas:compat:flat");
    assert_eq!(
        with_library["root_source"],
        json!({"offset": 0, "text": entry, "files": [
            {"offset": 0, "path": "main.vast"},
            {"offset": entry.len() + 1, "path": "library.vast", "text": "fn answer() -> Int { 42 }"}
        ]})
    );
    // APFS cannot create arbitrary Unix paths. Submit byte paths directly
    // to the real kernel on both hosts and check the enclosing revision.
    let mut byte_path = with_library.clone();
    byte_path["root_source"]["files"][1]["path"] = json!([108, 255]);
    let receipt = kernel(&byte_path, "function-revision");
    assert_eq!(receipt["ok"], true, "{receipt}");
    byte_path["expected_function_revision"] = receipt["function_revision"].clone();
    assert_eq!(kernel(&byte_path, "check")["ok"], true);
    byte_path["root_source"]["files"][1]["path"] = json!([108, 254]);
    assert_wire_rejected(&kernel(&byte_path, "check"), "E_FUNCTION_REVISION");
    for bad in [json!([]), json!([108]), json!([0, 255]), json!([256])] {
        byte_path["root_source"]["files"][1]["path"] = bad;
        assert_wire_rejected(&kernel(&byte_path, "check"), "E_PROTOCOL");
    }
    for raw in [
        request(PROGRAM, "edition.vast"),
        with_library,
        geometry_request(),
    ] {
        let packages = raw["packages"].as_array().unwrap();
        assert!(!packages.is_empty());
        for package in packages {
            assert_eq!(package["edition"], "2026");
        }
        for mode in ["check", "emit"] {
            assert_eq!(kernel(&raw, mode)["ok"], true);
        }
        // Bypass Rust and tamper each package independently, including every
        // dependency and the protected flat identity. Neither kernel mode may
        // accept a missing edition or normalize another JSON spelling of it.
        for i in 0..packages.len() {
            for edition in [
                None,
                Some(json!("2025")),
                Some(json!("2027")),
                Some(json!("2026 ")),
                Some(json!(2026)),
                Some(json!(true)),
                Some(Value::Null),
                Some(json!(["2026"])),
                Some(json!({"value":"2026"})),
            ] {
                let mut invalid = raw.clone();
                let package = invalid["packages"][i].as_object_mut().unwrap();
                match edition {
                    Some(value) => {
                        package.insert("edition".into(), value);
                    }
                    None => {
                        package.remove("edition");
                    }
                }
                for mode in ["check", "emit"] {
                    let response = kernel(&invalid, mode);
                    assert_wire_rejected(&response, "E_PROTOCOL");
                    assert!(
                        response["diagnostics"][0]["message"]
                            .as_str()
                            .unwrap()
                            .contains("edition"),
                        "{response}"
                    );
                }
            }
        }
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

#[test]
fn each_physical_dependency_alias_belongs_to_the_manifest_that_declares_it() {
    let s = common::Scratch::empty("manifest dependency declarations");
    s.write_package("dep", "pub fn answer() -> Int { 9 }", "");
    s.write_package(
        "app",
        PROGRAM,
        "alpha={path='../dep'}\nomega={path='../linked'}",
    );
    std::os::unix::fs::symlink(s.0.join("dep"), s.0.join("linked")).unwrap();
    let root = "app/Vastitas.toml";
    let raw = s.captured(root, CURRENT_PROTOCOL);
    let triple = "aarch64-apple-darwin";
    let layout = "e-m:o-i64:64-n32:64-S128";
    let accepted = common::kernel_with_args(&raw, &["llvm-check", triple, layout]);
    assert_eq!(accepted["ok"], true, "{accepted}");
    let mut stale = raw.clone();
    let row = &mut stale["root_source"]["files"][0];
    let offset = row["offset"].as_u64().unwrap() as usize;
    let text = common::checked_replace(row["text"].as_str().unwrap(), "omega=", "theta=");
    let start = text.find("theta=").unwrap();
    row["text"] = json!(text);
    for route in [
        &["check"][..],
        &["emit"],
        &["function-revision"],
        &["llvm-check", triple, layout],
        &["llvm-build", triple, layout],
    ] {
        let response = common::kernel_with_args(&stale, route);
        assert_wire_rejected(&response, "E_MANIFEST_SOURCE");
        let diagnostic = &response["diagnostics"][0];
        assert_eq!(diagnostic["span"]["start"], offset + start);
        assert_eq!(diagnostic["span"]["end"], offset + start + "theta".len());
        assert!(diagnostic["message"].as_str().unwrap().contains("theta"));
        assert!(response.get("llvm").is_none() && response.get("function_revision").is_none());
    }

    // The two written aliases can legitimately point to one canonical package.
    // Equivalent dotted, quoted and table syntax preserves the same LLVM bytes.
    let path = s.0.join(root);
    let manifest = std::fs::read_to_string(&path).unwrap();
    let start = manifest.find("[dependencies]").unwrap();
    let alternate = format!(
        "dependencies.\"o\\u006dega\".path='../linked'\n{}[dependencies.alpha]\npath='../dep'\n",
        &manifest[..start],
    );
    s.write(root, &alternate);
    let reordered = s.captured(root, CURRENT_PROTOCOL);
    assert_eq!(
        common::kernel_with_args(&reordered, &["llvm-check", triple, layout])["llvm"],
        accepted["llvm"]
    );
}

#[test]
fn legacy_geometry_exports_replay_the_physical_manifest_roles_and_presence() {
    let raw = geometry_request();
    assert_eq!(kernel(&raw, "check")["ok"], true);
    let old = "identity = \"self::scheme::id\"";
    for (from, to, written) in [
        (
            old,
            "identity = \"self::smooth::id\"",
            "\"self::smooth::id\"",
        ),
        (
            "point = \"self::Point\"",
            "point = \"self::Other\"",
            "\"self::Other\"",
        ),
        (
            "dimension = \"self::scheme::dim\"",
            "dimension = \"self::smooth::dim\"",
            "\"self::smooth::dim\"",
        ),
    ] {
        let mut changed = raw.clone();
        let row = changed["root_source"]["files"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|f| f["text"].as_str().is_some_and(|s| s.contains(old)))
            .unwrap();
        let offset = row["offset"].as_u64().unwrap() as usize;
        let source = row["text"].as_str().unwrap();
        let start = source.find(from).unwrap() + to.find(written).unwrap();
        let source = source.replacen(from, to, 1);
        row["text"] = json!(source);
        let response = kernel(&changed, "check");
        assert_wire_rejected(&response, "E_MANIFEST_SOURCE");
        let span = &response["diagnostics"][0]["span"];
        assert_eq!(span["start"], offset + start);
        assert_eq!(span["end"], offset + start + written.len());
        assert_eq!(span["line"], source[..start].lines().count());
    }
    let mut missing = raw;
    let row = missing["root_source"]["files"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|f| f["text"].as_str().is_some_and(|s| s.contains(old)))
        .unwrap();
    let source = row["text"].as_str().unwrap();
    let start = source.find("[geometry_compat]").unwrap();
    let absent = format!("{}{}", &source[..start], " ".repeat(source.len() - start));
    row["text"] = json!(absent);
    let response = kernel(&missing, "function-revision");
    assert_wire_rejected(&response, "E_MANIFEST_SOURCE");
    assert!(response.get("function_revision").is_none());
}
