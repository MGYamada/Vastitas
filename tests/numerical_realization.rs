//! Nominal realization and the bit-preserving identity on public resource points.
mod common;
use common::{CURRENT_PROTOCOL, assert_wire_rejected, checked_replace, exits, kernel};
use serde_json::{Value, json};

const MAIN: &str = include_str!("../examples/packages/float-identity/src/main.vast");
const MANIFEST: &str = "app/Vastitas.toml";

fn fixture(main: &str) -> common::Scratch {
    let manifest = include_str!("../examples/packages/float-identity/Vastitas.toml")
        .replace("../../../stdlib", "../stdlib")
        .replace("src/main.vast", "main.vast");
    common::stdlib_app("affine identity", &manifest, main, &[])
}

fn body(wire: &mut Value) -> &mut Vec<Value> {
    wire["packages"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .flat_map(|p| p["modules"].as_array_mut().unwrap())
        .filter_map(|m| m.get_mut("resource_functions")?.as_array_mut())
        .flatten()
        .find(|f| f["name"] == "main")
        .unwrap()["body"]
        .as_array_mut()
        .unwrap()
}

#[test]
fn canonical_realization_runs_into_existing_storage_and_replays_its_revision() {
    let source = checked_replace(MAIN, "use monad::float;", "use monad::float as fp;")
        .replace("float::", "fp::");
    let s = fixture(&source);
    assert_eq!(s.check_build_and_run(MANIFEST), exits(0));
    let mut wire = s.captured(MANIFEST, CURRENT_PROTOCOL);
    let response = kernel(&wire, "function-revision");
    assert_eq!(response["ok"], true, "{response}");
    let revision = &response["function_revision"];
    let sites = revision["resource_realizations"]["sites"]
        .as_array()
        .unwrap();
    let names = sites
        .iter()
        .map(|s| {
            let id = &s["id"];
            assert_eq!(id["package"]["source"], "vastitas:compat:float");
            assert_eq!(id["module"], json!(["float"]));
            id["name"].as_str().unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(names, ["realize", "interpret", "point", "point", "run"]);
    assert_eq!(sites[4]["graph"]["name"], "idP");
    assert_eq!(sites[4]["subject"]["name"], "Plane");
    assert_eq!(
        revision["resource_realizations"]["charts"][0]["coordinates"],
        json!(["x", "y"])
    );
    assert_eq!(sites[4]["representation"], "F64<RR>");
    assert_eq!(sites[4]["policy"], "NativeFast");
    assert_eq!(sites[4]["flags"], "Unavailable");
    let runs = revision["resource_realizations"]["runs"]
        .as_array()
        .unwrap();
    assert_eq!(runs.len(), 1);
    assert_ne!(runs[0]["source_loan"], runs[0]["destination_loan"]);
    wire["expected_function_revision"] = revision.clone();
    assert_eq!(kernel(&wire, "check")["function_revision_matched"], true);
    for (field, value) in [
        ("graph", Value::Null),
        ("flags", json!([])),
        ("representation", json!("F32<RR>")),
    ] {
        let mut forged = wire.clone();
        forged["expected_function_revision"]["resource_realizations"]["sites"][4][field] = value;
        for mode in ["check", "emit"] {
            assert_wire_rejected(&kernel(&forged, mode), "E_FUNCTION_REVISION");
        }
    }
}

#[test]
fn real32_identity_preserves_payloads_and_replays_its_precision() {
    let source = MAIN
        .replace("F64<RR>", "F32<RR>")
        .replace("f64_bits", "f32_bits")
        .replace("9223372036854775808", "2147483648")
        .replace("9218868437227405378", "2139095106");
    let s = fixture(&source);
    assert_eq!(s.check_build_and_run(MANIFEST), exits(0));
    let mut wire = s.captured(MANIFEST, CURRENT_PROTOCOL);
    let response = kernel(&wire, "function-revision");
    assert_eq!(response["ok"], true, "{response}");
    let revision = &response["function_revision"];
    let sites = revision["resource_realizations"]["sites"]
        .as_array()
        .unwrap();
    assert_eq!(sites.len(), 5);
    assert!(sites.iter().all(|s| s["representation"] == "F32<RR>"));
    assert_eq!(sites[4]["flags"], "Unavailable");
    wire["expected_function_revision"] = revision.clone();
    assert_eq!(kernel(&wire, "check")["function_revision_matched"], true);
    wire["expected_function_revision"]["resource_realizations"]["sites"][4]["representation"] =
        json!("F64<RR>");
    for mode in ["check", "emit"] {
        assert_wire_rejected(&kernel(&wire, mode), "E_FUNCTION_REVISION");
    }
}

#[test]
fn realization_rejects_wrong_chart_graph_precision_policy_or_live_point() {
    let plane = "indexed affine Plane(SmoothR) = Affine(2)[x, y];";
    let extended = checked_replace(
        MAIN,
        plane,
        &format!("{plane}\nindexed affine Other(SmoothR) = Affine(2)[x, y];"),
    );
    let s = fixture(&extended);
    let cases = [
        ("Plane::standard_chart", "Other::standard_chart"),
        ("Plane::standard_chart", "Plane::other_chart"),
        ("interpret(idP, r", "interpret(Plane, r"),
        ("realize::<F64<RR>>", "realize::<F64<CC>>"),
        ("realize::<F64<RR>>", "realize::<F32<RR>>"),
        ("NativeFast", "Strict"),
        ("NativeFast", "SafeFloat"),
        ("= identity;", "= pullback(x -> x, y -> y);"),
        ("float::run(e, p) -> q;", "float::run(e, q) -> p;"),
        (
            "float::run(e, p) -> q;",
            "release(output); float::run(e, p) -> q;",
        ),
        (
            "let q = float::point(r, output);",
            "let q = float::point(r, p);",
        ),
        (
            "write(outputBuffer, layout(0, 2, 1, 2, false))",
            "write(outputBuffer, layout(0, 1, 2, 1, false))",
        ),
        ("store(init, 1, 0, f64_bits(9218868437227405378));", ""),
    ];
    for (from, to) in cases {
        let source = checked_replace(&extended, from, to);
        s.write("app/main.vast", &source);
        let result = s.command("check", MANIFEST).output().unwrap();
        assert!(!result.status.success(), "accepted {to}");
        assert!(
            String::from_utf8_lossy(&result.stderr).contains("main.vast:"),
            "{to}: {result:?}"
        );
    }
}

#[test]
fn realization_wire_recomputes_authority_and_rejects_untrusted_targets() {
    let s = fixture(MAIN);
    let wire = s.captured(MANIFEST, CURRENT_PROTOCOL);
    for (field, value) in [
        ("function_id", json!("vastitas:compat:float")),
        ("callee", json!({"path":["float","other"], "span":null})),
        ("result", json!("input")),
        ("representation", json!("binary128")),
        ("into", json!(true)),
    ] {
        let mut forged = wire.clone();
        let site = body(&mut forged)
            .iter_mut()
            .find(|s| s["kind"] == "realization")
            .unwrap();
        if field == "callee" {
            site[field]["path"] = value["path"].clone();
        } else {
            site[field] = value;
        }
        for mode in ["check", "emit"] {
            let response = kernel(&forged, mode);
            assert_eq!(response["ok"], false, "{field}: {response}");
            assert!(response.get("lean_source").is_none());
        }
    }
}

#[test]
fn unused_realization_functions_still_check_point_layout_and_liveness() {
    let source = checked_replace(MAIN, "resource fn main()", "resource fn unused()");
    let s = fixture(&source);
    for (from, to) in [
        (
            "write(outputBuffer, layout(0, 2, 1, 2, false))",
            "write(outputBuffer, layout(0, 1, 2, 1, false))",
        ),
        (
            "float::run(e, p) -> q;",
            "release(output); float::run(e, p) -> q;",
        ),
    ] {
        let main =
            checked_replace(&source, from, to) + "\nresource fn main() -> Int { value { 0 } }\n";
        s.write("app/main.vast", &main);
        for mode in ["check", "emit"] {
            let wire = s.captured(MANIFEST, CURRENT_PROTOCOL);
            assert_wire_rejected(&kernel(&wire, mode), "E_REALIZATION_POINT");
        }
    }
}

#[test]
fn reborrowed_point_restores_its_parent_only_after_release() {
    let run = "float::run(e, p) -> q;";
    let child = "borrow child = read(input, layout(0, 2, 1, 2, false));
    let childPoint = float::point(r, child);
    float::run(e, childPoint) -> q;";
    let source = checked_replace(
        MAIN,
        run,
        &format!("{child}\n    release(child);\n    {run}"),
    );
    let s = fixture(&source);
    assert_eq!(s.check_build_and_run(MANIFEST), exits(0));
    s.write(
        "app/main.vast",
        &checked_replace(
            &source,
            &format!("release(child);\n    {run}"),
            &format!("{run}\n    release(child);"),
        ),
    );
    common::expect_code(&s.check_manifest(MANIFEST), "E_REALIZATION_POINT");
}

#[test]
fn dependency_names_do_not_grant_the_protected_float_identity() {
    let s = fixture(MAIN);
    let manifest = common::read(&s.0.join(MANIFEST));
    s.write_package(
        "impostor",
        "pub mod float { pub resource fn realize() -> Unit { value { () } } }",
        "",
    );
    s.write(
        MANIFEST,
        &(manifest + "\nmonad = { path = '../impostor' }\n"),
    );
    let wire = s.captured(MANIFEST, CURRENT_PROTOCOL);
    for mode in ["check", "emit"] {
        assert_wire_rejected(&kernel(&wire, mode), "E_REALIZATION");
    }
    let root = wire["root"].clone();
    let mut forged = wire;
    let app = forged["packages"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|pkg| pkg["source"] == root)
        .unwrap();
    let monad = app["dependencies"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|dep| dep["alias"] == "monad")
        .unwrap();
    monad["target"] = json!("vastitas:compat:float");
    for mode in ["check", "emit"] {
        assert_wire_rejected(&kernel(&forged, mode), "E_PROTOCOL");
    }
}

#[test]
fn realization_paths_keep_argument_diagnostics_and_reject_misplaced_spans() {
    let s = fixture(MAIN);
    let wire = s.captured(MANIFEST, CURRENT_PROTOCOL);
    let mut unknown = wire.clone();
    let site = body(&mut unknown)
        .iter_mut()
        .find(|s| s["callee"]["path"] == json!(["float", "realize"]))
        .unwrap();
    site["arguments"][1]["path"][1] = json!("wrong_chart");
    let expected = site["arguments"][1]["span"].clone();
    for mode in ["check", "emit"] {
        let response = kernel(&unknown, mode);
        assert_wire_rejected(&response, "E_REALIZATION_CHART");
        assert_eq!(response["diagnostics"][0]["span"], expected);
    }
    for location in [0, 1] {
        let mut misplaced = wire.clone();
        let site = body(&mut misplaced)
            .iter_mut()
            .find(|s| s["callee"]["path"] == json!(["float", "realize"]))
            .unwrap();
        if location == 0 {
            let end = site["span"]["end"].as_u64().unwrap();
            site["callee"]["span"]["start"] = json!(end + 1);
            site["callee"]["span"]["end"] = json!(end + 2);
        } else {
            site["arguments"][1]["span"] = site["arguments"][0]["span"].clone();
        }
        for mode in ["check", "emit"] {
            assert_wire_rejected(&kernel(&misplaced, mode), "E_PROTOCOL");
        }
    }
}
