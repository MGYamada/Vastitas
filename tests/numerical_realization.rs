//! Nominal realization and the bit-preserving identity on public resource points.
mod common;
use common::{CURRENT_PROTOCOL, assert_wire_rejected, checked_replace, exits, kernel};
use serde_json::{Value, json};

const MAIN: &str = include_str!("../examples/packages/float-identity/src/main.vast");
const MANIFEST: &str = "app/Vastitas.toml";

#[test]
fn physical_source_binds_realizations_even_when_the_descriptor_is_unused() {
    let source = "use monad::float; use monad::float as other;
        use std::geometry::smooth::affine::SmoothR;
        indexed affine Plane(SmoothR) = Affine(2)[x, y];
        resource fn main() -> Int {
            if true {
                let r = float::realize::<F32<RR>>(Plane, Plane::standard_chart,);
            } else { }
            value { 0 }
        }";
    let s = fixture(source);
    let wire = s.captured(MANIFEST, CURRENT_PROTOCOL);
    assert_eq!(kernel(&wire, "check")["ok"], true);
    for change in [
        "precision",
        "callee",
        "result",
        "location",
        "branch",
        "condition",
        "omit",
    ] {
        let mut changed = wire.clone();
        let branch = &mut body(&mut changed)[0];
        let site = &mut branch["yes"][0];
        match change {
            "precision" => site["representation"] = json!("real64"),
            "callee" => site["callee"]["path"][0] = json!("other"),
            "result" => site["result"] = json!("renamed"),
            "location" => site["arguments"][0]["span"]["column"] = json!(1),
            "branch" => {
                branch["no"] = branch["yes"].take();
                branch["yes"] = json!([]);
            }
            "condition" => branch["condition"] = json!(false),
            "omit" => branch["yes"] = json!([]),
            _ => unreachable!(),
        }
        for mode in ["check", "emit"] {
            assert_wire_rejected(&kernel(&changed, mode), "E_PROTOCOL");
        }
    }
}

#[test]
fn realization_calls_in_an_external_module_keep_their_owner_and_order() {
    let s = fixture("mod model; resource fn main() -> Int { value { 0 } }");
    let source = "use monad::float;
        use std::geometry::smooth::affine::SmoothR;
        indexed affine Plane(SmoothR) = Affine(2)[x, y];
        pub resource fn first() -> Unit {
            // 数値: this comment contains let fake = float::run(a,b) -> q;
            let a = float::realize::<F32<RR>>(Plane, Plane::standard_chart);
            let b = float :: realize :: < F64 < RR > >(Plane, Plane :: standard_chart,);
            value { () }
        }
        pub resource fn second() -> Unit { value { () } }";
    s.write("app/model.vast", &source.replace('\n', "\r\n"));
    let wire = s.captured(MANIFEST, CURRENT_PROTOCOL);
    assert_eq!(kernel(&wire, "check")["ok"], true);
    for change in ["order", "function", "visibility", "omit function"] {
        let mut changed = wire.clone();
        let module = changed["packages"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .flat_map(|p| p["modules"].as_array_mut().unwrap())
            .find(|m| m["path"] == json!(["model"]))
            .unwrap();
        let functions = module["resource_functions"].as_array_mut().unwrap();
        let first = functions.iter().position(|f| f["name"] == "first").unwrap();
        match change {
            "order" => functions[first]["body"].as_array_mut().unwrap().swap(0, 1),
            "function" => {
                let moved = functions[first]["body"].take();
                functions[first]["body"] = json!([]);
                let second = functions
                    .iter_mut()
                    .find(|f| f["name"] == "second")
                    .unwrap();
                second["body"] = moved;
            }
            "visibility" => functions[first]["public"] = json!(false),
            "omit function" => {
                functions.remove(first);
            }
            _ => unreachable!(),
        }
        assert_wire_rejected(&kernel(&changed, "check"), "E_PROTOCOL");
    }
}

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

fn preview_bytes(s: &common::Scratch, triple: &str, layout: &str) -> Vec<u8> {
    let output = s
        .command("check", MANIFEST)
        .args([
            "--llvm-preview",
            "--target-triple",
            triple,
            "--data-layout",
            layout,
        ])
        .output()
        .unwrap();
    common::success(&output);
    output.stdout
}

fn check_llvm_identity(s: &common::Scratch, scalar: u8) -> Vec<u8> {
    let bytes = preview_bytes(s, "x86_64-unknown-linux-gnu", "e-p:64:64");
    let ir = std::str::from_utf8(&bytes).unwrap();
    assert!(ir.contains(&format!(
        "call i32 @vq_storage_allocate(ptr %arena, i64 0, i64 {scalar}, i64 2)"
    )));
    assert_eq!(ir.matches("call i32 @vq_storage_copy(").count(), 1);
    assert_eq!(ir.matches("call i32 @vq_storage_expect(").count(), 2);
    assert_eq!(
        ir.matches("call void @vstorage_delete(ptr %arena)").count(),
        2
    );
    assert!(!ir.contains("fastcc") && !ir.contains("inbounds"));
    #[cfg(feature = "llvm-native")]
    {
        let build = s
            .command("build", MANIFEST)
            .args(["--llvm-preview", "-o", "llvm-program"])
            .output()
            .unwrap();
        common::success(&build);
        assert_eq!(
            common::ran(
                &std::process::Command::new(s.0.join("llvm-program"))
                    .output()
                    .unwrap()
            ),
            exits(0)
        );
    }
    bytes
}

#[test]
fn canonical_realization_runs_into_existing_storage_and_replays_its_revision() {
    let source = checked_replace(MAIN, "use monad::float;", "use monad::float as fp;")
        .replace("float::", "fp::");
    let s = fixture(&source);
    assert_eq!(s.check_build_and_run(MANIFEST), exits(0));
    check_llvm_identity(&s, 0);
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
    check_llvm_identity(&s, 2);
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
    s.write(
        "app/main.vast",
        &checked_replace(MAIN, "Plane::standard_chart", "Plane::wrong_chart"),
    );
    let mut unknown = s.captured(MANIFEST, CURRENT_PROTOCOL);
    let site = body(&mut unknown)
        .iter_mut()
        .find(|s| s["callee"]["path"] == json!(["float", "realize"]))
        .unwrap();
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

const COMPLEX: &str = include_str!("../examples/packages/float-complex-identity/src/main.vast");

#[test]
fn affine_wrappers_run_the_same_identity_bytes_at_all_four_representations() {
    let s = fixture(MAIN);
    for (repr, template, scalar) in [
        ("F64<RR>", MAIN, 0),
        ("F64<CC>", COMPLEX, 1),
        ("F32<RR>", MAIN, 2),
        ("F32<CC>", COMPLEX, 3),
    ] {
        let canonical = if repr.starts_with("F32") {
            template
                .replace("F64<", "F32<")
                .replace("f64_bits", "f32_bits")
                .replace("complex_bits", "complex32_bits")
                .replace("9223372036854775808", "2147483648")
                .replace("9218868437227405378", "2139095106")
        } else {
            template.to_owned()
        };
        s.write("app/main.vast", &canonical);
        let bytes = preview_bytes(&s, "x86_64-unknown-linux-gnu", "e-p:64:64");
        let resource = canonical.split_once("resource fn main").unwrap().1;
        let wrapper = format!("use monad::float;\nresource fn main{resource}")
            .replace(
                &format!("float::realize::<{repr}>(Plane, Plane::standard_chart)"),
                &format!("Affine({repr}, 2)"),
            )
            .replace("interpret(idP,", "interpret(r::identity,");
        s.write("app/main.vast", &wrapper);
        assert_eq!(s.check_build_and_run(MANIFEST), exits(0));
        assert_eq!(check_llvm_identity(&s, scalar), bytes, "{repr}");
        let corpus = match scalar {
            0 => Some(include_bytes!("../llvm/src/float-identity.ll").as_slice()),
            1 => Some(include_bytes!("../llvm/src/float-complex-identity.ll").as_slice()),
            _ => None,
        };
        if let Some(retained) = corpus {
            let emitted = preview_bytes(
                &s,
                "arm64-apple-darwin27.2.0",
                "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32",
            );
            assert_eq!(emitted, retained, "{repr}");
        }
        let mut wire = s.captured(MANIFEST, CURRENT_PROTOCOL);
        let response = kernel(&wire, "function-revision");
        let rev = &response["function_revision"];
        let site = &rev["resource_realizations"]["sites"][0];
        assert_eq!(site["constructor"]["name"], "Affine");
        assert_eq!(site["constructor"]["module"], json!(["geometry"]));
        assert_eq!(site["id"]["name"], "realize");
        assert_eq!(site["subject"], site["chart"]);
        assert_eq!(site["representation"], repr);
        wire["expected_function_revision"] = rev.clone();
        assert_eq!(kernel(&wire, "check")["function_revision_matched"], true);
        wire["expected_function_revision"]["resource_realizations"]["sites"][0]["constructor"] =
            site["id"].clone();
        assert_wire_rejected(&kernel(&wire, "check"), "E_FUNCTION_REVISION");
    }
}

#[test]
fn affine_wrappers_bind_fresh_subjects_constructor_dimension_and_physical_source() {
    let source = "use monad::float;
        resource fn main() -> Int {
            let a = Affine(F32<CC>, 2);
            let b = Affine(F32<CC>, 2,);
            let e = float::interpret(b::identity, b, NativeFast);
            value { 0 }
        }";
    let s = fixture(source);
    let wire = s.captured(MANIFEST, CURRENT_PROTOCOL);
    let response = kernel(&wire, "function-revision");
    assert_eq!(response["ok"], true, "{response}");
    let charts = response["function_revision"]["resource_realizations"]["charts"]
        .as_array()
        .unwrap();
    assert_eq!(charts.len(), 2);
    assert_ne!(charts[0]["subject"], charts[1]["subject"]);
    for (key, value) in [
        ("dimension", json!(3)),
        ("representation", json!("real32")),
        ("result", json!("other")),
    ] {
        let mut forged = wire.clone();
        body(&mut forged)[0][key] = value;
        assert_wire_rejected(&kernel(&forged, "check"), "E_PROTOCOL");
    }
    for (from, to, code) in [
        ("b::identity, b", "a::identity, b", "E_REALIZATION"),
        ("= Affine(", "= foreign(", "E_REALIZATION"),
        (
            "use monad::float;",
            "mod Affine {} use monad::float;",
            "E_REALIZATION",
        ),
        ("F32<CC>, 2", "F32<CC>, 17", "E_LIMIT"),
    ] {
        s.write("app/main.vast", &source.replace(from, to));
        common::expect_code(&s.check_manifest(MANIFEST), code);
    }
}

#[test]
fn complex_charts_copy_both_components_and_bind_the_full_model_chain() {
    let s = fixture(COMPLEX);
    let mut previous = None;
    for (rep, source) in [
        ("F64<CC>", COMPLEX.to_string()),
        (
            "F32<CC>",
            COMPLEX
                .replace("F64<CC>", "F32<CC>")
                .replace("complex_bits", "complex32_bits")
                .replace("9223372036854775808", "2147483648")
                .replace("9218868437227405378", "2139095106"),
        ),
    ] {
        s.write("app/main.vast", &source);
        assert_eq!(s.check_build_and_run(MANIFEST), exits(0));
        check_llvm_identity(&s, if rep == "F32<CC>" { 3 } else { 1 });
        let mut wire = s.captured(MANIFEST, CURRENT_PROTOCOL);
        let result = kernel(&wire, "function-revision");
        assert_eq!(result["ok"], true, "{result}");
        let revision = &result["function_revision"];
        let evidence = &revision["resource_realizations"];
        let chart = &evidence["charts"][0];
        for (field, name) in [
            ("subject", "Plane"),
            ("model", "CC"),
            ("carrier", "Pairs"),
            ("real_model", "RR"),
            ("real_carrier", "Cauchy"),
        ] {
            assert_eq!(chart[field]["name"], name, "{field}");
        }
        assert_eq!(chart["coordinates"], json!(["z", "w"]));
        assert!(
            evidence["sites"]
                .as_array()
                .unwrap()
                .iter()
                .all(|site| site["representation"] == rep)
        );
        assert_eq!(evidence["runs"][0]["flags"], "Unavailable");
        assert_eq!(evidence["runs"][0]["graph"]["name"], "idP");
        if let Some(old) = previous {
            wire["expected_function_revision"] = old;
            assert_wire_rejected(&kernel(&wire, "check"), "E_FUNCTION_REVISION");
        }
        previous = Some(revision.clone());
        wire["expected_function_revision"] = revision.clone();
        wire["expected_function_revision"]["resource_realizations"]["charts"][0]["real_model"] =
            chart["carrier"].clone();
        assert_wire_rejected(&kernel(&wire, "check"), "E_FUNCTION_REVISION");
    }
}

#[test]
fn complex_identity_rejects_other_objects_models_charts_and_precisions() {
    let extra = "indexed affine Other = Affine(CC, 2)[z, w];\nindexed affine Real = Affine(RR, 2)[z,w];\nindexed morphism otherId = identity(Other);\n";
    let source = COMPLEX.replace("resource fn main()", &format!("{extra}resource fn main()"));
    let s = fixture(&source);
    for (from, to) in [
        ("interpret(idP,", "interpret(otherId,"),
        ("Plane::standard_chart", "Other::standard_chart"),
        (
            "(Plane, Plane::standard_chart)",
            "(Real, Real::standard_chart)",
        ),
        ("realize::<F64<CC>>", "realize::<F64<RR>>"),
        ("realize::<F64<CC>>", "realize::<F32<CC>>"),
        ("identity(Plane)", "identity(CC)"),
        ("(idP, r, NativeFast)", "(idP, r, strict_profile)"),
    ] {
        s.write("app/main.vast", &checked_replace(&source, from, to));
        let output = s.check_manifest(MANIFEST);
        assert!(!output.status.success(), "accepted {to}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("main.vast:"),
            "{to}: {output:?}"
        );
    }
}
