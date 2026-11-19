mod common;

use common::{Scratch, assert_wire_rejected, checked_replace, exits, expect_code, kernel};
use serde_json::json;

const SOURCE: &str = include_str!("fixtures/exact-affine-model.vast");
const MANIFEST: &str = "app/Vastitas.toml";

#[test]
fn exact_affines_select_named_carriers_and_meadows_in_the_public_revision() {
    let p = Scratch::empty("exact affine model");
    p.write_package("app", SOURCE, "");
    assert_eq!(p.check_build_and_run(MANIFEST), exits(42));
    let wire = p.captured(MANIFEST, 10);
    let revision = kernel(&wire, "function-revision")["function_revision"].clone();
    assert!(revision.is_object());
    let mut same = wire.clone();
    same["expected_function_revision"] = revision.clone();
    assert_eq!(kernel(same, "check")["ok"], true);

    let changed = checked_replace(
        SOURCE,
        "indexed affine Plane",
        "indexed meadow Other = complex_meadow(ComplexCarrier, RR);\nindexed affine Plane",
    )
    .replace("Affine(CC, 2)", "Affine(Other, 2)");
    p.write("app/main.vast", &changed);
    let mut other = p.captured(MANIFEST, 10);
    assert_eq!(kernel(&other, "check")["ok"], true);
    other["expected_function_revision"] = revision;
    assert_wire_rejected(&kernel(other, "check"), "E_FUNCTION_REVISION");

    let mut forged = wire;
    let definition = &mut forged["packages"][0]["modules"][0]["indexed_declarations"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|d| d["name"] == "CC")
        .unwrap()["definition"];
    definition["is_field"] = json!(true);
    assert_wire_rejected(&kernel(forged, "check"), "E_PROTOCOL");
}

#[test]
fn static_model_selection_preserves_the_complete_constant_entry_module() {
    let p = Scratch::empty("static affine LLVM");
    p.write_package("app", SOURCE, "");
    let preview = || {
        let result = p
            .command("check", MANIFEST)
            .args([
                "--llvm-preview",
                "--target-triple",
                "x86_64-unknown-linux-gnu",
                "--data-layout",
                "e-p:64:64",
            ])
            .output()
            .unwrap();
        common::success(&result);
        result.stdout
    };
    let with_models = preview();
    assert!(
        std::str::from_utf8(&with_models)
            .unwrap()
            .ends_with("  ret i32 u0x2A\n}\n")
    );
    p.write("app/main.vast", "fn main() -> Int { 42 }");
    assert_eq!(preview(), with_models);
}

#[test]
fn exact_affines_reject_wrong_kinds_dimensions_and_nominal_components() {
    let p = Scratch::empty("rejected exact affine model");
    p.write_package("app", SOURCE, "");
    for (from, to, error) in [
        (
            "complex_pairs(RealCarrier)",
            "complex_pairs(RR)",
            "E_EXACT_MODEL",
        ),
        (
            "real_meadow(RealCarrier)",
            "real_meadow(ComplexCarrier)",
            "E_EXACT_MODEL",
        ),
        (
            "complex_meadow(ComplexCarrier, RR)",
            "complex_meadow(RealCarrier, RR)",
            "E_EXACT_MODEL",
        ),
        (
            "Affine(CC, 2)",
            "Affine(ComplexCarrier, 2)",
            "E_EXACT_MODEL",
        ),
        ("Affine(CC, 2)", "Affine(Plane, 2)", "E_EXACT_MODEL"),
        ("2)[z, w]", "1)[z, w]", "E_AFFINE_COORDINATE"),
        ("2)[z, w]", "2)[z, z]", "E_AFFINE_COORDINATE"),
        (
            "indexed meadow RR = real_meadow(RealCarrier);",
            "indexed carrier Alias = cauchy_qq;\nindexed meadow RR = real_meadow(Alias);",
            "E_EXACT_MODEL",
        ),
    ] {
        p.write("app/main.vast", &checked_replace(SOURCE, from, to));
        expect_code(&p.check_manifest(MANIFEST), error);
    }
}

#[test]
fn public_check_matches_physical_model_declarations_and_qualified_operand_spans() {
    let p = Scratch::empty("physical exact models");
    p.write_package("app", "mod fields;\nmod affine { pub indexed affine Plane = Affine(super::fields::CC, 01)[z,]; }\nfn main() -> Int { 0 }", "");
    p.write("app/fields.vast", "// 世界 indexed meadow Missing = real_meadow(Bad);\r\npub indexed carrier R = cauchy_qq; pub indexed carrier C = complex_pairs(R);\npub indexed meadow RR = real_meadow(R); pub indexed meadow CC = complex_meadow(C, RR);\npub indexed meadow DD = complex_meadow(C, RR);");
    let wire = p.captured(MANIFEST, 10);
    assert_eq!(kernel(&wire, "check")["ok"], true);
    for mutation in [
        "target",
        "operand span",
        "declaration span",
        "visibility",
        "missing",
        "chart",
    ] {
        let mut changed = wire.clone();
        let decls = changed["packages"][0]["modules"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .filter_map(|m| m["indexed_declarations"].as_array_mut())
            .find(|ds| ds.iter().any(|d| d["name"] == "Plane"))
            .unwrap();
        let i = decls.iter().position(|d| d["name"] == "Plane").unwrap();
        let decl = &mut decls[i];
        match mutation {
            "target" => decl["definition"]["model"]["path"][2] = json!("DD"),
            "operand span" => decl["definition"]["model"]["span"]["column"] = json!(1),
            "declaration span" => decl["span"]["line"] = json!(1),
            "visibility" => decl["public"] = json!(false),
            "missing" => {
                decls.remove(i);
            }
            "chart" => decl["definition"]["coordinates"][0] = json!("w"),
            _ => unreachable!(),
        }
        assert_wire_rejected(&kernel(changed, "check"), "E_PROTOCOL");
    }
}

#[test]
fn exact_declarations_keep_their_physical_package_and_module() {
    let p = Scratch::empty("exact declaration owners");
    p.write_package("dep", "pub indexed carrier Base = cauchy_qq;", "");
    p.write_package(
        "app",
        "mod outer { pub mod nested; } mod sibling; pub indexed carrier Root = cauchy_qq; fn main() -> Int { 42 }",
        "dep = { path = '../dep' }",
    );
    p.write(
        "app/outer/nested.vast",
        "pub indexed carrier Nested = cauchy_qq;",
    );
    p.write(
        "app/sibling.vast",
        "mod inner { pub indexed carrier Inner = cauchy_qq; }",
    );
    let wire = p.captured(MANIFEST, 10);
    let accepted = kernel(&wire, "check");
    assert_eq!(accepted["ok"], true, "{accepted}");
    for (from, to) in [("Nested", "Inner"), ("Inner", "Root"), ("Base", "Root")] {
        let mut forged = wire.clone();
        let packages = forged["packages"].as_array_mut().unwrap();
        let mut modules: Vec<_> = packages
            .iter_mut()
            .flat_map(|p| p["modules"].as_array_mut().unwrap())
            .filter_map(|m| m.get_mut("indexed_declarations")?.as_array_mut())
            .collect();
        let moved = modules
            .iter_mut()
            .find_map(|ds| {
                let i = ds.iter().position(|d| d["name"] == from)?;
                Some(ds.remove(i))
            })
            .unwrap();
        let destination = modules
            .into_iter()
            .find(|declarations| declarations.iter().any(|d| d["name"] == to))
            .unwrap();
        destination.push(moved);
        let result = kernel(forged, "check");
        assert_wire_rejected(&result, "E_PROTOCOL");
        assert!(
            result["diagnostics"][0]["message"]
                .as_str()
                .unwrap()
                .contains("physical package or module"),
            "{result}"
        );
    }
}
