mod common;
use common::{Scratch, cli, kernel, success};
use serde_json::{Value, json};

const GEO: &str = include_str!("../examples/packages/indexed/geo.vast");
const MAIN: &str = include_str!("../examples/packages/indexed/main.vast");

fn fixture(source: &str) -> Scratch {
    let s = Scratch::empty("indexed wire");
    s.write(
        "Vastitas.toml",
        "[package]\nname='indexed_test'\nversion='0.1.0'\nroot='main.vast'\n",
    );
    s.write("main.vast", source);
    s.write("geo.vast", GEO);
    s
}

fn check(s: &Scratch) -> std::process::Output {
    cli()
        .current_dir(&s.0)
        .args(["check", "--manifest-path", "Vastitas.toml"])
        .output()
        .unwrap()
}

fn request(s: &Scratch) -> Value {
    common::captured_wire(
        cli()
            .current_dir(&s.0)
            .args(["check", "--manifest-path", "Vastitas.toml"]),
        7,
    )
}

#[track_caller]
fn rejected(source: &str, code: &str) -> String {
    let result = check(&fixture(source));
    assert!(!result.status.success(), "accepted {source}");
    common::expect_code(&result, code)
}

#[test]
fn declaration_package_and_static_fn_compile_to_native() {
    let adjacent = MAIN
        .replace(
            "let q:",
            "let same: Object<geo::Scheme, geo::QQ>= Y;\n    let q:",
        )
        .replace("> =", ">=");
    let s = fixture(&adjacent);
    success(&check(&s));
    success(
        &cli()
            .current_dir(&s.0)
            .args(["build", "--manifest-path", "Vastitas.toml", "-o", "program"])
            .output()
            .unwrap(),
    );
    let output = std::process::Command::new(s.0.join("program"))
        .output()
        .unwrap();
    success(&output);
    assert_eq!(output.stdout, b"42\n");
}

#[test]
fn indexed_calls_explain_missing_conversion_and_literal_pair_inference() {
    for (source, hint, code) in [
        (
            "mod geo; fn main() -> Int { nat_to_int(1) }",
            "arithmetic standard library",
            "E_NAME",
        ),
        (
            "mod geo; fn first(p: Pair<Nat>) -> Nat { pair_first(p) } fn main() -> Int { int(first(pair(0, 1))) }",
            "pair infers its operands independently",
            "E_TYPE",
        ),
    ] {
        let result = check(&fixture(source));
        assert!(!result.status.success());
        let message = String::from_utf8_lossy(&result.stderr);
        assert!(message.contains(hint), "{message}");
        let response = kernel(request(&fixture(source)), "check");
        common::assert_wire_rejected(&response, code);
        assert!(
            response["diagnostics"][0]["notes"]
                .as_array()
                .unwrap()
                .iter()
                .any(|note| note["message"].as_str().unwrap().contains(hint)),
            "{response}"
        );
    }
}

#[test]
fn actual_rust_wire_is_seven_and_older_envelopes_reject_declarations() {
    let original = request(&fixture(MAIN));
    assert_eq!(original["version"], 7);
    assert_eq!(kernel(&original, "check")["ok"], true);
    for version in [2, 3, 4, 5, 6] {
        let mut raw = original.clone();
        raw["version"] = json!(version);
        let result = kernel(raw, "check");
        common::assert_wire_rejected(&result, "E_PROTOCOL");
        assert_eq!(result["version"], version);
    }
    let mut flat = common::request("fn main() -> Int { 42 }", "old.vast");
    flat["indexed_declarations"] = json!([]);
    common::assert_wire_rejected(&kernel(flat, "check"), "E_PROTOCOL");
}

#[test]
fn forged_wire_metadata_never_becomes_checked_authority() {
    let original = request(&fixture(MAIN));
    let root = original["packages"][0]["modules"]
        .as_array()
        .unwrap()
        .iter()
        .position(|m| m["path"] == json!([]))
        .unwrap();
    let geo = original["packages"][0]["modules"]
        .as_array()
        .unwrap()
        .iter()
        .position(|m| m["path"] == json!(["geo"]))
        .unwrap();
    let pointers = [
        "/checked_core".into(),
        "/namespace_receipt".into(),
        "/packages/0/owner".into(),
        format!("/packages/0/modules/{geo}/indexed_declarations/0/owner"),
        format!("/packages/0/modules/{root}/functions/0/body/result/checked"),
        format!("/packages/0/modules/{root}/functions/0/params/0/ty/owner"),
    ];
    for pointer in pointers {
        let mut raw = original.clone();
        let (parent, key) = pointer.rsplit_once('/').unwrap();
        raw.pointer_mut(parent).unwrap()[key] = json!(true);
        let result = kernel(raw, "emit");
        assert_eq!(result["ok"], false, "{pointer}: {result}");
        assert_eq!(result["diagnostics"][0]["code"], "E_PROTOCOL", "{result}");
        assert!(result.get("lean_source").is_none());
    }
    let mut raw = original;
    raw["input"] = json!("flat");
    common::assert_wire_rejected(&kernel(raw, "check"), "E_PROTOCOL");
}

#[test]
fn same_dimensions_do_not_identify_separately_generated_objects() {
    rejected(
        "mod geo; fn main() -> Int { let X = geo::affine(2); let Y = geo::affine(2); let p: geo::Point<Y, geo::Base> = geo::origin(X); 0 }",
        "E_TYPE",
    );
}

#[test]
fn indexed_annotations_and_lambdas_preserve_scope() {
    rejected(
        "mod geo; fn main() -> Int { let X = geo::affine(2); let f = fn(n: Int) -> Int { n + int(geo::dimension(X)) }; 0 }",
        "E_CAPTURE",
    );
    rejected(
        "mod geo; fn main() -> Int { let escaped = { let X = geo::affine(2); let packed = pack geo::Pointed<geo::Scheme, geo::QQ> { witness: X, fields: [geo::origin(X)] }; unpack packed as { witness: Y, fields: [p] }; p }; 0 }",
        "E_ESCAPE",
    );
    let message = rejected(
        "mod geo; fn bad(f: Fn<geo::Point<geo::Base, geo::Base>, Int>) -> Int { 0 } fn main() -> Int { 0 }",
        "E_PROTOCOL",
    );
    assert!(
        message.contains("Fn signatures contain only scalars and recursive Fn types"),
        "{message}"
    );
}

#[test]
fn all_package_fields_and_unapplied_method_bodies_are_checked() {
    rejected(
        "mod geo; fn main() -> Int { let X = geo::affine(2); let packed = pack geo::Pointed<geo::Scheme, geo::QQ> { witness: X, fields: [] }; 0 }",
        "E_ENDPOINT",
    );
    rejected(
        "mod geo; generic choose(x) { domain (Int); } method choose(x: Int) -> Int { x } contribution bad: choose { method choose(x: Int) -> Int { true } } fn main() -> Int { choose(42) }",
        "E_TYPE",
    );
}

#[test]
fn rich_bodies_work_inside_scalar_methods_and_explicit_assemblies() {
    let source = "mod geo; generic choose(x) { domain (Int); } contribution add: choose { method choose(x: Int) -> Int { let X = geo::affine(2); let f = fn(y: Int) -> Int { y + 1 }; f(x) + int(geo::dimension(X)) } } assembly { apply add; seal choose; } fn main() -> Int { choose(39) }";
    success(&check(&fixture(source)));
}

#[test]
fn nongeometric_indexed_family_uses_the_same_annotation_checker() {
    let source = "mod geo; indexed family Record(domain, marker, natural, object(geo::Scheme)) = token constraints(over(3, 1)); fn inspect(X: Object<geo::Scheme, geo::QQ>, token: Record<geo::Scheme, geo::QQ, 18446744073709551616, X>) -> Int { int(geo::dimension(X)) } fn main() -> Int { 42 }";
    success(&check(&fixture(source)));
    rejected(&source.replace("18446744073709551616", "geo::QQ"), "E_TYPE");
    rejected(
        &source.replace(
            "geo::QQ, 18446744073709551616, X",
            "geo::QQ, 18446744073709551616",
        ),
        "E_TYPE",
    );
}
