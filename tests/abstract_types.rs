//! Selector-only abstract declarations cross protocol 4 and independent Lean checks.
mod common;
use common::{Scratch, cli, kernel, native, request, success};
use serde_json::json;
use std::process::Command;

fn reject(source: &str, code: &str) {
    common::reject(source, code, "abstract.vast");
}

const NUMERIC: &str = "abstract type Numeric; subtype Nat <: Numeric; subtype Int <: Numeric;";

#[test]
fn nominal_inheritance_and_same_inhabitants_do_not_collapse_selectors() {
    let declarations = [
        "abstract type General;",
        "abstract type Specific <: General;",
        "subtype Int <: Specific;",
        "abstract type Variety;",
        "abstract type Manifold;",
    ];
    for reversed in [false, true] {
        let mut items = declarations.to_vec();
        if reversed {
            items.reverse();
        }
        let source = format!(
            "{}
generic choose(x) {{ domain (Int); }}
method choose(x: General) -> Int {{ 0 }}
method choose(x: Specific) -> Int {{ 42 }}
fn main() -> Int {{ let f = fn(x: Int) -> Int {{ choose(x) }}; f(1) }}",
            items.join("\n")
        );
        native(&source, &[], "42", "abstract.vast");
    }
    reject(
        "abstract type Left; abstract type Right; subtype Int <: Left; subtype Int <: Right;
generic choose(x) { domain (Int); }
method choose(x: Left) -> Int { 1 }
method choose(x: Right) -> Int { 2 }",
        "E_DISPATCH_AMBIGUOUS",
    );
}

#[test]
fn multiple_inheritance_preserves_nominal_capability_product_order() {
    let source = "abstract type Left; abstract type Right; abstract type Both <: (Left, Right);
subtype Nat <: Both; subtype Int <: Left; subtype Bool <: Right;
generic choose(x) { domain (Nat), (Int), (Bool); }
method choose(x: Left) -> Int { 0 }
method choose(x: Right) -> Int { 0 }
method choose(x: Both) -> Int { 42 }
fn main() -> Int { let n: Nat = 1; choose(n) }";
    native(source, &[], "42", "abstract.vast");
    let crossed = format!(
        "{NUMERIC}
generic choose(x) {{ domain (Int); }}
method choose(x: Numeric) -> Int {{ 1 }}
method choose(x: Any) requires (HasOrder) -> Int {{ 2 }}"
    );
    reject(&crossed, "E_DISPATCH_AMBIGUOUS");
    native(
        &format!(
            "{crossed}
method choose(x: Numeric) requires (HasOrder) -> Int {{ 42 }}
fn main() -> Int {{ choose(1) }}"
        ),
        &[],
        "42",
        "abstract.vast",
    );
}

#[test]
fn malformed_hierarchies_and_memberships_are_rejected_even_without_generics() {
    for (source, code) in [
        ("abstract type A <: B; abstract type B <: A;", "E_HIERARCHY"),
        ("abstract type A <: A;", "E_HIERARCHY"),
        ("abstract type A <: Missing;", "E_NAME"),
        ("abstract type A <: Int;", "E_TYPE"),
        ("abstract type A <: (Any, Any);", "E_DUPLICATE"),
        (
            "abstract type A; subtype Int <: A; subtype Int <: A;",
            "E_DUPLICATE",
        ),
        ("abstract type A; subtype A <: A;", "E_TYPE"),
        (
            "abstract type A <: Number; subtype Bool <: A;",
            "E_HIERARCHY",
        ),
        ("subtype Bool <: Number;", "E_OWNER"),
        ("abstract type A; subtype Int <: Missing;", "E_NAME"),
    ] {
        reject(source, code);
        let response = kernel(request(source, "abstract.vast"), "check");
        assert_eq!(response["ok"], false, "{source}: {response}");
        assert_eq!(response["diagnostics"][0]["code"], code, "{response}");
    }
    let allowed = (0..58)
        .map(|i| format!("abstract type A{i};\n"))
        .collect::<String>();
    success(&common::check(&allowed, "abstract.vast"));
    reject(&(allowed + "abstract type Overflow;"), "E_LIMIT");
}

#[test]
fn selectors_do_not_create_value_types_or_change_body_audits() {
    for source in [
        format!("{NUMERIC} fn f(x: Numeric) -> Int {{ 0 }}"),
        format!("{NUMERIC} fn f(x: Fn<Numeric, Int>) -> Int {{ 0 }}"),
    ] {
        reject(&source, "E_UNSUPPORTED");
    }
    let mut forged = request(
        &format!("{NUMERIC} fn f(x: Int) -> Int {{ 0 }}"),
        "abstract.vast",
    );
    forged["functions"][0]["params"][0]["ty"]["name"] = json!("Numeric");
    assert_eq!(kernel(forged, "check")["diagnostics"][0]["code"], "E_TYPE");
    for source in [
        format!("{NUMERIC} generic f(x) {{ domain (Numeric); }}"),
        format!("{NUMERIC} generic f(x) {{ domain; }} method f(x: Numeric) -> Nat {{ x }}"),
        format!(
            "{NUMERIC} generic f(x) {{ domain (Nat); }} method f(x: Numeric) -> Int {{ x }} method f(x: Nat) -> Int {{ int(x) }}"
        ),
    ] {
        reject(&source, "E_TYPE");
    }
    reject(
        &format!(
            "{NUMERIC} generic f(x) {{ domain (Nat); }} method f(x: Numeric) -> Int {{ 0 }} fn main() -> Int {{ f(0) }}"
        ),
        "E_DISPATCH_DOMAIN",
    );
}

#[test]
fn protocol_four_is_explicit_and_legacy_requests_stay_unchanged() {
    let raw = request(
        &format!("{NUMERIC} fn main() -> Int {{ 42 }}"),
        "abstract.vast",
    );
    assert_eq!(raw["version"], 4);
    assert_eq!(raw["input"], "flat");
    assert_eq!(kernel(&raw, "check")["ok"], true);
    for mutation in ["downgrade", "mode", "missing_mode", "owner", "path", "span"] {
        let mut bad = raw.clone();
        match mutation {
            "downgrade" => {
                bad["version"] = json!(2);
                bad.as_object_mut().unwrap().remove("input");
            }
            "mode" => bad["input"] = json!("package"),
            "missing_mode" => {
                bad.as_object_mut().unwrap().remove("input");
            }
            "owner" => bad["abstract_types"][0]["owner"] = json!("trusted"),
            "path" => bad["subtypes"][0]["target"]["path"] = json!([]),
            _ => bad["abstract_types"][0]["span"]["line"] = json!(0),
        }
        assert_eq!(kernel(bad, "check")["ok"], false, "{mutation}");
    }
    let legacy = request("fn main() -> Int { 42 }", "legacy.vast");
    assert_eq!(legacy["version"], 2);
    assert!(legacy.get("input").is_none());
    assert!(legacy.get("abstract_types").is_none());
    assert_eq!(kernel(legacy, "check")["ok"], true);
}

fn package(s: &Scratch, name: &str, source: &str, deps: &str) {
    s.write(
        &format!("{name}/Vastitas.toml"),
        &format!(
            "[package]\nname='{name}'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\n{deps}\n"
        ),
    );
    s.write(&format!("{name}/main.vast"), source);
}
fn package_check(s: &Scratch) -> std::process::Output {
    cli()
        .current_dir(&s.0)
        .args(["check", "--manifest-path", "app/Vastitas.toml"])
        .output()
        .unwrap()
}

#[test]
fn package_aliases_preserve_nominal_identity_and_exact_module_membership_authority() {
    let s = Scratch::empty("abstract packages");
    package(
        &s,
        "lib",
        "pub mod types { pub abstract type Numeric; subtype Int <: Numeric; } pub use types::Numeric as Exported;",
        "",
    );
    let app = "use dep::Exported as N; generic f(x) { domain (Int); } method f(x: N) -> Int { 42 } fn main() -> Int { f(1) }";
    package(&s, "app", app, "dep={path='../lib'}");
    success(&package_check(&s));
    success(
        &cli()
            .current_dir(&s.0)
            .args([
                "build",
                "--manifest-path",
                "app/Vastitas.toml",
                "-o",
                "program",
            ])
            .output()
            .unwrap(),
    );
    let out = Command::new(s.0.join("program")).output().unwrap();
    success(&out);
    assert_eq!(out.stdout, b"42\n");
    for source in [
        format!("{app} subtype Nat <: N;"),
        "mod a { pub abstract type A; mod child { subtype Int <: super::A; } }".into(),
    ] {
        s.write("app/main.vast", &source);
        let output = package_check(&s);
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("E_OWNER"));
    }
    s.write("app/main.vast", "mod a { abstract type Hidden; } generic f(x) { domain; } method f(x: a::Hidden) -> Int { 0 }");
    let output = package_check(&s);
    assert!(String::from_utf8_lossy(&output.stderr).contains("E_VISIBILITY"));
}

fn raw_module(source: &str) -> serde_json::Value {
    let mut flat = request(source, "abstract-package.vast");
    for field in ["functions", "generics", "abstract_types"] {
        if let Some(declarations) = flat
            .get_mut(field)
            .and_then(serde_json::Value::as_array_mut)
        {
            for declaration in declarations {
                declaration["public"] = json!(true);
            }
        }
    }
    json!({"path":[], "public":true, "span":{"start":0,"end":0,"line":1,"column":1},
        "imports":[], "functions":flat["functions"], "generics":flat["generics"], "methods":flat["methods"],
        "abstract_types":flat.get("abstract_types").cloned().unwrap_or(json!([])),
        "subtypes":flat.get("subtypes").cloned().unwrap_or(json!([]))})
}

#[test]
fn raw_package_ir_cannot_forge_membership_authority_visibility_or_winners() {
    let mut app = raw_module(
        "generic f(x) { domain (Int); } method f(x: Numeric) -> Int { 42 } fn main() -> Int { f(1) }",
    );
    app["methods"][0]["params"][0]["ty"]["name"] = json!("lib::Numeric");
    let raw = json!({"version":4,"input":"package","file":"raw.vast","root":"/app/Vastitas.toml","packages":[
        {"source":"/app/Vastitas.toml","name":"app","version":"0.1.0","dependencies":[{"alias":"lib","target":"/lib/Vastitas.toml"}],"modules":[app]},
        {"source":"/lib/Vastitas.toml","name":"lib","version":"0.1.0","dependencies":[],"modules":[raw_module("abstract type Numeric; subtype Int <: Numeric;")]}
    ]});
    assert_eq!(kernel(&raw, "check")["ok"], true);
    let mut unauthorized = raw.clone();
    let mut membership = unauthorized["packages"][1]["modules"][0]["subtypes"][0].clone();
    membership["target"]["path"] = json!(["lib", "Numeric"]);
    unauthorized["packages"][0]["modules"][0]["subtypes"] = json!([membership]);
    assert_eq!(
        kernel(unauthorized, "check")["diagnostics"][0]["code"],
        "E_OWNER"
    );
    let mut hidden = raw.clone();
    hidden["packages"][1]["modules"][0]["abstract_types"][0]["public"] = json!(false);
    assert_eq!(
        kernel(hidden, "check")["diagnostics"][0]["code"],
        "E_VISIBILITY"
    );
    for field in ["owner", "selected", "hierarchy"] {
        let mut forged = raw.clone();
        forged["packages"][0]["modules"][0]["methods"][0][field] = json!("trusted");
        assert_eq!(
            kernel(forged, "check")["diagnostics"][0]["code"],
            "E_PROTOCOL"
        );
    }
}
