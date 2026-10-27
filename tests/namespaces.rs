//! Protocol-3 adversarial inputs bypass the Rust namespace frontend entirely.
mod common;
use serde_json::{Value, json};

fn span() -> Value {
    json!({"start":0,"end":1,"line":1,"column":1})
}

fn module(source: &str) -> Value {
    let mut flat =
        serde_json::to_value(vastitas::frontend::parse(source, "raw.vast").unwrap()).unwrap();
    for f in flat["functions"].as_array_mut().unwrap() {
        f["public"] = json!(true);
    }
    for g in flat["generics"].as_array_mut().unwrap() {
        g["public"] = json!(true);
    }
    json!({"path":[],"public":true,"span":span(),"imports":[],
        "functions":flat["functions"],"generics":flat["generics"],"methods":flat["methods"]})
}

fn request() -> Value {
    let mut app = module("fn main() -> Int { 0 }");
    app["functions"][0]["body"]["result"] =
        json!({"kind":"call","callee":"lib::value","args":[],"span":span()});
    json!({"version":3,"file":"raw.vast","root":"/app/Vastitas.toml","packages":[
        {"source":"/app/Vastitas.toml","name":"app","version":"0.1.0",
         "dependencies":[{"alias":"lib","target":"/lib/Vastitas.toml"}],"modules":[app]},
        {"source":"/lib/Vastitas.toml","name":"lib","version":"0.1.0",
         "dependencies":[],"modules":[module("fn value() -> Int { 42 }")]}
    ]})
}

fn check(raw: &Value) -> Value {
    let response = common::kernel(raw, "check");
    assert_eq!(response["version"], raw["version"]);
    response
}

fn rejects(raw: &Value, code: &str) {
    let response = check(raw);
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(response["diagnostics"][0]["code"], code, "{response}");
}

#[test]
fn package_order_and_aliases_preserve_resolution() {
    let mut raw = request();
    assert_eq!(check(&raw)["ok"], true);
    raw["packages"].as_array_mut().unwrap().reverse();
    assert_eq!(check(&raw)["ok"], true);
    raw["packages"][1]["dependencies"][0]["alias"] = json!("renamed");
    raw["packages"][1]["modules"][0]["functions"][0]["body"]["result"]["callee"] =
        json!("renamed::value");
    assert_eq!(check(&raw)["ok"], true);
}

#[test]
fn forged_owner_dependency_visibility_and_reference_are_rejected() {
    let base = request();
    let mut raw = base.clone();
    raw["packages"][1]["modules"][0]["functions"][0]["owner"] = json!("app");
    rejects(&raw, "E_PROTOCOL");
    let mut raw = base.clone();
    raw["packages"][0]["dependencies"][0]["target"] = json!("missing");
    rejects(&raw, "E_NAME");
    let mut raw = base.clone();
    raw["packages"][1]["modules"][0]["functions"][0]["public"] = json!(false);
    rejects(&raw, "E_VISIBILITY");
    let mut raw = base.clone();
    raw["packages"][0]["modules"][0]["functions"][0]["body"]["result"]["callee"] =
        json!("lib::missing");
    rejects(&raw, "E_NAME");
    let mut raw = base;
    raw["version"] = json!(2);
    rejects(&raw, "E_PROTOCOL");
}

#[test]
fn imports_do_not_grant_method_ownership() {
    let mut raw = request();
    let declarations = module("generic choose() { domain (); } method choose() -> Int { 1 }");
    raw["packages"][1]["modules"][0]["generics"] = declarations["generics"].clone();
    let mut method = declarations["methods"][0].clone();
    method["name"] = json!("lib::choose");
    raw["packages"][0]["modules"][0]["methods"] = json!([method]);
    rejects(&raw, "E_OWNER");
}

#[test]
fn unused_dependencies_and_legacy_protocol_remain_checked() {
    let mut raw = request();
    raw["packages"][1]["modules"][0]["functions"]
        .as_array_mut()
        .unwrap()
        .push(module("fn unused() -> Int { 0 }")["functions"][0].clone());
    raw["packages"][1]["modules"][0]["functions"][1]["body"]["result"] =
        json!({"kind":"boolean","value":true,"span":span()});
    rejects(&raw, "E_TYPE");
    let legacy = serde_json::to_value(
        vastitas::frontend::parse("fn main() -> Int { 42 }", "legacy.vast").unwrap(),
    )
    .unwrap();
    assert_eq!(check(&legacy)["ok"], true);
}

#[test]
fn many_declarations_share_indexed_resolution_and_retain_visibility() {
    let mut raw = request();
    let mut source = String::from("fn value() -> Int { 42 }\n");
    for i in 0..1500 {
        source.push_str(&format!(
            "fn check{i}() -> Int {{ let local = value(); local }}\n"
        ));
    }
    raw["packages"][1]["modules"][0] = module(&source);
    assert_eq!(check(&raw)["ok"], true);
    // Reordering the declaration table cannot change identity or visibility.
    raw["packages"][1]["modules"][0]["functions"]
        .as_array_mut()
        .unwrap()
        .reverse();
    assert_eq!(check(&raw)["ok"], true);
    raw["packages"][1]["modules"][0]["functions"][1500]["public"] = json!(false);
    rejects(&raw, "E_VISIBILITY");
}
