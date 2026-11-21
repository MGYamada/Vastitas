//! Adversarial package requests bypass the Rust namespace frontend entirely.
mod common;
use common::{CURRENT_PROTOCOL, Scratch, assert_wire_rejected, kernel};
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

const LIBRARY: &str = "pub fn value() -> Int { 42 }";

fn request_with(alias: &str, library: &str) -> Value {
    let scratch = common::Scratch::empty("physical namespace request");
    scratch.write_package("lib", library, "");
    scratch.write_package(
        "app",
        &format!("fn main() -> Int {{ {alias}::value() }}"),
        &format!("{alias}={{path='../lib'}}"),
    );
    let mut wire = scratch.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    wire["packages"]
        .as_array_mut()
        .unwrap()
        .sort_by(|a, b| a["name"].as_str().cmp(&b["name"].as_str()));
    wire
}

fn request() -> Value {
    request_with("lib", LIBRARY)
}

fn check(raw: &Value) -> Value {
    let response = common::kernel(raw, "check");
    assert_eq!(response["version"], raw["version"]);
    response
}

fn rejects(raw: &Value, code: &str) {
    let response = check(raw);
    common::assert_wire_rejected(&response, code);
}

#[test]
fn package_order_and_aliases_preserve_resolution() {
    let mut raw = request();
    assert_eq!(check(&raw)["ok"], true);
    raw["packages"].as_array_mut().unwrap().reverse();
    assert_eq!(check(&raw)["ok"], true);
    // A coherent alias change updates its physical spelling and envelope together.
    let renamed = request_with("renamed", LIBRARY);
    assert_eq!(check(&renamed)["ok"], true);
    raw["packages"][1]["dependencies"][0]["alias"] = json!("alt");
    raw["packages"][1]["modules"][0]["functions"][0]["body"]["result"]["callee"] =
        json!("alt::value");
    rejects(&raw, "E_MANIFEST_SOURCE");

    let scratch = Scratch::empty("physical call through a dependency alias");
    scratch.write_package("lib", LIBRARY, "");
    scratch.write_package(
        "app",
        "fn main() -> Int { lib::value() }",
        "lib={path='../lib'}\nalt={path='../lib'}",
    );
    let mut two_aliases = scratch.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    assert_eq!(check(&two_aliases)["ok"], true);
    let app = two_aliases["packages"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|pkg| pkg["name"] == "app")
        .unwrap();
    app["modules"][0]["functions"][0]["body"]["result"]["callee"] = json!("alt::value");
    rejects(&two_aliases, "E_FUNCTION_SOURCE");
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
    let mut raw = base;
    raw["packages"][0]["modules"][0]["functions"][0]["body"]["result"]["callee"] =
        json!("lib::missing");
    rejects(&raw, "E_NAME");
}

#[test]
fn imports_do_not_grant_method_ownership() {
    let mut raw = request();
    let declarations = module("fn choose() domain(()); fn choose() -> Int { 1 }");
    raw["packages"][1]["modules"][0]["generics"] = declarations["generics"].clone();
    let mut method = declarations["methods"][0].clone();
    method["name"] = json!("lib::choose");
    raw["packages"][0]["modules"][0]["methods"] = json!([method]);
    rejects(&raw, "E_OWNER");
}

#[test]
fn unused_dependency_functions_remain_checked() {
    let mut raw = request();
    raw["packages"][1]["modules"][0]["functions"]
        .as_array_mut()
        .unwrap()
        .push(module("fn unused() -> Int { 0 }")["functions"][0].clone());
    raw["packages"][1]["modules"][0]["functions"][1]["body"]["result"] =
        json!({"kind":"boolean","value":true,"span":span()});
    rejects(&raw, "E_TYPE");
}

#[test]
fn many_declarations_share_indexed_resolution_and_retain_visibility() {
    let mut source = format!("{LIBRARY}\n");
    for i in 0..1500 {
        source.push_str(&format!(
            "fn check{i}() -> Int {{ let local = value(); local }}\n"
        ));
    }
    let mut raw = request_with("lib", &source);
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

fn module_at<'a>(request: &'a mut Value, path: &[&str]) -> &'a mut Value {
    request["packages"][0]["modules"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|m| m["path"] == json!(path))
        .unwrap()
}

#[test]
fn an_import_cannot_redirect_an_unchanged_call_to_another_function() {
    let scratch = Scratch::empty("physical import path");
    let source = "mod defs;\nuse defs::left as picked;\nfn main() -> Int { picked() }";
    scratch.write_package("choice", source, "");
    scratch.write(
        "choice/defs.vast",
        "pub fn left() -> Int { 42 }\npub fn next() -> Int { 7 }",
    );
    let manifest = "choice/Vastitas.toml";
    let first = scratch.captured(manifest, CURRENT_PROTOCOL);
    scratch.write("choice/main.vast", &source.replace("::left", "::next"));
    let second = scratch.captured(manifest, CURRENT_PROTOCOL);
    let llvm_check = [
        "llvm-check",
        "aarch64-apple-darwin",
        "e-m:o-i64:64-n32:64-S128",
    ];
    let before = common::kernel_with_args(&first, &llvm_check);
    let after = common::kernel_with_args(&second, &llvm_check);
    assert_eq!(before["ok"], true, "{before}");
    assert_eq!(after["ok"], true, "{after}");
    assert_ne!(before["llvm"]["ir"], after["llvm"]["ir"]);

    let mut stale = second;
    stale["root_source"] = first["root_source"].clone();
    let llvm_build = ["llvm-build", llvm_check[1], llvm_check[2]];
    for args in [
        &["check"][..],
        &["emit"],
        &["function-revision"],
        &llvm_check,
        &llvm_build,
    ] {
        let rejected = common::kernel_with_args(&stale, args);
        assert_wire_rejected(&rejected, "E_IMPORT_SOURCE");
        let span = &rejected["diagnostics"][0]["span"];
        assert_eq!(
            (span["line"].as_u64(), span["column"].as_u64()),
            (Some(2), Some(11))
        );
        assert!(rejected.get("llvm").is_none());
    }
}

#[test]
fn unused_reexports_replay_their_alias_visibility_module_and_full_span() {
    let scratch = Scratch::empty("physical reexport");
    let source = "mod defs; mod inner { pub use super::defs::left as public_name; use super::defs::right; }\nfn main() -> Int { 7 }";
    scratch.write_package("choice", source, "");
    scratch.write(
        "choice/defs.vast",
        "pub fn left() -> Int { 42 } pub fn right() -> Int { 7 }",
    );
    let original = scratch.captured("choice/Vastitas.toml", CURRENT_PROTOCOL);
    assert_eq!(kernel(&original, "check")["ok"], true);
    for (from, to) in [
        ("as public_name", "as public_mark"),
        ("pub use", "    use"),
        ("use super::defs::right;", "                       "),
    ] {
        let mut changed = original.clone();
        changed["root_source"]["text"] = json!(common::checked_replace(source, from, to));
        assert_wire_rejected(&kernel(changed, "emit"), "E_IMPORT_SOURCE");
    }
    let mut omitted = original.clone();
    module_at(&mut omitted, &["inner"])["imports"]
        .as_array_mut()
        .unwrap()
        .pop();
    assert_wire_rejected(&kernel(omitted, "function-revision"), "E_IMPORT_SOURCE");
    let mut span = original.clone();
    module_at(&mut span, &["inner"])["imports"][0]["span"]["column"] = json!(1);
    assert_wire_rejected(&kernel(span, "check"), "E_IMPORT_SOURCE");
    let mut renamed = original;
    module_at(&mut renamed, &["inner"])["imports"][1]["alias"] = json!("other");
    assert_wire_rejected(&kernel(renamed, "check"), "E_IMPORT_SOURCE");
}

#[test]
fn assembled_family_aliases_bind_the_written_import_even_for_an_identical_target() {
    let source = include_str!("../llvm/fixtures/borrowed-operator/main.vast");
    let manifest = format!(
        "{}peer = {{ path = \"../lib\" }}\n",
        include_str!("../examples/packages/authority/edit-borrow/app/Vastitas.toml")
    );
    let scratch = common::example_package(
        "two names for one borrowed family",
        "examples/packages/authority/edit-borrow",
        &[("app/main.vast", source), ("app/Vastitas.toml", &manifest)],
    );
    let original = scratch.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    let revision = kernel(&original, "function-revision");
    assert_eq!(revision["ok"], true);
    let llvm = [
        "llvm-build",
        "aarch64-apple-darwin",
        "e-m:o-i64:64-n32:64-S128",
    ];
    let before = common::kernel_with_args(&original, &llvm);
    assert_eq!(before["ok"], true, "{before}");
    scratch.write(
        "app/main.vast",
        &common::checked_replace(source, "use base::", "use peer::"),
    );
    let mut changed = scratch.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    let after = common::kernel_with_args(&changed, &llvm);
    assert_eq!(after["ok"], true, "{after}");
    assert_eq!(before["llvm"]["ir"], after["llvm"]["ir"]);
    let mut mixed = changed.clone();
    mixed["root_source"] = original["root_source"].clone();
    assert_wire_rejected(&common::kernel_with_args(&mixed, &llvm), "E_IMPORT_SOURCE");
    changed["expected_function_revision"] = revision["function_revision"].clone();
    assert_wire_rejected(
        &common::kernel_with_args(&changed, &llvm),
        "E_FUNCTION_REVISION",
    );
}

#[test]
fn an_implicit_indexed_name_cannot_become_an_explicit_reserved_alias() {
    let scratch = Scratch::empty("written indexed import alias");
    let source = "pub indexed finite Point { x; }\nmod exposed { pub use super::Point         ; } fn main() -> Int { 7 }";
    scratch.write_package("choice", source, "");
    let mut original = scratch.captured("choice/Vastitas.toml", CURRENT_PROTOCOL);
    assert_eq!(kernel(&original, "check")["ok"], true);
    let explicit = source.replace("Point         ;", "Point as Point;");
    assert_eq!(source.len(), explicit.len());
    scratch.write("choice/main.vast", &explicit);
    common::expect_code(
        &scratch.check_manifest("choice/Vastitas.toml"),
        "E_RESERVED",
    );
    original["root_source"]["text"] = json!(explicit);
    let rejected = kernel(&original, "check");
    assert_wire_rejected(&rejected, "E_RESERVED");
    assert_eq!(rejected["diagnostics"][0]["span"]["column"], 39);
}

#[test]
fn inline_and_external_modules_replay_their_declarations_in_the_parent_file() {
    let scratch = Scratch::empty("module declaration origins");
    let source = "pub mod ext;\nmod outer { pub mod nested {} }\nfn main() -> Int { 7 }";
    scratch.write_package("choice", source, "");
    scratch.write("choice/ext.vast", "pub fn value() -> Int { 42 }");
    let original = scratch.captured("choice/Vastitas.toml", CURRENT_PROTOCOL);
    assert_eq!(kernel(&original, "check")["ok"], true);
    for (path, from, to) in [
        (&["ext"][..], "pub mod ext;", "    mod ext;"),
        (&["outer", "nested"][..], "pub mod nested", "    mod nested"),
    ] {
        let mut changed = original.clone();
        let decl = module_at(&mut changed, path)["span"].clone();
        changed["root_source"]["text"] = json!(common::checked_replace(source, from, to));
        let rejected = kernel(&changed, "emit");
        assert_wire_rejected(&rejected, "E_MODULE_SOURCE");
        assert_eq!(rejected["diagnostics"][0]["span"]["start"], decl["start"]);
        let mut shortened = original.clone();
        module_at(&mut shortened, path)["span"]["end"] = decl["start"].clone();
        assert_wire_rejected(&kernel(shortened, "function-revision"), "E_MODULE_SOURCE");
    }
    let mut omitted = original;
    omitted["packages"][0]["modules"]
        .as_array_mut()
        .unwrap()
        .retain(|m| m["path"] != json!(["outer", "nested"]));
    assert_wire_rejected(&kernel(omitted, "check"), "E_MODULE_SOURCE");
}
