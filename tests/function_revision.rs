mod common;

use common::{CURRENT_PROTOCOL, Scratch, assert_wire_rejected, kernel};
use serde_json::{Value, json};

fn pin(input: &Value, revision: &Value) -> Value {
    let mut pinned = input.clone();
    pinned["expected_function_revision"] = revision.clone();
    pinned
}

fn revision(input: &Value) -> Value {
    let response = kernel(input, "function-revision");
    assert_eq!(response["ok"], true, "{response}");
    response.get("function_revision").unwrap().clone()
}

#[test]
fn assembled_owners_come_from_their_physical_package_manifests() {
    let raw = common::captured_wire(
        common::manifest_command(
            "check",
            common::root().join("llvm/fixtures/borrowed-operator/Vastitas.toml"),
        ),
        CURRENT_PROTOCOL,
    );
    let evidence = revision(&raw);
    let target: Value = serde_json::from_str(include_str!(
        "../experiments/compiler_validation/llvm/results/macos-arm64/unary-table.json"
    ))
    .unwrap();
    let triple = target["target"]["triple"].as_str().unwrap();
    let layout = target["target"]["layout"].as_str().unwrap();
    let llvm = ["llvm-check", triple, layout];
    let expected = include_str!("../llvm/src/borrowed-operator.ll");
    assert_eq!(
        common::kernel_with_args(pin(&raw, &evidence), &llvm)["llvm"]["ir"],
        expected
    );

    for (i, pkg) in raw["packages"].as_array().unwrap().iter().enumerate() {
        let path = pkg["source"].as_str().unwrap();
        for (field, replacement) in [("name", "other"), ("version", "0.2.0")] {
            let mut changed = raw.clone();
            changed["packages"][i][field] = json!(replacement);
            for args in [
                &["check"][..],
                &["emit"],
                &["function-revision"],
                &llvm,
                &["llvm-build", triple, layout],
            ] {
                let response = common::kernel_with_args(&changed, args);
                assert_wire_rejected(&response, "E_PROTOCOL");
                assert!(
                    response["diagnostics"][0]["message"]
                        .as_str()
                        .unwrap()
                        .contains(path)
                );
                assert!(
                    response.get("function_revision").is_none() && response.get("llvm").is_none()
                );
            }
        }
    }

    // Releasing the defining package under a new version preserves its code and
    // its chosen method's ordinal, but changes the family ID in the revision.
    let mut changed = raw.clone();
    let pkg = changed["packages"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|p| p["name"] == "edit_base")
        .unwrap();
    pkg["version"] = json!("0.2.0");
    let path = pkg["source"].clone();
    let file = changed["root_source"]["files"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|f| f["path"] == path)
        .unwrap();
    file["text"] = common::checked_replace(file["text"].as_str().unwrap(), "0.1.0", "0.2.0").into();
    let revised = revision(&changed);
    let call = &revised["pure"]["dispatch_calls"][0];
    assert_eq!(call["id"]["package"]["version"], "0.2.0");
    assert_eq!(
        call["method"],
        evidence["pure"]["dispatch_calls"][0]["method"]
    );
    assert_eq!(
        common::kernel_with_args(pin(&changed, &revised), &llvm)["llvm"]["ir"],
        expected
    );
    assert_wire_rejected(
        &common::kernel_with_args(pin(&changed, &evidence), &llvm),
        "E_FUNCTION_REVISION",
    );
}

#[test]
fn selected_contribution_and_core_symbol_share_one_exact_revision() {
    let s = Scratch::empty("exact family revision");
    let base =
        "pub fn choose(x: Int) -> Int { 0 } pub grant write : choose to ext { domain (Int); }";
    s.write_package("base", base, "");
    s.write_package("ext", "pub contribution shifted : base::choose { fn base::choose(x: Int) requires (HasOrder) -> Int { x + 1 } }", "base={path='../base'}");
    let main = "use base::choose as pick; assemble pick { borrow base::write { apply ext::shifted; } } fn get() -> Fn<Int, Int> { pick } fn main() -> Int { get()(41) }";
    s.write_package("app", main, "base={path='../base'}\next={path='../ext'}");
    let raw = s.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    let evidence = revision(&raw);
    assert_eq!(evidence["input"], raw);
    let choose = evidence["families"]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f["id"]["name"] == "choose")
        .unwrap();
    let call = &evidence["pure"]["dispatch_calls"].as_array().unwrap()[0];
    assert_eq!(choose["id"]["package"]["name"], "base");
    assert_eq!(choose["id"], call["id"]);
    let row = &choose["dispatch"][0];
    assert_eq!(row["key"], call["key"]);
    assert_eq!(row["selected"]["ordinal"], call["method"]);
    assert_eq!(row["selected"]["origin"]["contribution"]["name"], "shifted");
    let symbol = &evidence["pure"]["symbols"][call["core"].as_u64().unwrap() as usize];
    assert_eq!(
        symbol["specialization"]["definition"],
        row["selected"]["definition"]
    );
    assert_eq!(symbol["id"], choose["id"]);
    assert!(evidence["resource_values"].is_null());

    for mode in ["check", "emit"] {
        assert_eq!(
            kernel(pin(&raw, &evidence), mode)["function_revision_matched"],
            true
        );
        for (pointer, fake) in [
            ("/pure/dispatch_calls/0/id/name", json!("pick")),
            ("/pure/dispatch_calls/0/method", json!(999)),
            ("/pure/dispatch_calls/0/core", json!(999)),
            ("/pure/dispatch_calls/0/key", json!([0])),
            ("/schema", json!(10)),
        ] {
            let mut changed = evidence.clone();
            *changed.pointer_mut(pointer).unwrap() = fake;
            assert_wire_rejected(&kernel(pin(&raw, &changed), mode), "E_FUNCTION_REVISION");
        }
    }
    // Same selected method, same byte offsets, different nonwinning body.
    s.write("base/main.vast", &base.replace("{ 0 }", "{ 3 }"));
    let other = s.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    assert_eq!(
        revision(&other)["pure"]["dispatch_calls"],
        evidence["pure"]["dispatch_calls"]
    );
    assert_wire_rejected(
        &kernel(pin(&other, &evidence), "check"),
        "E_FUNCTION_REVISION",
    );
    s.write("base/main.vast", base);
    s.write(
        "app/main.vast",
        &main.replace("borrow base::write { apply ext::shifted; }", ""),
    );
    let other = s.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    let selected = revision(&other);
    assert_ne!(
        selected["pure"]["dispatch_calls"],
        evidence["pure"]["dispatch_calls"]
    );
    assert_wire_rejected(
        &kernel(pin(&other, &evidence), "emit"),
        "E_FUNCTION_REVISION",
    );
}

#[test]
fn resource_values_cannot_replay_another_specialization_table() {
    let s = Scratch::empty("resource function revisions");
    s.write_package(
        "app",
        "fn offset(x: Int) -> Int { x + 1 } resource fn main() -> Int { value { offset(41) } }",
        "",
    );
    let raw = s.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    let evidence = revision(&raw);
    assert!(
        evidence["resource_values"]["symbols"]
            .as_array()
            .unwrap()
            .len()
            > 1
    );
    assert_eq!(
        kernel(pin(&raw, &evidence), "emit")["function_revision_matched"],
        true
    );
    let mut forged = evidence.clone();
    forged["resource_values"] = evidence["pure"].clone();
    assert_wire_rejected(&kernel(pin(&raw, &forged), "emit"), "E_FUNCTION_REVISION");
}
