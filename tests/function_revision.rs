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
