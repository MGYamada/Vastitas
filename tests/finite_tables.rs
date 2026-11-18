//! Edition 2026 finite declarations, including independent rejection of bad wire.
mod common;
use common::{Scratch, assert_wire_rejected, kernel};
use serde_json::json;

const MAIN: &str = "indexed table swap(Bit) -> Bit { (off) => on; (on) => off; }\nindexed finite Bit { off; on; }\nindexed finite Empty {}\nindexed finite Labels { Nat; }\nindexed table vacuous(Bit, Empty) -> Empty {}\nindexed table point() -> Bit { () => off; }\nfn main() -> Int { 42 }";

#[test]
fn forward_references_and_degenerate_products_are_checked_on_wire() {
    let s = Scratch::empty("finite tables");
    s.write_package("app", MAIN, "");
    let raw = s.captured("app/Vastitas.toml", 10);
    let response = kernel(&raw, "check");
    assert_eq!(response["ok"], true, "{response}");
    let declarations = &raw["packages"][0]["modules"][0]["indexed_declarations"];
    let table = declarations
        .as_array()
        .unwrap()
        .iter()
        .position(|d| d["name"] == "swap")
        .unwrap();
    let root = format!("/packages/0/modules/0/indexed_declarations/{table}");
    let rows = &raw.pointer(&root).unwrap()["rows"];
    let span = &rows[0]["value"]["span"];
    let base = declarations[table]["span"]["start"].as_u64().unwrap();
    assert_eq!(
        &MAIN[(span["start"].as_u64().unwrap() - base) as usize
            ..(span["end"].as_u64().unwrap() - base) as usize],
        "on"
    );
    for (suffix, replacement) in [
        ("rows/0/value/name", json!("outside")),
        ("rows/1/key/0/name", json!("off")),
        ("rows/1/key", json!([])),
        ("rows", json!([rows[0]])),
    ] {
        let mut changed = raw.clone();
        *changed.pointer_mut(&format!("{root}/{suffix}")).unwrap() = replacement;
        let error = kernel(changed, "emit");
        assert_wire_rejected(&error, "E_FINITE_TABLE");
    }
}

#[test]
fn unknown_output_points_to_original_tag() {
    let s = Scratch::empty("finite tag error");
    s.write_package("app", &MAIN.replacen("=> on;", "=> nowhere;", 1), "");
    let output = s.check_manifest("app/Vastitas.toml");
    assert!(!output.status.success());
    let error = String::from_utf8_lossy(&output.stderr);
    let column = MAIN.find("=> on;").unwrap() + 4;
    assert!(
        error.contains(&format!("main.vast:1:{column}: E_FINITE_TABLE")),
        "{error}"
    );
}
