//! A finite tag keeps its declaring carrier across argument passing and comparison.
mod common;
use common::{Scratch, assert_wire_rejected, exits, expect_code, kernel};
use serde_json::Value;

const LIB: &str = "pub indexed finite Bit { off; on; }
pub fn flip(x: Bit<>) -> Bit<> { if x == Bit::on { Bit::off } else { Bit::on } }";
const APP: &str = "use left::Bit as Bit; use left::flip as flip;
fn main() -> Int { if flip(Bit::off) == Bit::on && flip(Bit::on) != Bit::on { 42 } else { 1 } }";
const MANIFEST: &str = "left={path='../left'}\nright={path='../right'}";

fn build_source(src: &str) -> Scratch {
    let p = Scratch::empty("finite tag values");
    p.write_package("left", LIB, "");
    p.write_package("right", LIB, "");
    p.write_package("app", src, MANIFEST);
    p
}

#[test]
fn native_branch_compares_members_of_a_visible_carrier() {
    let p = build_source(APP);
    assert_eq!(p.check_build_and_run("app/Vastitas.toml"), exits(42));
}

#[test]
fn finite_value_has_no_integer_or_cross_owner_conversion() {
    for (bad, code) in [
        (APP.replace("flip(Bit::off)", "flip(0)"), "E_TYPE"),
        (
            APP.replace("flip(Bit::off)", "flip(right::Bit::off)"),
            "E_TYPE",
        ),
        (APP.replace("== Bit::on", "== right::Bit::on"), "E_TYPE"),
        (APP.replace("flip(Bit::off)", "flip(Bit::bad)"), "E_TYPE"),
        (
            APP.replace("flip(Bit::off)", "(Bit::off + Bit::on)"),
            "E_OPERATOR",
        ),
        (
            format!("fn unused(x: left::Bit<>) -> left::Bit<> {{ 1 }}\n{APP}"),
            "E_TYPE",
        ),
    ] {
        let p = build_source(&bad);
        let output = p.check_manifest("app/Vastitas.toml");
        expect_code(&output, code);
    }
}

#[test]
fn changing_a_member_in_the_wire_reaches_the_independent_checker() {
    fn forge(value: &mut Value) -> bool {
        match value {
            Value::Object(obj)
                if obj.get("kind").and_then(Value::as_str) == Some("variable")
                    && obj.get("name").and_then(Value::as_str) == Some("Bit::on") =>
            {
                obj.insert("name".into(), Value::String("Bit::forged".into()));
                true
            }
            Value::Object(obj) => obj.values_mut().any(forge),
            Value::Array(xs) => xs.iter_mut().any(forge),
            _ => false,
        }
    }
    let p = build_source(APP);
    let mut req = p.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    assert!(forge(&mut req));
    for mode in ["check", "emit"] {
        assert_wire_rejected(&kernel(&req, mode), "E_TYPE");
    }
}
