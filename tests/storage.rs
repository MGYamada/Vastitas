//! Shared untrusted component schema; public protocol 8 is deliberately pending.
mod common;
use serde_json::{Value, json};
use vastitas::storage::{Action, Literal, Plan, Statement};

fn fixture() -> Value {
    serde_json::from_str(include_str!("fixtures/storage.json")).unwrap()
}

#[test]
fn actual_rust_resource_ir_matches_the_lean_fixture_without_payload_narrowing() {
    let raw = fixture();
    let plan: Plan = serde_json::from_value(raw.clone()).unwrap();
    assert_eq!(plan.statements.len(), 30);
    assert_eq!(serde_json::to_value(&plan).unwrap(), raw);
    let Statement::Action {
        action: Action::Fill { value, .. },
    } = &plan.statements[12]
    else {
        panic!("expected complex fill");
    };
    assert_eq!(
        value,
        &Literal::ComplexF64 {
            real: u64::MAX,
            imaginary: 1 << 63
        }
    );
}

#[test]
fn resource_input_does_not_accept_state_certificates_or_truncate_integers() {
    let original = fixture();
    for (path, value) in [
        ("/checked_state", json!({})),
        ("/statements/0/action/initialized", json!(true)),
        ("/statements/0/action/allocation", json!(0)),
        ("/statements/0/action/owner", json!(1_u64 << 32)),
        ("/statements/0/action/elements", json!(-1)),
        ("/statements/1/action/layout/disjoint", json!(true)),
    ] {
        let mut changed = original.clone();
        let (parent, field) = path.rsplit_once('/').unwrap();
        changed
            .pointer_mut(parent)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .insert(field.into(), value);
        assert!(serde_json::from_value::<Plan>(changed).is_err(), "{path}");
    }
    assert!(
        serde_json::from_str::<Literal>(r#"{"kind":"f64","bits":18446744073709551616}"#).is_err()
    );
}

#[test]
fn internal_resource_components_cannot_bypass_public_protocol_acceptance() {
    let mut request = common::request("fn main() -> Int { 0 }", "resource-envelope.vast");
    request["resources"] = fixture();
    let response = common::kernel(&request, "check");
    assert_eq!(response["ok"], false, "{response}");
    request["version"] = json!(8);
    let response = common::kernel(&request, "check");
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(response["version"], 8);
}
