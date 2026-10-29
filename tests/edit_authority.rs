mod common;
use common::{Scratch, cli, kernel, success};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;

const BASE: &str = r#"
pub generic choose(x, y) { domain (Int, Int), (Bool, Bool); }
method choose(x: Any, y: Any) -> Int { 0 }
pub grant outer : choose to module("../addon/Vastitas.toml", "") delegable { domain (Int, Int); }
pub transfer handoff : choose to module("../addon/Vastitas.toml", "");
pub contribution old : choose { method choose(x: Int, y: Int) -> Int { 99 } }
"#;
const ADDON: &str = r#"
pub delegation inner : base::choose to module("Vastitas.toml", "ops") { domain (Int, Int); }
pub contribution fresh : base::choose { method base::choose(x: Bool, y: Bool) -> Int { 2 } }
pub mod ops {
  pub contribution sum : base::choose { method base::choose(x: Int, y: Int) -> Int { x + y } }
}
"#;
const NESTED: &str = "borrow base::outer as parent; reborrow parent via addon::inner as child; apply addon::ops::sum using child; return child; return parent;";

fn package(s: &Scratch, name: &str, source: &str, dependencies: &str) {
    s.write(&format!("{name}/Vastitas.toml"), &format!("[package]\nname='{name}'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\n{dependencies}\n"));
    s.write(&format!("{name}/main.vast"), source);
}
fn fixture(base: &str, addon: &str, events: &str) -> Scratch {
    let s = Scratch::empty("edit authority");
    package(&s, "base", base, "");
    package(&s, "addon", addon, "base={path='../base'}");
    package(
        &s,
        "app",
        &format!(
            "assembly {{ {events} }} fn main() -> Int {{ base::choose(40, 2) + base::choose(true, true) }}"
        ),
        "base={path='../base'}\naddon={path='../addon'}\nalias={path='../addon'}",
    );
    s
}
fn check(s: &Scratch) -> std::process::Output {
    cli()
        .current_dir(&s.0)
        .args(["check", "--manifest-path", "app/Vastitas.toml"])
        .output()
        .unwrap()
}
fn reject(s: &Scratch, code: &str) {
    let output = check(s);
    assert!(!output.status.success(), "accepted invalid authority");
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(error.contains(code), "expected {code}: {error}");
}
fn native(s: &Scratch, expected: &[u8]) {
    success(&check(s));
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
    let output = std::process::Command::new(s.0.join("program"))
        .output()
        .unwrap();
    success(&output);
    assert_eq!(output.stdout, expected);
}
fn request(s: &Scratch) -> Value {
    // Capture the actual frontend's wire request, then use the real kernel for
    // all mutations. The stub has no acceptance authority.
    let backend = s.write("capture", "#!/bin/sh\ncat > \"$(dirname \"$0\")/wire.json\"\nprintf '%s\\n' '{\"version\":6,\"ok\":false,\"diagnostics\":[{\"code\":\"E_CAPTURED\",\"message\":\"captured\"}]}'\nexit 1\n");
    std::fs::set_permissions(&backend, std::fs::Permissions::from_mode(0o755)).unwrap();
    let output = cli()
        .current_dir(&s.0)
        .env("VASTITAS_KERNEL", backend)
        .args(["check", "--manifest-path", "app/Vastitas.toml"])
        .output()
        .unwrap();
    assert!(String::from_utf8_lossy(&output.stderr).contains("E_CAPTURED"));
    serde_json::from_slice(&std::fs::read(s.0.join("wire.json")).unwrap()).unwrap()
}

#[test]
fn nested_loans_and_transfer_preserve_function_identity_and_installed_methods() {
    let events = format!("{NESTED} transfer base::handoff; apply addon::fresh; seal base::choose;");
    let s = fixture(BASE, ADDON, &events);
    native(&s, b"44\n");
    // Reexports/aliases preserve both declaration identity and provenance.
    let replay = events.replace(
        "return child;",
        "apply alias::ops::sum using child; return child;",
    );
    native(&fixture(BASE, ADDON, &replay), b"44\n");
    // Grants survive permanent transfer; using the original grant still needs
    // an explicit active loan, while its old owner cannot directly edit.
    let events = format!("transfer base::handoff; {NESTED} apply addon::fresh; seal base::choose;");
    native(&fixture(BASE, ADDON, &events), b"44\n");
    let deeper = ADDON.replace("\"ops\") {", "\"ops\") delegable {").replace(
        "pub mod ops {",
        r#"pub mod ops {
        pub delegation deeper : base::choose to module("Vastitas.toml", "ops::deep") { domain (Int, Int); }
        pub mod deep { pub contribution sum : base::choose { method base::choose(x: Int, y: Int) -> Int { x + y } } }
        "#,
    );
    let events = events.replace("apply addon::ops::sum using child;",
        "reborrow child via addon::ops::deeper as grandchild; apply addon::ops::deep::sum using grandchild; return grandchild;");
    native(&fixture(BASE, &deeper, &events), b"44\n");
    let addon = format!(
        "{ADDON} pub contribution numeric : base::choose {{ method base::choose(x: Int, y: Int) -> Int {{ x + y }} }}"
    );
    for order in [
        "apply addon::numeric; apply addon::fresh;",
        "apply addon::fresh; apply addon::numeric;",
    ] {
        native(
            &fixture(
                BASE,
                &addon,
                &format!("transfer base::handoff; {order} seal base::choose;"),
            ),
            b"44\n",
        );
    }
}

#[test]
fn protocol_seven_preserves_nested_loans_transfer_and_unapplied_audits() {
    let base = format!("indexed marker Wire; {BASE}");
    let events = format!("{NESTED} transfer base::handoff; apply addon::fresh; seal base::choose;");
    native(&fixture(&base, ADDON, &events), b"44\n");
    reject(
        &fixture(
            &base,
            ADDON,
            &format!("transfer base::handoff; apply base::old; {NESTED}"),
        ),
        "E_OWNER",
    );
    reject(
        &fixture(
            &base,
            ADDON,
            "borrow base::outer as parent; reborrow parent via addon::inner as child; return parent;",
        ),
        "E_BORROW",
    );
    reject(
        &fixture(&base.replace("{ 99 }", "{ true }"), ADDON, &events),
        "E_TYPE",
    );
}

#[test]
fn suspended_parent_return_order_and_exact_delegation_are_enforced() {
    let prefix = "borrow base::outer as parent; reborrow parent via addon::inner as child;";
    for suffix in [
        "apply addon::fresh using parent;",
        "return parent;",
        "reborrow parent via addon::inner as another;",
        "transfer base::handoff;",
        "apply base::old;",
    ] {
        reject(
            &fixture(BASE, ADDON, &format!("{prefix} {suffix}")),
            "E_BORROW",
        );
    }
    reject(
        &fixture(
            &BASE.replace(" delegable", ""),
            ADDON,
            &format!("{NESTED} seal base::choose;"),
        ),
        "E_OWNER",
    );
    reject(
        &fixture(
            BASE,
            &ADDON.replace("domain (Int, Int);", "domain (Int, Int), (Nat, Nat);"),
            &format!("{NESTED} seal base::choose;"),
        ),
        "E_OWNER",
    );
    reject(
        &fixture(
            BASE,
            &ADDON.replace("\"ops\"", "\"\""),
            &format!("{NESTED} seal base::choose;"),
        ),
        "E_OWNER",
    );
    reject(&fixture(BASE, ADDON, prefix), "E_BORROW");
}

#[test]
fn transfer_revokes_old_authority_and_requires_returned_loans_and_completion() {
    for (events, code) in [
        ("transfer base::handoff; apply base::old;", "E_OWNER"),
        ("apply addon::fresh;", "E_OWNER"),
        (
            "borrow base::outer as parent; transfer base::handoff;",
            "E_BORROW",
        ),
        ("transfer base::handoff; transfer base::handoff;", "E_OWNER"),
        ("transfer base::handoff;", "E_ASSEMBLY"),
        ("seal base::choose; transfer base::handoff;", "E_ASSEMBLY"),
    ] {
        reject(&fixture(BASE, ADDON, events), code);
    }
    // A grant declared by the recipient becomes usable only after it acquires
    // authority. It cannot bootstrap itself or be silently ignored if unused.
    let addon = format!(
        "{ADDON} pub grant own : base::choose to module(\"Vastitas.toml\", \"ops\") {{ domain (Int, Int); }}"
    );
    reject(&fixture(BASE, &addon, ""), "E_OWNER");
    reject(
        &fixture(BASE, &addon, "borrow addon::own as edit;"),
        "E_OWNER",
    );
    native(
        &fixture(
            BASE,
            &addon,
            "transfer base::handoff; borrow addon::own as edit; apply addon::ops::sum using edit; return edit; seal base::choose;",
        ),
        b"42\n",
    );
}

#[test]
fn protocol_six_reconstructs_authority_and_checks_all_bodies() {
    let events = format!("{NESTED} transfer base::handoff; apply addon::fresh; seal base::choose;");
    let s = fixture(BASE, ADDON, &events);
    let raw = request(&s);
    assert_eq!(raw["version"], 6);
    assert_eq!(kernel(&raw, "check")["ok"], true);
    let packages = raw["packages"].as_array().unwrap();
    let base = packages.iter().position(|p| p["name"] == "base").unwrap();
    let app = packages.iter().position(|p| p["name"] == "app").unwrap();
    for version in [2, 3, 4, 5] {
        let mut bad = raw.clone();
        bad["version"] = json!(version);
        assert_eq!(kernel(bad, "check")["diagnostics"][0]["code"], "E_PROTOCOL");
    }
    for mutation in ["issuer", "permission", "event", "body"] {
        let mut bad = raw.clone();
        let code = match mutation {
            "issuer" => {
                bad["packages"][base]["modules"][0]["transfers"][0]["issuer"] = json!("trusted");
                "E_PROTOCOL"
            }
            "permission" => {
                bad["packages"][base]["modules"][0]["grants"][0]["delegable"] = json!(false);
                "E_OWNER"
            }
            "event" => {
                bad["packages"][app]["modules"][0]["assembly"]["events"][1]["authorized"] =
                    json!(true);
                "E_PROTOCOL"
            }
            "body" => {
                bad["packages"][base]["modules"][0]["contributions"][0]["methods"][0]["return_type"] =
                    json!({"kind":"named","name":"Bool"});
                "E_TYPE"
            }
            _ => unreachable!(),
        };
        let response = kernel(bad, "check");
        assert_eq!(response["diagnostics"][0]["code"], code, "{response}");
        assert!(response.get("lean_source").is_none());
    }
}

#[test]
fn open_obligations_survive_nested_returns_and_transfer_until_owner_repairs() {
    let scalars = ["Nat", "Int", "Bool", "Unit"];
    let region = scalars
        .iter()
        .flat_map(|a| scalars.iter().map(move |b| format!("({a}, {b})")))
        .collect::<Vec<_>>()
        .join(", ");
    let base = BASE.replace("{ domain (Int, Int); }", &format!("{{ domain {region}; }}"));
    let addon = format!(
        r#"
pub delegation inner : base::choose to module("Vastitas.toml", "ops") {{ domain {region}; }}
pub contribution fresh : base::choose {{ method base::choose(x: Number, y: Number) -> Int {{ 42 }} }}
pub mod ops {{ pub contribution sum : base::choose {{
  method base::choose(x: Number, y: Any) -> Int {{ 1 }}
  method base::choose(x: Any, y: Number) -> Int {{ 2 }}
}} }}
"#
    );
    reject(
        &fixture(
            &base,
            &addon,
            &format!("{NESTED} transfer base::handoff; seal base::choose;"),
        ),
        "E_DISPATCH_AMBIGUOUS",
    );
    let repaired =
        format!("{NESTED} transfer base::handoff; apply addon::fresh; seal base::choose;");
    native(&fixture(&base, &addon, &repaired), b"42\n");
    reject(
        &fixture(&base, &addon.replace("{ 1 }", "{ true }"), &repaired),
        "E_TYPE",
    );
    // Containment in a parent is necessary but not sufficient: the final
    // winning footprint must also lie inside the effective child region.
    reject(
        &fixture(
            BASE,
            &ADDON.replace("domain (Int, Int);", "domain;"),
            &format!("{NESTED} seal base::choose;"),
        ),
        "E_IMPACT",
    );
}

#[test]
fn transfer_does_not_grant_membership_or_abstract_contract_authority() {
    let base = format!("{BASE} pub abstract type Logical;");
    for extra in [
        "subtype Bool <: base::Logical;",
        "abstract method base::choose(x: Int, y: Int) -> Int { domain (Int, Int); }",
    ] {
        reject(
            &fixture(
                &base,
                &format!("{ADDON} {extra}"),
                "transfer base::handoff; seal base::choose;",
            ),
            "E_OWNER",
        );
    }
    for field in [
        "grants",
        "contributions",
        "assembly",
        "delegations",
        "transfers",
    ] {
        let mut flat = common::request("fn main() -> Int { 42 }", "downgrade.vast");
        flat[field] = json!([]);
        assert_eq!(
            kernel(flat, "check")["diagnostics"][0]["code"],
            "E_PROTOCOL"
        );
    }
}
