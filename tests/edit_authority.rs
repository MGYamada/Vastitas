mod common;
use common::{Scratch, cli, kernel, success};
use serde_json::{Value, json};

const BASE: &str = r#"
pub generic choose(x, y) { domain (Int, Int), (Bool, Bool); }
method choose(x: Any, y: Any) -> Int { 0 }
pub grant outer : choose to addon delegable { domain (Int, Int); }
pub transfer handoff : choose to addon;
pub contribution old : choose { method choose(x: Int, y: Int) -> Int { 99 } }
"#;
const ADDON: &str = r#"
pub delegation inner : base::choose to addon::ops { domain (Int, Int); }
pub contribution fresh : base::choose { method base::choose(x: Bool, y: Bool) -> Int { 2 } }
pub mod ops {
  pub contribution sum : base::choose { method base::choose(x: Int, y: Int) -> Int { x + y } }
}
"#;
const NESTED: &str = "borrow base::outer as parent; reborrow parent via addon::inner as child; apply addon::ops::sum using child; return child; return parent;";

fn fixture(base: &str, addon: &str, events: &str) -> Scratch {
    let s = Scratch::empty("edit authority");
    s.write_package("base", base, "");
    s.write_package("addon", addon, "base={path='../base'}");
    s.write_package("app",
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
    common::expect_code(&output, code);
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
    common::captured_wire(
        cli()
            .current_dir(&s.0)
            .args(["check", "--manifest-path", "app/Vastitas.toml"]),
        9,
    )
}

#[test]
fn authority_ir_matches_public_checker_fixture() {
    let events = format!("{NESTED} transfer base::handoff; apply addon::fresh; seal base::choose;");
    let s = fixture(BASE, ADDON, &events);
    let mut raw = request(&s);
    // Relocate the complete temporary source graph consistently. Preserve
    // module paths, relative references, spans and all other frontend fields.
    // The kernel checks IR provenance, not authenticity of filesystem contents.
    fn relocate(value: &mut Value, root: &str) {
        match value {
            Value::String(text) => {
                if let Some(relative) = text.strip_prefix(root)
                    && (relative.is_empty() || relative.starts_with('/'))
                {
                    *text = format!("/authority-fixture{relative}");
                }
            }
            Value::Array(values) => values.iter_mut().for_each(|value| relocate(value, root)),
            Value::Object(fields) => fields.values_mut().for_each(|value| relocate(value, root)),
            _ => {}
        }
    }
    relocate(&mut raw, s.0.canonicalize().unwrap().to_str().unwrap());
    let path = common::root().join("tests/fixtures/edit-recipients.json");
    if common::regenerate_fixture("VASTITAS_UPDATE_RECIPIENT_FIXTURE") {
        std::fs::write(
            &path,
            format!("{}\n", serde_json::to_string_pretty(&raw).unwrap()),
        )
        .unwrap();
    }
    let fixture: Value = serde_json::from_slice(
        &std::fs::read(path).expect("regenerate the authority fixture as documented"),
    )
    .unwrap();
    assert_eq!(
        raw, fixture,
        "frontend authority IR differs from the Lean public regression fixture"
    );
    for mode in ["check", "emit"] {
        let response = kernel(&fixture, mode);
        assert_eq!(response["ok"], true, "{mode}: {response}");
    }
}

#[test]
fn named_recipients_keep_manifest_identity_and_ignore_dependency_aliases() {
    let events = format!("{NESTED} transfer base::handoff; apply addon::fresh; seal base::choose;");
    let s = fixture(BASE, ADDON, &events);
    let raw = request(&s);
    let packages = raw["packages"].as_array().unwrap();
    assert!(
        packages.iter().find(|p| p["name"] == "base").unwrap()["dependencies"]
            .as_array()
            .unwrap()
            .is_empty()
    );
    for package in packages {
        for module in package["modules"].as_array().unwrap() {
            for field in ["grants", "delegations", "transfers"] {
                for item in module[field].as_array().into_iter().flatten() {
                    assert_eq!(item["grantee_package"], "addon");
                    assert!(item.get("grantee_source").is_none());
                }
            }
        }
    }
    // `alias` is a real root dependency alias, but not the manifest name.
    reject(
        &fixture(&BASE.replace("to addon", "to alias"), ADDON, &events),
        "E_OWNER",
    );
    // The receiver need not be a sibling of the issuer on disk.
    let moved = s.0.join("vendor/deep/receiver");
    std::fs::create_dir_all(moved.parent().unwrap()).unwrap();
    std::fs::rename(s.0.join("addon"), &moved).unwrap();
    s.write("vendor/deep/receiver/Vastitas.toml", "[package]\nname='addon'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\nbase={path='../../../base'}\n");
    s.write("app/Vastitas.toml", "[package]\nname='app'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\nbase={path='../base'}\naddon={path='../vendor/deep/receiver'}\nalias={path='../vendor/deep/receiver'}\n");
    native(&s, b"44\n");
}

#[test]
fn every_unused_recipient_declaration_rejects_ambiguous_packages_before_modules() {
    for kind in ["grants", "delegations", "transfers"] {
        let s = fixture(BASE, ADDON, "");
        let mut raw = request(&s);
        for package in raw["packages"].as_array_mut().unwrap() {
            for module in package["modules"].as_array_mut().unwrap() {
                module.as_object_mut().unwrap().remove("assembly");
                for other in ["grants", "delegations", "transfers"] {
                    if other != kind {
                        module.as_object_mut().unwrap().remove(other);
                    }
                }
            }
        }
        assert_eq!(kernel(&raw, "check")["ok"], true, "{kind}: {raw}");
        // Different version and source; only the original has `ops`.
        // Neither difference is a permitted name disambiguator.
        let mut duplicate = raw["packages"]
            .as_array()
            .unwrap()
            .iter()
            .find(|p| p["name"] == "addon")
            .unwrap()
            .clone();
        duplicate["source"] = json!("/second-addon/Vastitas.toml");
        duplicate["version"] = json!("2.0.0");
        duplicate["modules"]
            .as_array_mut()
            .unwrap()
            .retain(|m| m["path"] == json!([]));
        let root = duplicate["modules"][0].as_object_mut().unwrap();
        for field in ["grants", "delegations", "transfers", "contributions"] {
            root.remove(field);
        }
        raw["packages"].as_array_mut().unwrap().push(duplicate);
        let root = raw["root"].clone();
        let app = raw["packages"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|p| p["source"] == root)
            .unwrap();
        app["dependencies"]
            .as_array_mut()
            .unwrap()
            .push(json!({"alias":"second", "target":"/second-addon/Vastitas.toml"}));
        for reverse in [false, true] {
            if reverse {
                raw["packages"].as_array_mut().unwrap().reverse();
            }
            for mode in ["check", "emit"] {
                let result = kernel(&raw, mode);
                assert_eq!(
                    result["diagnostics"][0]["code"], "E_OWNER",
                    "{kind}/{mode}: {result}"
                );
                assert!(
                    result["diagnostics"][0]["message"]
                        .as_str()
                        .unwrap()
                        .contains("ambiguous"),
                    "{result}"
                );
            }
        }
    }
}

#[test]
fn named_recipient_wire_rejects_forged_locations_and_unselected_records() {
    let s = fixture(BASE, ADDON, "");
    let raw = request(&s);
    let base = raw["packages"]
        .as_array()
        .unwrap()
        .iter()
        .position(|p| p["name"] == "base")
        .unwrap();
    for field in ["grants", "transfers"] {
        for forgery in ["location", "identity", "missing"] {
            let mut bad = raw.clone();
            let item = &mut bad["packages"][base]["modules"][0][field][0];
            match forgery {
                "location" => item["grantee_source"] = json!("/trusted/Vastitas.toml"),
                "identity" => item["grantee_package"] = json!({"name":"addon","version":"0.1.0"}),
                _ => {
                    item.as_object_mut().unwrap().remove("grantee_package");
                }
            }
            assert_eq!(
                kernel(&bad, "check")["diagnostics"][0]["code"],
                "E_PROTOCOL"
            );
        }
    }
    let mut orphan = raw;
    let app = orphan["packages"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|p| p["name"] == "app")
        .unwrap();
    app["dependencies"]
        .as_array_mut()
        .unwrap()
        .retain(|d| d["alias"] == "base");
    app["modules"][0]["functions"][0]["body"]["result"] =
        json!({"kind":"integer","value":"0","span":{"start":0,"end":0,"line":1,"column":1}});
    assert_eq!(
        kernel(&orphan, "check")["diagnostics"][0]["code"],
        "E_OWNER"
    );
}

#[test]
fn recipient_source_migration_keeps_legacy_wire_and_optional_runtime_boundaries() {
    let legacy: Value = serde_json::from_str(include_str!("fixtures/edit-authority.json")).unwrap();
    for version in [6, 7, 8] {
        let mut raw = legacy.clone();
        raw["version"] = json!(version);
        for mode in ["check", "emit"] {
            assert_eq!(kernel(&raw, mode)["ok"], true);
        }
    }
    for source in [
        BASE.replace("to addon", "to module(\"../addon/Vastitas.toml\", \"\")"),
        BASE.replace(
            "pub transfer handoff : choose to addon",
            "pub transfer handoff : choose to module(\"../addon/Vastitas.toml\", \"\")",
        ),
    ] {
        reject(&fixture(&source, ADDON, ""), "E_UNSUPPORTED");
    }
    reject(
        &fixture(
            BASE,
            &ADDON.replace("to addon::ops", "to module(\"Vastitas.toml\", \"ops\")"),
            "",
        ),
        "E_UNSUPPORTED",
    );
    let s = fixture(BASE, ADDON, "");
    s.write("app/main.vast", "resource fn main() -> Int { allocate data: F64[1]; borrow w = write(data, layout(0, 1, 1, 1, false)); fill(w, f64(2.0)); release(w); drop(data); value { base::choose(40, 2) } }");
    let raw = request(&s);
    let response = kernel(&raw, "emit");
    assert_eq!(raw["version"], 9);
    assert_eq!(response["storage_runtime"], true, "{response}");
    assert_eq!(response["numerical_runtime"], false);
    native(&s, b"0\n");
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
    let deeper = ADDON.replace("to addon::ops {", "to addon::ops delegable {").replace(
        "pub mod ops {",
        r#"pub mod ops {
        pub delegation deeper : base::choose to addon::ops::deep { domain (Int, Int); }
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
fn indexed_declarations_preserve_nested_loans_transfer_and_unapplied_audits() {
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
            &ADDON.replace("to addon::ops", "to addon"),
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
    let addon =
        format!("{ADDON} pub grant own : base::choose to addon::ops {{ domain (Int, Int); }}");
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
fn protocol_nine_reconstructs_authority_and_checks_all_bodies() {
    let events = format!("{NESTED} transfer base::handoff; apply addon::fresh; seal base::choose;");
    let s = fixture(BASE, ADDON, &events);
    let raw = request(&s);
    assert_eq!(raw["version"], 9);
    assert_eq!(kernel(&raw, "check")["ok"], true);
    let packages = raw["packages"].as_array().unwrap();
    let base = packages.iter().position(|p| p["name"] == "base").unwrap();
    let app = packages.iter().position(|p| p["name"] == "app").unwrap();
    for version in 2..=8 {
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
pub delegation inner : base::choose to addon::ops {{ domain {region}; }}
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
