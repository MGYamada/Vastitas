mod common;
use common::{Scratch, kernel};
use serde_json::{Value, json};

const BASE: &str = r#"
pub fn choose(x, y) domain((Int, Int), (Bool, Bool));
fn choose(x: Any, y: Any) -> Int { 0 }
pub grant outer : choose to addon delegable { domain (Int, Int); }
pub transfer handoff : choose to addon;
pub contribution old : choose { fn choose(x: Int, y: Int) -> Int { 99 } }
"#;
const ADDON: &str = r#"
pub delegation inner : base::choose to addon::ops { domain (Int, Int); }
pub contribution fresh : base::choose { fn base::choose(x: Bool, y: Bool) -> Int { 2 } }
pub mod ops {
  pub contribution sum : base::choose { fn base::choose(x: Int, y: Int) -> Int { x + y } }
}
"#;
const NESTED: &str =
    "borrow base::outer as parent { delegate addon::inner as child { apply addon::ops::sum; } }";
const MAIN: &str = "fn main() -> Int { base::choose(40, 2) + base::choose(true, true) }";

fn fixture(base: &str, addon: &str, events: &str) -> Scratch {
    let s = Scratch::empty("edit authority");
    s.write_package("base", base, "");
    s.write_package("addon", addon, "base={path='../base'}");
    s.write_package(
        "app",
        &format!("assemble base::choose {{ {events} }} {MAIN}"),
        "base={path='../base'}\naddon={path='../addon'}\nalias={path='../addon'}",
    );
    s
}
fn check(s: &Scratch) -> std::process::Output {
    s.check_manifest("app/Vastitas.toml")
}
fn reject(s: &Scratch, code: &str) {
    let output = check(s);
    assert!(!output.status.success(), "accepted invalid authority");
    common::expect_code(&output, code);
}
fn native(s: &Scratch, expected: common::Run) {
    assert_eq!(s.check_build_and_run("app/Vastitas.toml"), expected);
}
fn request(s: &Scratch) -> Value {
    // Capture the actual frontend's wire request, then use the real kernel for
    // all mutations. The stub has no acceptance authority.
    s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL)
}

fn root_events(raw: &mut Value) -> &mut Vec<Value> {
    raw["packages"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|p| p["name"] == "app")
        .unwrap()["modules"][0]["assembly"]["events"]
        .as_array_mut()
        .unwrap()
}

#[test]
fn authority_ir_matches_public_checker_fixture() {
    let events = format!("{NESTED} transfer base::handoff; apply addon::fresh;");
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
    let events = format!("{NESTED} transfer base::handoff; apply addon::fresh;");
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
    s.write("vendor/deep/receiver/Vastitas.toml", "[package]\nedition = \"2026\"\nname='addon'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\nbase={path='../../../base'}\n");
    s.write("app/Vastitas.toml", "[package]\nedition = \"2026\"\nname='app'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\nbase={path='../base'}\naddon={path='../vendor/deep/receiver'}\nalias={path='../vendor/deep/receiver'}\n");
    native(&s, common::exits(44));
}

#[test]
fn every_unused_recipient_declaration_rejects_ambiguous_packages_before_modules() {
    for kind in ["grants", "delegations", "transfers"] {
        let base = BASE
            .lines()
            .filter(|line| {
                (!line.starts_with("pub grant ") || kind == "grants")
                    && (!line.starts_with("pub transfer ") || kind == "transfers")
            })
            .collect::<Vec<_>>()
            .join("\n");
        let addon = ADDON
            .lines()
            .filter(|line| !line.starts_with("pub delegation ") || kind == "delegations")
            .collect::<Vec<_>>()
            .join("\n");
        let s = fixture(&base, &addon, "");
        s.write("app/main.vast", MAIN);
        assert_eq!(kernel(request(&s), "check")["ok"], true, "{kind}");
        // Use two actual manifests. Only the first package has `ops`;
        // neither module contents nor version disambiguates the recipient.
        s.write(
            "second/Vastitas.toml",
            "[package]\nedition='2026'\nname='addon'\nversion='2.0.0'\nroot='main.vast'\n",
        );
        s.write("second/main.vast", "");
        let manifest = std::fs::read_to_string(s.0.join("app/Vastitas.toml")).unwrap();
        s.write(
            "app/Vastitas.toml",
            &(manifest + "second={path='../second'}\n"),
        );
        let mut raw = request(&s);
        for reverse in [false, true] {
            if reverse {
                raw["packages"].as_array_mut().unwrap().reverse();
            }
            for mode in ["check", "emit"] {
                let result = kernel(&raw, mode);
                common::assert_wire_rejected(&result, "E_OWNER");
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
            common::assert_wire_rejected(&kernel(&bad, "check"), "E_PROTOCOL");
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
    common::assert_wire_rejected(&kernel(&orphan, "check"), "E_OWNER");
}

#[test]
fn module_recipients_are_unsupported_and_authority_keeps_optional_runtime_boundaries() {
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
    s.write("app/main.vast", "resource fn main() -> Int { allocate data: F64<RR>[1]; borrow w = write(data, layout(0, 1, 1, 1, false)); fill(w, f64(2.0)); release(w); drop(data); value { base::choose(40, 2) } }");
    let raw = request(&s);
    let response = kernel(&raw, "emit");
    assert_eq!(raw["version"], common::CURRENT_PROTOCOL);
    assert_eq!(response["storage_runtime"], true, "{response}");
    assert_eq!(response["numerical_runtime"], false);
    native(&s, common::exits(0));
}

#[test]
fn nested_loans_and_transfer_preserve_function_identity_and_installed_methods() {
    let events = format!("{NESTED} transfer base::handoff; apply addon::fresh;");
    let s = fixture(BASE, ADDON, &events);
    native(&s, common::exits(44));
    // Reexports/aliases preserve both declaration identity and provenance.
    let replay = events.replace(
        "apply addon::ops::sum;",
        "apply addon::ops::sum, alias::ops::sum;",
    );
    native(&fixture(BASE, ADDON, &replay), common::exits(44));
    // Grants survive permanent transfer; using the original grant still needs
    // an explicit active loan, while its old owner cannot directly edit.
    let events = format!("transfer base::handoff; {NESTED} apply addon::fresh;");
    native(&fixture(BASE, ADDON, &events), common::exits(44));
    let deeper = ADDON.replace("to addon::ops {", "to addon::ops delegable {").replace(
        "pub mod ops {",
        r#"pub mod ops {
        pub delegation deeper : base::choose to addon::ops::deep { domain (Int, Int); }
        pub mod deep { pub contribution sum : base::choose { fn base::choose(x: Int, y: Int) -> Int { x + y } } }
        "#,
    );
    let events = events.replace(
        "apply addon::ops::sum;",
        "delegate addon::ops::deeper as grandchild { apply addon::ops::deep::sum; }",
    );
    native(&fixture(BASE, &deeper, &events), common::exits(44));
    let addon = format!(
        "{ADDON} pub contribution numeric : base::choose {{ fn base::choose(x: Int, y: Int) -> Int {{ x + y }} }}"
    );
    for order in [
        "apply addon::numeric; apply addon::fresh;",
        "apply addon::fresh; apply addon::numeric;",
    ] {
        native(
            &fixture(BASE, &addon, &format!("transfer base::handoff; {order}")),
            common::exits(44),
        );
    }
}

#[test]
fn indexed_declarations_preserve_nested_loans_transfer_and_unapplied_audits() {
    let base = format!("indexed marker Wire; {BASE}");
    let events = format!("{NESTED} transfer base::handoff; apply addon::fresh;");
    native(&fixture(&base, ADDON, &events), common::exits(44));
    let mut bad = request(&fixture(&base, ADDON, &events));
    root_events(&mut bad)[3]["loan"] = json!("parent");
    common::assert_wire_rejected(&kernel(bad, "check"), "E_BORROW");
    reject(
        &fixture(
            &base,
            ADDON,
            &format!("transfer base::handoff; apply base::old; {NESTED}"),
        ),
        "E_OWNER",
    );
    reject(
        &fixture(&base.replace("{ 99 }", "{ true }"), ADDON, &events),
        "E_TYPE",
    );
}

#[test]
fn suspended_parent_return_order_and_exact_delegation_are_enforced() {
    let raw = request(&fixture(
        BASE,
        ADDON,
        &format!("{NESTED} transfer base::handoff;"),
    ));
    for (index, key, value) in [
        (2, "loan", "parent"),
        (3, "loan", "parent"),
        (1, "parent", "child"),
    ] {
        let mut bad = raw.clone();
        root_events(&mut bad)[index][key] = json!(value);
        common::assert_wire_rejected(&kernel(&bad, "check"), "E_BORROW");
    }
    for fault in [
        "reborrow_suspended_parent",
        "transfer_during_child",
        "owner_edit_during_child",
        "unreturned_children",
        "transfer_during_root",
        "transfer_without_seal",
        "transfer_after_seal",
    ] {
        let mut bad = raw.clone();
        let events = root_events(&mut bad);
        let code = match fault {
            "reborrow_suspended_parent" => {
                let mut second = events[1].clone();
                second["loan"] = json!("another");
                events.insert(2, second);
                "E_BORROW"
            }
            "transfer_during_child" => {
                events.swap(2, 5);
                "E_BORROW"
            }
            "owner_edit_during_child" => {
                events[2]["loan"] = Value::Null;
                events[2]["contribution"] = json!(["base", "old"]);
                "E_BORROW"
            }
            "unreturned_children" => {
                events.truncate(2);
                "E_BORROW"
            }
            "transfer_during_root" => {
                events.swap(1, 5);
                "E_BORROW"
            }
            "transfer_without_seal" => {
                events.pop();
                "E_ASSEMBLY"
            }
            "transfer_after_seal" => {
                events.swap(5, 6);
                "E_ASSEMBLY"
            }
            _ => unreachable!(),
        };
        common::assert_wire_rejected(&kernel(&bad, "check"), code);
    }
    reject(
        &fixture(&BASE.replace(" delegable", ""), ADDON, NESTED),
        "E_OWNER",
    );
    reject(
        &fixture(
            BASE,
            &ADDON.replace("domain (Int, Int);", "domain (Int, Int), (Nat, Nat);"),
            NESTED,
        ),
        "E_OWNER",
    );
    reject(
        &fixture(BASE, &ADDON.replace("to addon::ops", "to addon"), NESTED),
        "E_OWNER",
    );
}

#[test]
fn transfer_revokes_old_authority_and_requires_returned_loans_and_completion() {
    for (events, code) in [
        ("transfer base::handoff; apply base::old;", "E_OWNER"),
        ("apply addon::fresh;", "E_OWNER"),
        ("transfer base::handoff; transfer base::handoff;", "E_OWNER"),
    ] {
        reject(&fixture(BASE, ADDON, events), code);
    }
    // A grant declared by the recipient becomes usable only after it acquires
    // authority. It cannot bootstrap itself or be silently ignored if unused.
    let addon =
        format!("{ADDON} pub grant own : base::choose to addon::ops {{ domain (Int, Int); }}");
    reject(&fixture(BASE, &addon, ""), "E_OWNER");
    reject(
        &fixture(BASE, &addon, "borrow addon::own as edit {}"),
        "E_OWNER",
    );
    native(
        &fixture(
            BASE,
            &addon,
            "transfer base::handoff; borrow addon::own as edit { apply addon::ops::sum; }",
        ),
        common::exits(42),
    );
}

#[test]
fn the_wire_reconstructs_authority_and_checks_all_bodies() {
    let events = format!("{NESTED} transfer base::handoff; apply addon::fresh;");
    let s = fixture(BASE, ADDON, &events);
    let raw = request(&s);
    assert_eq!(raw["version"], common::CURRENT_PROTOCOL);
    assert_eq!(kernel(&raw, "check")["ok"], true);
    let packages = raw["packages"].as_array().unwrap();
    let base = packages.iter().position(|p| p["name"] == "base").unwrap();
    let app = packages.iter().position(|p| p["name"] == "app").unwrap();
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
        common::assert_wire_rejected(&response, code);
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
pub contribution fresh : base::choose {{ fn base::choose(x: Number, y: Number) -> Int {{ 42 }} }}
pub mod ops {{ pub contribution sum : base::choose {{
  fn base::choose(x: Number, y: Any) -> Int {{ 1 }}
  fn base::choose(x: Any, y: Number) -> Int {{ 2 }}
}} }}
"#
    );
    reject(
        &fixture(&base, &addon, &format!("{NESTED} transfer base::handoff;")),
        "E_DISPATCH_AMBIGUOUS",
    );
    let repaired = format!("{NESTED} transfer base::handoff; apply addon::fresh;");
    native(&fixture(&base, &addon, &repaired), common::exits(42));
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
            NESTED,
        ),
        "E_IMPACT",
    );
}

#[test]
fn transfer_does_not_grant_membership_or_abstract_contract_authority() {
    let base = format!("{BASE} pub abstract type Logical;");
    for extra in [
        "subtype Bool <: base::Logical;",
        "fn base::choose(x: Int, y: Int) -> Int domain((Int, Int));",
    ] {
        reject(
            &fixture(
                &base,
                &format!("{ADDON} {extra}"),
                "transfer base::handoff;",
            ),
            "E_OWNER",
        );
    }
    // Authority records belong to a module: at the top of a request they are
    // unknown fields.
    for field in [
        "grants",
        "contributions",
        "assembly",
        "delegations",
        "transfers",
    ] {
        let mut flat = common::request("fn main() -> Int { 42 }", "flat.vast");
        flat[field] = json!([]);
        common::assert_wire_rejected(&kernel(flat, "check"), "E_PROTOCOL");
    }
}

#[test]
fn physical_declarations_bind_unused_authority_and_contributed_signatures() {
    let (addon, _) = ADDON.split_once("pub mod ops {").unwrap();
    let s = fixture(BASE, &format!("{addon}pub mod ops;"), "");
    s.write(
        "addon/ops.vast",
        "pub contribution sum : base::choose {
            fn base::choose(x: Int, y: Int,) requires (HasEq,) -> Int { x + y }
            fn base::choose(x: Bool, y: Bool) -> Int requires (HasEq) { 3 }
        }",
    );
    let wire = request(&s);
    let packages = wire["packages"].as_array().unwrap();
    let base = packages.iter().position(|p| p["name"] == "base").unwrap();
    let addon = packages.iter().position(|p| p["name"] == "addon").unwrap();
    let modules = packages[addon]["modules"].as_array().unwrap();
    let ops = modules
        .iter()
        .position(|m| m["path"] == json!(["ops"]))
        .unwrap();
    let root = modules.iter().position(|m| m["path"] == json!([])).unwrap();
    for mode in ["check", "emit"] {
        let good = kernel(&wire, mode);
        assert_eq!(good["ok"], true, "{good}");
        for mutation in [
            "visibility",
            "recipient",
            "region",
            "delegable",
            "transfer",
            "drop",
            "method order",
            "requires",
            "body span",
            "parameter span",
            "module",
        ] {
            let mut bad = wire.clone();
            let module = &mut bad["packages"][base]["modules"][0];
            match mutation {
                "visibility" => module["grants"][0]["public"] = json!(false),
                "recipient" => module["transfers"][0]["grantee_package"] = json!("app"),
                "region" => module["grants"][0]["region"] = json!([["Bool", "Bool"]]),
                "delegable" => module["grants"][0]["delegable"] = json!(false),
                "transfer" => module["transfers"][0]["name"] = json!("other"),
                "drop" => {
                    module.as_object_mut().unwrap().remove("grants");
                }
                "module" => {
                    let modules = &mut bad["packages"][addon]["modules"];
                    let contribution = modules[ops]["contributions"]
                        .as_array_mut()
                        .unwrap()
                        .remove(0);
                    modules[root]["contributions"]
                        .as_array_mut()
                        .unwrap()
                        .push(contribution);
                }
                change => {
                    let module = &mut bad["packages"][addon]["modules"][ops];
                    let methods = module["contributions"][0]["methods"]
                        .as_array_mut()
                        .unwrap();
                    match change {
                        "method order" => methods.swap(0, 1),
                        "requires" => methods[0]["requires"] = json!([]),
                        "body span" => methods[1]["body"]["span"]["column"] = json!(1),
                        "parameter span" => methods[1]["params"][0]["span"]["column"] = json!(1),
                        _ => unreachable!(),
                    }
                }
            }
            let rejected = kernel(bad, mode);
            assert_eq!(
                rejected["diagnostics"][0]["code"], "E_ASSEMBLY",
                "{mode} {mutation}: {rejected}"
            );
        }
        let mut bad = wire.clone();
        bad["packages"][addon]["modules"][root]["delegations"][0]["region"] = json!([]);
        common::assert_wire_rejected(&kernel(bad, mode), "E_ASSEMBLY");
    }
}

#[test]
fn physical_dependency_files_reject_omitted_edits_and_retired_declarations() {
    let marker = "// placeholder for a same-length physical declaration                    ";
    let s = fixture(BASE, &format!("{ADDON} pub mod generic;"), "");
    s.write(
        "addon/generic.vast",
        &format!("fn grant() -> Int {{ 3 }}\n{marker}\n"),
    );
    let wire = request(&s);
    for mode in ["check", "emit"] {
        let good = kernel(&wire, mode);
        assert_eq!(good["ok"], true, "{good}");
        for declaration in [
            "assemble base::choose { }",
            "assembly {}",
            "generic f(x);",
            "method f(x: Int) -> Int { x }",
            "abstract method f(x: Int) -> Int;",
            "pub transfer handoff : base::choose to addon;",
            "contribution extra : base::choose {}",
        ] {
            let mut bad = wire.clone();
            let file = bad["root_source"]["files"]
                .as_array_mut()
                .unwrap()
                .iter_mut()
                .find(|row| {
                    row["path"]
                        .as_str()
                        .is_some_and(|p| p.ends_with("/generic.vast"))
                })
                .unwrap();
            let original = file["text"].as_str().unwrap();
            let replacement = format!("{declaration:<width$}", width = marker.len());
            assert_eq!(replacement.len(), marker.len());
            file["text"] = json!(original.replace(marker, &replacement));
            common::assert_wire_rejected(&kernel(bad, mode), "E_ASSEMBLY");
        }
    }
}

#[test]
fn flat_library_bytes_cannot_supply_an_unreported_assembly() {
    let s = Scratch::empty("flat library edit");
    s.write("main.vast", "fn main() -> Int { identity(42) }");
    s.write(
        "lib.vast",
        "fn identity(x: Int) -> Int { x }\n// assemble identity {}\n",
    );
    let wire = common::captured_wire(
        s.cli().args(["check", "main.vast", "--lib", "lib.vast"]),
        common::CURRENT_PROTOCOL,
    );
    let mut changed = wire.clone();
    let file = changed["root_source"]["files"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|file| {
            file["text"]
                .as_str()
                .is_some_and(|t| t.contains("// assemble"))
        })
        .unwrap();
    file["text"] = json!(
        file["text"]
            .as_str()
            .unwrap()
            .replace("// assemble", "   assemble")
    );
    for mode in ["check", "emit"] {
        let good = kernel(&wire, mode);
        assert_eq!(good["ok"], true, "{good}");
        common::assert_wire_rejected(&kernel(&changed, mode), "E_ASSEMBLY");
    }
}
