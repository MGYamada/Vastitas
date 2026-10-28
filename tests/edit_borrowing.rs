mod common;
use common::{Scratch, cli, kernel, request, success};
use serde_json::{Value, json};

const BASE: &str = r#"
pub generic choose(x, y) { domain (Int, Int); }
method choose(x: Number, y: Number) -> Int { 0 }
pub grant integers : choose to module("../addon/Vastitas.toml", "") { domain (Int, Int); }
pub grant second : choose to module("../addon/Vastitas.toml", "") { domain (Int, Int); }
"#;
const ADDON: &str =
    "pub contribution sum : base::choose { method base::choose(x: Int, y: Int) -> Int { x + y } }";
const EVENTS: &str =
    "borrow base::integers as edit; apply addon::sum using edit; return edit; seal base::choose;";

fn package(s: &Scratch, name: &str, source: &str, dependencies: &str) {
    s.write(&format!("{name}/Vastitas.toml"), &format!("[package]\nname='{name}'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\n{dependencies}\n"));
    s.write(&format!("{name}/main.vast"), source);
}
fn fixture(base: &str, addon: &str, events: &str) -> Scratch {
    let s = Scratch::empty("edit borrowing");
    package(&s, "base", base, "");
    package(&s, "addon", addon, "base={path='../base'}");
    package(
        &s,
        "app",
        &format!("assembly {{ {events} }} fn main() -> Int {{ base::choose(40, 2) }}"),
        "base={path='../base'}\naddon={path='../addon'}\ndiamond={path='../addon'}",
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
fn rejects(s: &Scratch, code: &str) {
    let output = check(s);
    assert!(!output.status.success(), "accepted {code}");
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(error.contains(code), "expected {code}: {error}");
}

#[test]
fn external_edit_and_diamond_replay_execute_once() {
    let events = EVENTS.replace(
        "return edit;",
        "apply diamond::sum using edit; return edit;",
    );
    let s = fixture(BASE, ADDON, &events);
    success(&check(&s));
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
    assert_eq!(output.stdout, b"42\n");
}

#[test]
fn loans_are_exclusive_and_grants_do_not_activate_edit_authority() {
    for (events, code) in [
        (
            "borrow base::integers as a; borrow base::integers as b;",
            "E_BORROW",
        ),
        ("apply addon::sum using absent;", "E_BORROW"),
        ("apply addon::sum;", "E_OWNER"),
        ("borrow base::integers as a; seal base::choose;", "E_BORROW"),
        (
            "borrow base::integers as a; return a; return a;",
            "E_BORROW",
        ),
        ("borrow base::integers as a;", "E_BORROW"),
        (
            "borrow base::integers as a; apply addon::sum using a; return a;",
            "E_ASSEMBLY",
        ),
        (
            "seal base::choose; borrow base::integers as a;",
            "E_ASSEMBLY",
        ),
        (
            "borrow base::integers as a; return a; apply addon::sum using a;",
            "E_BORROW",
        ),
        (
            "borrow base::integers as a; apply addon::sum using a; return a; borrow base::second as b; apply addon::sum using b;",
            "E_PROVENANCE",
        ),
    ] {
        rejects(&fixture(BASE, ADDON, events), code);
    }
    let base = format!(
        "{BASE} pub contribution own : choose {{ method choose(x: Int, y: Int) -> Int {{ 42 }} }}"
    );
    rejects(
        &fixture(&base, ADDON, "borrow base::integers as a; apply base::own;"),
        "E_BORROW",
    );
}

#[test]
fn final_winning_footprint_and_all_bodies_are_checked() {
    let wrong_region = BASE.replace("domain (Int, Int); }", "domain (Nat, Nat); }");
    rejects(&fixture(&wrong_region, ADDON, EVENTS), "E_IMPACT");
    let bad = ADDON.replace("{ x + y }", "{ true }");
    rejects(&fixture(BASE, &bad, ""), "E_TYPE");
    rejects(&fixture(BASE, &bad, EVENTS), "E_TYPE");
    // A valid unused contribution is checked but cannot alter execution.
    let s = fixture(BASE, ADDON, "");
    success(&check(&s));
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
    assert_eq!(
        std::process::Command::new(s.0.join("program"))
            .output()
            .unwrap()
            .stdout,
        b"0\n"
    );
    let duplicate = format!(
        "{ADDON} pub contribution other : base::choose {{ method base::choose(a: Int, b: Int) -> Int {{ 1 }} }}"
    );
    rejects(
        &fixture(
            BASE,
            &duplicate,
            "borrow base::integers as a; apply addon::sum using a; apply addon::other using a; return a; seal base::choose;",
        ),
        "E_DUPLICATE",
    );
}

#[test]
fn open_return_can_be_repaired_by_owner_before_seal() {
    let scalars = ["Nat", "Int", "Bool", "Unit"];
    let region = scalars
        .iter()
        .flat_map(|a| scalars.iter().map(move |b| format!("({a}, {b})")))
        .collect::<Vec<_>>()
        .join(", ");
    let base = format!(
        r#"
pub generic choose(x, y) {{ domain (Int, Int); }}
method choose(x: Any, y: Any) -> Int {{ 0 }}
pub grant integers : choose to module("../addon/Vastitas.toml", "") {{ domain {region}; }}
pub contribution repair : choose {{ method choose(x: Number, y: Number) -> Int {{ 42 }} }}
"#
    );
    let addon = "pub contribution cross : base::choose {
method base::choose(x: Number, y: Any) -> Int { 1 }
method base::choose(x: Any, y: Number) -> Int { 2 } }";
    let events = "borrow base::integers as a; apply addon::cross using a; return a; apply base::repair; seal base::choose;";
    success(&check(&fixture(&base, addon, events)));
    rejects(
        &fixture(&base, addon, &events.replace("apply base::repair;", "")),
        "E_DISPATCH_AMBIGUOUS",
    );
}

#[test]
fn exact_module_root_placement_and_selected_closure_are_required() {
    let wrong = BASE.replace("\"\")", "\"child\")");
    rejects(&fixture(&wrong, ADDON, EVENTS), "E_OWNER");
    // The named module exists, but its parent is not the grantee.
    let s = fixture(&wrong, &format!("pub mod child; {ADDON}"), EVENTS);
    s.write("addon/child.vast", "pub fn marker() -> Int { 0 }");
    rejects(&s, "E_OWNER");
    let s = fixture(BASE, ADDON, EVENTS);
    s.write("addon/main.vast", &format!("{ADDON} assembly {{ }}"));
    rejects(&s, "E_ASSEMBLY");
    let s = fixture(BASE, ADDON, EVENTS);
    package(&s, "unselected", "fn f() -> Int { 0 }", "");
    s.write(
        "base/main.vast",
        &BASE.replace("../addon/", "../unselected/"),
    );
    rejects(&s, "E_OWNER");
    let s = fixture(BASE, ADDON, EVENTS);
    s.write("app/main.vast", "fn main() -> Int { 0 }");
    rejects(&s, "E_ASSEMBLY");
}

#[test]
fn nonwinning_applied_body_is_checked_even_with_an_empty_footprint() {
    let base = BASE.replace(
        r#"module("../addon/Vastitas.toml", "") { domain (Int, Int); }"#,
        r#"module("../addon/Vastitas.toml", "") { domain; }"#,
    ) + "method choose(x: Int, y: Int) requires (HasOrder) -> Int { 42 }";
    let addon = ADDON.replace("-> Int { x + y }", "requires (HasEq) -> Int { true }");
    rejects(&fixture(&base, &addon, EVENTS), "E_TYPE");
}

#[test]
fn hierarchy_and_contract_changes_revalidate_the_entire_assembly() {
    let base = BASE.replace("x: Number, y: Number", "x: Any, y: Any")
        + "pub abstract type Selected <: Any; subtype Int <: Selected;";
    let addon = "pub contribution sum : base::choose { method base::choose(x: base::Selected, y: Int) -> Int { 42 } }";
    let s = fixture(&base, addon, EVENTS);
    success(&check(&s));
    // A newly admitted key lies outside the original exact grant region.
    s.write(
        "base/main.vast",
        &(base.clone() + "subtype Bool <: Selected;"),
    );
    rejects(&s, "E_IMPACT");
    s.write(
        "base/main.vast",
        &(base + "abstract method choose(x: Int, y: Int) -> Bool { domain (Int, Int); }"),
    );
    rejects(&s, "E_CONTRACT_RESULT");
}

fn raw_module(source: &str) -> Value {
    let flat = request(source, "edit-raw.vast");
    let public = |key: &str| {
        flat[key]
            .as_array()
            .unwrap()
            .iter()
            .map(|item| {
                let mut item = item.clone();
                item["public"] = json!(true);
                item
            })
            .collect::<Vec<_>>()
    };
    json!({"path":[],"public":true,"span":{"start":0,"end":0,"line":1,"column":1},"imports":[],
        "functions":public("functions"),"generics":public("generics"),"methods":flat["methods"]})
}
fn raw_program() -> Value {
    let span = json!({"start":0,"end":0,"line":1,"column":1});
    let mut base = raw_module(
        "generic choose(x, y) { domain (Int, Int); } method choose(x: Number, y: Number) -> Int { 0 }",
    );
    base["grants"] = json!([{"name":"integers","target":["choose"],"grantee_source":"/addon/Vastitas.toml","grantee_path":[],
        "region":[["Int","Int"]],"span":span,"public":true}]);
    let mut addon = raw_module("");
    let mut method = request(
        "generic choose(x,y) { domain; } method choose(x: Int,y: Int) -> Int { x+y }",
        "edit-raw.vast",
    )["methods"][0]
        .clone();
    method["name"] = json!("base::choose");
    addon["contributions"] = json!([{"name":"sum","target":["base","choose"],"methods":[method],"span":span,"public":true}]);
    let mut app = raw_module("fn main() -> Int { 42 }");
    app["assembly"] = json!({"span":span,"events":[
        {"op":"borrow","grant":["base","integers"],"loan":"edit","span":span},
        {"op":"apply","contribution":["addon","sum"],"loan":"edit","span":span},
        {"op":"return","loan":"edit","span":span},
        {"op":"seal","target":["base","choose"],"span":span}]});
    json!({"version":5,"input":"package","file":"edit-raw.vast","root":"/app/Vastitas.toml","packages":[
        {"source":"/app/Vastitas.toml","name":"app","version":"0.1.0","modules":[app],"dependencies":[{"alias":"base","target":"/base/Vastitas.toml"},{"alias":"addon","target":"/addon/Vastitas.toml"}]},
        {"source":"/addon/Vastitas.toml","name":"addon","version":"0.1.0","modules":[addon],"dependencies":[{"alias":"base","target":"/base/Vastitas.toml"}]},
        {"source":"/base/Vastitas.toml","name":"base","version":"0.1.0","modules":[base],"dependencies":[]}
    ]})
}

#[test]
fn protocol_five_rejects_forged_authority_targets_and_stale_inputs() {
    let raw = raw_program();
    assert_eq!(kernel(&raw, "check")["ok"], true);
    for (mutation, code) in [
        ("issuer", "E_PROTOCOL"),
        ("grant", "E_PROTOCOL"),
        ("callee", "E_NAME"),
        ("region", "E_IMPACT"),
        ("grantee", "E_OWNER"),
        ("downgrade", "E_PROTOCOL"),
        ("input", "E_PROTOCOL"),
        ("body", "E_TYPE"),
        ("provenance", "E_PROTOCOL"),
    ] {
        let mut bad = raw.clone();
        match mutation {
            "issuer" => bad["packages"][2]["modules"][0]["grants"][0]["issuer"] = json!("trusted"),
            "grant" => {
                bad["packages"][0]["modules"][0]["assembly"]["events"][0]["authorized"] =
                    json!(true)
            }
            "callee" => {
                bad["packages"][1]["modules"][0]["contributions"][0]["methods"][0]["body"]["result"] = json!({"kind":"call","callee":"base::absent","args":[],"span":{"start":0,"end":0,"line":1,"column":1}})
            }
            "region" => {
                bad["packages"][2]["modules"][0]["grants"][0]["region"] = json!([["Nat", "Nat"]])
            }
            "grantee" => {
                bad["packages"][2]["modules"][0]["grants"][0]["grantee_source"] =
                    json!("/app/Vastitas.toml")
            }
            "downgrade" => bad["version"] = json!(4),
            "input" => bad["input"] = json!("flat"),
            "body" => {
                bad["packages"][1]["modules"][0]["contributions"][0]["methods"][0]["return_type"] =
                    json!({"kind":"named","name":"Bool"})
            }
            _ => bad["packages"][1]["modules"][0]["contributions"][0]["id"] = json!("trusted"),
        }
        let response = kernel(bad, "check");
        assert_eq!(
            response["diagnostics"][0]["code"], code,
            "{mutation}: {response}"
        );
    }
}

#[test]
fn new_words_are_contextual_and_ordinary_return_stays_unsupported() {
    let source = "fn grant(borrow: Int) -> Int { let seal = borrow; let contribution = seal; contribution } fn main() -> Int { grant(42) }";
    assert_eq!(
        kernel(request(source, "contextual.vast"), "check")["ok"],
        true
    );
    let errors =
        vastitas::frontend::parse("fn main() -> Int { return 42; }", "return.vast").unwrap_err();
    assert_eq!(errors[0].code, "E_UNSUPPORTED");
}
