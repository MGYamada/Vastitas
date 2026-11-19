mod common;
use common::{Scratch, cli, flat_module, kernel, request, success};
use serde_json::{Value, json};

const BASE: &str = r#"
pub fn choose(x, y) domain((Int, Int));
fn choose(x: Number, y: Number) -> Int { 0 }
pub grant integers : choose to addon { domain (Int, Int); }
pub grant second : choose to addon { domain (Int, Int); }
"#;
const ADDON: &str =
    "pub contribution sum : base::choose { fn base::choose(x: Int, y: Int) -> Int { x + y } }";
const EVENTS: &str = "borrow base::integers as edit { apply addon::sum; }";

fn fixture(base: &str, addon: &str, events: &str) -> Scratch {
    let s = Scratch::empty("edit borrowing");
    s.write_package("base", base, "");
    s.write_package("addon", addon, "base={path='../base'}");
    s.write_package(
        "app",
        &format!("assemble base::choose {{ {events} }} fn main() -> Int {{ base::choose(40, 2) }}"),
        "base={path='../base'}\naddon={path='../addon'}\ndiamond={path='../addon'}",
    );
    s
}
fn check(s: &Scratch) -> std::process::Output {
    s.check_manifest("app/Vastitas.toml")
}
fn rejects(s: &Scratch, code: &str) {
    let output = check(s);
    assert!(!output.status.success(), "accepted {code}");
    common::expect_code(&output, code);
}

#[test]
fn external_edit_and_diamond_replay_execute_once() {
    let events = EVENTS.replace("apply addon::sum;", "apply addon::sum, diamond::sum;");
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
    assert_eq!(common::ran(&output), common::exits(42));
}

#[test]
fn loans_are_exclusive_and_grants_do_not_activate_edit_authority() {
    rejects(&fixture(BASE, ADDON, "apply addon::sum;"), "E_OWNER");
    rejects(
        &fixture(
            BASE,
            ADDON,
            "borrow base::integers as a { apply addon::sum; } borrow base::second as b { apply addon::sum; }",
        ),
        "E_PROVENANCE",
    );

    // These ill-scoped traces have no structured source spelling. Start with
    // an accepted public request and replace only the event sequence.
    let raw = raw_program();
    let events = raw["packages"][0]["modules"][0]["assembly"]["events"]
        .as_array()
        .unwrap();
    let (open, apply, close, seal) = (&events[0], &events[1], &events[2], &events[3]);
    let mut absent = apply.clone();
    absent["loan"] = json!("absent");
    let mut other = open.clone();
    other["loan"] = json!("other");
    for (forged, code) in [
        (json!([open, other, close, seal]), "E_BORROW"),
        (json!([absent, seal]), "E_BORROW"),
        (json!([open, seal]), "E_BORROW"),
        (json!([open, close, close, seal]), "E_BORROW"),
        (json!([open]), "E_BORROW"),
        (json!([open, apply, close]), "E_ASSEMBLY"),
        (json!([seal, open]), "E_ASSEMBLY"),
        (json!([open, close, apply, seal]), "E_BORROW"),
    ] {
        let mut bad = raw.clone();
        bad["packages"][0]["modules"][0]["assembly"]["events"] = forged;
        common::assert_wire_rejected(&kernel(&bad, "check"), code);
    }
    let base = format!(
        "{BASE} pub contribution own : choose {{ fn choose(x: Int, y: Int) -> Int {{ 42 }} }}"
    );
    let s = fixture(&base, ADDON, "borrow base::integers {} apply base::own;");
    let mut raw = s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    let events = raw["packages"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|p| p["name"] == "app")
        .unwrap()["modules"][0]["assembly"]["events"]
        .as_array_mut()
        .unwrap();
    events.swap(1, 2); // Attempt the owner's edit while borrowed.
    common::assert_wire_rejected(&kernel(raw, "check"), "E_BORROW");
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
        common::ran(
            &std::process::Command::new(s.0.join("program"))
                .output()
                .unwrap()
        ),
        common::exits(0)
    );
    let duplicate = format!(
        "{ADDON} pub contribution other : base::choose {{ fn base::choose(a: Int, b: Int) -> Int {{ 1 }} }}"
    );
    rejects(
        &fixture(
            BASE,
            &duplicate,
            "borrow base::integers as a { apply addon::sum; apply addon::other; }",
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
pub fn choose(x, y) domain((Int, Int));
fn choose(x: Any, y: Any) -> Int {{ 0 }}
pub grant integers : choose to addon {{ domain {region}; }}
pub contribution repair : choose {{ fn choose(x: Number, y: Number) -> Int {{ 42 }} }}
"#
    );
    let addon = "pub contribution cross : base::choose {
fn base::choose(x: Number, y: Any) -> Int { 1 }
fn base::choose(x: Any, y: Number) -> Int { 2 } }";
    let events = "borrow base::integers as a { apply addon::cross; } apply base::repair;";
    success(&check(&fixture(&base, addon, events)));
    rejects(
        &fixture(&base, addon, &events.replace("apply base::repair;", "")),
        "E_DISPATCH_AMBIGUOUS",
    );
}

#[test]
fn exact_module_root_placement_and_selected_closure_are_required() {
    let wrong = BASE.replace("to addon", "to addon::child");
    rejects(&fixture(&wrong, ADDON, EVENTS), "E_OWNER");
    // The named module exists, but its parent is not the grantee.
    let s = fixture(&wrong, &format!("pub mod child; {ADDON}"), EVENTS);
    s.write("addon/child.vast", "pub fn marker() -> Int { 0 }");
    rejects(&s, "E_OWNER");
    let s = fixture(BASE, ADDON, EVENTS);
    s.write(
        "addon/main.vast",
        &format!("{ADDON} assemble base::choose {{ }}"),
    );
    rejects(&s, "E_ASSEMBLY");
    let s = fixture(BASE, ADDON, EVENTS);
    s.write_package("unselected", "fn f() -> Int { 0 }", "");
    s.write("base/main.vast", &BASE.replace("to addon", "to unselected"));
    rejects(&s, "E_OWNER");
    let s = fixture(BASE, ADDON, EVENTS);
    s.write("app/main.vast", "fn main() -> Int { 0 }");
    success(&check(&s));
}

#[test]
fn nonwinning_applied_body_is_checked_even_with_an_empty_footprint() {
    let base = BASE.replace("to addon { domain (Int, Int); }", "to addon { domain; }")
        + "fn choose(x: Int, y: Int) requires (HasOrder) -> Int { 42 }";
    let addon = ADDON.replace("-> Int { x + y }", "requires (HasEq) -> Int { true }");
    rejects(&fixture(&base, &addon, EVENTS), "E_TYPE");
}

#[test]
fn hierarchy_and_contract_changes_revalidate_the_entire_assembly() {
    let base = BASE.replace("x: Number, y: Number", "x: Any, y: Any")
        + "pub abstract type Selected <: Any; subtype Int <: Selected;";
    let addon = "pub contribution sum : base::choose { fn base::choose(x: base::Selected, y: Int) -> Int { 42 } }";
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
        &(base + "fn choose(x: Int, y: Int) -> Bool domain((Int, Int));"),
    );
    rejects(&s, "E_CONTRACT_RESULT");
}

/// The root module of the request of the flat unit `source`, in which every
/// function and generic is public.
fn raw_module(source: &str) -> Value {
    flat_module(&mut request(source, "edit-raw.vast")).take()
}
const RAW_MAIN: &str = "fn main() -> Int { 42 }";

fn raw_program() -> Value {
    let span = json!({"start":0,"end":0,"line":1,"column":1});
    let mut base = raw_module(
        "fn choose(x, y) domain((Int, Int)); fn choose(x: Number, y: Number) -> Int { 0 }",
    );
    base["grants"] = json!([{"name":"integers","target":["choose"],"grantee_package":"addon","grantee_path":[],
        "region":[["Int","Int"]],"span":span,"public":true}]);
    let mut addon = raw_module("");
    let mut method = raw_module("fn choose(x,y) domain(); fn choose(x: Int,y: Int) -> Int { x+y }")
        ["methods"][0]
        .take();
    method["name"] = json!("base::choose");
    addon["contributions"] = json!([{"name":"sum","target":["base","choose"],"methods":[method],"span":span,"public":true}]);
    let mut app = raw_module(RAW_MAIN);
    // A handwritten protocol request with real, ordered lexical locations.
    let text = format!(
        "{RAW_MAIN}\nassemble base::choose {{ borrow base::integers as edit {{ apply addon::sum; }} }}"
    );
    let line_start = RAW_MAIN.len() + 1;
    let place = |start: usize, end: usize| json!({"start":line_start+start,"end":line_start+end,"line":2,"column":start+1});
    app["assembly"] = json!({"span":place(0,77),"source":[
        {"kind":"family","target":["base","choose"],"span":place(0,23)},
        {"kind":"borrow","grant":["base","integers"],"label":"edit","span":place(24,55)},
        {"kind":"apply","contributions":[["addon","sum"]],"span":place(56,73)},
        {"kind":"close","span":place(74,75)}, {"kind":"close","span":place(76,77)}],
      "events":[
        {"op":"borrow","grant":["base","integers"],"loan":"edit","span":place(24,55)},
        {"op":"apply","contribution":["addon","sum"],"loan":"edit","span":place(56,73)},
        {"op":"return","loan":"edit","span":place(74,75)},
        {"op":"seal","target":["base","choose"],"span":place(76,77)}]});
    json!({"version":common::CURRENT_PROTOCOL,"file":"edit-raw.vast","root":"/app/Vastitas.toml","root_source":{"offset":0,"text":text},"packages":[
        {"source":"/app/Vastitas.toml","name":"app","version":"0.1.0","edition":"2026","modules":[app],"dependencies":[{"alias":"base","target":"/base/Vastitas.toml"},{"alias":"addon","target":"/addon/Vastitas.toml"}]},
        {"source":"/addon/Vastitas.toml","name":"addon","version":"0.1.0","edition":"2026","modules":[addon],"dependencies":[{"alias":"base","target":"/base/Vastitas.toml"}]},
        {"source":"/base/Vastitas.toml","name":"base","version":"0.1.0","edition":"2026","modules":[base],"dependencies":[]}
    ]})
}

#[test]
fn raw_edit_requests_reject_forged_authority_targets_and_stale_inputs() {
    let raw = raw_program();
    assert_eq!(kernel(&raw, "check")["ok"], true);
    for (mutation, code) in [
        ("issuer", "E_PROTOCOL"),
        ("grant", "E_PROTOCOL"),
        ("callee", "E_NAME"),
        ("region", "E_IMPACT"),
        ("grantee", "E_OWNER"),
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
                bad["packages"][2]["modules"][0]["grants"][0]["grantee_package"] = json!("app")
            }
            "input" => bad["input"] = json!("flat"),
            "body" => {
                bad["packages"][1]["modules"][0]["contributions"][0]["methods"][0]["return_type"] =
                    json!({"kind":"named","name":"Bool"})
            }
            _ => bad["packages"][1]["modules"][0]["contributions"][0]["id"] = json!("trusted"),
        }
        let response = kernel(bad, "check");
        common::assert_wire_rejected(&response, code);
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

#[test]
fn omitted_assembly_keeps_all_declaration_and_unapplied_body_audits() {
    for empty in ["", "assemble base::choose { }"] {
        let s = fixture(BASE, ADDON, "");
        s.write(
            "app/main.vast",
            &format!("{empty} fn main() -> Int {{ base::choose(40, 2) }}"),
        );
        success(&check(&s));
        s.write("addon/main.vast", &ADDON.replace("{ x + y }", "{ true }"));
        rejects(&s, "E_TYPE");
        s.write("addon/main.vast", ADDON);
        s.write(
            "base/main.vast",
            &BASE.replace("to addon", "to addon::absent"),
        );
        rejects(&s, "E_OWNER");
    }
    let mut raw = raw_program();
    raw["packages"][0]["modules"][0]
        .as_object_mut()
        .unwrap()
        .remove("assembly");
    raw["root_source"]["text"] = json!(RAW_MAIN);
    assert_eq!(kernel(&raw, "check")["ok"], true);
    raw["packages"][1]["modules"][0]["contributions"][0]["methods"][0]["return_type"] =
        json!({"kind":"named","name":"Bool"});
    common::assert_wire_rejected(&kernel(&raw, "check"), "E_TYPE");
}

#[test]
fn domains_share_trailing_comma_rules_and_contract_results_are_checked() {
    let base = BASE.replace("(Int, Int);", "(Int, Int,), ;")
        + "fn choose(x: Int, y: Int) -> Int domain((Int, Int,),);";
    success(&check(&fixture(&base, ADDON, EVENTS)));
    let s = fixture(
        &base.replace("-> Int domain", "-> Bool domain"),
        ADDON,
        EVENTS,
    );
    let output = check(&s);
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("E_CONTRACT_RESULT"));
}
