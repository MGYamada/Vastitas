mod common;

use common::{Scratch, expect_code, kernel, success};
use serde_json::json;

#[test]
fn published_examples_lower_to_their_original_authority_traces() {
    let f = json!({"op":"seal","target":["base","choose"]});
    let cases = [
        (
            "edit-borrow",
            json!([
                {"op":"borrow","grant":["base","integers"],"loan":"edit"},
                {"op":"apply","contribution":["addon","sum"],"loan":"edit"},
                {"op":"return","loan":"edit"}, f
            ]),
        ),
        (
            "edit-authority",
            json!([
                {"op":"borrow","grant":["base","outer"],"loan":"parent"},
                {"op":"reborrow","delegation":["addon","inner"],"parent":"parent","loan":"child"},
                {"op":"apply","contribution":["addon","ops","sum"],"loan":"child"},
                {"op":"return","loan":"child"}, {"op":"return","loan":"parent"},
                {"op":"transfer","declaration":["base","handoff"]},
                {"op":"apply","contribution":["addon","boolean"],"loan":null}, f
            ]),
        ),
    ];
    for (example, expected) in cases {
        let s = common::example_package(
            "authority goldens",
            &format!("examples/packages/authority/{example}"),
            &[],
        );
        let raw = s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
        let mut actual = raw["packages"]
            .as_array()
            .unwrap()
            .iter()
            .flat_map(|p| p["modules"].as_array().unwrap())
            .find_map(|m| m.get("assembly"))
            .unwrap()["events"]
            .clone();
        common::remove_spans(&mut actual);
        assert_eq!(actual, expected, "{example}");
    }
}

// These families have identical signatures and different defining owners:
// only the declaration resolved by the block path may be edited.
fn fixture(blocks: &str) -> Scratch {
    let s = Scratch::empty("per-family assemble");
    for pkg in ["left", "right"] {
        s.write_package(
            pkg,
            "pub fn f(x) domain((Int)); fn f(x: Int) -> Int { x } pub grant g : f to app { domain (Int); }",
            "",
        );
    }
    s.write_package(
        "app",
        &format!("use left::f as via; {blocks} fn main() -> Int {{ via(42) }}"),
        "left={path='../left'}\nright={path='../right'}",
    );
    s
}

#[test]
fn assembly_binds_the_resolved_family_even_without_installing_a_method() {
    let s = fixture("assemble via { borrow left::g {} } assemble right::f {}");
    success(&s.check_manifest("app/Vastitas.toml"));
    let mut wire = s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    let assembly = wire["packages"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .flat_map(|p| p["modules"].as_array_mut().unwrap())
        .find_map(|m| m.get_mut("assembly"))
        .unwrap();
    // The borrow and its return are valid alone, as are the two seals. The
    // independent checker still rejects the forged cross-family grouping.
    assembly["events"][0]["grant"] = json!(["right", "g"]);
    for mode in ["check", "emit"] {
        common::assert_wire_rejected(&kernel(&wire, mode), "E_ASSEMBLY");
    }
    expect_code(
        &fixture("assemble via { borrow right::g {} } assemble right::f {}")
            .check_manifest("app/Vastitas.toml"),
        "E_ASSEMBLY",
    );
    expect_code(
        &fixture("assemble via {} assemble left::f {}").check_manifest("app/Vastitas.toml"),
        "E_ASSEMBLY",
    );
}

#[test]
fn a_granted_singleton_can_be_extended_through_its_alias() {
    let s = Scratch::empty("structured singleton extension");
    s.write_package(
        "lib",
        "pub fn choose(x: Int) -> Int { 0 } pub grant ordered : choose to ext { domain (Int); }",
        "",
    );
    s.write_package("ext",
        "pub contribution inc : lib::choose { fn lib::choose(x: Int) requires (HasOrder) -> Int { x + 1 } }",
        "lib={path='../lib'}");
    s.write_package("app",
        "use lib::choose as via; assemble via { borrow lib::ordered { apply ext::inc; } } fn main() -> Int { via(41) }",
        "lib={path='../lib'}\next={path='../ext'}");
    assert_eq!(
        s.check_build_and_run("app/Vastitas.toml"),
        common::exits(42)
    );
}

#[test]
fn a_reexport_preserves_the_unedited_singleton_family_identity() {
    let s = Scratch::empty("reexported singleton seal");
    s.write_package("lib", "pub fn choose(x: Int) -> Int { x }", "");
    s.write_package(
        "relay",
        "pub use lib::choose as forwarded;",
        "lib={path='../lib'}",
    );
    let deps = "lib={path='../lib'}\nrelay={path='../relay'}";
    s.write_package(
        "app",
        "assemble relay::forwarded {} fn main() -> Int { lib::choose(42) }",
        deps,
    );
    success(&s.check_manifest("app/Vastitas.toml"));
    s.write(
        "app/main.vast",
        "assemble relay::forwarded {} assemble lib::choose {} fn main() -> Int { lib::choose(42) }",
    );
    expect_code(&s.check_manifest("app/Vastitas.toml"), "E_ASSEMBLY");
}

#[test]
fn a_higher_order_singleton_seals_by_its_defining_owner() {
    let s = Scratch::empty("higher order singleton seal");
    s.write_package(
        "lib",
        "pub fn twice(f: Fn<Int, Int>, x: Int) -> Int { f(f(x)) }",
        "",
    );
    let source = "use lib::twice as run; assemble run {} fn inc(x: Int) -> Int { x + 1 } fn main() -> Int { run(inc, 40) }";
    s.write_package("app", source, "lib={path='../lib'}");
    assert_eq!(
        s.check_build_and_run("app/Vastitas.toml"),
        common::exits(42)
    );
    s.write(
        "app/main.vast",
        &format!("{source} assemble lib::twice {{}}"),
    );
    expect_code(&s.check_manifest("app/Vastitas.toml"), "E_ASSEMBLY");
}

#[test]
fn a_grant_through_many_aliases_selects_the_current_assembly() {
    let s = Scratch::empty("function family alias chain");
    let mut library =
        String::from("pub fn choose(x: Int) -> Int { x } pub use choose as link300;\n");
    for index in (0..300).rev() {
        library.push_str(&format!("pub use link{} as link{index};\n", index + 1));
    }
    library.push_str("pub grant write : link0 to ext { domain (Int); }");
    s.write_package("lib", &library, "");
    s.write_package(
        "ext",
        "pub contribution shifted : lib::link0 { fn lib::link0(x: Int) requires (HasOrder) -> Int { x + 1 } }",
        "lib={path='../lib'}",
    );
    let caller = "use lib::link0 as selected; fn callback() -> Fn<Int, Int> { selected } fn main() -> Int { callback()(41) }";
    let manifest = "lib={path='../lib'}\next={path='../ext'}";
    s.write_package("app", &format!("{caller} assemble selected {{}}"), manifest);
    assert_eq!(
        s.check_build_and_run("app/Vastitas.toml"),
        common::exits(41)
    );
    s.write(
        "app/main.vast",
        &format!("{caller} assemble selected {{ borrow lib::write {{ apply ext::shifted; }} }}"),
    );
    assert_eq!(
        s.check_build_and_run("app/Vastitas.toml"),
        common::exits(42)
    );
}

#[test]
fn independently_replays_source_operands_labels_and_closing_braces() {
    let s = fixture("assemble via { borrow left::g {} } assemble right::f {}");
    let raw = s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    // Package order does not choose the root identity.
    let index = raw["packages"]
        .as_array()
        .unwrap()
        .iter()
        .position(|p| p["source"] == raw["root"])
        .unwrap();
    let path = format!("/packages/{index}/modules/0/assembly");
    let a = raw.pointer(&path).unwrap();
    let items = a["source"].as_array().unwrap();
    assert_eq!(items[0]["kind"], "family");
    assert_eq!(items[1]["kind"], "borrow");
    assert!(items[1]["label"].is_null());
    assert_eq!(items[2]["kind"], "close");
    for mode in ["check", "emit"] {
        assert_eq!(kernel(&raw, mode)["ok"], true);
        for (at, replacement) in [
            // Each of the changed traces has legal authority on its own.
            ("events/2/target", json!(["left", "f"])), // same FunctionId, different source spelling
            ("events/1/span", items[3]["span"].clone()),
            ("source/0/target", json!(["right", "f"])),
            ("source/1/label", json!("different")),
        ] {
            let mut stale = raw.clone();
            *stale.pointer_mut(&format!("{path}/{at}")).unwrap() = replacement;
            common::assert_wire_rejected(&kernel(&stale, mode), "E_ASSEMBLY");
        }
        let mut absent = raw.clone();
        absent
            .pointer_mut(&path)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .remove("source");
        common::assert_wire_rejected(&kernel(&absent, mode), "E_PROTOCOL");
    }

    let mut changed = raw.clone();
    changed.pointer_mut(&path).unwrap()["source"][1]["label"] = json!("named");
    changed.pointer_mut(&path).unwrap()["events"][0]["loan"] = json!("named");
    changed.pointer_mut(&path).unwrap()["events"][1]["loan"] = json!("named");
    for mode in ["check", "emit", "function-revision"] {
        common::assert_wire_rejected(&kernel(&changed, mode), "E_ASSEMBLY");
    }
    // The same label edit made in the physical file supplies matching spans
    // and commands, but requires its own function revision.
    let original = raw["root_source"]["text"].as_str().unwrap();
    s.write(
        "app/main.vast",
        &original.replace("borrow left::g {", "borrow left::g as named {"),
    );
    let mut fresh = s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    assert_eq!(kernel(&fresh, "check")["ok"], true);
    fresh["expected_function_revision"] =
        kernel(&raw, "function-revision")["function_revision"].clone();
    common::assert_wire_rejected(&kernel(&fresh, "check"), "E_FUNCTION_REVISION");
}

#[test]
fn entry_bytes_bind_every_assembly_even_if_the_entire_trace_is_removed() {
    let s = fixture("");
    let source = "// β assemble via {}\r\nuse left::f as via;\n\u{3000}assemble via { // }\r\n  borrow left::g {}\n}\nfn main() -> Int { via(42) }";
    s.write("app/main.vast", source);
    let raw = s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    assert_eq!(raw["root_source"]["text"], source);
    let base = raw["root_source"]["offset"].as_u64().unwrap() as usize;
    assert!(base > 0);
    let pkg = raw["packages"]
        .as_array()
        .unwrap()
        .iter()
        .position(|p| p["source"] == raw["root"])
        .unwrap();
    let path = format!("/packages/{pkg}/modules/0");
    let a = &raw.pointer(&path).unwrap()["assembly"];
    let header = &a["source"][0]["span"];
    assert_eq!(header["line"], 3);
    assert_eq!(header["column"], 2);
    assert_eq!(
        header["start"].as_u64().unwrap() as usize - base,
        source.find("assemble via { //").unwrap()
    );
    for mode in ["check", "emit"] {
        assert_eq!(kernel(&raw, mode)["ok"], true);
        let mut missing = raw.clone();
        missing
            .pointer_mut(&path)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .remove("assembly");
        common::assert_wire_rejected(&kernel(&missing, mode), "E_ASSEMBLY");
        let mut location = raw.clone();
        location["root_source"]["offset"] = (base + 1).into();
        common::assert_wire_rejected(&kernel(&location, mode), "E_PROTOCOL");
        missing.as_object_mut().unwrap().remove("root_source");
        common::assert_wire_rejected(&kernel(&missing, mode), "E_PROTOCOL");
    }
}

#[test]
fn protected_flat_entry_starts_at_zero_and_cannot_supply_edit_authority() {
    let mut raw = common::request("fn main() -> Int { 0 }", "flat.vast");
    assert_eq!(raw["root_source"]["offset"], 0);
    raw["root_source"]["offset"] = 1.into();
    common::assert_wire_rejected(&kernel(&raw, "check"), "E_PROTOCOL");

    // Keep the file, structured commands and authority events consistent.
    // Only the protected flat package identity prevents this empty seal.
    let s = Scratch::empty("flat assemble");
    s.write_package("app", "pub fn main() -> Int { 0 } assemble main {}", "");
    let mut package = s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    assert_eq!(kernel(&package, "check")["ok"], true);
    let base = package["root_source"]["offset"].as_u64().unwrap();
    fn rebase(value: &mut serde_json::Value, base: u64) {
        if let Some(fields) = value.as_object_mut() {
            if let Some(span) = fields.get_mut("span") {
                for key in ["start", "end"] {
                    let offset = span[key].as_u64().unwrap();
                    span[key] = (offset - base).into();
                }
            }
            fields.values_mut().for_each(|v| rebase(v, base));
        } else if let Some(items) = value.as_array_mut() {
            items.iter_mut().for_each(|v| rebase(v, base));
        }
    }
    let mut flat = common::request("fn main() -> Int { 0 }", "flat.vast");
    let assembly = &mut package["packages"][0]["modules"][0]["assembly"];
    rebase(assembly, base);
    flat["packages"][0]["modules"][0]["assembly"] = assembly.take();
    flat["root_source"]["text"] = package["root_source"]["text"].take();
    let response = kernel(&flat, "check");
    common::assert_wire_rejected(&response, "E_ASSEMBLY");
    assert!(
        response["diagnostics"][0]["message"]
            .as_str()
            .unwrap()
            .contains("package source file")
    );
}

#[test]
fn an_assembled_branch_returns_the_integer_from_the_taken_arm() {
    let scratch = Scratch::empty("assembled branch");
    let source = include_str!("../llvm/fixtures/ConditionalMethod.vast");
    scratch.write_package("branch_method", source, "");
    for (program, expected) in [
        (source.to_owned(), 43),
        (
            common::checked_replace(source, "choose(true,", "choose(false,"),
            237,
        ),
        (
            common::checked_replace(source, "apply conditional;", ""),
            237,
        ),
    ] {
        scratch.write("branch_method/main.vast", &program);
        assert_eq!(
            scratch.check_build_and_run("branch_method/Vastitas.toml"),
            common::exits(expected)
        );
    }
}
