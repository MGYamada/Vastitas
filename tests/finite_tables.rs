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

#[test]
fn finite_declarations_match_their_files_even_when_the_other_table_is_valid() {
    let s = Scratch::empty("physical finite rows");
    let source = "// λ\r\npub indexed finite Bit { lo; hi; }\n\
        pub indexed table point() -> Bit { () => hi; }\n\
        pub indexed table id(Bit,) -> Bit { (lo,) => lo; (hi,) => hi; }";
    s.write_package("app", "mod bits; fn main() -> Int { 7 }", "");
    s.write("app/bits.vast", source);
    let original = s.captured("app/Vastitas.toml", 10);
    for changed in [
        source.replace("() => hi;", "() => lo;"),
        source.replace("{ lo; hi; }", "{ hi; lo; }"),
        source.replace("pub indexed table id", "    indexed table id"),
    ] {
        s.write("app/bits.vast", &changed);
        let other = s.captured("app/Vastitas.toml", 10);
        assert_eq!(kernel(&other, "check")["ok"], true);
        let mut inconsistent = original.clone();
        inconsistent["root_source"] = other["root_source"].clone();
        for mode in ["check", "function-revision", "emit"] {
            let error = kernel(&inconsistent, mode);
            assert_wire_rejected(&error, "E_FINITE_SOURCE");
            if changed.contains("() => lo;") {
                let line = changed.lines().nth(2).unwrap();
                assert_eq!(error["diagnostics"][0]["span"]["line"], 3);
                assert_eq!(
                    error["diagnostics"][0]["span"]["column"],
                    line.find("lo;").unwrap() + 1
                );
            }
        }
    }

    let mut shifted = original.clone();
    let module = shifted["packages"][0]["modules"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|m| m["path"] == json!(["bits"]))
        .unwrap();
    let decls = module["indexed_declarations"].as_array_mut().unwrap();
    let point = decls.iter_mut().find(|d| d["name"] == "point").unwrap();
    point["rows"][0]["span"]["column"] = json!(1);
    let error = kernel(&shifted, "check");
    assert_wire_rejected(&error, "E_FINITE_SOURCE");
    assert_eq!(error["diagnostics"][0]["span"]["line"], 3);

    let mut omitted = original.clone();
    for m in omitted["packages"][0]["modules"].as_array_mut().unwrap() {
        m["indexed_declarations"] = json!([]);
    }
    assert_wire_rejected(&kernel(&omitted, "check"), "E_FINITE_SOURCE");
}

#[test]
fn category_and_monad_fields_match_the_selected_source_operands() {
    let s = Scratch::empty("physical finite instances");
    let src = format!(
        "{}\nfn main() -> Int {{ 7 }}",
        include_str!("../llvm/fixtures/ClosureUnit.vast")
    );
    s.write_package("app", &src, "");
    let raw = s.captured("app/Vastitas.toml", 10);
    assert_eq!(kernel(&raw, "check")["ok"], true);
    for (from, to) in [
        ("finite_category;", "finite_functor ;"),
        ("composable(s, t)", "composable(t, s)"),
        ("finite_graph(Obj, Arr, s, t", "finite_graph(Obj, Arr, t, s"),
        ("Closure::objects", "Closure::arrows "),
        ("Closure, Eta, Mu", "Closure, Mu, Eta"),
    ] {
        assert_eq!(from.len(), to.len());
        assert!(src.contains(from));
        let mut different = raw.clone();
        different["root_source"]["text"] = json!(src.replacen(from, to, 1));
        assert_wire_rejected(&kernel(&different, "emit"), "E_FINITE_SOURCE");
    }
}

#[test]
fn changing_a_physical_nullary_table_changes_the_llvm_case_and_revision() {
    let s = Scratch::empty("finite table LLVM");
    let source = "indexed finite Bit { lo; hi; }\nindexed table point() -> Bit { () => hi; }\n\
        fn main() -> Int { if finite::lookup::<point>() == Bit::hi { 42 } else { 7 } }";
    let manifest = "app/Vastitas.toml";
    s.write_package("app", source, "");
    let revision = s
        .command("check", manifest)
        .arg("--print-function-revision")
        .output()
        .unwrap();
    assert!(revision.status.success());
    let saved = s.0.join("revision.json");
    std::fs::write(&saved, revision.stdout).unwrap();
    let preview = || {
        let mut cmd = s.command("check", manifest);
        cmd.args([
            "--llvm-preview",
            "--target-triple",
            "x86_64-unknown-linux-gnu",
            "--data-layout",
            "e-m:e-i64:64-n8:16:32:64-S128",
        ]);
        cmd
    };
    let high = preview()
        .arg("--expect-function-revision")
        .arg(&saved)
        .output()
        .unwrap();
    s.write("app/main.vast", &source.replace("=> hi;", "=> lo;"));
    let stale = preview()
        .arg("--expect-function-revision")
        .arg(saved)
        .output()
        .unwrap();
    common::expect_code(&stale, "E_FUNCTION_REVISION");
    let low = preview().output().unwrap();
    assert!(high.status.success() && low.status.success());
    let high = String::from_utf8(high.stdout).unwrap();
    let high_case = "case0:\n  ret i32 1\n";
    assert_eq!(high.matches(high_case).count(), 1);
    assert_eq!(
        high.replace(high_case, "case0:\n  ret i32 0\n").as_bytes(),
        low.stdout
    );
}
