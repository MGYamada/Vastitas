//! Lookup uses a checked nominal table, its ordered arguments and its selected category.
mod common;
use common::{Scratch, assert_wire_rejected, exits, kernel};
use serde_json::{Value, json};

const BITS: &str = "pub indexed finite Bit { high; low; }
pub indexed finite Empty {}
pub indexed table reset() -> Bit { () => low; }
pub indexed table choose(Bit, Bit) -> Bit {
    (low, low) => high; (high, high) => high;
    (low, high) => high; (high, low) => low;
}
pub indexed table vacuous(Empty) -> Empty {}
fn empty(x: Empty<>) -> Empty<> { finite::lookup::<vacuous>(x) }";
const APP: &str = "use lib::choose as pick;
fn main() -> Int {
  let x = finite::lookup::<lib::reset>();
  if finite::lookup::<pick>(lib::Bit::high, x) == lib::Bit::low
     && finite::lookup::<pick>(x, lib::Bit::high) == lib::Bit::high { 42 } else { 1 }
}";
const S3: &str = include_str!("../examples/packages/finite-category/src/main.vast");
const MANIFEST: &str = "app/Vastitas.toml";

#[test]
fn standard_category_composes_an_applications_noncommuting_arrows() {
    let (graph, _) = S3.split_once("fn composeArrow").unwrap();
    let graph = graph
        .replace(
            "indexed schema GroupCategory = finite_category;",
            "use std::category::Category;",
        )
        .replace("S3 : GroupCategory", "S3 : Category");
    let application = format!(
        "{graph}
use std::category::compose;
fn main() -> Int {{
    let after = std::category::compose::<S3, Obj::o, Obj::o, Obj::o>(S3::p021, S3::p102);
    let before = compose(S3::p102, S3::p021);
    let independent = fn(ok: Bool) -> Bool {{
        ok && compose::<S3, Obj::o, Obj::o, Obj::o>(S3::p021, S3::p102) == S3::p201
    }};
    if after == S3::p201 && before == S3::p120 && independent(true) {{ 42 }} else {{ 1 }}
}}"
    );
    let p = Scratch::empty("standard finite category");
    p.copy_stdlib(&common::STDLIB_PACKAGES, &[]);
    p.write_package("app", &application, "std={path='../stdlib'}");
    assert_eq!(p.check_build_and_run(MANIFEST), exits(42));
    for (result, code) in [("S3::missing", "E_TYPE"), ("after", "E_CAPTURE")] {
        let changed =
            common::checked_replace(&application, "== S3::p201\n", &format!("== {result}\n"));
        p.write("app/main.vast", &changed);
        common::expect_code(&p.check_manifest(MANIFEST), code);
    }
}

#[test]
fn imported_total_tables_execute_in_cartesian_order() {
    let p = Scratch::empty("finite lookup");
    p.write_package("lib", BITS, "");
    p.write_package("app", APP, "lib={path='../lib'}");
    assert_eq!(p.check_build_and_run(MANIFEST), exits(42));
}

fn replace_table(value: &mut Value, path: Value) -> bool {
    match value {
        Value::Object(o)
            if o.get("kind") == Some(&json!("finite_lookup"))
                && o["table"]["path"] == json!(["pick"]) =>
        {
            o["table"]["path"] = path;
            true
        }
        Value::Object(o) => o.values_mut().any(|v| replace_table(v, path.clone())),
        Value::Array(a) => a.iter_mut().any(|v| replace_table(v, path.clone())),
        _ => false,
    }
}

#[test]
fn lookup_checks_argument_arity_and_nominal_owner_in_both_kernel_modes() {
    let p = Scratch::empty("forged lookup");
    p.write_package("lib", BITS, "");
    p.write_package("other", BITS, "");
    p.write_package("app", APP, "lib={path='../lib'}\nother={path='../other'}");
    let wire = p.captured(MANIFEST, 10);
    for (path, code) in [
        (json!(["other", "choose"]), "E_TYPE"),
        (json!(["lib", "reset"]), "E_ARITY"),
        (json!(["lib", "Bit"]), "E_FINITE_TABLE"),
    ] {
        let mut changed = wire.clone();
        assert!(replace_table(&mut changed, path));
        for mode in ["emit", "check"] {
            assert_wire_rejected(&kernel(&changed, mode), code);
        }
    }
}

#[test]
fn noncommuting_homs_execute_only_through_the_selected_composition() {
    let p = Scratch::empty("noncommuting Hom");
    p.write_package("app", S3, "");
    assert_eq!(p.check_build_and_run(MANIFEST), exits(0));
    for (bad, code) in [
        (S3.replace("lookup::<S3::composition>", "lookup::<comp>"), "E_FINITE_TABLE"),
        (S3.replace(">(g, f)", ">(Arr::p021, Arr::p102)"), "E_TYPE"),
        (S3.replace("fn composeArrow", "indexed instance Other : GroupCategory = finite_graph(Obj, Arr, sourceOf, targetOf, ids, comp);\nfn composeArrow")
             .replace("lookup::<S3::composition>", "lookup::<Other::composition>"), "E_TYPE"),
    ] {
        p.write_package("app", &bad, "");
        assert_wire_rejected(&kernel(p.captured(MANIFEST, 10), "check"), code);
    }
}
