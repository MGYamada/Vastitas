//! Static models and endpoints follow actual Hom arguments across package boundaries.
mod common;

use common::{CURRENT_PROTOCOL, Scratch, assert_wire_rejected, exits, kernel};
use serde_json::{Value, json};

const MANIFEST: &str = "app/Vastitas.toml";
const DEP: &str = "ops={path='../ops'}";
const CHAIN: &str = include_str!("fixtures/finite-chain.vast");
const S3: &str = include_str!("../examples/packages/finite-category/src/main.vast");
const OPS: &str = "pub indexed schema Small = finite_category;
pub fn combine<M: Small, X: Obj<M>, Y: Obj<M>, Z: Obj<M>>(
    g: Hom<M,Y,Z>, f: Hom<M,X,Y>) -> Hom<M,X,Z> {
    let h: Hom<M,X,Z> = finite::lookup::<M::composition>(g, f);
    if g == g { h } else { finite::lookup::<M::composition>(g, f) }
}";

fn chain(main: &str) -> String {
    CHAIN
        .replace("indexed schema Small = finite_category;", "")
        .replace("instance C : Small", "instance C : ops::Small")
        .replace("fn main() -> Int { 0 }", main)
}

fn template<'a>(wire: &'a mut Value, name: &str) -> &'a mut Value {
    wire["packages"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .flat_map(|p| p["modules"].as_array_mut().unwrap())
        .flat_map(|m| m["functions"].as_array_mut().unwrap())
        .find(|f| f["name"] == name)
        .unwrap()
}

#[test]
fn inferred_and_explicit_indices_select_the_same_nominal_specialization() {
    let p = Scratch::empty("finite binder revision");
    p.write_package("ops", OPS, "");
    let app = chain(
        "use ops::combine as after;
        indexed instance D : ops::Small = finite_graph(Obj, Arr, s, t, ids, comp);
        fn main() -> Int {
            let a = after(C::rightId, C::up);
            let b = after::<C, Obj::lo, Obj::hi, Obj::hi>(C::rightId, C::up);
            let d = after(D::rightId, D::up);
            if a == b && a == C::up && d == D::up { 42 } else { 1 }
        }",
    );
    p.write_package("app", &app, DEP);
    let wire = p.captured(MANIFEST, CURRENT_PROTOCOL);
    let response = kernel(&wire, "function-revision");
    assert_eq!(response["ok"], true, "{response}");
    let rev = &response["function_revision"];
    let row = rev["families"]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r["id"]["name"] == "combine")
        .unwrap();
    assert_eq!(row["finite_binders"][0]["schema"]["package"]["name"], "ops");
    assert_eq!(row["finite_binders"][1], json!({"category_slot": 0}));
    let symbols = rev["pure"]["symbols"].as_array().unwrap();
    let indices = symbols
        .iter()
        .enumerate()
        .filter(|(_, symbol)| symbol["id"] == row["id"])
        .collect::<Vec<_>>();
    assert_eq!(indices.len(), 2, "{symbols:?}");
    let mut models = Vec::new();
    for (_, sym) in &indices {
        let key = sym["specialization"]["finite_indices"].as_array().unwrap();
        assert_eq!(key.len(), 4);
        let cat = &key[0]["category"];
        assert_eq!(cat["package"]["name"], "app");
        models.push(cat["name"].as_str().unwrap());
        for (slot, tag) in key[1..].iter().zip(["lo", "hi", "hi"]) {
            assert_eq!(slot["category"], *cat);
            assert_eq!(slot["object"], tag);
        }
    }
    assert_eq!(p.check_build_and_run(MANIFEST), exits(42));
    models.sort_unstable();
    assert_eq!(models, ["C", "D"]);
    let mut pinned = wire.clone();
    pinned["expected_function_revision"] = rev.clone();
    assert_eq!(kernel(&pinned, "check")["function_revision_matched"], true);
    pinned["expected_function_revision"]["pure"]["symbols"][indices[0].0]["specialization"]["finite_indices"]
        [1]["object"] = json!("hi");
    for mode in ["check", "emit"] {
        assert_wire_rejected(&kernel(&pinned, mode), "E_FUNCTION_REVISION");
    }
}

#[test]
fn symbolic_composition_preserves_noncommuting_order() {
    let p = Scratch::empty("S3 finite template");
    p.write_package("ops", OPS, "");
    let decls = S3
        .split_once("fn composeArrow")
        .unwrap()
        .0
        .replace("indexed schema GroupCategory = finite_category;", "")
        .replace("instance S3 : GroupCategory", "instance S3 : ops::Small");
    let app = format!(
        "{decls}
        fn main() -> Int {{
            let a = ops::combine(S3::p021, S3::p102);
            let b = ops::combine(S3::p102, S3::p021);
            if a == S3::p201 && b == S3::p120 {{ 0 }} else {{ 1 }}
        }}"
    );
    p.write_package("app", &app, DEP);
    let emitted = kernel(p.captured(MANIFEST, CURRENT_PROTOCOL), "emit");
    assert_eq!(emitted["ok"], true, "{emitted}");
    assert_eq!(p.check_build_and_run(MANIFEST), exits(0));
}

#[test]
fn an_unused_template_is_checked_without_any_inhabited_model() {
    let p = Scratch::empty("symbolic body without models");
    p.write_package("ops", OPS, "");
    p.write_package("app", "fn main() -> Int { 0 }", DEP);
    let wire = p.captured(MANIFEST, CURRENT_PROTOCOL);
    assert_eq!(kernel(&wire, "check")["ok"], true);
    for (bad, code) in [
        (
            OPS.replace("composition>(g, f)", "composition>(f, g)"),
            "E_TYPE",
        ),
        (OPS.replace("-> Hom<M,X,Z>", "-> Hom<M,Z,X>"), "E_TYPE"),
        (OPS.replace("Z: Obj<M>", "Z: Obj<X>"), "E_CATEGORY"),
        (OPS.replace("Z: Obj<M>", "X: Obj<M>"), "E_DUPLICATE"),
    ] {
        p.write_package("ops", &bad, "");
        for mode in ["check", "emit"] {
            assert_wire_rejected(&kernel(p.captured(MANIFEST, CURRENT_PROTOCOL), mode), code);
        }
    }
    let mut forged = wire.clone();
    template(&mut forged, "combine")["finite_binders"][0]["schema"]["path"] = json!(["combine"]);
    assert_wire_rejected(&kernel(&forged, "check"), "E_CATEGORY");
}

#[test]
fn inference_rejects_foreign_models_ambiguous_indices_and_conflicting_endpoints() {
    let p = Scratch::empty("nominal static argument inference");
    p.write_package(
        "ops",
        &format!(
            "{OPS}
        pub fn flag<M: Small, X: Obj<M>>(b: Bool) -> Bool {{ b }}"
        ),
        "",
    );
    for call in [
        "ops::combine(C::up, C::rightId) == C::up",
        "ops::combine(C::rightId, D::up) == C::up",
        "ops::combine(D::rightId, D::up) == D::up",
        "ops::combine::<C, Obj::hi, Obj::hi, Obj::hi>(C::rightId, C::up) == C::up",
        "ops::flag(true)",
    ] {
        let app = chain(&format!(
            "indexed schema Other = finite_category;
            indexed instance D : Other = finite_graph(Obj, Arr, s, t, ids, comp);
            fn main() -> Int {{ if {call} {{ 0 }} else {{ 1 }} }}"
        ));
        p.write_package("app", &app, DEP);
        let wire = p.captured(MANIFEST, CURRENT_PROTOCOL);
        for mode in ["check", "emit"] {
            assert_wire_rejected(&kernel(&wire, mode), "E_TYPE");
        }
    }
}

#[test]
fn discovering_repeated_static_calls_keeps_each_functions_own_let_budget() {
    let p = Scratch::empty("finite function call budget");
    // Both functions are small. Inlining the callee at every site during key
    // discovery would incorrectly charge more than 4,096 generated lets to main.
    let locals = (0..65)
        .map(|i| format!("let saved{i} = arrow;"))
        .collect::<Vec<_>>()
        .join("\n");
    p.write_package(
        "ops",
        &format!(
            "pub indexed schema Small = finite_category;
            pub fn keep<M: Small, X: Obj<M>, Y: Obj<M>>(arrow: Hom<M,X,Y>) -> Hom<M,X,Y> {{
                {locals} saved64
            }}"
        ),
        "",
    );
    let calls = (0..65)
        .map(|i| format!("let result{i} = ops::keep(C::up);"))
        .collect::<Vec<_>>()
        .join("\n");
    p.write_package(
        "app",
        &chain(&format!(
            "fn main() -> Int {{ {calls} if result64 == C::up {{ 0 }} else {{ 1 }} }}"
        )),
        DEP,
    );
    common::success(&p.check_manifest(MANIFEST));
}
