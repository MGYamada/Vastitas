//! Finite category instances go through the public parser and independent checker.
mod common;
use common::{Scratch, assert_wire_rejected, kernel};

const S3: &str = include_str!("../examples/packages/finite-category/src/main.vast");
const CHAIN: &str = include_str!("fixtures/finite-chain.vast");

#[test]
fn s3_and_partial_composition_check_independently() {
    for source in [S3, CHAIN] {
        let p = Scratch::empty("finite category");
        p.write_package("app", source, "");
        let wire = p.captured("app/Vastitas.toml", 10);
        let result = kernel(&wire, "check");
        assert_eq!(result["ok"], true, "{result}");
        let mut forged = wire;
        let inst = forged["packages"][0]["modules"][0]["indexed_declarations"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|d| d["kind"] == "instance")
            .unwrap();
        inst["schema"] = inst["graph"]["objects"].clone();
        let result = kernel(forged, "emit");
        assert_wire_rejected(&result, "E_CATEGORY");
    }
}

#[test]
fn wrong_composition_law_and_wrong_sparse_domain_reject() {
    for (bad, code, reason) in [
        (
            S3.replace("(p021, p021) => p012", "(p021, p021) => p021"),
            "E_CATEGORY",
            "associativity",
        ),
        (
            CHAIN.replace("(rightId, up) => up;", "(up, rightId) => up;"),
            "E_FINITE_TABLE",
            "not composable",
        ),
        (
            CHAIN.replace("(rightId, up) => up;", "(rightId, up) => rightId;"),
            "E_CATEGORY",
            "identity law",
        ),
        (
            CHAIN.replace("(hi) => rightId;", "(hi) => leftId;"),
            "E_CATEGORY",
            "incorrect endpoints",
        ),
        (
            CHAIN
                .replace(
                    "indexed schema Small",
                    "indexed finite Other { lo; hi; }\nindexed schema Small",
                )
                .replace("finite_graph(Obj,", "finite_graph(Other,"),
            "E_CATEGORY",
            "nominal endpoints",
        ),
    ] {
        assert!(bad != S3 && bad != CHAIN);
        let p = Scratch::empty("finite category law");
        p.write_package("app", &bad, "");
        let wire = p.captured("app/Vastitas.toml", 10);
        let result = kernel(wire, "check");
        assert_wire_rejected(&result, code);
        assert!(
            result["diagnostics"][0]["message"]
                .as_str()
                .unwrap()
                .contains(reason),
            "{result}"
        );
    }
}

#[test]
fn category_projections_follow_the_instance_owner_and_remain_checked() {
    let lib = CHAIN
        .replace("indexed schema Small", "pub indexed schema Small")
        .replace("indexed instance C", "pub indexed instance C")
        .replace("fn main() -> Int { 0 }", "");
    let app = "use lib::C as Chosen;
indexed finite Obj { shadow; }
indexed table reflect(Chosen::objects) -> Chosen::objects { (lo) => hi; (hi) => lo; }
indexed instance Clone : lib::Small = finite_graph(Chosen::objects, Chosen::arrows, Chosen::source, Chosen::target, Chosen::identities, Chosen::composition);
fn main() -> Int { 0 }";
    let p = Scratch::empty("finite projections");
    p.write_package("lib", &lib, "");
    p.write_package("app", app, "lib={path='../lib'}");
    common::success(&p.check_manifest("app/Vastitas.toml"));
    let wire = p.captured("app/Vastitas.toml", 10);
    for mode in ["check", "emit"] {
        let result = kernel(&wire, mode);
        assert_eq!(result["ok"], true, "{result}");
    }
    let mut forged = wire;
    let projected = forged["packages"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .flat_map(|pkg| pkg["modules"].as_array_mut().unwrap())
        .flat_map(|m| m["indexed_declarations"].as_array_mut().unwrap())
        .find(|decl| decl["name"] == "Clone")
        .unwrap();
    projected["graph"]["comp"] = projected["graph"]["ids"].clone();
    assert_wire_rejected(&kernel(&forged, "check"), "E_CATEGORY");
    // The underlying object carrier is private; exporting an instance does
    // not grant the caller direct namespace visibility or write authority.
    for (bad, code) in [
        (app.replace("table reflect(Chosen::objects)", "table reflect(lib::Obj)"), "E_VISIBILITY"),
        (app.replace("Chosen::identities", "Chosen::unknown"), "E_CATEGORY"),
        (app.replace("Chosen::composition", "Clone::composition"), "E_CYCLE"),
        (app.replace("use lib::C as Chosen;", "indexed instance Chosen : lib::Small = finite_graph(Clone::objects, Clone::arrows, Clone::source, Clone::target, Clone::identities, Clone::composition);"), "E_CYCLE"),
    ] {
        p.write_package("app", &bad, "lib={path='../lib'}");
        let result = kernel(p.captured("app/Vastitas.toml", 10), "check");
        assert_wire_rejected(&result, code);
    }
}

#[test]
fn a_projection_can_refer_to_a_later_instance() {
    let p = Scratch::empty("finite projection independent of declaration order");
    let forward = "indexed table reflect(C::objects) -> C::objects { (lo) => hi; (hi) => lo; }\n";
    p.write_package("app", &format!("{forward}{CHAIN}"), "");
    let result = kernel(p.captured("app/Vastitas.toml", 10), "check");
    assert_eq!(result["ok"], true, "{result}");
}

#[test]
fn concrete_hom_checks_category_and_endpoints_on_the_native_path() {
    let lib = CHAIN
        .replace("indexed instance C", "pub indexed instance C")
        .replace("fn main() -> Int { 0 }", "");
    let app = "use lib::C as M;
fn keep(f: Hom<M, M::objects::lo, M::objects::hi>) -> Hom<M, M::objects::lo, M::objects::hi> { f }
fn main() -> Int { if keep(M::up) == M::up { 42 } else { 1 } }";
    let p = Scratch::empty("finite hom across a private carrier");
    p.write_package("lib", &lib, "");
    p.write_package("app", app, "lib={path='../lib'}");
    assert_eq!(
        p.check_build_and_run("app/Vastitas.toml"),
        common::exits(42)
    );
}

#[test]
fn concrete_hom_rejects_wrong_endpoints_raw_tags_and_identical_graph_clones() {
    let base = CHAIN.replace(
        "fn main() -> Int { 0 }",
        "
indexed instance D : Small = finite_graph(Obj, Arr, s, t, ids, comp);
fn keep(f: Hom<C, Obj::lo, Obj::hi>) -> Hom<C, Obj::lo, Obj::hi> { f }
fn main() -> Int { if keep(C::up) == C::up { 42 } else { 1 } }",
    );
    let p = Scratch::empty("finite hom nominal indices");
    for (from, to) in [
        ("keep(C::up)", "keep(C::leftId)"),
        ("keep(C::up)", "keep(D::up)"),
        ("keep(C::up)", "keep(Arr::up)"),
        ("keep(C::up)", "keep(0)"),
        ("keep(C::up)", "keep(C::missing)"),
        ("Hom<C, Obj::lo, Obj::hi>", "Hom<C, Obj::hi, Obj::lo>"),
        ("Hom<C, Obj::lo, Obj::hi>", "Hom<C, Obj::lo, Obj::missing>"),
        ("Hom<C, Obj::lo, Obj::hi>", "Hom<C, Arr::up, Obj::hi>"),
        ("Hom<C, Obj::lo, Obj::hi>", "Hom<Small, Obj::lo, Obj::hi>"),
    ] {
        p.write_package("app", &base.replace(from, to), "");
        common::expect_code(&p.check_manifest("app/Vastitas.toml"), "E_TYPE");
    }

    p.write_package("app", &base, "");
    let mut wire = p.captured("app/Vastitas.toml", 10);
    fn change_index(value: &mut serde_json::Value) -> bool {
        if value["kind"] == "finite_hom" {
            value["source"]["path"] = serde_json::json!(["Obj", "hi"]);
            return true;
        }
        match value {
            serde_json::Value::Object(fields) => fields.values_mut().any(change_index),
            serde_json::Value::Array(items) => items.iter_mut().any(change_index),
            _ => false,
        }
    }
    assert!(change_index(&mut wire));
    for mode in ["check", "emit"] {
        assert_wire_rejected(&kernel(&wire, mode), "E_TYPE");
    }
}
