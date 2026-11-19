//! Finite naturality is checked from the selected functors and component table.
mod common;
use common::{Scratch, assert_wire_rejected, checked_replace, expect_code, kernel};
use serde_json::{Value, json};

const EXAMPLE: &str =
    include_str!("../examples/packages/finite-natural-transformation/src/main.vast");
const S3: &str = include_str!("../examples/packages/finite-category/src/main.vast");
const MANIFEST: &str = "app/Vastitas.toml";

fn local_source() -> String {
    EXAMPLE
        .replace(
            "use std::category::Category;",
            "indexed schema Category = finite_category;",
        )
        .replace(
            "use std::category::Functor;",
            "indexed schema Functor = finite_functor;",
        )
        .replace(
            "use std::category::NatTrans;",
            "indexed schema NatTrans = finite_nat_trans;",
        )
}

fn decl<'a>(wire: &'a mut Value, name: &str) -> &'a mut Value {
    wire["packages"][0]["modules"][0]["indexed_declarations"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|d| d["name"] == name)
        .unwrap()
}

#[test]
fn closure_unit_uses_the_standard_schema_and_retains_component_path_spans() {
    let p = Scratch::empty("natural transformation example");
    common::prepare_stdlib_package();
    let example =
        common::root().join("examples/packages/finite-natural-transformation/Vastitas.toml");
    assert_eq!(
        p.check_build_and_run(example.to_str().unwrap()),
        common::exits(0)
    );
    let source = local_source();
    p.write_package("app", &source, "");
    let mut wire = p.captured(MANIFEST, 10);
    let offset = wire["root_source"]["offset"].as_u64().unwrap();
    assert_eq!(
        decl(&mut wire, "NatTrans")["schema_kind"],
        "finite_nat_trans"
    );
    let eta = decl(&mut wire, "Eta");
    assert_eq!(eta["kind"], "instance");
    assert!(eta.get("graph").is_none() && eta.get("functor").is_none());
    let fields = &eta["transformation"];
    assert_eq!(fields.as_object().unwrap().len(), 3);
    for (path, name) in [
        (&eta["schema"], "NatTrans"),
        (&fields["source"], "Id"),
        (&fields["target"], "Closure"),
        (&fields["components"], "etaAt"),
    ] {
        assert_eq!(path["path"], json!([name]));
        let at = |key: &str| (path["span"][key].as_u64().unwrap() - offset) as usize;
        assert_eq!(&source[at("start")..at("end")], name);
    }
    wire["packages"][0]["modules"][0]["indexed_declarations"]
        .as_array_mut()
        .unwrap()
        .reverse();
    assert_eq!(kernel(wire, "emit")["ok"], true);
}

#[test]
fn nominal_parallel_functors_and_component_types_are_required_even_when_unused() {
    let source = local_source();
    let declarations = source.split_once("fn componentAt").unwrap().0;
    let fixture = format!(
        "{declarations}
indexed instance D : Category = finite_graph(Obj, Arr, s, t, ids, comp);
indexed finite Twin {{ lo; hi; }}
fn main() -> Int {{ 0 }}"
    );
    let p = Scratch::empty("invalid component source");
    for (from, to, reason) in [
        (
            "finite_functor(C, C, closeObj",
            "finite_functor(D, C, closeObj",
            "same nominal source and target",
        ),
        (
            "finite_functor(C, C, closeObj",
            "finite_functor(C, D, closeObj",
            "same nominal source and target",
        ),
        ("Eta : NatTrans", "Eta : Functor", "schema"),
        (
            "finite_nat_trans(Id, Closure",
            "finite_nat_trans(C, Closure",
            "source must name a finite functor",
        ),
        ("etaAt(Obj)", "etaAt(Twin)", "nominal source object"),
        (
            "(lo) => up; (hi) => rightId;",
            "(lo) => leftId; (hi) => rightId;",
            "incorrect endpoints",
        ),
    ] {
        p.write_package("app", &checked_replace(&fixture, from, to), "");
        let error = expect_code(&p.check_manifest(MANIFEST), "E_NAT_TRANS");
        assert!(error.contains(reason), "{error}");
    }
    for replacement in [
        "finite_nat_trans(Id, Closure)",
        "finite_nat_trans(Id, Closure, etaAt, s)",
    ] {
        p.write_package(
            "app",
            &checked_replace(
                &fixture,
                "finite_nat_trans(Id, Closure, etaAt)",
                replacement,
            ),
            "",
        );
        expect_code(&p.check_manifest(MANIFEST), "E_PARSE");
    }
}

#[test]
fn conjugation_in_s3_distinguishes_both_sides_of_the_naturality_equation() {
    let group = S3.split_once("fn composeArrow").unwrap().0;
    // h = p120; G(f) = h f h⁻¹ gives G(f) h = h f for every f in S3.
    let source = format!("{group}
indexed schema Mapping = finite_functor;
indexed table obj(Obj) -> Obj {{ (o) => o; }}
indexed table same(Arr) -> Arr {{
    (p012) => p012; (p021) => p021; (p102) => p102;
    (p120) => p120; (p201) => p201; (p210) => p210;
}}
indexed table conjugate(Arr) -> Arr {{
    (p012) => p012; (p021) => p210; (p102) => p021;
    (p120) => p120; (p201) => p201; (p210) => p102;
}}
indexed instance F : Mapping = finite_functor(S3, S3, obj, same);
indexed instance G : Mapping = finite_functor(S3, S3, obj, conjugate);
indexed schema Transformation = finite_nat_trans;
indexed instance H : Transformation = finite_nat_trans(F, G, h);
indexed table h(Obj) -> Arr {{ (o) => p120; }}
fn main() -> Int {{ if finite::lookup::<H::components>(Obj::o) == Arr::p120 {{ 42 }} else {{ 1 }} }}");
    let p = Scratch::empty("noncommutative naturality");
    p.write_package("app", &source, "");
    assert_eq!(p.check_build_and_run(MANIFEST), common::exits(42));
    for other in ["finite_nat_trans(F, F, h)", "finite_nat_trans(G, F, h)"] {
        p.write(
            "app/main.vast",
            &checked_replace(&source, "finite_nat_trans(F, G, h)", other),
        );
        let error = expect_code(&p.check_manifest(MANIFEST), "E_NAT_TRANS");
        assert!(error.contains("naturality"), "{error}");
    }
    p.write("app/main.vast", &source);
    let mut wire = p.captured(MANIFEST, 10);
    // Recreate the ill-commuting Id ⇒ Id square directly in untrusted wire.
    decl(&mut wire, "H")["transformation"]["target"]["path"] = json!(["F"]);
    for mode in ["check", "emit"] {
        assert_wire_rejected(&kernel(&wire, mode), "E_NAT_TRANS");
    }
}

#[test]
fn component_projection_across_categories_uses_the_defining_packages_private_table() {
    let source = local_source();
    let declarations = source
        .split_once("indexed instance Eta")
        .unwrap()
        .0
        .replace("indexed finite Arr", "pub indexed finite Arr");
    let lib = format!(
        "{declarations}
pub indexed finite UObj {{ pt; }}
indexed finite UArr {{ triv; }}
indexed table us(UArr) -> UObj {{ (triv) => pt; }}
indexed table uid(UObj) -> UArr {{ (pt) => triv; }}
indexed table uc(UArr, UArr) -> UArr where composable(us, us) {{ (triv, triv) => triv; }}
indexed instance UnitCat : Category = finite_graph(UObj, UArr, us, us, uid, uc);
indexed table lowObj(UObj) -> Obj {{ (pt) => lo; }}
indexed table lowArr(UArr) -> Arr {{ (triv) => leftId; }}
indexed table highObj(UObj) -> Obj {{ (pt) => hi; }}
indexed table highArr(UArr) -> Arr {{ (triv) => rightId; }}
indexed instance Low : Functor = finite_functor(UnitCat, C, lowObj, lowArr);
indexed instance High : Functor = finite_functor(UnitCat, C, highObj, highArr);
pub indexed instance Shift : NatTrans = finite_nat_trans(Low, High, arrowAt);
indexed table arrowAt(UObj) -> Arr {{ (pt) => up; }}"
    );
    let app = "use lib::Shift as E;
indexed finite Local { pt; }
indexed table arrowAt(Local) -> Local { (pt) => pt; }
fn main() -> Int { if finite::lookup::<E::components>(lib::UObj::pt) == lib::Arr::up { 42 } else { 1 } }";
    let p = Scratch::empty("exported natural transformation");
    p.write_package("lib", &lib, "");
    p.write_package("app", app, "lib={path='../lib'}");
    assert_eq!(p.check_build_and_run(MANIFEST), common::exits(42));
    for (from, to, code) in [
        ("E::components", "lib::arrowAt", "E_VISIBILITY"),
        ("lib::UObj::pt", "Local::pt", "E_TYPE"),
        ("E::components", "E::objects", "E_NAT_TRANS"),
    ] {
        p.write("app/main.vast", &checked_replace(app, from, to));
        expect_code(&p.check_manifest(MANIFEST), code);
    }
}

#[test]
fn malformed_or_forged_transformation_records_fail_without_output() {
    let p = Scratch::empty("malformed transformation");
    p.write_package("app", &local_source(), "");
    let mut wire = p.captured(MANIFEST, 10);
    let graph = decl(&mut wire, "C")["graph"].clone();
    let functor = decl(&mut wire, "Closure")["functor"].clone();
    for (field, record) in [("graph", graph), ("functor", functor)] {
        let mut copy = wire.clone();
        decl(&mut copy, "Eta")[field] = record;
        assert_wire_rejected(&kernel(copy, "emit"), "E_PROTOCOL");
    }
    for (field, path) in [
        ("source", "NatTrans"),
        ("target", "C"),
        ("components", "sameObj"),
    ] {
        let mut copy = wire.clone();
        decl(&mut copy, "Eta")["transformation"][field]["path"] = json!([path]);
        assert_wire_rejected(&kernel(copy, "emit"), "E_NAT_TRANS");
    }
    decl(&mut wire, "Eta")["transformation"]["natural"] = json!(true);
    assert_wire_rejected(&kernel(wire, "emit"), "E_PROTOCOL");
}

#[test]
fn replay_rejects_an_equal_component_table_with_a_new_nominal_owner() {
    let source = format!(
        "{}\nindexed table etaBt(Obj) -> Arr {{ (lo) => up; (hi) => rightId; }}",
        local_source()
    );
    let p = Scratch::empty("natural transformation revision");
    p.write_package("app", &source, "");
    let old = kernel(p.captured(MANIFEST, 10), "function-revision");
    assert_eq!(old["ok"], true, "{old}");
    p.write(
        "app/main.vast",
        &checked_replace(&source, "Closure, etaAt)", "Closure, etaBt)"),
    );
    let mut changed = p.captured(MANIFEST, 10);
    let accepted = kernel(&changed, "check");
    assert_eq!(accepted["ok"], true, "{accepted}");
    changed["expected_function_revision"] = old["function_revision"].clone();
    assert_wire_rejected(&kernel(changed, "emit"), "E_FUNCTION_REVISION");
}
