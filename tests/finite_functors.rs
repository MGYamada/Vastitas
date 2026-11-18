//! A named finite functor is independently checked even when no body uses it.
mod common;
use common::{Scratch, assert_wire_rejected, checked_replace, expect_code, kernel};
use serde_json::{Value, json};

const CLOSURE: &str = include_str!("../examples/packages/finite-functor/src/main.vast");
const CHAIN: &str = include_str!("fixtures/finite-chain.vast");
const S3: &str = include_str!("../examples/packages/finite-category/src/main.vast");
const MANIFEST: &str = "app/Vastitas.toml";

fn local_closure() -> String {
    checked_replace(
        CLOSURE,
        "use std::category::Functor as Mapping;",
        "indexed schema Mapping = finite_functor;",
    )
}

fn declaration<'a>(wire: &'a mut Value, name: &str) -> &'a mut Value {
    wire["packages"][0]["modules"][0]["indexed_declarations"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|d| d["name"] == name)
        .unwrap()
}

#[test]
fn functor_grammar_rejects_unknown_schemas_and_wrong_argument_counts() {
    let scratch = Scratch::empty("finite functor grammar");
    for (from, to) in [
        ("Mapping = finite_functor;", "Mapping = finite_mapping;"),
        (
            "finite_functor(C, C, onObj, onArr)",
            "finite_functor(C, C, onObj)",
        ),
        (
            "finite_functor(C, C, onObj, onArr)",
            "finite_functor(C, C, onObj, onArr, ids)",
        ),
    ] {
        scratch.write_package("app", &checked_replace(&local_closure(), from, to), "");
        let error = expect_code(&scratch.check_manifest(MANIFEST), "E_PARSE");
        assert!(error.contains("main.vast:"), "{error}");
    }
}

#[test]
fn closure_endofunctor_checks_executes_and_preserves_all_path_spans() {
    let scratch = Scratch::empty("finite closure");
    let source = local_closure();
    scratch.write_package("app", &source, "");
    let mut wire = scratch.captured(MANIFEST, 10);
    let offset = wire["root_source"]["offset"].as_u64().unwrap();
    assert_eq!(
        declaration(&mut wire, "Mapping")["schema_kind"],
        "finite_functor"
    );
    let instance = declaration(&mut wire, "Closure");
    assert_eq!(instance["kind"], "instance");
    assert!(instance.get("graph").is_none());
    let fields = &instance["functor"];
    assert_eq!(fields.as_object().unwrap().len(), 4);
    for (reference, expected) in [
        (&instance["schema"], "Mapping"),
        (&fields["source"], "C"),
        (&fields["target"], "C"),
        (&fields["objects"], "onObj"),
        (&fields["arrows"], "onArr"),
    ] {
        assert_eq!(reference["path"], json!([expected]));
        let start = (reference["span"]["start"].as_u64().unwrap() - offset) as usize;
        let end = (reference["span"]["end"].as_u64().unwrap() - offset) as usize;
        assert_eq!(&source[start..end], expected);
    }
    assert_ne!(fields["source"]["span"], fields["target"]["span"]);
    common::prepare_stdlib_package();
    let example = common::root().join("examples/packages/finite-functor/Vastitas.toml");
    assert_eq!(
        scratch.check_build_and_run(example.to_str().unwrap()),
        common::exits(0)
    );
    wire["packages"][0]["modules"][0]["indexed_declarations"]
        .as_array_mut()
        .unwrap()
        .reverse();
    let result = kernel(&wire, "emit");
    assert_eq!(result["ok"], true, "{result}");
}

#[test]
fn object_and_arrow_projections_cross_distinct_nominal_categories() {
    let lib = CHAIN
        .split_once("fn main")
        .unwrap()
        .0
        .replace("indexed finite", "pub indexed finite")
        .replace("indexed instance C", "pub indexed instance C");
    let app = "use lib::C as Input;
indexed instance Forget : Mapping = finite_functor(Input, Terminal, onObj, onArr);
indexed schema Mapping = finite_functor;
indexed schema Small = finite_category;
indexed instance Terminal : Small = finite_graph(Apex, Identity, src, dst, ids, comp);
indexed finite Apex { pt; }
indexed finite Identity { id; }
indexed table src(Identity) -> Apex { (id) => pt; }
indexed table dst(Identity) -> Apex { (id) => pt; }
indexed table ids(Apex) -> Identity { (pt) => id; }
indexed table comp(Identity, Identity) -> Identity where composable(src, dst) { (id, id) => id; }
indexed table onObj(Input::objects) -> Apex { (lo) => pt; (hi) => pt; }
indexed table onArr(Input::arrows) -> Identity { (leftId) => id; (up) => id; (rightId) => id; }
fn atApex(x: lib::Obj<>) -> Apex<> { finite::lookup::<Forget::objects>(x) }
fn atIdentity(f: lib::Arr<>) -> Identity<> { finite::lookup::<Forget::arrows>(f) }
fn main() -> Int {
    if atApex(lib::Obj::hi) == Apex::pt && atIdentity(lib::Arr::up) == Identity::id { 42 } else { 1 }
}";
    let scratch = Scratch::empty("finite functor to terminal category");
    scratch.write_package("lib", &lib, "");
    scratch.write_package("app", app, "lib={path='../lib'}");
    assert_eq!(scratch.check_build_and_run(MANIFEST), common::exits(42));
    for (from, to, code) in [
        (
            "functor(Input, Terminal",
            "functor(Terminal, Input",
            "E_FUNCTOR",
        ),
        ("atApex(lib::Obj::hi)", "atApex(Apex::pt)", "E_TYPE"),
        (
            "-> Identity<> { finite::lookup",
            "-> lib::Arr<> { finite::lookup",
            "E_TYPE",
        ),
    ] {
        scratch.write("app/main.vast", &checked_replace(app, from, to));
        expect_code(&scratch.check_manifest(MANIFEST), code);
    }
}

#[test]
fn exported_functor_projects_its_private_tables_from_the_defining_package() {
    let lib = local_closure()
        .split_once("fn closeObject")
        .unwrap()
        .0
        .replace("indexed finite", "pub indexed finite")
        .replace("indexed instance Closure", "pub indexed instance Closure");
    let app = "use lib::Closure as F;
indexed finite Bit { off; on; }
indexed table onObj(Bit) -> Bit { (off) => off; (on) => on; }
fn main() -> Int {
    if finite::lookup::<F::objects>(lib::Obj::lo) == lib::Obj::hi &&
       finite::lookup::<F::arrows>(lib::Arr::up) == lib::Arr::rightId { 42 } else { 1 }
}";
    let scratch = Scratch::empty("imported finite functor");
    scratch.write_package("lib", &lib, "");
    scratch.write_package("app", app, "lib={path='../lib'}");
    assert_eq!(scratch.check_build_and_run(MANIFEST), common::exits(42));
    scratch.write(
        "app/main.vast",
        &checked_replace(app, "F::objects", "lib::onObj"),
    );
    expect_code(&scratch.check_manifest(MANIFEST), "E_VISIBILITY");
}

#[test]
fn unused_functor_checks_signatures_endpoints_identity_and_composition() {
    let scratch = Scratch::empty("unused finite functor laws");
    let source = local_closure();
    let closure = source.split_once("fn closeObject").unwrap().0;
    let group = S3.split_once("fn composeArrow").unwrap().0;
    // Inversion in S3 preserves endpoints and identities, but reverses composition.
    let inversion = "indexed schema Mapping = finite_functor;
indexed table onObj(Obj) -> Obj { (o) => o; }
indexed table invert(Arr) -> Arr {
    (p012) => p012; (p021) => p021; (p102) => p102;
    (p120) => p201; (p201) => p120; (p210) => p210;
}
indexed instance F : Mapping = finite_functor(S3, S3, onObj, invert);";
    let s3 = format!("{group}{inversion}");
    for (source, reason) in [
        (
            checked_replace(closure, "(up) => rightId;", "(up) => up;"),
            "endpoint",
        ),
        (
            checked_replace(closure, "onObj, onArr", "onArr, onObj"),
            "nominal",
        ),
        (checked_replace(closure, " : Mapping", " : Small"), "schema"),
        (
            checked_replace(closure, "onObj(Obj)", "onObj(Twin)").replace(
                "indexed finite Obj",
                "indexed finite Twin { lo; hi; }\nindexed finite Obj",
            ),
            "nominal",
        ),
        (
            checked_replace(&s3, "(p012) => p012;", "(p012) => p021;"),
            "identit",
        ),
        (s3, "composition"),
    ] {
        scratch.write_package("app", &format!("{source}\nfn main() -> Int {{ 0 }}"), "");
        let error = expect_code(&scratch.check_manifest(MANIFEST), "E_FUNCTOR");
        assert!(error.contains(reason), "{error}");
    }
}

#[test]
fn raw_functor_rejects_forged_paths_and_ambiguous_constructor_records() {
    let scratch = Scratch::empty("finite functor forged wire");
    scratch.write_package("app", &local_closure(), "");
    let mut wire = scratch.captured(MANIFEST, 10);
    let graph = declaration(&mut wire, "C")["graph"].clone();
    for (field, path) in [("source", "Obj"), ("target", "Mapping"), ("arrows", "s")] {
        let mut tampered = wire.clone();
        declaration(&mut tampered, "Closure")["functor"][field]["path"] = json!([path]);
        for mode in ["check", "emit"] {
            assert_wire_rejected(&kernel(&tampered, mode), "E_FUNCTOR");
        }
    }
    let mut ambiguous = wire.clone();
    declaration(&mut ambiguous, "Closure")["graph"] = graph;
    let mut neither = wire.clone();
    declaration(&mut neither, "Closure")
        .as_object_mut()
        .unwrap()
        .remove("functor");
    let mut unknown = wire;
    declaration(&mut unknown, "Closure")["functor"]["trusted"] = json!(true);
    for malformed in [ambiguous, neither, unknown] {
        assert_wire_rejected(&kernel(malformed, "emit"), "E_PROTOCOL");
    }
}

#[test]
fn vacuous_maps_from_empty_category_accept_but_cannot_be_reversed() {
    let source = format!(
        "{CHAIN}
indexed finite EObj {{}}
indexed finite EArr {{}}
indexed table es(EArr) -> EObj {{}}
indexed table et(EArr) -> EObj {{}}
indexed table eids(EObj) -> EArr {{}}
indexed table ecomp(EArr, EArr) -> EArr where composable(es, et) {{}}
indexed instance Empty : Small = finite_graph(EObj, EArr, es, et, eids, ecomp);
indexed schema Mapping = finite_functor;
indexed table onObj(EObj) -> Obj {{}}
indexed table onArr(EArr) -> Arr {{}}
indexed instance F : Mapping = finite_functor(Empty, C, onObj, onArr);"
    );
    let scratch = Scratch::empty("empty category functor");
    scratch.write_package("app", &source, "");
    common::success(&scratch.check_manifest(MANIFEST));
    let reverse = source
        .replace("onObj(EObj) -> Obj", "onObj(Obj) -> EObj")
        .replace("onArr(EArr) -> Arr", "onArr(Arr) -> EArr")
        .replace("functor(Empty, C", "functor(C, Empty");
    scratch.write("app/main.vast", &reverse);
    expect_code(&scratch.check_manifest(MANIFEST), "E_FINITE_TABLE");
}

#[test]
fn changing_to_an_equivalent_category_instance_invalidates_the_functor_revision() {
    let scratch = Scratch::empty("finite functor revision");
    let source = format!(
        "{}\nindexed instance D : Small = finite_graph(Obj, Arr, s, t, ids, comp);",
        local_closure()
    );
    scratch.write_package("app", &source, "");
    let original = scratch.captured(MANIFEST, 10);
    let evidence = kernel(&original, "function-revision");
    assert_eq!(evidence["ok"], true, "{evidence}");
    scratch.write(
        "app/main.vast",
        &checked_replace(&source, "functor(C, C,", "functor(C, D,"),
    );
    let mut other = scratch.captured(MANIFEST, 10);
    let result = kernel(&other, "check");
    assert_eq!(result["ok"], true, "{result}");
    other["expected_function_revision"] = evidence["function_revision"].clone();
    assert_wire_rejected(&kernel(other, "emit"), "E_FUNCTION_REVISION");
}
