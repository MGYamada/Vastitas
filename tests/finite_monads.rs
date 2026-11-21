//! A finite monad retains both natural transformations as part of its structure.
mod common;
use common::{Scratch, assert_wire_rejected, checked_replace, expect_code, kernel};
use serde_json::{Value, json};

const EXAMPLE: &str = include_str!("../examples/packages/finite-monad/src/main.vast");
const MANIFEST: &str = "app/Vastitas.toml";
const C2: &str = "indexed schema Cat = finite_category;
indexed schema Map = finite_functor;
indexed schema Transformation = finite_nat_trans;
indexed schema Structure = finite_monad;
indexed finite Obj { o; }
indexed finite Arr { e; s; }
indexed table pt(Arr) -> Obj { (e) => o; (s) => o; }
indexed table identity(Obj) -> Arr { (o) => e; }
indexed table group(Arr, Arr) -> Arr where composable(pt, pt) {
    (e, e) => e; (e, s) => s; (s, e) => s; (s, s) => e;
}
indexed instance C : Cat = finite_graph(Obj, Arr, pt, pt, identity, group);
indexed table sameObj(Obj) -> Obj { (o) => o; }
indexed table sameArr(Arr) -> Arr { (e) => e; (s) => s; }
indexed instance T : Map = finite_functor(C, C, sameObj, sameArr);
indexed table involution(Obj) -> Arr { (o) => s; }
indexed instance Trivial : Transformation = finite_nat_trans(T, T, identity);
indexed instance Twist : Transformation = finite_nat_trans(T, T, involution);
indexed instance A : Structure = finite_monad(C, T, Trivial, Trivial);
indexed instance B : Structure = finite_monad(C, T, Twist, Twist);";

fn local_example() -> String {
    let mut source = EXAMPLE.to_owned();
    for (name, kind) in [
        ("Category", "finite_category"),
        ("Functor", "finite_functor"),
        ("NatTrans", "finite_nat_trans"),
        ("Monad", "finite_monad"),
    ] {
        source = checked_replace(
            &source,
            &format!("use std::category::{name};"),
            &format!("indexed schema {name} = {kind};"),
        );
    }
    source
}

#[test]
fn static_hom_callables_keep_their_declaring_package_and_fiber() {
    let (chain, _) = include_str!("fixtures/finite-chain.vast")
        .split_once("fn main")
        .unwrap();
    let public = chain
        .replace("indexed instance C :", "pub indexed instance C :")
        .replace("indexed finite Obj", "pub indexed finite Obj");
    let models = format!(
        "{public}
        fn upArrow() -> Hom<C, Obj::lo, Obj::hi> {{ C::up }}
        pub fn provider() -> Fn<(), Hom<C, Obj::lo, Obj::hi>> {{ upArrow }}
        pub fn run(k: Fn<(), Hom<C, Obj::lo, Obj::hi>>) -> Hom<C, Obj::lo, Obj::hi> {{ k() }}
        pub fn applyArrow(k: Fn<Hom<C, Obj::lo, Obj::hi>, Hom<C, Obj::lo, Obj::hi>>,
            f: Hom<C, Obj::lo, Obj::hi>) -> Hom<C, Obj::lo, Obj::hi> {{ k(f) }}"
    );
    let app = format!(
        "{chain}
        use models::Obj as Vertices;
        fn localArrow() -> Hom<C, Obj::lo, Obj::hi> {{ C::up }}
        fn main() -> Int {{
            let k: Fn<(), Hom<models::C, Vertices::lo, Vertices::hi>> = models::provider();
            let identity = fn(f: Hom<models::C, Vertices::lo, Vertices::hi>)
                -> Hom<models::C, Vertices::lo, Vertices::hi> {{ f }};
            if models::applyArrow(identity, models::run(k)) == models::C::up {{ 42 }} else {{ 7 }}
        }}"
    );
    let p = Scratch::empty("nominal Hom callback");
    p.write_package("models", &models, "");
    p.write_package("app", &app, "models={path='../models'}");
    assert_eq!(p.check_build_and_run(MANIFEST), common::exits(42));
    let mut wire = p.captured(MANIFEST, 10);
    let run = wire["packages"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .flat_map(|package| package["modules"].as_array_mut().unwrap())
        .flat_map(|module| module["functions"].as_array_mut().unwrap())
        .find(|f| f["name"] == "run")
        .unwrap();
    let result = &mut run["params"][0]["ty"]["return_type"];
    assert_eq!(result["target"]["path"], json!(["Obj", "hi"]));
    result["target"]["path"] = json!(["Obj", "lo"]);
    assert_wire_rejected(&kernel(wire, "check"), "E_TYPE");
    for (from, to) in [
        ("models::provider()", "localArrow"),
        ("Vertices::hi>>", "Vertices::lo>>"),
        ("Fn<(), Hom<models::C", "Fn<Unit, Hom<models::C"),
    ] {
        p.write("app/main.vast", &checked_replace(&app, from, to));
        expect_code(&p.check_manifest(MANIFEST), "E_TYPE");
    }
}

#[test]
fn nested_callbacks_with_an_empty_hom_result_are_audited_without_a_sample_arrow() {
    let (chain, _) = include_str!("fixtures/finite-chain.vast")
        .split_once("fn main")
        .unwrap();
    let source = format!(
        "{chain}
        fn run(k: Fn<(), Hom<C, Obj::hi, Obj::lo>>) -> Hom<C, Obj::hi, Obj::lo> {{ k() }}
        fn nested(g: Fn<(), Fn<(), Hom<C, Obj::hi, Obj::lo>>>) -> Hom<C, Obj::hi, Obj::lo> {{
            run(g())
        }}
        fn main() -> Int {{ 42 }}"
    );
    let p = Scratch::empty("empty Hom result in a nested callable");
    p.write_package("app", &source, "");
    common::success(&p.check_manifest(MANIFEST));
    p.write(
        "app/main.vast",
        &checked_replace(&source, "run(g())", "C::up"),
    );
    expect_code(&p.check_manifest(MANIFEST), "E_TYPE");
}

#[test]
fn kleisli_projections_use_the_visible_monad_and_its_private_maps() {
    let declarations = local_example();
    let models = declarations
        .split_once("pub fn unitAt")
        .unwrap()
        .0
        .replace("indexed finite Obj", "pub indexed finite Obj")
        .replace("indexed instance C :", "pub indexed instance C :")
        .replace("indexed instance M :", "pub indexed instance M :");
    let library = format!(
        "{models}
        indexed instance Hidden : Monad = finite_monad(C, Closure, Eta, Mu);
        pub fn first<Mdl: Monad, X: Obj<Mdl::category>>()
            -> Hom<Mdl::category, X, Mdl::T<X>> {{ finite::lookup::<Mdl::unit>(X) }}"
    );
    let app = "use models::C;
        use models::Obj;
        indexed finite Arr { trap; }
        indexed table closeArr(Arr) -> Arr { (trap) => trap; }
        fn mapped(f: Hom<models::M::category, Obj::lo, Obj::hi>)
              -> Hom<models::M::category, models::M::T<Obj::lo>, models::M::T<Obj::hi>> {
            finite::lookup::<models::M::arrows>(f)
        }
        fn main() -> Int {
            let u = models::first::<models::M, Obj::lo>();
            if u == C::up && mapped(u) == C::rightId { 42 } else { 1 }
        }";
    let p = Scratch::empty("private Kleisli projections");
    p.write_package("models", &library, "");
    p.write_package("app", app, "models={path='../models'}");
    assert_eq!(p.check_build_and_run(MANIFEST), common::exits(42));
    for (from, to) in [
        ("models::M::arrows", "models::closeArr"),
        ("models::M::T<Obj::lo>", "models::Hidden::T<Obj::lo>"),
        ("::<models::M, Obj::lo>", "::<models::Hidden, Obj::lo>"),
    ] {
        p.write("app/main.vast", &checked_replace(app, from, to));
        expect_code(&p.check_manifest(MANIFEST), "E_VISIBILITY");
    }
}

#[test]
fn kleisli_inference_cannot_recover_a_monad_from_a_hom_or_an_expected_type() {
    let source = format!(
        "{C2}
        fn current<M: Structure, X: Obj<M::category>>()
            -> Hom<M::category, X, M::T<X>> {{ finite::lookup::<M::unit>(X) }}
        fn keep<M: Structure, X: Obj<M::category>, Y: Obj<M::category>>(
            f: Hom<M::category, X, Y>) -> Hom<M::category, X, Y> {{ f }}
        fn main() -> Int {{
            let a: Hom<C,Obj::o,Obj::o> = current::<A,Obj::o>();
            let b: Hom<C,Obj::o,Obj::o> = current::<B,Obj::o>();
            if a == C::e && keep::<B,Obj::o,Obj::o>(b) == C::s {{ 0 }} else {{ 1 }}
        }}"
    );
    let p = Scratch::empty("ambiguous Kleisli indices");
    p.write_package("app", &source, "");
    assert_eq!(p.check_build_and_run(MANIFEST), common::exits(0));
    for (from, to) in [
        ("current::<A,Obj::o>()", "current()"),
        ("keep::<B,Obj::o,Obj::o>(b)", "keep(b)"),
        ("current::<A,Obj::o>()", "current::<C,Obj::o>()"),
    ] {
        p.write("app/main.vast", &checked_replace(&source, from, to));
        expect_code(&p.check_manifest(MANIFEST), "E_TYPE");
    }
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
fn closure_monad_exercises_both_projections_and_preserves_four_named_paths() {
    let p = Scratch::empty("closure monad");
    common::prepare_stdlib_package();
    let manifest = common::root().join("examples/packages/finite-monad/Vastitas.toml");
    assert_eq!(
        p.check_build_and_run(manifest.to_str().unwrap()),
        common::exits(0)
    );
    let source = local_example();
    p.write_package("app", &source, "");
    let mut wire = p.captured(MANIFEST, 10);
    let offset = wire["root_source"]["offset"].as_u64().unwrap();
    assert_eq!(decl(&mut wire, "Monad")["schema_kind"], "finite_monad");
    let m = decl(&mut wire, "M");
    assert_eq!(m["kind"], "instance");
    assert!(
        ["graph", "functor", "transformation"]
            .iter()
            .all(|key| m.get(key).is_none())
    );
    let fields = &m["monad"];
    assert_eq!(fields.as_object().unwrap().len(), 4);
    for (field, name) in [
        ("category", "C"),
        ("functor", "Closure"),
        ("unit", "Eta"),
        ("multiplication", "Mu"),
    ] {
        let path = &fields[field];
        assert_eq!(path["path"], json!([name]));
        let at = |key: &str| (path["span"][key].as_u64().unwrap() - offset) as usize;
        assert_eq!(&source[at("start")..at("end")], name);
    }
    wire["packages"][0]["modules"][0]["indexed_declarations"]
        .as_array_mut()
        .unwrap()
        .reverse();
    let result = kernel(wire, "emit");
    assert_eq!(result["ok"], true, "{result}");
}

#[test]
fn exact_target_unit_identity_and_squared_functor_source_are_independently_required() {
    let source = format!(
        "{}\nindexed instance Other : Category = finite_graph(Obj, Arr, s, t, ids, comp);",
        local_example()
    );
    let p = Scratch::empty("invalid monad");
    // Each replacement still leaves lawful named functors and natural transformations.
    for (from, to) in [
        ("finite_monad(C, Closure", "finite_monad(Other, Closure"),
        ("M : Monad", "M : NatTrans"),
        ("Closure, Eta, Mu)", "Closure, Mu, Mu)"),
        ("Closure, Eta, Mu)", "Closure, Eta, Eta)"),
        (
            "finite_nat_trans(Id, Closure, etaAt)",
            "finite_nat_trans(Id, Twice, etaAt)",
        ),
        (
            "finite_nat_trans(Twice, Closure, muAt)",
            "finite_nat_trans(Twice, Twice, muAt)",
        ),
    ] {
        p.write_package("app", &checked_replace(&source, from, to), "");
        expect_code(&p.check_manifest(MANIFEST), "E_MONAD");
    }
    p.write_package(
        "app",
        &checked_replace(
            &source,
            "finite_monad(C, Closure, Eta, Mu)",
            "finite_monad(C, Closure, Eta)",
        ),
        "",
    );
    expect_code(&p.check_manifest(MANIFEST), "E_PARSE");
}

#[test]
fn two_structures_on_one_endofunctor_select_distinct_units_and_multiplications() {
    let p = Scratch::empty("two monads on same functor");
    let app = format!(
        "{C2}
fn main() -> Int {{
    if finite::lookup::<A::unit>(Obj::o) == Arr::e &&
       finite::lookup::<A::multiplication>(Obj::o) == Arr::e &&
       finite::lookup::<B::unit>(Obj::o) == Arr::s &&
       finite::lookup::<B::multiplication>(Obj::o) == Arr::s {{ 42 }} else {{ 1 }}
}}"
    );
    p.write_package("app", &app, "");
    assert_eq!(p.check_build_and_run(MANIFEST), common::exits(42));
    for (eta, mu) in [("Trivial", "Twist"), ("Twist", "Trivial")] {
        let bad = checked_replace(&app, "T, Twist, Twist)", &format!("T, {eta}, {mu})"));
        p.write("app/main.vast", &bad);
        let error = expect_code(&p.check_manifest(MANIFEST), "E_MONAD");
        assert!(error.contains("unit"), "{error}");
    }
}

#[test]
fn a_natural_multiplication_can_fail_the_associativity_diagram() {
    // Adjoin an absorbing zero to C2. T sends every arrow to e; consequently
    // μ Tμ is s·e = s, whereas μ μ_T is s·s = e. The unit laws also fail.
    let declarations = C2
        .split_once("indexed instance T")
        .unwrap()
        .0
        .replace("Arr { e; s; }", "Arr { e; s; zero; }")
        .replace("(s) => o;", "(s) => o; (zero) => o;")
        .replace(
            "(s, s) => e;",
            "(s, s) => e; (s, zero) => zero; (e, zero) => zero;
            (zero, s) => zero; (zero, e) => zero; (zero, zero) => zero;",
        )
        .replace("(s) => s;", "(s) => s; (zero) => zero;");
    let source = format!(
        "{declarations}
indexed instance Id : Map = finite_functor(C, C, sameObj, sameArr);
indexed table collapse(Arr) -> Arr {{ (e) => e; (s) => e; (zero) => e; }}
indexed instance T : Map = finite_functor(C, C, sameObj, collapse);
indexed table etaAt(Obj) -> Arr {{ (o) => zero; }}
indexed table muAt(Obj) -> Arr {{ (o) => s; }}
indexed instance Eta : Transformation = finite_nat_trans(Id, T, etaAt);
indexed instance Mu : Transformation = finite_nat_trans(T, T, muAt);
fn main() -> Int {{
    if finite::lookup::<Mu::components>(Obj::o) == Arr::s &&
       finite::lookup::<T::arrows>(Arr::s) == Arr::e &&
       finite::lookup::<C::composition>(C::s, C::e) != finite::lookup::<C::composition>(C::s, C::s)
       {{ 42 }} else {{ 1 }} }}"
    );
    let p = Scratch::empty("nonassociative natural multiplication");
    p.write_package("app", &source, "");
    assert_eq!(p.check_build_and_run(MANIFEST), common::exits(42));
    p.write(
        "app/main.vast",
        &format!("{source}\nindexed instance M : Structure = finite_monad(C, T, Eta, Mu);"),
    );
    expect_code(&p.check_manifest(MANIFEST), "E_MONAD");
}

#[test]
fn monad_projection_resolves_components_in_the_transformations_defining_package() {
    let lib = C2
        .split_once("indexed instance A")
        .unwrap()
        .0
        .replace("indexed finite", "pub indexed finite")
        .replace("indexed instance C", "pub indexed instance C")
        .replace("indexed instance T", "pub indexed instance T");
    let p = Scratch::empty("monad projection owner");
    p.write_package("lib", &lib, "");
    let app = "use lib::C as C;
use lib::T as T;
use lib::Twist as W;
indexed schema MSchema = finite_monad;
indexed instance M : MSchema = finite_monad(C, T, W, W);
indexed finite Bit { o; }
indexed table involution(Bit) -> Bit { (o) => o; }
fn main() -> Int { if finite::lookup::<M::multiplication>(lib::Obj::o) == lib::Arr::s &&
finite::lookup::<M::unit>(lib::Obj::o) == lib::Arr::s { 42 } else { 1 } }";
    p.write_package("app", app, "lib={path='../lib'}");
    assert_eq!(p.check_build_and_run(MANIFEST), common::exits(42));
    for (from, to, code) in [
        ("M::unit", "lib::involution", "E_VISIBILITY"),
        ("M::unit", "M::components", "E_MONAD"),
        ("M::unit>(lib::Obj::o)", "M::unit>(Bit::o)", "E_TYPE"),
    ] {
        p.write("app/main.vast", &checked_replace(app, from, to));
        expect_code(&p.check_manifest(MANIFEST), code);
    }
}

#[test]
fn forged_fields_and_stale_revisions_cannot_select_a_different_monad() {
    let p = Scratch::empty("monad wire");
    let app = format!("{C2}\nfn main() -> Int {{ 0 }}");
    p.write_package("app", &app, "");
    let mut wire = p.captured(MANIFEST, 10);
    let evidence = kernel(&wire, "function-revision");
    assert_eq!(evidence["ok"], true, "{evidence}");
    for (field, path) in [
        ("category", "T"),
        ("functor", "Trivial"),
        ("unit", "T"),
        ("multiplication", "identity"),
    ] {
        let mut bad = wire.clone();
        decl(&mut bad, "B")["monad"][field]["path"] = json!([path]);
        assert_wire_rejected(&kernel(bad, "emit"), "E_MONAD");
    }
    for (field, name) in [
        ("graph", "C"),
        ("functor", "T"),
        ("transformation", "Twist"),
    ] {
        let mut both = wire.clone();
        let other = decl(&mut both, name)[field].clone();
        decl(&mut both, "B")[field] = other;
        assert_wire_rejected(&kernel(both, "emit"), "E_PROTOCOL");
    }
    decl(&mut wire, "B")["monad"]["associative"] = json!(true);
    assert_wire_rejected(&kernel(wire, "emit"), "E_PROTOCOL");
    p.write(
        "app/main.vast",
        &checked_replace(&app, "T, Twist, Twist)", "T, Trivial, Trivial)"),
    );
    let mut other = p.captured(MANIFEST, 10);
    let accepted = kernel(&other, "check");
    assert_eq!(accepted["ok"], true, "{accepted}");
    other["expected_function_revision"] = evidence["function_revision"].clone();
    assert_wire_rejected(&kernel(other, "emit"), "E_FUNCTION_REVISION");
}

#[test]
fn closure_kleisli_operations_bind_to_the_selected_revision() {
    let p = Scratch::empty("public closure Kleisli");
    common::prepare_stdlib_package();
    let manifest = common::root().join("examples/packages/finite-kleisli/Vastitas.toml");
    let manifest = manifest.to_str().unwrap();
    assert_eq!(p.check_build_and_run(manifest), common::exits(0));
    let mut wire = p.captured(manifest, 10);
    let response = kernel(&wire, "function-revision");
    assert_eq!(response["ok"], true, "{response}");
    let revision = &response["function_revision"];
    for (function, objects) in [
        ("unit", vec!["lo"]),
        ("bind", vec!["lo", "lo", "hi"]),
        ("compose", vec!["lo", "lo", "hi"]),
        ("lift", vec!["hi", "hi"]),
    ] {
        let symbols: Vec<_> = revision["pure"]["symbols"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|s| {
                s["id"]["name"] == function && s["specialization"]["finite_indices"].is_array()
            })
            .collect();
        assert_eq!(symbols.len(), 1, "{symbols:?}");
        assert_eq!(symbols[0]["id"]["package"]["name"], "vastitas_monad");
        assert_eq!(symbols[0]["id"]["module"], json!(["kleisli"]));
        let indices = symbols[0]["specialization"]["finite_indices"]
            .as_array()
            .unwrap();
        assert_eq!(indices[0]["monad"]["name"], "M");
        assert_eq!(
            indices[0]["monad"]["package"]["name"],
            "finite_kleisli_example"
        );
        assert_eq!(indices.len(), objects.len() + 1);
        for (index, object) in indices[1..].iter().zip(objects) {
            assert_eq!(index["object"], object);
            assert_eq!(index["category"]["name"], "C");
        }
    }
    wire["expected_function_revision"] = revision.clone();
    assert_eq!(kernel(&wire, "check")["function_revision_matched"], true);
    let bind = wire["expected_function_revision"]["pure"]["symbols"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|s| s["id"]["name"] == "bind" && s["specialization"]["finite_indices"].is_array())
        .unwrap();
    bind["specialization"]["finite_indices"][0]["monad"]["name"] = json!("Closure");
    assert_wire_rejected(&kernel(&wire, "emit"), "E_FUNCTION_REVISION");
}

#[test]
fn only_category_exports_the_schema_and_only_kleisli_exports_the_operations() {
    let source = include_str!("../examples/packages/finite-kleisli/src/main.vast");
    let p = Scratch::empty("Kleisli namespace");
    p.copy_stdlib(&common::STDLIB_PACKAGES, &[]);
    p.copy_sources(&common::root().join("monad"), "monad", &[]);
    p.write_package(
        "app",
        source,
        "std={path='../stdlib'}\nmonad={path='../monad'}",
    );
    common::success(&p.check_manifest(MANIFEST));
    for name in ["unit", "bind", "compose", "lift"] {
        for prefix in ["monad", "std::monad", "std::monad::kleisli"] {
            let misplaced = checked_replace(
                source,
                &format!("monad::kleisli::{name}::"),
                &format!("{prefix}::{name}::"),
            );
            p.write("app/main.vast", &misplaced);
            expect_code(&p.check_manifest(MANIFEST), "E_NAME");
        }
    }
    for (path, code) in [
        ("monad::Monad", "E_NAME"),
        ("monad::kleisli::Monad", "E_VISIBILITY"),
        ("std::monad::Monad", "E_NAME"),
    ] {
        let misplaced =
            checked_replace(source, "use std::category::Monad;", &format!("use {path};"));
        p.write("app/main.vast", &misplaced);
        expect_code(&p.check_manifest(MANIFEST), code);
    }
    p.write_package("app", EXAMPLE, "std={path='../stdlib'}");
    let std_only = p.captured(MANIFEST, 10);
    let pkgs = std_only["packages"].as_array().unwrap();
    let names: Vec<_> = pkgs
        .iter()
        .map(|pkg| pkg["name"].as_str().unwrap())
        .collect();
    assert!(names.contains(&"vastitas_category"));
    assert!(!names.contains(&"vastitas_monad"));
    let accepted = kernel(&std_only, "check");
    assert_eq!(accepted["ok"], true, "{accepted}");
    p.write("app/main.vast", source);
    expect_code(&p.check_manifest(MANIFEST), "E_NAME");
}

#[test]
fn kleisli_specializations_distinguish_two_monads_on_one_functor() {
    let p = Scratch::empty("two selected Kleisli structures");
    p.copy_stdlib(&common::STDLIB_PACKAGES, &[]);
    p.copy_sources(&common::root().join("monad"), "monad", &[]);
    let declarations = checked_replace(
        C2,
        "indexed schema Structure = finite_monad;",
        "use std::category::Monad as Structure;",
    );
    let program = format!(
        "{declarations}
indexed instance KA : monad::kleisli::Kleisli = finite_kleisli(A);
indexed instance KB : monad::kleisli::Kleisli = finite_kleisli(B);
indexed instance TA : monad::kleisli::KleisliTriple = finite_kleisli_triple(A);
indexed instance TB : monad::kleisli::KleisliTriple = finite_kleisli_triple(B);
fn main() -> Int {{
    let e = C::e;
    let a = monad::kleisli::bind::<KA,Obj::o,Obj::o,Obj::o>(e,e);
    let b = monad::kleisli::bind::<TB,Obj::o,Obj::o,Obj::o>(e,e);
    let ae = monad::kleisli::extend::<TA,Obj::o,Obj::o>(e);
    let be = monad::kleisli::extend::<KB,Obj::o,Obj::o>(e);
    if a == e && b == C::s && ae == e && be == C::s &&
       monad::kleisli::extend::<TB,Obj::o,Obj::o>(C::s) == e &&
       monad::kleisli::unit::<TA,Obj::o>() == e &&
       monad::kleisli::unit::<KB,Obj::o>() == C::s {{ 0 }} else {{ 1 }}
}}"
    );
    p.write_package(
        "app",
        &program,
        "std={path='../stdlib'}\nmonad={path='../monad'}",
    );
    assert_eq!(p.check_build_and_run(MANIFEST), common::exits(0));
    let response = kernel(p.captured(MANIFEST, 10), "function-revision");
    assert_eq!(response["ok"], true, "{response}");
    for name in ["bind", "unit", "extend"] {
        let mut owners: Vec<_> = response["function_revision"]["pure"]["symbols"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|s| s["id"]["name"] == name)
            .filter_map(|s| s["specialization"]["finite_indices"][0]["monad"]["name"].as_str())
            .collect();
        owners.sort_unstable();
        assert_eq!(owners, ["A", "B"]);
    }
    #[cfg(feature = "llvm-native")]
    {
        common::success(
            &p.command("build", MANIFEST)
                .args(["--llvm-preview", "-o", "two-monads"])
                .output()
                .unwrap(),
        );
        let status = std::process::Command::new(p.0.join("two-monads"))
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(0));
    }
}

#[test]
fn concrete_kleisli_hom_pulls_back_the_target_along_the_selected_object_map() {
    let example = local_example();
    let (declarations, _) = example.split_once("pub fn unitAt").unwrap();
    let source = format!(
        "{declarations}
indexed schema KShape = finite_kleisli(Monad);
indexed schema TShape = finite_kleisli_triple(Monad);
indexed instance K : KShape = finite_kleisli(M);
indexed instance V : TShape = finite_kleisli_triple(M);
indexed instance Action : Functor = finite_functor(C, C, Closure::objects, K::arrows);
indexed instance ViewUnit : NatTrans = finite_nat_trans(Id, Closure, K::unit);
indexed instance ViewMu : NatTrans = finite_nat_trans(Twice, Closure, V::multiplication);
fn underlying(f: Hom<K, K::objects::lo, K::objects::lo>) -> Hom<C, Obj::lo, Obj::hi> {{ f }}
fn recover(f: Hom<C, Obj::lo, Obj::hi>) -> Hom<K, Obj::lo, Obj::lo> {{ f }}
fn mapped(f: Hom<K::category, Obj::lo, Obj::hi>)
    -> Hom<V::category, K::T<Obj::lo>, V::T<Obj::hi>> {{ finite::lookup::<K::arrows>(f) }}
fn main() -> Int {{
    let other: Hom<K, Obj::hi, Obj::lo> = C::rightId;
    if underlying(recover(C::up)) == C::up && other == C::rightId && mapped(C::up) == C::rightId &&
       finite::lookup::<Action::arrows>(Arr::up) == Arr::rightId &&
       finite::lookup::<K::unit>(Obj::lo) == finite::lookup::<ViewUnit::components>(Obj::lo) &&
       finite::lookup::<V::unit>(Obj::lo) == Arr::up &&
       finite::lookup::<K::multiplication>(Obj::lo) == finite::lookup::<ViewMu::components>(Obj::lo) &&
       finite::lookup::<V::multiplication>(Obj::lo) == Arr::rightId {{ 42 }} else {{ 1 }}
}}"
    );
    let p = Scratch::empty("Kleisli hom endpoints");
    p.write_package("app", &source, "");
    assert_eq!(p.check_build_and_run(MANIFEST), common::exits(42));
    for (from, to) in [
        ("recover(C::up)", "recover(C::leftId)"),
        ("Obj::lo> = C::rightId", "Obj::lo> = C::up"),
        ("Hom<K, Obj::lo, Obj::lo>", "Hom<V, Obj::lo, Obj::lo>"),
    ] {
        p.write("app/main.vast", &checked_replace(&source, from, to));
        expect_code(&p.check_manifest(MANIFEST), "E_TYPE");
    }
}

#[test]
fn derived_view_declarations_require_the_exact_kind_schema_and_direct_monad() {
    let source = format!(
        "{C2}
indexed schema Other = finite_monad;
indexed instance Foreign : Other = finite_monad(C, T, Trivial, Trivial);
indexed schema KShape = finite_kleisli(Structure);
indexed schema TShape = finite_kleisli_triple(Structure);
indexed instance K : KShape = finite_kleisli(A);
indexed instance V : TShape = finite_kleisli_triple(A);
fn main() -> Int {{ 0 }}"
    );
    let p = Scratch::empty("Kleisli view declaration validation");
    p.write_package("app", &source, "");
    common::success(&p.check_manifest(MANIFEST));
    let wire = p.captured(MANIFEST, 10);
    for (from, to) in [
        ("finite_kleisli(Structure)", "finite_kleisli(Map)"),
        (
            "finite_kleisli_triple(Structure)",
            "finite_kleisli_triple(A)",
        ),
        ("K : KShape", "K : TShape"),
        ("V : TShape", "V : KShape"),
        ("finite_kleisli(A)", "finite_kleisli(Foreign)"),
        ("finite_kleisli_triple(A)", "finite_kleisli_triple(Foreign)"),
        ("finite_kleisli(A)", "finite_kleisli(V)"),
        ("finite_kleisli_triple(A)", "finite_kleisli_triple(K)"),
    ] {
        p.write("app/main.vast", &checked_replace(&source, from, to));
        expect_code(&p.check_manifest(MANIFEST), "E_KLEISLI");
    }

    // Send the unmodified physical source to the public kernel along with a forged declaration.
    for (name, slot, replacement) in [
        ("KShape", "/monad_schema", "Cat"),
        ("TShape", "/monad_schema", "KShape"),
        ("K", "/schema", "TShape"),
        ("V", "/schema", "KShape"),
        ("K", "/kleisli/monad", "Foreign"),
        ("V", "/kleisli_triple/monad", "K"),
    ] {
        let mut forged = wire.clone();
        let path = decl(&mut forged, name).pointer_mut(slot).unwrap();
        let span = path["span"].clone();
        path["path"] = json!([replacement]);
        let rejected = kernel(forged, "emit");
        assert_wire_rejected(&rejected, "E_KLEISLI");
        assert_eq!(rejected["diagnostics"][0]["span"], span, "{name} {slot}");
    }
    let mut mixed = wire.clone();
    let triple = decl(&mut mixed, "V")["kleisli_triple"].clone();
    decl(&mut mixed, "K")["kleisli_triple"] = triple;
    assert_wire_rejected(&kernel(mixed, "emit"), "E_PROTOCOL");
    let mut missing = wire;
    decl(&mut missing, "KShape")
        .as_object_mut()
        .unwrap()
        .remove("monad_schema");
    assert_wire_rejected(&kernel(missing, "emit"), "E_PROTOCOL");
}

#[test]
fn distinct_views_of_one_monad_share_specialization_and_reject_stale_public_revision() {
    let source = format!(
        "{C2}
indexed schema KShape = finite_kleisli(Structure);
indexed instance K1 : KShape = finite_kleisli(A);
indexed instance K2 : KShape = finite_kleisli(A);
fn selected<M: Structure, X: Obj<M::category>>() -> Hom<M::category, X, M::T<X>> {{
    finite::lookup::<M::unit>(X)
}}
fn main() -> Int {{ if selected::<K1,Obj::o>() == C::e {{ 42 }} else {{ 1 }} }}"
    );
    let p = Scratch::empty("same Monad distinct view revisions");
    p.write_package("app", &source, "");
    let first = kernel(p.captured(MANIFEST, 10), "function-revision");
    assert_eq!(first["ok"], true, "{first}");
    let second_source = checked_replace(&source, "::<K1,", "::<K2,");
    p.write("app/main.vast", &second_source);
    let mut wire = p.captured(MANIFEST, 10);
    let second = kernel(&wire, "function-revision");
    assert_eq!(second["ok"], true, "{second}");
    let changed_source = checked_replace(
        &second_source,
        "K2 : KShape = finite_kleisli(A)",
        "K2 : KShape = finite_kleisli(B)",
    );
    p.write("app/main.vast", &changed_source);
    let mut changed_wire = p.captured(MANIFEST, 10);
    let changed = kernel(&changed_wire, "function-revision");
    assert_eq!(changed["ok"], true, "{changed}");
    let specializations = [&first, &second, &changed].map(|accepted| {
        let matches: Vec<_> = accepted["function_revision"]["pure"]["symbols"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|s| {
                s["id"]["name"] == "selected" && s["specialization"]["finite_indices"].is_array()
            })
            .collect();
        assert_eq!(matches.len(), 1);
        &matches[0]["specialization"]
    });
    assert_eq!(specializations[0], specializations[1]);
    for (specialization, monad) in specializations.into_iter().zip(["A", "A", "B"]) {
        assert_eq!(specialization["finite_indices"][0]["monad"]["name"], monad);
    }
    assert_ne!(first["function_revision"], second["function_revision"]);
    wire["expected_function_revision"] = second["function_revision"].clone();
    assert_eq!(kernel(&wire, "check")["function_revision_matched"], true);
    let mut forged = wire.clone();
    let operand = &mut decl(&mut forged, "K2")["kleisli"]["monad"];
    let span = operand["span"].clone();
    operand["path"] = json!(["B"]);
    let rejected = kernel(forged, "emit");
    assert_wire_rejected(&rejected, "E_FINITE_SOURCE");
    assert_eq!(rejected["diagnostics"][0]["span"], span);
    wire["expected_function_revision"] = first["function_revision"].clone();
    assert_wire_rejected(&kernel(wire, "emit"), "E_FUNCTION_REVISION");
    changed_wire["expected_function_revision"] = second["function_revision"].clone();
    for mode in ["check", "emit"] {
        assert_wire_rejected(&kernel(&changed_wire, mode), "E_FUNCTION_REVISION");
    }
    changed_wire["expected_function_revision"] = changed["function_revision"].clone();
    assert_eq!(
        kernel(changed_wire, "emit")["function_revision_matched"],
        true
    );
}

#[test]
fn kleisli_bind_and_compose_preserve_noncommuting_s3_order() {
    let permutations = include_str!("../examples/packages/finite-category/src/main.vast");
    let (graph, _) = permutations.split_once("fn composeArrow").unwrap();
    // The digits encode the images of 0, 1, 2. Compute each expected tag
    // independently of both the fixture's 36 rows and the two library bodies.
    let product = |after: [usize; 3], before: [usize; 3]| {
        let [x, y, z] = before.map(|i| after[i]);
        format!("p{x}{y}{z}")
    };
    let f = [0, 2, 1];
    let g = [1, 0, 2];
    let gf = product(g, f);
    let fg = product(f, g);
    assert_ne!(gf, fg);
    let program = format!(
        "{graph}
use std::category::Functor;
use std::category::NatTrans;
use std::category::Monad;
indexed table sameObject(Obj) -> Obj {{ (o) => o; }}
indexed table sameArrow(Arr) -> Arr {{
    (p012) => p012; (p021) => p021; (p102) => p102;
    (p120) => p120; (p201) => p201; (p210) => p210;
}}
indexed instance Identity : Functor = finite_functor(S3, S3, sameObject, sameArrow);
indexed instance Trivial : NatTrans = finite_nat_trans(Identity, Identity, ids);
indexed instance M : Monad = finite_monad(S3, Identity, Trivial, Trivial);
fn firstArrow() -> Hom<S3,Obj::o,Obj::o> {{ S3::p021 }}
fn secondArrow() -> Hom<S3,Obj::o,Obj::o> {{ S3::p102 }}
fn firstFactory() -> Fn<(),Hom<S3,Obj::o,Obj::o>> {{ firstArrow }}
fn secondFactory() -> Fn<(),Hom<S3,Obj::o,Obj::o>> {{ secondArrow }}
fn main() -> Int {{
    let f = S3::p021;
    let g = S3::p102;
    let seqFG = monad::kleisli::bind::<M,Obj::o,Obj::o,Obj::o>(f,g);
    let seqGF = monad::kleisli::bind::<M,Obj::o,Obj::o,Obj::o>(g,f);
    let afterFG = monad::kleisli::compose::<M,Obj::o,Obj::o,Obj::o>(f,g);
    let afterGF = monad::kleisli::compose::<M,Obj::o,Obj::o,Obj::o>(g,f);
    let direct = monad::kleisli::bind::<M,Obj::o,Obj::o,Obj::o>(f,secondArrow);
    let left = monad::kleisli::compose::<M,Obj::o,Obj::o,Obj::o>(firstArrow,g);
    let right = monad::kleisli::compose::<M,Obj::o,Obj::o,Obj::o>(f,secondArrow);
    let both = monad::kleisli::compose::<M,Obj::o,Obj::o,Obj::o>(secondFactory(),firstFactory());
    if seqFG == S3::{gf} && seqGF == S3::{fg} && afterFG == S3::{fg} && afterGF == S3::{gf}
        && direct == seqFG && left == afterFG && right == afterFG && both == afterGF {{ 42 }} else {{ 1 }}
}}"
    );
    let p = Scratch::empty("noncommuting Kleisli arrows");
    p.copy_stdlib(&common::STDLIB_PACKAGES, &[]);
    p.copy_sources(&common::root().join("monad"), "monad", &[]);
    p.write_package(
        "app",
        &program,
        "std={path='../stdlib'}\nmonad={path='../monad'}",
    );
    assert_eq!(p.check_build_and_run(MANIFEST), common::exits(42));
    let preview = p
        .command("check", MANIFEST)
        .args([
            "--llvm-preview",
            "--target-triple",
            "aarch64-apple-darwin",
            "--data-layout",
            "e-m:o-i64:64-n32:64-S128",
        ])
        .output()
        .unwrap();
    common::success(&preview);
    let ll = std::str::from_utf8(&preview.stdout).unwrap();
    assert!(ll.contains("switch i32"));
    let checked = kernel(p.captured(MANIFEST, 10), "function-revision");
    let pure = &checked["function_revision"]["pure"];
    let sites = pure["finite_forwards"].as_array().unwrap();
    assert_eq!(sites.len(), 4);
    // The linker preserves Core order for these seven reachable definitions.
    let mut linked: Vec<_> = pure["symbols"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|s| {
            let name = s["id"]["name"].as_str()?;
            match (s["id"]["package"]["name"].as_str()?, name) {
                (
                    "app",
                    "main" | "firstArrow" | "secondArrow" | "firstFactory" | "secondFactory",
                )
                | ("vastitas_monad", "bind" | "compose") => Some((s["core"].as_u64()?, name)),
                _ => None,
            }
        })
        .collect();
    linked.sort_unstable();
    assert_eq!(linked.len(), 7);
    let id = |name| linked.iter().position(|(_, n)| *n == name).unwrap();
    let (_, main) = ll
        .split_once(&format!("define internal i32 @f{} ( ) {{\n", id("main")))
        .unwrap();
    let calls: Vec<usize> = main
        .split_once("\n}")
        .unwrap()
        .0
        .lines()
        .filter_map(|line| line.split_once(" @f"))
        .map(|(_, callee)| callee.split_once(" (").unwrap().0.parse().unwrap())
        .collect();
    assert!(
        calls.ends_with(
            &[
                "secondFactory",
                "firstFactory",
                "secondArrow",
                "firstArrow",
                "compose"
            ]
            .map(id)
        ),
        "{calls:?} {linked:?}"
    );
    #[cfg(feature = "llvm-native")]
    {
        common::success(
            &p.command("build", MANIFEST)
                .args(["--llvm-preview", "-o", "s3"])
                .output()
                .unwrap(),
        );
        let status = std::process::Command::new(p.0.join("s3")).status().unwrap();
        assert_eq!(status.code(), Some(42));
    }
}

#[test]
fn direct_function_producing_a_represented_arrow_precedes_bind_and_compose_in_llvm() {
    let (declarations, _) = EXAMPLE.split_once("pub fn unitAt").unwrap();
    let source = format!(
        "{declarations}
fn continuation() -> Hom<C, Obj::lo, Obj::hi> {{ C::up }}
fn main() -> Int {{
    let p = C::up;
    let b = monad::kleisli::bind::<M,Obj::lo,Obj::lo,Obj::hi>(p, continuation());
    let c = monad::kleisli::compose::<M,Obj::lo,Obj::lo,Obj::hi>(continuation(), p);
    if b == C::up && c == C::up {{ 42 }} else {{ 1 }}
}}"
    );
    let p = Scratch::empty("direct function producing a Kleisli arrow");
    p.copy_stdlib(&common::STDLIB_PACKAGES, &[]);
    p.copy_sources(&common::root().join("monad"), "monad", &[]);
    p.write_package(
        "app",
        &source,
        "std={path='../stdlib'}\nmonad={path='../monad'}",
    );
    let checked = p
        .command("check", MANIFEST)
        .arg("--print-function-revision")
        .output()
        .unwrap();
    common::success(&checked);
    let revision: Value = serde_json::from_slice(&checked.stdout).unwrap();

    // The package linker numbers retained definitions in their original Core order.
    let mut selected = Vec::new();
    for symbol in revision["pure"]["symbols"].as_array().unwrap() {
        let id = &symbol["id"];
        let name = id["name"].as_str().unwrap();
        match (id["package"]["name"].as_str().unwrap(), name) {
            ("app", "main" | "continuation") => assert_eq!(id["module"], json!([])),
            ("vastitas_monad", "bind" | "compose") => {
                assert_eq!(id["module"], json!(["kleisli"]));
                assert_eq!(
                    symbol["specialization"]["finite_indices"][0]["monad"]["name"],
                    "M"
                );
            }
            _ => continue,
        }
        selected.push((symbol["core"].as_u64().unwrap(), name));
    }
    selected.sort_unstable();
    assert_eq!(selected.len(), 4);
    let linked = |name| {
        format!(
            "f{}",
            selected.iter().position(|(_, n)| *n == name).unwrap()
        )
    };
    let preview = p
        .command("check", MANIFEST)
        .args([
            "--llvm-preview",
            "--target-triple",
            "aarch64-apple-darwin",
            "--data-layout",
            "e-m:o-i64:64-n32:64-S128",
        ])
        .output()
        .unwrap();
    common::success(&preview);
    let ll = std::str::from_utf8(&preview.stdout).unwrap();
    assert_eq!(ll.matches("define internal i32 @f").count(), selected.len());
    let main = linked("main");
    assert!(ll.contains(&format!("%result = call i32 @{main} ( )")));
    let (_, body) = ll
        .split_once(&format!("define internal i32 @{main} ( ) {{\n"))
        .unwrap();
    let (body, _) = body.split_once("\n}").unwrap();
    let calls: Vec<_> = body
        .lines()
        .filter(|line| line.contains("call "))
        .map(|line| {
            let (result, call) = line.trim().split_once(" = call i32 @").unwrap();
            let (callee, arguments) = call.split_once(" (").unwrap();
            let args: Vec<_> = arguments
                .strip_suffix(')')
                .unwrap()
                .trim()
                .split(',')
                .filter(|operand| !operand.is_empty())
                .map(|operand| operand.trim().strip_prefix("i32 ").unwrap())
                .collect();
            (result, callee, args)
        })
        .collect();
    let [first, bind, second, compose] = calls.as_slice() else {
        panic!("unexpected LLVM calls in main: {calls:?}");
    };
    assert_eq!(
        [first.1, bind.1, second.1, compose.1],
        [
            linked("continuation"),
            linked("bind"),
            linked("continuation"),
            linked("compose")
        ]
    );
    assert!(first.2.is_empty() && second.2.is_empty());
    let [p_ref, after_p] = bind.2.as_slice() else {
        panic!("unexpected bind operands: {bind:?}");
    };
    assert_eq!(*after_p, first.0);
    assert_eq!(compose.2, [second.0, *p_ref]);
    #[cfg(feature = "llvm-native")]
    {
        common::success(
            &p.command("build", MANIFEST)
                .args(["--llvm-preview", "-o", "direct"])
                .output()
                .unwrap(),
        );
        let status = std::process::Command::new(p.0.join("direct"))
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(42));
    }
}

#[test]
fn finite_callable_methods_are_audited_before_selection() {
    let p = Scratch::empty("unused finite forwarding methods");
    p.copy_stdlib(&common::STDLIB_PACKAGES, &[]);
    p.copy_sources(&common::root().join("monad"), "monad", &[]);
    let module = include_str!("../monad/src/kleisli/mod.vast");
    let path = "monad/src/kleisli/mod.vast";
    let source = "fn main() -> Int { 42 }";
    p.write_package("app", source, "monad={path='../monad'}");
    common::success(&p.check_manifest(MANIFEST));
    let mut wire = p.captured(MANIFEST, 10);
    let both = wire["packages"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .flat_map(|package| package["modules"].as_array_mut().unwrap())
        .flat_map(|module| module["functions"].as_array_mut().unwrap())
        .find(|f| {
            f["name"] == "compose"
                && f["params"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|p| p["ty"]["return_type"].is_object())
        })
        .unwrap();
    let args = both["body"]["result"]["args"].as_array_mut().unwrap();
    assert_eq!(args.len(), 2);
    args.swap(0, 1);
    assert_wire_rejected(&kernel(wire, "check"), "E_TYPE");
    for (from, to, code) in [
        ("(g(), f())", "(g(), g())", "E_TYPE"),
        ("(g(), f())", "(g, f())", "E_TYPE"),
        (
            "compose::<M, X, Y, Z>(g(), f())",
            "compose::<M, X, Z, Y>(g(), f())",
            "E_TYPE",
        ),
        (
            "compose::<M, X, Y, Z>(g(), f())",
            "bind::<M, X, Y, Z>(g(), f())",
            "E_OWNER",
        ),
        (
            "k: Fn<(), Hom<M::category, X, M::T<Y>>>",
            "k: Fn<Unit, Hom<M::category, X, M::T<Y>>>",
            "E_TYPE",
        ),
    ] {
        p.write(path, &checked_replace(module, from, to));
        expect_code(&p.check_manifest(MANIFEST), code);
    }
    // Source order does not grant ownership to the first declared method.
    let (head, methods) = module.split_once("pub fn bind").unwrap();
    let (base, methods) = methods.split_once("pub fn bind").unwrap();
    let (forward, tail) = methods.split_once("pub fn compose").unwrap();
    p.write(
        path,
        &format!("{head}pub fn bind{forward}pub fn bind{base}pub fn compose{tail}"),
    );
    common::success(&p.check_manifest(MANIFEST));
    p.write(path, &format!("{module}\npub fn bind{forward}"));
    expect_code(&p.check_manifest(MANIFEST), "E_DUPLICATE");
}

#[test]
fn kleisli_forwarding_requires_declared_positions_and_exact_producer_fibers() {
    let p = Scratch::empty("real closure bound to a producer");
    p.copy_stdlib(&common::STDLIB_PACKAGES, &[]);
    p.copy_sources(&common::root().join("monad"), "monad", &[]);
    let (decls, _) = EXAMPLE.split_once("pub fn unitAt").unwrap();
    let source = format!(
        "{decls}
fn upArrow() -> Hom<C,Obj::lo,Obj::hi> {{ C::up }}
fn otherArrow() -> Hom<C,Obj::hi,Obj::hi> {{ C::rightId }}
fn withArg(x: Hom<C,Obj::lo,Obj::hi>) -> Hom<C,Obj::lo,Obj::hi> {{ x }}
fn main() -> Int {{
    let b = monad::kleisli::bind::<M,Obj::lo,Obj::lo,Obj::hi>(C::up,upArrow);
    if b == C::up {{ 42 }} else {{ 1 }}
}}"
    );
    p.write_package(
        "app",
        &source,
        "std={path='../stdlib'}\nmonad={path='../monad'}",
    );
    assert_eq!(p.check_build_and_run(MANIFEST), common::exits(42));
    for args in ["(C::up,otherArrow)", "(C::up,withArg)", "(upArrow,C::up)"] {
        p.write(
            "app/main.vast",
            &checked_replace(&source, "(C::up,upArrow)", args),
        );
        expect_code(&p.check_manifest(MANIFEST), "E_TYPE");
    }
}
