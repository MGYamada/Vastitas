//! Physical method bodies and the revision that installs them.
mod common;
use common::{CURRENT_PROTOCOL, Scratch, assert_wire_rejected, kernel};
use serde_json::{Value, json};

const SCALAR: &str = r#"
fn choose(x, y) domain((Int, Int));
fn choose(x: Number, y: Number) -> Int { 0017 }
fn choose(x: Bool, y: Bool) -> Int { 301 }
contribution winner : choose {
    fn choose(x: Int, y: Int) -> Int {
        let times: Fn<(Int,), Int>= fn(t: Int) -> Int { t * 2 };
        let a = (((std::operator::add)))(x, y,);
        let p = (fn(t: Int) -> Int { -t })(001);
        let u: Unit = {};
        if !((x == y) || false) { { times(a) + p } }
        else if x <= y && true { x } else { y }
    }
}
contribution spare : choose {
    fn choose(x: Int, y: Int) -> Int { x + y * 2 }
}
assemble choose { apply winner; }
fn main() -> Int { choose(40, 2) }
"#;

fn rejected(wire: &Value) {
    for action in ["check", "emit"] {
        assert_wire_rejected(&kernel(wire, action), "E_ASSEMBLY");
    }
}

#[test]
fn edits_bind_the_selected_fallback_and_unapplied_method_bodies() {
    let s = Scratch::empty("method body source");
    s.write_package("app", SCALAR, "");
    assert_eq!(
        s.check_build_and_run("app/Vastitas.toml"),
        common::exits(83)
    );
    let wire = s.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    for (before, after) in [
        ("0017", "0018"),
        ("301", "302"),
        ("(x, y,)", "(y, x,)"),
        ("{ -t }", "{  t }"),
        ("x <= y", "x >= y"),
        ("{ { times(a) + p } }", "{ { times(a) - p } }"),
        ("001)", "002)"),
        ("Unit = {}", "Unit = ()"),
        ("Int) -> Int { t * 2 }", "Int) -> Int { t + 2 }"),
        ("x + y * 2", "x - y * 2"),
    ] {
        assert_eq!(SCALAR.matches(before).count(), 1);
        assert_eq!(before.len(), after.len());
        let mut bad = wire.clone();
        bad["root_source"]["text"] = json!(SCALAR.replace(before, after));
        rejected(&bad);
    }

    // Same tokens, same leaf and enclosing spans, different association.
    let mut bad = wire.clone();
    let result =
        &mut bad["packages"][0]["modules"][0]["contributions"][1]["methods"][0]["body"]["result"];
    let (x, y, two) = (
        result["left"].clone(),
        result["right"]["left"].clone(),
        result["right"]["right"].clone(),
    );
    let mut span = x["span"].clone();
    span["end"] = y["span"]["end"].clone();
    result["op"] = json!("*");
    result["left"] = json!({"kind":"binary","op":"+","left":x,"right":y,"span":span});
    result["right"] = two;
    rejected(&bad);

    let mut bad = wire.clone();
    bad["packages"][0]["modules"][0]["methods"]
        .as_array_mut()
        .unwrap()
        .swap(0, 1);
    rejected(&bad);
    let mut bad = wire;
    bad["packages"][0]["modules"][0]["methods"]
        .as_array_mut()
        .unwrap()
        .remove(1);
    rejected(&bad);
}

#[test]
fn a_method_token_error_reports_the_dependency_file_position() {
    let mut wire: Value =
        serde_json::from_str(include_str!("fixtures/edit-recipients.json")).unwrap();
    let file = wire["root_source"]["files"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|file| file["path"].as_str().unwrap().ends_with("/addon/main.vast"))
        .unwrap();
    let text = file["text"].as_str().unwrap();
    let index = text.find("x + y").unwrap() + 2;
    let before = &text[..index];
    let start = file["offset"].as_u64().unwrap() + index as u64;
    let span = json!({
        "start": start, "end": start + 1, "line": before.lines().count(),
        "column": before.rsplit('\n').next().unwrap().chars().count() + 1
    });
    file["text"] = json!(text.replacen("x + y", "x - y", 1));
    for action in ["check", "emit"] {
        let response = kernel(&wire, action);
        assert_wire_rejected(&response, "E_ASSEMBLY");
        assert_eq!(response["diagnostics"][0]["span"], span, "{response}");
    }
}

#[test]
fn contributed_method_reads_indexed_pack_unpack_and_nominal_types() {
    let s = Scratch::empty("indexed edit body");
    s.write_package(
        "app",
        r#"
mod geo;
fn inspect(n) domain((Nat));
fn inspect(n: Number) -> Int { 0 }
contribution geometry : inspect {
  fn inspect(n: Nat) -> Int {
    let X: Object<geo::Scheme, geo::QQ> = geo::affine(n);
    let packed = pack geo::Pointed<geo::Scheme, geo::QQ,> {
      witness: X, fields: [geo::origin(X),], };
    unpack packed as { witness: Y, fields: [p,], };
    let q: geo::Point<Y, geo::Base>= geo::apply(geo::identity(Y), p);
    int(geo::dim(Y))
  }
}
assemble inspect { apply geometry; }
fn main() -> Int { let n: Nat = 42; inspect(n) }
"#,
        "",
    );
    s.write(
        "app/geo.vast",
        include_str!("../examples/packages/geometry/indexed/geo.vast"),
    );
    assert_eq!(
        s.check_build_and_run("app/Vastitas.toml"),
        common::exits(42)
    );
    let mut wire = s.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    let physical = wire["root_source"]["text"].as_str().unwrap();
    wire["root_source"]["text"] = json!(physical.replace("int(geo::dim(Y))", "int(geo::dim(X))"));
    rejected(&wire);
}

#[test]
fn contributed_finite_calls_keep_index_paths_and_lookup_operands() {
    let fixture = include_str!("../examples/packages/finite-kleisli/src/main.vast");
    let (category, _) = fixture.split_once("fn mappedUp").unwrap();
    let source = format!(
        "{category}{}",
        r#"
fn probe(flag) domain((Bool));
fn probe(flag: Any) -> Int { 0 }
contribution checked : probe {
  fn probe(flag: Bool) -> Int {
    let f: Hom<M::category, M::T<Obj::lo>, M::T<Obj::hi>> = (finite::lookup::<M::arrows>(C::up));
    let u = monad::kleisli::unit::<Triple, Obj::lo,>();
    let g = monad::kleisli::bind::<K, Obj::lo, Obj::lo, Obj::hi,>(u, C::up,);
    if f == C::rightId && g == C::up { 42 } else { 1 }
  }
}
assemble probe { apply checked; }
fn main() -> Int { probe(true) }
"#
    );
    let s = Scratch::empty("finite method source");
    s.copy_stdlib(&common::STDLIB_PACKAGES, &[]);
    s.copy_sources(&common::root().join("monad"), "monad", &[]);
    s.write_package(
        "app",
        &source,
        "std={path='../stdlib'}\nmonad={path='../monad'}",
    );
    assert_eq!(
        s.check_build_and_run("app/Vastitas.toml"),
        common::exits(42)
    );
    let wire = s.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    for (original, changed) in [
        ("M::T<Obj::hi>", "M::T<Obj::lo>"),
        ("M::arrows>(C::up)", "M::arrows>(C::lo)"),
        ("Obj::hi,>(u, C::up,)", "Obj::lo,>(u, C::up,)"),
    ] {
        let mut bad = wire.clone();
        let text = source.replace(original, changed);
        assert_ne!(text, source);
        assert_eq!(text.len(), source.len());
        bad["root_source"]["text"] = json!(text);
        rejected(&bad);
    }
}

#[test]
fn a_defining_method_checks_legacy_pack_pairs_and_static_function_values() {
    let s = Scratch::empty("defining body syntax");
    s.write_package(
        "app",
        r#"
mod ops { pub fn twice(t: Int) -> Int { t + t } }
fn inspect(flag) domain((Bool));
fn inspect(flag: Bool) -> Int {
    let X: Scheme = Affine(QQ, 21);
    let p: Point<X, Base(QQ)> = origin(X);
    let f: Morphism<X, X> = id(X);
    let parcel: Pointed<Scheme, QQ>= pack { scheme: X, point: apply(f, p), };
    unpack parcel as { scheme: Y, point: q, };
    let cb: Fn<Int, Int> = ops::twice;
    let pairValue: Pair<Int> = pair(cb(int(dim(Y))), 0);
    pair_first(pairValue)
}
assemble inspect {}
fn main() -> Int { inspect(true) }
"#,
        "",
    );
    assert_eq!(
        s.check_build_and_run("app/Vastitas.toml"),
        common::exits(42)
    );
    let wire = s.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    for (old, new) in [
        ("cb(int(dim(Y)))", "cb(int(dim(X)))"),
        ("ops::twice;", "ops::other;"),
    ] {
        let mut bad = wire.clone();
        let source = wire["root_source"]["text"].as_str().unwrap();
        bad["root_source"]["text"] = json!(source.replace(old, new));
        rejected(&bad);
    }
}

#[test]
fn unedited_package_families_bind_domains_contracts_visibility_and_bodies() {
    let source = r#"
pub fn choose(arg,) domain((Int,), (Bool,),);
fn choose(x: Any) -> Int { 17 }
fn choose(x: Int) requires (HasEq,) -> Int { x + 1 }
fn choose(x: Int) -> Int requires (HasEq) domain((Int,),);
fn choose(x: Bool) -> Int;
pub fn convert(x: Bool) -> Int { 3 }
pub fn convert(x: Int) -> Int { 4 }
fn main() -> Int { choose(38) + convert(true) }
"#;
    let s = Scratch::empty("family files");
    s.write_package("app", source, "");
    assert_eq!(
        s.check_build_and_run("app/Vastitas.toml"),
        common::exits(42)
    );
    let wire = s.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    let mut reordered = wire.clone();
    reordered["packages"][0]["modules"][0]["methods"]
        .as_array_mut()
        .unwrap()
        .reverse();
    for action in ["check", "emit"] {
        assert_eq!(kernel(&reordered, action)["ok"], true);
    }
    reordered["root_source"]["text"] = json!(source.replace("{ 17 }", "{ 71 }"));
    rejected(&reordered);
    for (from, to) in [
        ("arg,", "foo,"),
        ("(Int,), (Bool,),", "(Nat,), (Bool,),"),
        ("omain((Int,),);", "omain((Nat,),);"),
        ("{ 17 }", "{ 71 }"),
        ("{ x + 1 }", "{ x - 1 }"),
        ("{ 4 }", "{ 5 }"),
        ("pub fn convert(x: Int)", "    fn convert(x: Int)"),
    ] {
        assert_eq!(source.matches(from).count(), 1);
        assert_eq!(from.len(), to.len());
        let mut bad = wire.clone();
        bad["root_source"]["text"] = json!(source.replace(from, to));
        rejected(&bad);
    }
    let mut bad = wire.clone();
    bad["packages"][0]["modules"][0]["abstract_methods"]
        .as_array_mut()
        .unwrap()
        .pop();
    rejected(&bad);
    let mut bad = wire.clone();
    let implied =
        &mut bad["packages"][0]["modules"][0]["abstract_methods"][1]["domain"][0][0]["span"];
    let old_column = implied["column"].as_u64().unwrap();
    implied["column"] = json!(old_column + 1);
    rejected(&bad);
    let mut bad = wire;
    let inferred = bad["packages"][0]["modules"][0]["generics"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|g| g["name"] == "convert")
        .unwrap();
    inferred["params"][0]["name"] = json!("other");
    rejected(&bad);
}

#[test]
fn flat_libraries_bind_inferred_methods_to_their_own_file() {
    let s = Scratch::empty("flat family files");
    let entry = "fn main() -> Int { choose(40) }";
    s.write("entry.vast", entry);
    let library = s.write("overload.vast", "fn choose(x: Int) -> Int { x + 2 }");
    let unused = s.write("other.vast", "// β\nfn choose(b: Bool) -> Int { 71 }");
    common::native(entry, &[library, unused], common::exits(42), "flat.vast");
    let mut capture = s.cli();
    capture.args([
        "check",
        "entry.vast",
        "--lib",
        "overload.vast",
        "--lib",
        "other.vast",
    ]);
    let wire = common::captured_wire(capture, CURRENT_PROTOCOL);
    assert_eq!(kernel(&wire, "check")["ok"], true);
    for (source, old, new) in [("overload.vast", "+", "-"), ("other.vast", "71", "72")] {
        let mut bad = wire.clone();
        let row = bad["root_source"]["files"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|f| f["path"].as_str().unwrap().ends_with(source))
            .unwrap();
        let original = row["text"].as_str().unwrap();
        let start = row["offset"].as_u64().unwrap() + original.find(old).unwrap() as u64;
        row["text"] = json!(original.replace(old, new));
        for action in ["check", "emit"] {
            let response = kernel(&bad, action);
            assert_wire_rejected(&response, "E_ASSEMBLY");
            assert_eq!(response["diagnostics"][0]["span"]["start"], start);
        }
    }
}

#[test]
fn omitting_a_whole_dispatch_family_cannot_turn_its_bodies_into_singletons() {
    let entry = "fn main() -> Int { 42 }";
    for declarations in [
        "fn unused(x: Int) -> Int { 1 } fn unused(b: Bool) -> Int { 2 }",
        "fn unused(x: Number) -> Int { 1 }",
        "fn unused(x: Int) -> Int requires (HasEq) { x }",
        "fn unused(x) domain();",
    ] {
        let mut wire = common::request(&format!("{entry} {declarations}"), "omitted.vast");
        assert_eq!(kernel(&wire, "check")["ok"], true);
        let module = common::flat_module(&mut wire);
        module["generics"] = json!([]);
        module["methods"] = json!([]);
        rejected(&wire);
    }
    let s = Scratch::empty("omitted family across files");
    s.write("main.vast", entry);
    s.write("first.vast", "fn unused(x: Int) -> Int { x }");
    s.write("second.vast", "fn unused(b: Bool) -> Bool { b }");
    let mut capture = s.cli();
    capture.args([
        "check",
        "main.vast",
        "--lib",
        "first.vast",
        "--lib",
        "second.vast",
    ]);
    let mut wire = common::captured_wire(capture, CURRENT_PROTOCOL);
    assert_eq!(kernel(&wire, "check")["ok"], true);
    let module = common::flat_module(&mut wire);
    module["generics"] = json!([]);
    module["methods"] = json!([]);
    rejected(&wire);
}
