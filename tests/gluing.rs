//! The Stage 7 (#878) source forms through the public source path: glued
//! objects, covers, and separation, manifold and projective claims, in the
//! Zariski site of presented objects and in the smooth site of `Affine(n)`
//! objects. The frontend parses each form into the wire record that the
//! kernel decodes; these tests capture the wire, check its records, submit it
//! to the kernel and forge it, and check, build and run the program that
//! glues the projective line over QQ and the real projective line. Stage 7
//! declarations have no runtime value, so they leave the generated code
//! unchanged.
mod common;
use common::{Scratch, assert_wire_rejected, expect_code, kernel, remove_spans};
use serde_json::{Value, json};

const MANIFEST: &str = "[package]\nname = \"gluing\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n";

/// The charts of both sites, with the Stage 2 transition of #104 as declared
/// morphisms, which the entry point uses.
const CHARTS: &str = "// The charts of the projective line over QQ and of the real one (#878).
indexed marker QQ;
indexed implementation AffineQQ(QQ, presented_affine(rational)) capabilities();
indexed classification AffineScheme { parents(); domain(AffineQQ); };
indexed family Over(object(AffineScheme), object(AffineScheme), object(AffineScheme))
    = relative constraints(structural(0, 2), structural(1, 2));
indexed primitive compose = relative_compose(Over);
indexed primitive same = relative_equal(Over);
indexed affine SpecQQ(AffineQQ) = spec[];
indexed affine L1(AffineQQ) = spec[x] over SpecQQ;
indexed affine L2(AffineQQ) = spec[y] over SpecQQ;
indexed affine U1(AffineQQ) = localize(L1, x) inverse xi;
indexed affine U2(AffineQQ) = localize(L2, y) inverse yi;
indexed morphism there: Over<U1, U2, SpecQQ> = pullback(y -> xi, yi -> x);
indexed morphism back: Over<U2, U1, SpecQQ> = pullback(x -> yi, xi -> y);
indexed morphism stay: Over<U1, U1, SpecQQ> = identity;
indexed affine V1(AffineQQ) = localize(L1, x) inverse a;
indexed affine V2(AffineQQ) = localize(L2, y) inverse b;
indexed affine Line(AffineQQ) = spec[t] over SpecQQ;
indexed affine Dt(AffineQQ) = localize(Line, t) inverse u;
indexed affine Dmt(AffineQQ) = localize(Line, 1 - t) inverse w;
indexed marker CInfReal;
indexed implementation SmoothR(CInfReal, smooth_affine) capabilities();
indexed affine M1(SmoothR) = Affine(1)[x];
indexed affine M2(SmoothR) = Affine(1)[y];
";

/// The Stage 7 declarations: ℙ¹ with its separation and its projective
/// claim, the doubled origin, a cover of the line, and the smooth opens and
/// ℝP¹ with its manifold claim.
const GLUING: &str = "
indexed glued P(AffineQQ) = glue(U1, U2) by(y -> xi, yi -> x) inverse(x -> yi, xi -> y);
indexed separated sep = separated(P) by(xi -> L2::y);
indexed projective line = proj(P)[s, t] chart(L1, s, x) inverse(x -> t) chart(L2, t, y) inverse(y -> s);
indexed glued Doubled(AffineQQ) = glue(V1, V2) by(y -> x, b -> a) inverse(x -> y, a -> b);
indexed cover halves = cover(Line, Dt, Dmt) by(1, 1);
indexed affine W1(SmoothR) = localize(M1, x) inverse u;
indexed affine W2(SmoothR) = localize(M2, y) inverse v;
indexed glued RP1(SmoothR) = glue(W1, W2) by(y -> u, v -> x) inverse(x -> v, u -> y);
indexed manifold circle = manifold(RP1, 1) by(u -> M2::y);
";

/// The entry point: the declared transition and its inverse compose to the
/// identity of U1.
const MAIN: &str = "
fn main() -> Int {
    let inverse = if same(compose(back(), there()), stay()) { 1 } else { 0 };
    let shown = show!(inverse);
    if inverse == 1 { 0 } else { 1 }
}
";

fn shown() -> common::Run {
    common::shows(&["inverse = 1"])
}

fn package(main: &str) -> Scratch {
    let s = Scratch::empty("gluing");
    s.write("Vastitas.toml", MANIFEST);
    s.write("main.vast", main);
    s
}

fn check(s: &Scratch) -> std::process::Output {
    s.check_manifest("Vastitas.toml")
}

fn program(extra: &str) -> String {
    format!("{CHARTS}{GLUING}{extra}{MAIN}")
}

/// The diagnostic of `extra` after the accepted program.
fn rejected(extra: &str, code: &str) -> String {
    expect_code(&check(&package(&program(extra))), code)
}

fn declaration<'a>(wire: &'a Value, name: &str) -> &'a Value {
    wire["packages"][0]["modules"][0]["indexed_declarations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|d| d["name"] == name)
        .unwrap_or_else(|| panic!("no declaration {name}"))
}

fn without_spans(value: &Value) -> Value {
    let mut value = value.clone();
    remove_spans(&mut value);
    value
}

fn p(name: &str) -> Value {
    json!({ "path": [name] })
}

fn coordinate(name: &str) -> Value {
    json!({ "op": "coordinate", "name": name })
}

fn binding(name: &str, image: &str) -> Value {
    json!({ "name": name, "image": coordinate(image) })
}

/// Every Stage 7 form serializes to the record that the kernel decodes, and
/// a smooth open keeps the record of a principal open.
#[test]
fn the_stage7_forms_serialize_to_their_records() {
    let wire = package(&program("")).captured("Vastitas.toml", common::CURRENT_PROTOCOL);
    let record = |name: &str| {
        let mut record = without_spans(declaration(&wire, name));
        let object = record.as_object_mut().unwrap();
        object.remove("name");
        object.remove("public");
        record
    };
    assert_eq!(
        record("P"),
        json!({ "kind": "glued", "implementation": p("AffineQQ"), "opens": [p("U1"), p("U2")],
            "forward": [binding("y", "xi"), binding("yi", "x")],
            "inverse": [binding("x", "yi"), binding("xi", "y")] })
    );
    assert_eq!(
        record("sep"),
        json!({ "kind": "separated", "glued": p("P"), "witness": binding("xi", "L2::y") })
    );
    assert_eq!(
        record("circle"),
        json!({ "kind": "manifold", "glued": p("RP1"), "dimension": "1",
            "witness": binding("u", "M2::y") })
    );
    assert_eq!(
        record("halves"),
        json!({ "kind": "cover", "object": p("Line"), "opens": [p("Dt"), p("Dmt")],
            "coefficients": [{ "op": "natural", "value": "1" }, { "op": "natural", "value": "1" }] })
    );
    assert_eq!(
        record("line"),
        json!({ "kind": "projective", "glued": p("P"), "homogeneous": ["s", "t"], "charts": [
            { "chart": p("L1"), "dehomogenized": "s", "image": coordinate("x"), "inverse": [binding("x", "t")] },
            { "chart": p("L2"), "dehomogenized": "t", "image": coordinate("y"), "inverse": [binding("y", "s")] }] })
    );
    assert_eq!(record("W1")["kind"], "affine_localization");
    assert_eq!(record("W1")["implementation"], p("SmoothR"));
}

/// The acceptance program of Stage 7 checks, builds and runs.
#[test]
fn the_projective_line_checks_builds_and_runs() {
    assert_eq!(
        package(&program("")).check_build_and_run("Vastitas.toml"),
        shown()
    );
}

/// Stage 7 declarations are evidence with no runtime value: the kernel
/// emits the same code, byte for byte, with and without them.
#[test]
fn stage7_declarations_leave_the_generated_code_unchanged() {
    let emitted = |source: &str| {
        let response = kernel(
            package(source).captured("Vastitas.toml", common::CURRENT_PROTOCOL),
            "emit",
        );
        assert_eq!(response["ok"], true, "{response}");
        response["lean_source"].as_str().unwrap().to_owned()
    };
    assert_eq!(
        emitted(&format!("{CHARTS}{GLUING}{MAIN}")),
        emitted(&format!("{CHARTS}{MAIN}"))
    );
}

/// No function names a Stage 7 declaration as a value.
#[test]
fn a_stage7_declaration_is_not_a_value() {
    for (name, kind) in [
        ("P", "a glued object"),
        ("sep", "a separation claim"),
        ("circle", "a manifold claim"),
        ("halves", "a cover"),
        ("line", "a projective claim"),
        ("W1", "a smooth open"),
    ] {
        let source =
            format!("{CHARTS}{GLUING}fn main() -> Int {{\n    let value = {name};\n    0\n}}\n");
        let stderr = expect_code(&check(&package(&source)), "E_TYPE");
        assert!(
            stderr.contains(&format!("names {kind}, which is not a value")),
            "{stderr}"
        );
    }
}

/// The kernel decides every rule of the profile, with the code of its rule.
#[test]
fn stage7_rejections_have_their_codes() {
    for (extra, code, text) in [
        (
            "indexed glued Three(AffineQQ) = glue(U1, U2, V1) by(y -> xi, yi -> x) inverse(x -> yi, xi -> y);\n",
            "E_GLUE",
            "exactly two charts",
        ),
        (
            "indexed glued Same(AffineQQ) = glue(U1, V1) by(x -> xi, a -> x) inverse(x -> a, xi -> x);\n",
            "E_GLUE",
            "a gluing needs two charts",
        ),
        (
            "indexed glued Half(AffineQQ) = glue(U1, U2) by(y -> 2 * xi, yi -> x) inverse(x -> yi, xi -> y);\n",
            "E_GLUE",
            "does not respect the target's relations",
        ),
        (
            "indexed glued Flip(AffineQQ) = glue(U1, U2) by(y -> -xi, yi -> -x) inverse(x -> yi, xi -> y);\n",
            "E_GLUE",
            "not mutually inverse",
        ),
        (
            "indexed glued Mixed(SmoothR) = glue(U1, U2) by(y -> xi, yi -> x) inverse(x -> yi, xi -> y);\n",
            "E_GLUE",
            "the smooth site",
        ),
        (
            "indexed glued Mixed(AffineQQ) = glue(W1, W2) by(y -> u, v -> x) inverse(x -> v, u -> y);\n",
            "E_GLUE",
            "the Zariski site",
        ),
        (
            "indexed separated no = separated(Doubled) by(a -> L2::y);\n",
            "E_GLUE",
            "inverse coordinate",
        ),
        (
            "indexed separated no = separated(RP1) by(u -> M2::y);\n",
            "E_GLUE",
            "manifold(",
        ),
        (
            "indexed manifold no = manifold(RP1, 2) by(u -> M2::y);\n",
            "E_GLUE",
            "dimension 2",
        ),
        (
            "indexed projective no = proj(Doubled)[s, t] chart(L1, s, x) inverse(x -> t) chart(L2, t, y) inverse(y -> s);\n",
            "E_GLUE",
            "disagree on the overlap",
        ),
        (
            "indexed projective no = proj(P)[s, t] chart(L1, s, x) inverse(x -> t) chart(L2, s, y) inverse(y -> t);\n",
            "E_GLUE",
            "different coordinates",
        ),
        (
            "indexed affine Dsq(AffineQQ) = localize(Line, t^2 + 1) inverse k;\n\
             indexed cover no = cover(Line, Dsq) by(1);\n",
            "E_GLUE",
            "do not combine the opens to 1",
        ),
        (
            "indexed cover no = cover(Line, Dt, U1) by(1, 1);\n",
            "E_GLUE",
            "not of `gluing::Line`",
        ),
        (
            "indexed glued Short(AffineQQ) = glue(U1, U2) by(y -> xi) inverse(x -> yi, xi -> y);\n",
            "E_AFFINE_COORDINATE",
            "exactly one image",
        ),
    ] {
        let stderr = rejected(extra, code);
        assert!(stderr.contains(text), "{extra}: {stderr}");
    }
}

/// A witness is one binding, and a cover names its object.
#[test]
fn stage7_syntax_errors_are_reported() {
    for extra in [
        "indexed separated no = separated(P) by(xi -> L2::y, yi -> L1::x);\n",
        "indexed cover no = cover() by();\n",
        "indexed manifold no = manifold(RP1, one) by(u -> M2::y);\n",
    ] {
        rejected(extra, "E_PARSE");
    }
}

/// The kernel checks the wire records, not the frontend: forged images,
/// witnesses, coefficients, opens and chart entries are rejected.
#[test]
fn forged_stage7_records_are_rejected_by_the_kernel() {
    let wire = package(&program("")).captured("Vastitas.toml", common::CURRENT_PROTOCOL);
    let index = |name: &str| {
        wire["packages"][0]["modules"][0]["indexed_declarations"]
            .as_array()
            .unwrap()
            .iter()
            .position(|d| d["name"] == name)
            .unwrap()
    };
    // A forged path carries a span, as every path of the wire does.
    let span = declaration(&wire, "P")["span"].clone();
    let p = |name: &str| json!({ "path": [name], "span": span });
    let forged = |name: &str, field: &str, value: Value| {
        let mut changed = wire.clone();
        let target = format!("/packages/0/modules/0/indexed_declarations/{}", index(name));
        changed
            .pointer_mut(&target)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .insert(field.into(), value);
        kernel(changed, "check")
    };
    assert_wire_rejected(
        &forged(
            "P",
            "forward",
            json!([binding("y", "x"), binding("yi", "x")]),
        ),
        "E_GLUE",
    );
    assert_wire_rejected(&forged("P", "opens", json!([p("U1"), p("V1")])), "E_GLUE");
    assert_wire_rejected(&forged("P", "implementation", p("SmoothR")), "E_GLUE");
    assert_wire_rejected(&forged("sep", "witness", binding("xi", "L1::x")), "E_GLUE");
    assert_wire_rejected(&forged("sep", "glued", p("Doubled")), "E_GLUE");
    assert_wire_rejected(&forged("circle", "dimension", json!("2")), "E_GLUE");
    assert_wire_rejected(
        &forged(
            "halves",
            "coefficients",
            json!([{ "op": "natural", "value": "2" }, { "op": "natural", "value": "1" }]),
        ),
        "E_GLUE",
    );
    assert_wire_rejected(&forged("line", "homogeneous", json!(["s", "s"])), "E_GLUE");
    for (name, field) in [
        ("P", "transition"),
        ("sep", "certificate"),
        ("line", "isomorphism"),
    ] {
        assert_wire_rejected(&forged(name, field, json!([])), "E_PROTOCOL");
    }
    assert_wire_rejected(&forged("circle", "dimension", json!("one")), "E_PROTOCOL");
}
