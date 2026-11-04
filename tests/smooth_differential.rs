//! Smooth objects and smooth maps through the public protocol-9 source path.
//! `Affine(n)[...]` declares a smooth real affine space; `Smooth<X, Y>` maps
//! are exact QQ polynomial maps. The kernel elaborates and checks every map;
//! these tests exercise acceptance, native execution, rejections, protocol
//! selection and forged wire.
mod common;
use common::{Scratch, assert_wire_rejected, cli, expect_code, kernel, remove_spans, success};
use serde_json::{Value, json};

const PROFILE: &str = include_str!("../examples/packages/smooth-objects/src/profile.vast");
const MAIN: &str = include_str!("../examples/packages/smooth-objects/src/main.vast");

/// The presented Stage 2 profile, declared next to the smooth one.
const PRESENTED: &str = "indexed marker QQ;
indexed implementation AffineQQ(QQ, presented_affine(rational)) capabilities();
indexed classification AffineScheme { parents(); domain(AffineQQ); };
indexed affine SpecQQ(AffineQQ) = spec[];
indexed affine QLine(AffineQQ) = spec[t] over SpecQQ;";

fn fixture(main: &str) -> Scratch {
    let s = Scratch::empty("smooth objects");
    s.write(
        "Vastitas.toml",
        include_str!("../examples/packages/smooth-objects/Vastitas.toml"),
    );
    s.write("src/main.vast", main);
    s.write("src/profile.vast", PROFILE);
    s
}

fn check(s: &Scratch) -> std::process::Output {
    cli()
        .current_dir(&s.0)
        .args(["check", "--manifest-path", "Vastitas.toml"])
        .output()
        .unwrap()
}

/// The example with extra items inserted before its helper and entrypoint.
fn with(extra: &str) -> String {
    assert!(MAIN.contains("fn verdict("));
    MAIN.replacen("fn verdict(", &format!("{extra}\nfn verdict("), 1)
}

#[track_caller]
fn rejects(main: &str, code: &str) -> String {
    expect_code(&check(&fixture(main)), code)
}

fn run(s: &Scratch) -> Vec<u8> {
    let output = s.0.join("program");
    success(
        &cli()
            .current_dir(&s.0)
            .args(["build", "--manifest-path", "Vastitas.toml", "-o"])
            .arg(&output)
            .output()
            .unwrap(),
    );
    let result = std::process::Command::new(output).output().unwrap();
    success(&result);
    result.stdout
}

fn request(s: &Scratch) -> Value {
    common::captured_wire(
        {
            let mut command = cli();
            command
                .current_dir(&s.0)
                .args(["check", "--manifest-path", "Vastitas.toml"]);
            command
        },
        9,
    )
}

/// JSON pointer to a named declaration in the first package.
fn declaration_pointer(raw: &Value, name: &str) -> String {
    let modules = raw["packages"][0]["modules"].as_array().unwrap();
    for (m, module) in modules.iter().enumerate() {
        if let Some(d) = module["indexed_declarations"]
            .as_array()
            .and_then(|declarations| declarations.iter().position(|d| d["name"] == name))
        {
            return format!("/packages/0/modules/{m}/indexed_declarations/{d}");
        }
    }
    panic!("no declaration {name}")
}

#[test]
fn smooth_example_checks_builds_and_executes() {
    let s = fixture(MAIN);
    success(&check(&s));
    assert_eq!(run(&s), b"42\n");
}

#[test]
fn mutated_observations_change_the_native_result() {
    let main = common::checked_replace(
        MAIN,
        "verdict(same(compose(g(), f()), gf()), 1)",
        "verdict(same(compose(g(), f()), sq()), 1)",
    );
    let main = common::checked_replace(
        &main,
        "verdict(!same(compose(shearA(), shearB()), compose(shearB(), shearA())), 2)",
        "verdict(same(compose(shearA(), shearB()), compose(shearB(), shearA())), 2)",
    );
    let main = common::checked_replace(
        &main,
        "line_at(3)), nine()), 6)",
        "line_at(2)), nine()), 6)",
    );
    // Written order, sign and coordinate order each change an observation.
    let main = common::checked_replace(
        &main,
        "pullback(y -> y, x -> x + y);",
        "pullback(y -> x + y, x -> y);",
    );
    let main = common::checked_replace(
        &main,
        "same(line_at(-3), minusThree())",
        "same(line_at(3), minusThree())",
    );
    let main = common::checked_replace(
        &main,
        "same(plane_at(1, 2), onePlusTwo())",
        "same(plane_at(2, 1), onePlusTwo())",
    );
    assert_eq!(run(&fixture(&main)), b"83\n");
}

#[test]
fn smooth_programs_lower_to_the_shared_smooth_runtime() {
    let raw = request(&fixture(MAIN));
    let emitted = kernel(&raw, "emit");
    assert_eq!(emitted["ok"], true, "{emitted}");
    let source = emitted["lean_source"].as_str().unwrap();
    assert!(
        source.contains("import VastitasKernel.SmoothRuntime\n"),
        "{source}"
    );
    assert!(
        source.contains("VastitasKernel.SmoothRuntime.Program.compose"),
        "{source}"
    );
    assert!(
        source.contains("VastitasKernel.SmoothRuntime.composite"),
        "{source}"
    );
    assert!(
        source.contains("VastitasKernel.SmoothRuntime.intPoint"),
        "{source}"
    );
    assert!(
        source.contains(": VastitasKernel.SmoothRuntime.Program"),
        "{source}"
    );
}

#[test]
fn smooth_declarations_reject_mismatched_forms_with_specific_codes() {
    for (declaration, code, message) in [
        (
            "indexed affine Bad(SmoothR) = spec[t];",
            "E_SMOOTH",
            "is a smooth implementation",
        ),
        (
            "indexed affine Bad(SmoothR) = Affine(2)[t];",
            "E_SMOOTH",
            "Affine(2) needs 2 coordinates, but 1 are given",
        ),
        (
            "indexed affine Bad(SmoothR) = Affine(2)[t, t];",
            "E_SMOOTH",
            "smooth coordinates must be distinct",
        ),
        (
            "indexed global G(SmoothR);",
            "E_SMOOTH",
            "cannot use the smooth implementation",
        ),
        (
            "indexed primitive bad = smooth_int_point(Smooth, Plane, Line);",
            "E_SMOOTH",
            "must be 0-dimensional, but it has dimension 1",
        ),
        (
            "indexed morphism bad: Smooth<Line, Plane> = identity;",
            "E_SMOOTH",
            "needs the same source and target",
        ),
        (
            "indexed morphism bad: Smooth<Line, Line> = structure;",
            "E_SMOOTH",
            "is given by `pullback(…)` or `identity`",
        ),
    ] {
        let stderr = rejects(&with(declaration), code);
        assert!(stderr.contains(message), "{declaration}: {stderr}");
    }
    let presented = rejects(
        &with(&format!(
            "{PRESENTED}\nindexed affine Bad(AffineQQ) = Affine(1)[t];"
        )),
        "E_SMOOTH",
    );
    assert!(
        presented.contains("`AffineQQ` is a presented implementation"),
        "{presented}"
    );
    let coordinates: Vec<String> = (0..17).map(|i| format!("x{i}")).collect();
    rejects(
        &with(&format!(
            "indexed affine Big(SmoothR) = Affine(17)[{}];",
            coordinates.join(", ")
        )),
        "E_LIMIT",
    );
    success(&check(&fixture(&with(&format!(
        "indexed affine Edge(SmoothR) = Affine(16)[{}];",
        coordinates[..16].join(", ")
    )))));
    rejects(
        &with("indexed affine Bad(SmoothR) = Affine(t)[t];"),
        "E_PARSE",
    );
    // The frontend bounds the dimension before the kernel sees it.
    let digits = rejects(
        &with(&format!(
            "indexed affine Big(SmoothR) = Affine({})[t];",
            "9".repeat(65)
        )),
        "E_LIMIT",
    );
    assert!(
        digits.contains("an `Affine` dimension has at most 64 decimal digits"),
        "{digits}"
    );
    let large = rejects(
        &with("indexed affine Big(SmoothR) = Affine(99999999999999999999)[t];"),
        "E_LIMIT",
    );
    assert!(
        large.contains("`Affine(99999999999999999999)` exceeds the limit of 16 coordinates"),
        "{large}"
    );
    let sugar = rejects(
        &with(&format!(
            "{PRESENTED}\nindexed affine Big(AffineQQ) = Affine(SpecQQ, 17)[t];"
        )),
        "E_LIMIT",
    );
    assert!(
        sugar.contains("exceeds the limit of 16 coordinates"),
        "{sugar}"
    );
}

#[test]
fn smooth_maps_resolve_source_coordinates_and_reject_variance_errors() {
    for (declaration, code) in [
        // A foreign coordinate.
        (
            "indexed morphism bad: Smooth<Line, Plane> = pullback(x -> s, y -> t);",
            "E_AFFINE_COORDINATE",
        ),
        // Target coordinates in an image: the variance is swapped.
        (
            "indexed morphism bad: Smooth<Line, Plane> = pullback(x -> x, y -> t);",
            "E_AFFINE_COORDINATE",
        ),
        // A missing target coordinate.
        (
            "indexed morphism bad: Smooth<Line, Plane> = pullback(x -> t);",
            "E_AFFINE_COORDINATE",
        ),
        (
            "indexed morphism bad: Smooth<Line, Line> = pullback(t -> t^17);",
            "E_LIMIT",
        ),
        (
            "indexed family BadSmooth(object(profile::CInfAffine), object(profile::CInfAffine)) = smooth constraints(canonical(0));",
            "E_TYPE",
        ),
        (
            "indexed implementation Caps(profile::CInfReal, smooth_affine) capabilities(dimension);",
            "E_TYPE",
        ),
    ] {
        rejects(&with(declaration), code);
    }
    // Images are stored in the target's coordinate order, whatever the written order.
    success(&check(&fixture(&with(
        "indexed morphism swapped: Smooth<Line, Plane> = pullback(y -> t^2, x -> t);\nfn agrees() -> Bool { same(swapped(), f()) }",
    ))));
    // Composition and equality need matching objects.
    for body in [
        "fn bad() -> Bool { same(compose(f(), f()), gf()) }",
        "fn bad() -> Bool { same(f(), g()) }",
        "fn bad() -> Bool { same(compose(g(), f()), idP()) }",
    ] {
        rejects(&with(body), "E_ENDPOINT");
    }
    rejects(
        &with("fn bad() -> Bool { same(line_at(1, 2), nine()) }"),
        "E_ARITY",
    );
}

#[test]
fn smooth_and_presented_objects_stay_disjoint() {
    success(&check(&fixture(&with(PRESENTED))));
    for (declaration, code) in [
        (
            "indexed family BadSmooth(object(AffineScheme), object(AffineScheme)) = smooth constraints(canonical(0), canonical(1));",
            "E_TYPE",
        ),
        (
            "indexed family BadOver(object(profile::CInfAffine), object(profile::CInfAffine), object(profile::CInfAffine)) = relative constraints(structural(0, 2), structural(1, 2));",
            "E_TYPE",
        ),
        (
            "indexed morphism bad: Smooth<QLine, QLine> = identity;",
            "E_SMOOTH",
        ),
        (
            "fn probe(arrow: Smooth<Line, QLine>) -> Int { 0 }",
            "E_TYPE",
        ),
        (
            "indexed affine Bad(SmoothR) = Affine(SpecQQ, 1)[t];",
            "E_SMOOTH",
        ),
    ] {
        rejects(&with(&format!("{PRESENTED}\n{declaration}")), code);
    }
}

#[test]
fn smooth_forms_select_protocol_nine_and_older_envelopes_reject_them() {
    let raw = request(&fixture(MAIN));
    assert_eq!(raw["version"], 9);
    let accepted = kernel(&raw, "emit");
    assert_eq!(accepted["ok"], true, "{accepted}");
    for version in [7, 8] {
        let mut changed = raw.clone();
        changed["version"] = json!(version);
        assert_wire_rejected(&kernel(changed, "emit"), "E_PROTOCOL");
    }
    for version in 2..7 {
        let mut changed = raw.clone();
        changed["version"] = json!(version);
        let rejected = kernel(changed, "emit");
        assert_eq!(rejected["ok"], false, "version {version}: {rejected}");
    }
}

#[test]
fn raw_wire_rejects_forged_smooth_records() {
    let raw = request(&fixture(MAIN));
    let plane = declaration_pointer(&raw, "Plane");
    let f = declaration_pointer(&raw, "f");
    let compose = declaration_pointer(&raw, "compose");
    assert_eq!(raw.pointer(&plane).unwrap()["kind"], "smooth_affine");
    let forged = |path: &str, value: Value| {
        let mut changed = raw.clone();
        *changed.pointer_mut(path).unwrap() = value;
        changed
    };
    // Unknown fields, stored maps and malformed dimensions are protocol errors.
    let mut extra = raw.clone();
    extra.pointer_mut(&plane).unwrap()["map"] = json!([]);
    assert_wire_rejected(&kernel(extra, "emit"), "E_PROTOCOL");
    let mut extra = raw.clone();
    extra.pointer_mut(&f).unwrap()["map"] = json!({"images": []});
    assert_wire_rejected(&kernel(extra, "emit"), "E_PROTOCOL");
    for (path, value) in [
        (format!("{plane}/dimension"), json!("-1")),
        (format!("{plane}/dimension"), json!("1e3")),
        (format!("{plane}/dimension"), json!(2)),
        (format!("{plane}/dimension"), json!("9".repeat(65))),
        (format!("{plane}/coordinates"), json!([1, 2])),
        (format!("{compose}/binding/op"), json!("smooth_gradient")),
        (format!("{compose}/binding/op"), json!("smooth_")),
        (format!("{compose}/binding/op"), json!("relative_gradient")),
        (
            format!("{f}/definition"),
            json!({"kind": "cached", "images": []}),
        ),
    ] {
        assert_wire_rejected(&kernel(forged(&path, value), "emit"), "E_PROTOCOL");
    }
    // Consistent but wrong data is rejected by the checker with its own code.
    for (path, value, code) in [
        (format!("{plane}/dimension"), json!("3"), "E_SMOOTH"),
        (
            format!("{plane}/coordinates"),
            json!(["x", "x"]),
            "E_SMOOTH",
        ),
        (format!("{plane}/dimension"), json!("17"), "E_LIMIT"),
        (
            format!("{f}/definition/images/0/image"),
            json!({"op": "coordinate", "name": "x"}),
            "E_AFFINE_COORDINATE",
        ),
        (
            format!("{f}/definition"),
            json!({"kind": "structure"}),
            "E_SMOOTH",
        ),
    ] {
        assert_wire_rejected(&kernel(forged(&path, value), "emit"), code);
    }
}

#[test]
fn algebraic_affine_spelling_is_sugar_for_spec_over_a_base() {
    let declarations = |spelling: &str| {
        let raw = request(&fixture(&with(&format!(
            "{PRESENTED}\nindexed affine L4(AffineQQ) = {spelling};"
        ))));
        let mut declaration = raw
            .pointer(&declaration_pointer(&raw, "L4"))
            .unwrap()
            .clone();
        remove_spans(&mut declaration);
        declaration
    };
    let sugar = declarations("Affine(SpecQQ, 1)[t]");
    assert_eq!(sugar, declarations("spec[t] over SpecQQ"));
    assert_eq!(sugar["kind"], "affine");
    // The algebraic spelling has no wire form, so the frontend checks its dimension.
    let stderr = rejects(
        &with(&format!(
            "{PRESENTED}\nindexed affine L4(AffineQQ) = Affine(SpecQQ, 2)[t];"
        )),
        "E_AFFINE_COORDINATE",
    );
    assert!(
        stderr.contains("Affine(SpecQQ, 2) needs 2 coordinates"),
        "{stderr}"
    );
    success(&check(&fixture(&with(&format!(
        "{PRESENTED}\nindexed affine L4(AffineQQ) = Affine(SpecQQ, 1)[t];\nindexed affine P4(AffineQQ) = Affine(SpecQQ, 2)[u, v];"
    )))));
}

#[test]
fn function_body_affine_spellings_still_use_the_geometry_compatibility_export() {
    let s = Scratch::empty("smooth geometry compat");
    let library = common::root().join("stdlib/src/geometry");
    for name in [
        "Vastitas.toml",
        "mod.vast",
        "scheme/mod.vast",
        "scheme/affine/mod.vast",
        "smooth/mod.vast",
    ] {
        s.write(
            &format!("geo/{name}"),
            &std::fs::read_to_string(library.join(name)).unwrap(),
        );
    }
    s.write(
        "app/Vastitas.toml",
        "[package]\nname='app'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\ngeo={path='../geo'}\n",
    );
    s.write(
        "app/main.vast",
        "indexed marker Reals;
indexed implementation SmoothR(Reals, smooth_affine) capabilities();
indexed classification CInfAffine { parents(); domain(SmoothR); };
indexed family Smooth(object(CInfAffine), object(CInfAffine)) = smooth constraints(canonical(0), canonical(1));
indexed affine Line(SmoothR) = Affine(1)[t];
indexed morphism sq: Smooth<Line, Line> = pullback(t -> t^2);
indexed primitive same = smooth_equal(Smooth);

fn main() -> Int {
    let X: Scheme = Affine(QQ, 20);
    let Y: CInfScheme = Affine(CInfReal, 22);
    if same(sq(), sq()) { int(dimension(X)) + int(dimension(Y)) } else { 0 }
}
",
    );
    success(
        &cli()
            .current_dir(&s.0)
            .args(["check", "--manifest-path", "app/Vastitas.toml"])
            .output()
            .unwrap(),
    );
    success(
        &cli()
            .current_dir(&s.0)
            .args([
                "build",
                "--manifest-path",
                "app/Vastitas.toml",
                "-o",
                "program",
            ])
            .output()
            .unwrap(),
    );
    let result = std::process::Command::new(s.0.join("program"))
        .output()
        .unwrap();
    success(&result);
    assert_eq!(result.stdout, b"42\n");
}

// Covectors, vectors, tapes and the reverse pass (protocol 9). The example
// checks the roadmap identity and its failure cases natively.

const COTANGENT_PROFILE: &str =
    include_str!("../examples/packages/smooth-cotangent/src/profile.vast");
const COTANGENT_MAIN: &str = include_str!("../examples/packages/smooth-cotangent/src/main.vast");

fn cotangent_fixture(main: &str) -> Scratch {
    let s = Scratch::empty("smooth cotangent");
    s.write(
        "Vastitas.toml",
        include_str!("../examples/packages/smooth-cotangent/Vastitas.toml"),
    );
    s.write("src/main.vast", main);
    s.write("src/profile.vast", COTANGENT_PROFILE);
    s
}

/// The cotangent example with extra items inserted before its helpers.
fn with_cotangent(extra: &str) -> String {
    assert!(COTANGENT_MAIN.contains("fn verdict("));
    COTANGENT_MAIN.replacen("fn verdict(", &format!("{extra}\nfn verdict("), 1)
}

#[track_caller]
fn rejects_cotangent(main: &str, code: &str) -> String {
    expect_code(&check(&cotangent_fixture(main)), code)
}

#[test]
fn cotangent_example_checks_builds_and_executes() {
    let s = cotangent_fixture(COTANGENT_MAIN);
    success(&check(&s));
    assert_eq!(run(&s), b"42\n");
}

#[test]
fn mutated_cotangent_observations_change_the_native_result() {
    // Code 1: the stepwise pullback is 12 dt, not 13 dt.
    let main = common::checked_replace(
        COTANGENT_MAIN,
        "reads(stepwise(seed), 12, 1), 1)",
        "reads(stepwise(seed), 13, 1), 1)",
    );
    // Codes 6, 7 and 8: a seed at 18 instead of 17 no longer fails.
    let main = common::checked_replace(&main, "dline(line_at(17), 1)", "dline(line_at(18), 1)");
    // Code 12: a tape from 3 accepts a seed at sq(3) = 9.
    let main = common::checked_replace(
        &main,
        "dline(line_at(16), 1)), x), 12)",
        "dline(line_at(9), 1)), x), 12)",
    );
    // Code 14: B after A pulls dx back to (1, 1), not (2, 1).
    let main = common::checked_replace(
        &main,
        "dplane(plane_at(0, 0), 1, 1)), 14)",
        "dplane(plane_at(0, 0), 2, 1)), 14)",
    );
    assert_eq!(run(&cotangent_fixture(&main)), b"90\n");
}

#[test]
fn cotangent_programs_lower_to_the_shared_smooth_runtime() {
    let raw = request(&cotangent_fixture(COTANGENT_MAIN));
    let emitted = kernel(&raw, "emit");
    assert_eq!(emitted["ok"], true, "{emitted}");
    let source = emitted["lean_source"].as_str().unwrap();
    for expected in [
        "import VastitasKernel.SmoothRuntime\n",
        "(VastitasKernel.SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.saved ",
        "(VastitasKernel.SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.recomputed ",
        "(VastitasKernel.SmoothRuntime.differential ",
        "(VastitasKernel.SmoothRuntime.backward (VastitasKernel.SmoothRuntime.linearize ",
        "(VastitasKernel.SmoothRuntime.vector ",
        "(VastitasKernel.SmoothRuntime.component ",
        "(VastitasKernel.SmoothRuntime.pairing ",
        "(VastitasKernel.SmoothRuntime.fiberAt ",
        "(VastitasKernel.SmoothRuntime.fiberEqual ",
        ": (Option VastitasKernel.SmoothRuntime.Fiber)",
    ] {
        assert!(source.contains(expected), "{expected}\n{source}");
    }
}

#[test]
fn cotangent_operations_reject_wrong_objects_variances_and_points() {
    // A seed over the wrong object, a tangent seed, a point from a 1-dimensional
    // object, a covector compared as a vector, and a differential of a map to
    // the plane are endpoint errors that name the operand types.
    for (body, types) in [
        (
            "fn bad() -> Bool { lies_over(pullback(g(), plane_at(3, 9), dplane(plane_at(3, 9), 1, 0)), plane_at(3, 9)) }",
            "Smooth<Plane, Line>, Smooth<Pt, Plane>, Cotangent<Plane>",
        ),
        (
            "indexed primitive vline = fiber_vector(Tangent, Smooth, Line);\nfn bad() -> Bool { lies_over(pullback(sq(), line_at(3), vline(line_at(9), 1)), line_at(3)) }",
            "Smooth<Line, Line>, Smooth<Pt, Line>, Tangent<Line>",
        ),
        (
            "fn bad() -> Bool { lies_over(pullback(sq(), sq(), dline(line_at(9), 1)), line_at(3)) }",
            "Smooth<Line, Line>, Smooth<Line, Line>, Cotangent<Line>",
        ),
        (
            "fn bad() -> Bool { same_covector(vplane(plane_at(1, 2), 1, 0), vplane(plane_at(1, 2), 1, 0)) }",
            "Tangent<Plane>, Tangent<Plane>",
        ),
        (
            "fn bad() -> Bool { lies_over(differential(f(), line_at(3)), line_at(3)) }",
            "Smooth<Line, Plane>, Smooth<Pt, Line>",
        ),
        (
            "fn bad() -> Bool { lies_over(backward(linearize(f(), line_at(3)), dline(line_at(3), 1)), line_at(3)) }",
            "Tape<Line, Plane>, Cotangent<Line>",
        ),
        (
            "fn bad() -> Int { pair_first(pairing(dplane(plane_at(1, 2), 1, 0), vplane(plane_at(1, 2), 1, 0))) + pair_first(pairing(dline(line_at(1), 1), vplane(plane_at(1, 2), 1, 0))) }",
            "Cotangent<Line>, Tangent<Plane>",
        ),
    ] {
        let stderr = rejects_cotangent(&with_cotangent(body), "E_ENDPOINT");
        assert!(stderr.contains(types), "{body}: {stderr}");
    }
    // A tape is built only by linearize.
    rejects_cotangent(
        &with_cotangent("fn bad() -> profile::Tape<Line, Line> { sq() }"),
        "E_TYPE",
    );
    rejects_cotangent(
        &with_cotangent("fn bad() -> Bool { lies_over(dline(line_at(3), 1, 2), line_at(3)) }"),
        "E_ARITY",
    );
}

#[test]
fn cotangent_declarations_reject_malformed_contracts_with_specific_codes() {
    for (declaration, code, message) in [
        (
            "indexed primitive bad = differential(Smooth, Cotangent, Plane);",
            "E_SMOOTH",
            "the line object `Plane` of `differential` must be 1-dimensional, but it has dimension 2",
        ),
        (
            "indexed primitive bad = cotangent_pullback(Smooth, Tangent, saved);",
            "E_SMOOTH",
            "`cotangent_pullback` needs a cotangent family, but `Tangent` is a tangent family",
        ),
        (
            "indexed primitive bad = fiber_pairing(Tangent, Cotangent);",
            "E_SMOOTH",
            "`fiber_pairing` needs a cotangent family",
        ),
        (
            "indexed primitive bad = cotangent_pullback(Smooth, Cotangent, cached);",
            "E_TYPE",
            "a cotangent pullback mode is saved or recomputed",
        ),
        (
            "indexed primitive bad = fiber_component(Cotangent, Plane, t);",
            "E_AFFINE_COORDINATE",
            "`Plane` has no coordinate t",
        ),
        (
            "indexed family BadFiber(object(profile::CInfAffine)) = cotangent constraints();",
            "E_TYPE",
            "",
        ),
        (
            "indexed family BadFiber(object(profile::CInfAffine), object(profile::CInfAffine)) = tangent constraints(canonical(0), canonical(1));",
            "E_TYPE",
            "",
        ),
        (
            "indexed family BadTape(object(profile::CInfAffine), object(profile::CInfAffine)) = tape constraints(canonical(0));",
            "E_TYPE",
            "",
        ),
        (
            "indexed primitive bad = linearize(Smooth, Cotangent);",
            "E_TYPE",
            "",
        ),
        (
            "indexed primitive bad = cotangent_backward(Smooth, Cotangent);",
            "E_TYPE",
            "",
        ),
    ] {
        let stderr = rejects_cotangent(&with_cotangent(declaration), code);
        assert!(stderr.contains(message), "{declaration}: {stderr}");
    }
    // Fiber and tape families range over smooth objects only.
    for declaration in [
        "indexed family BadFiber(object(AffineScheme)) = cotangent constraints(canonical(0));",
        "indexed family BadTape(object(AffineScheme), object(AffineScheme)) = tape constraints(canonical(0), canonical(1));",
    ] {
        rejects_cotangent(
            &with_cotangent(&format!("{PRESENTED}\n{declaration}")),
            "E_TYPE",
        );
    }
    rejects_cotangent(
        &with_cotangent(&format!(
            "{PRESENTED}\nindexed primitive bad = fiber_vector(Cotangent, Smooth, QLine);"
        )),
        "E_SMOOTH",
    );
}

#[test]
fn cotangent_forms_select_protocol_nine_and_older_envelopes_reject_them() {
    let raw = request(&cotangent_fixture(COTANGENT_MAIN));
    assert_eq!(raw["version"], 9);
    let accepted = kernel(&raw, "emit");
    assert_eq!(accepted["ok"], true, "{accepted}");
    for version in [7, 8] {
        let mut changed = raw.clone();
        changed["version"] = json!(version);
        assert_wire_rejected(&kernel(changed, "emit"), "E_PROTOCOL");
    }
}

#[test]
fn raw_wire_rejects_forged_fiber_and_tape_records() {
    let raw = request(&cotangent_fixture(COTANGENT_MAIN));
    let pullback = declaration_pointer(&raw, "pullback");
    let differential = declaration_pointer(&raw, "differential");
    let linearize = declaration_pointer(&raw, "linearize");
    let dx = declaration_pointer(&raw, "dx");
    let cotangent = declaration_pointer(&raw, "Cotangent");
    let tape = declaration_pointer(&raw, "Tape");
    assert_eq!(
        raw.pointer(&pullback).unwrap()["binding"]["op"],
        "cotangent_pullback"
    );
    assert_eq!(raw.pointer(&pullback).unwrap()["binding"]["mode"], "saved");
    assert_eq!(
        raw.pointer(&cotangent).unwrap()["representation"],
        "cotangent"
    );
    assert_eq!(raw.pointer(&tape).unwrap()["representation"], "tape");
    let forged = |path: &str, value: Value| {
        let mut changed = raw.clone();
        *changed.pointer_mut(path).unwrap() = value;
        changed
    };
    // Tapes, fibers and certificates never come from the wire; unknown
    // operations, modes and representations are protocol errors.
    let mut extra = raw.clone();
    extra.pointer_mut(&linearize).unwrap()["binding"]["tape_value"] = json!({"steps": []});
    assert_wire_rejected(&kernel(extra, "emit"), "E_PROTOCOL");
    let mut extra = raw.clone();
    extra.pointer_mut(&dx).unwrap()["binding"]["index"] = json!(0);
    assert_wire_rejected(&kernel(extra, "emit"), "E_PROTOCOL");
    for (path, value) in [
        (format!("{pullback}/binding/mode"), json!("cached")),
        (format!("{pullback}/binding/mode"), json!(0)),
        (format!("{pullback}/binding/op"), json!("cotangent_")),
        (format!("{pullback}/binding/op"), json!("gradient")),
        (format!("{linearize}/binding/op"), json!("tape")),
        (format!("{linearize}/binding/op"), json!("tape_literal")),
        (format!("{dx}/binding/op"), json!("fiber_gradient")),
        (format!("{dx}/binding/coordinate"), json!(0)),
        (
            format!("{cotangent}/representation"),
            json!("cotangent_bundle"),
        ),
        (format!("{tape}/representation"), json!({"tape": []})),
    ] {
        assert_wire_rejected(&kernel(forged(&path, value), "emit"), "E_PROTOCOL");
    }
    // Consistent but wrong data is rejected by the checker with its own code.
    for (path, value, code) in [
        (
            format!("{differential}/binding/line/path"),
            json!(["Plane"]),
            "E_SMOOTH",
        ),
        (
            format!("{pullback}/binding/cotangent/path"),
            json!(["Tangent"]),
            "E_SMOOTH",
        ),
        (
            format!("{dx}/binding/coordinate"),
            json!("z"),
            "E_AFFINE_COORDINATE",
        ),
        (
            format!("{cotangent}/representation"),
            json!("tangent"),
            "E_SMOOTH",
        ),
        (format!("{tape}/representation"), json!("smooth"), "E_TYPE"),
        (
            format!("{linearize}/binding/tape/path"),
            json!(["Cotangent"]),
            "E_TYPE",
        ),
    ] {
        assert_wire_rejected(&kernel(forged(&path, value), "emit"), code);
    }
    // The recomputing mode is a different, equally valid binding.
    let recomputed = forged(&format!("{pullback}/binding/mode"), json!("recomputed"));
    assert_eq!(kernel(recomputed, "emit")["ok"], true);
}

// Metrics, evidence, flat and sharp (protocol 9). The differential needs no
// metric; a gradient is an ordinary function that applies sharp to it.

const METRIC_PROFILE: &str = include_str!("../examples/packages/smooth-metric/src/profile.vast");
const METRIC_MAIN: &str = include_str!("../examples/packages/smooth-metric/src/main.vast");

fn metric_fixture_with(profile: &str, main: &str) -> Scratch {
    let s = Scratch::empty("smooth metric");
    s.write(
        "Vastitas.toml",
        include_str!("../examples/packages/smooth-metric/Vastitas.toml"),
    );
    s.write("src/main.vast", main);
    s.write("src/profile.vast", profile);
    s
}

fn metric_fixture(main: &str) -> Scratch {
    metric_fixture_with(METRIC_PROFILE, main)
}

/// The metric example with extra items inserted before its helpers.
fn with_metric(extra: &str) -> String {
    assert!(METRIC_MAIN.contains("fn verdict("));
    METRIC_MAIN.replacen("fn verdict(", &format!("{extra}\nfn verdict("), 1)
}

/// The metric example with one declaration replaced.
fn replacing_metric(from: &str, to: &str) -> String {
    common::checked_replace(METRIC_MAIN, from, to)
}

#[track_caller]
fn rejects_metric(main: &str, code: &str) -> String {
    expect_code(&check(&metric_fixture(main)), code)
}

#[test]
fn metric_example_checks_builds_and_executes() {
    let s = metric_fixture(METRIC_MAIN);
    success(&check(&s));
    assert_eq!(run(&s), b"42\n");
}

#[test]
fn mutated_metric_observations_change_the_native_result() {
    // Code 3: the Skew gradient is (1, 0), not (1, 1).
    let main = common::checked_replace(
        METRIC_MAIN,
        "reads(gradient_skew(g(), p), 1, 0), 3)",
        "reads(gradient_skew(g(), p), 1, 1), 3)",
    );
    // Code 9: another Gram matrix lowers (5, -7) to (3, -9). The gradient of
    // dg is still (1, 0), so no other observation changes.
    let main = common::checked_replace(&main, "gram((2, 1), (1, 1))", "gram((2, 1), (1, 2))");
    // Code 4: with the Euclidean Gram matrix, Lorentz no longer flips dy.
    let main = common::checked_replace(&main, "gram((1, 0), (0, -1))", "gram((1, 0), (0, 1))");
    assert_eq!(run(&metric_fixture(&main)), b"58\n");
}

#[test]
fn metric_programs_lower_to_the_shared_smooth_runtime() {
    let raw = request(&metric_fixture(METRIC_MAIN));
    let emitted = kernel(&raw, "emit");
    assert_eq!(emitted["ok"], true, "{emitted}");
    let source = emitted["lean_source"].as_str().unwrap();
    for expected in [
        "import VastitasKernel.SmoothRuntime\n",
        // flat applies the declared Gram matrix of Skew.
        "(VastitasKernel.SmoothRuntime.flat ([[(mkRat (2 : Int) 1), (mkRat (1 : Int) 1)], [(mkRat (1 : Int) 1), (mkRat (1 : Int) 1)]] : VastitasKernel.SmoothRuntime.Matrix) ",
        // sharp applies the inverse that the kernel certified.
        "(VastitasKernel.SmoothRuntime.sharp ([[(mkRat (1 : Int) 1), (mkRat (-1 : Int) 1)], [(mkRat (-1 : Int) 1), (mkRat (2 : Int) 1)]] : VastitasKernel.SmoothRuntime.Matrix) ",
        "(VastitasKernel.SmoothRuntime.sharp ([[(mkRat (1 : Int) 1), (mkRat (0 : Int) 1)], [(mkRat (0 : Int) 1), (mkRat (-1 : Int) 1)]] : VastitasKernel.SmoothRuntime.Matrix) ",
        "(VastitasKernel.SmoothRuntime.differential ",
    ] {
        assert!(source.contains(expected), "{expected}\n{source}");
    }
    // Neither a gradient operation nor the Riemannian certificate reaches
    // the generated program.
    assert!(!source.contains("gradient"), "{source}");
    assert!(!source.contains("(mkRat (1 : Int) 2)"), "{source}");
}

#[test]
fn metric_declarations_reject_malformed_metrics_and_evidence_with_specific_codes() {
    for (from, to, code, message) in [
        (
            "gram((2, 1), (1, 1))",
            "gram((2, 1), (0, 1))",
            "E_METRIC",
            "the metric `Skew` is not symmetric",
        ),
        (
            "gram((2, 1), (1, 1))",
            "gram((2, 1, 0), (1, 1, 0), (0, 0, 1))",
            "E_METRIC",
            "needs 2 rows of 2 entries, but it has 3 rows",
        ),
        (
            "gram((2, 1), (1, 1))",
            "gram((2, 1), (1))",
            "E_METRIC",
            "needs 2 entries in each row, but row 2 has 1",
        ),
        (
            "gram((2, 1), (1, 1))",
            "gram((2, x), (x, 1))",
            "E_METRIC",
            "the Gram entry in row 1, column 2 is not constant",
        ),
        (
            "gram((2, 1), (1, 1))",
            "gram((2, z), (z, 1))",
            "E_AFFINE_COORDINATE",
            "unknown coordinate z",
        ),
        // diag(1, -1) has an inverse but no positive LDLᵀ factorization.
        (
            "indexed evidence SkewPositive = riemannian(Skew);",
            "indexed evidence SkewPositive = riemannian(Lorentz);",
            "E_METRIC",
            "the metric `Lorentz` is not positive definite, so it has no Riemannian evidence",
        ),
        (
            "indexed evidence SkewInvertible = nondegenerate(Skew);",
            "indexed evidence SkewInvertible = nondegenerate(Plane);",
            "E_METRIC",
            "evidence names a metric, but `Plane` is not a metric",
        ),
        // sharp with another metric's evidence, or with the wrong kind.
        (
            "using = Skew, evidence = SkewInvertible",
            "using = Skew, evidence = EuclidInvertible",
            "E_METRIC",
            "`sharp` uses the metric `Skew`, but the evidence `EuclidInvertible` certifies `Euclid`",
        ),
        (
            "using = Skew, evidence = SkewInvertible",
            "using = Skew, evidence = SkewPositive",
            "E_METRIC",
            "`sharp` needs nondegenerate evidence, but `SkewPositive` is Riemannian evidence",
        ),
        (
            "flat(Tangent, Cotangent, using = Skew)",
            "flat(Tangent, Cotangent, using = SkewInvertible)",
            "E_METRIC",
            "`flat` needs a metric after `using =`, but `SkewInvertible` is not a metric",
        ),
        (
            "flat(Tangent, Cotangent, using = Skew)",
            "flat(Cotangent, Cotangent, using = Skew)",
            "E_SMOOTH",
            "`flat` needs a tangent family, but `Cotangent` is a cotangent family",
        ),
        (
            "indexed metric Euclid: MetricForm<Plane> = euclidean;",
            "indexed metric Euclid: Cotangent<Plane> = euclidean;",
            "E_METRIC",
            "a metric is declared at a `metric_form` family, but `Cotangent` is not one",
        ),
        (
            "indexed metric Euclid: MetricForm<Plane> = euclidean;",
            "indexed metric Euclid: MetricForm<Plane, Line> = euclidean;",
            "E_METRIC",
            "a metric names one object",
        ),
        // A missing metric or missing evidence is a parse error: nothing is
        // ever selected by default, not even the Euclidean metric.
        (
            "flat(Tangent, Cotangent, using = Euclid)",
            "flat(Tangent, Cotangent)",
            "E_PARSE",
            "`flat` needs an explicit metric: write `using = …`",
        ),
        (
            "sharp(Cotangent, Tangent, using = Euclid, evidence = EuclidInvertible)",
            "sharp(Cotangent, Tangent, using = Euclid)",
            "E_PARSE",
            "`sharp` needs explicit nondegeneracy evidence: write `evidence = …`",
        ),
        (
            "sharp(Cotangent, Tangent, using = Euclid, evidence = EuclidInvertible)",
            "sharp(Cotangent, Tangent, evidence = EuclidInvertible)",
            "E_PARSE",
            "`sharp` needs an explicit metric: write `using = …`",
        ),
        (
            "indexed metric Euclid: MetricForm<Plane> = euclidean;",
            "indexed metric Euclid: MetricForm<Plane> = identity;",
            "E_TYPE",
            "a metric is `euclidean` or `gram((…), …)`",
        ),
        (
            "indexed evidence SkewPositive = riemannian(Skew);",
            "indexed evidence SkewPositive = positive(Skew);",
            "E_TYPE",
            "evidence is nondegenerate(metric) or riemannian(metric)",
        ),
    ] {
        let stderr = rejects_metric(&replacing_metric(from, to), code);
        assert!(stderr.contains(message), "{to}: {stderr}");
    }
    // diag(1, 0) is singular: it has no nondegenerate evidence.
    let stderr = rejects_metric(
        &with_metric(
            "indexed metric Diag10: MetricForm<Plane> = gram((1, 0), (0, 0));\nindexed evidence Bad = nondegenerate(Diag10);",
        ),
        "E_METRIC",
    );
    assert!(
        stderr.contains("the metric `Diag10` is singular, so it has no nondegenerate evidence"),
        "{stderr}"
    );
    // diag(1, -1) is accepted as nondegenerate: the example uses it.
    success(&check(&metric_fixture(METRIC_MAIN)));
    // A metric on a presented object is a foreign-object metric.
    let stderr = rejects_metric(
        &with_metric(&format!(
            "{PRESENTED}\nindexed metric Foreign: MetricForm<QLine> = euclidean;"
        )),
        "E_METRIC",
    );
    assert!(
        stderr.contains("the metric `Foreign` is on `QLine`, which is not a smooth object"),
        "{stderr}"
    );
    // Metric forms range over smooth objects only.
    rejects_metric(
        &with_metric(&format!(
            "{PRESENTED}\nindexed family BadForm(object(AffineScheme)) = metric_form constraints(canonical(0));"
        )),
        "E_TYPE",
    );
    rejects_metric(
        &with_metric(
            "indexed family BadForm(object(profile::CInfAffine)) = metric_form constraints();",
        ),
        "E_TYPE",
    );
}

#[test]
fn metric_selection_is_explicit_and_unambiguous() {
    // Two modules declare a metric named `Skew`. Importing both makes the
    // name ambiguous, so `using = Skew` is rejected before any metric is
    // selected; importing one selects that one.
    let profile = format!(
        "{METRIC_PROFILE}\npub indexed metric Skew: MetricForm<Plane> = gram((2, 1), (1, 1));"
    );
    let two_metrics = |imports: &str| {
        let main = common::checked_replace(
            METRIC_MAIN,
            "indexed metric Skew: MetricForm<Plane> = gram((2, 1), (1, 1));\n",
            "mod alt { pub indexed metric Skew: super::profile::MetricForm<super::profile::Plane> = gram((2, 1), (1, 1)); }\n",
        );
        common::checked_replace(
            &main,
            "use profile::pairing;\n",
            &format!("use profile::pairing;\n{imports}"),
        )
    };
    success(&check(&metric_fixture_with(
        &profile,
        &two_metrics("use alt::Skew;\n"),
    )));
    success(&check(&metric_fixture_with(
        &profile,
        &two_metrics("use profile::Skew;\n"),
    )));
    let stderr = expect_code(
        &check(&metric_fixture_with(
            &profile,
            &two_metrics("use profile::Skew;\nuse alt::Skew;\n"),
        )),
        "E_DUPLICATE",
    );
    assert!(stderr.contains("collision"), "{stderr}");
    // A metric named by path is that metric: evidence for another metric
    // with the same name does not certify it.
    let s = metric_fixture_with(
        &profile,
        &common::checked_replace(
            METRIC_MAIN,
            "using = Skew, evidence = SkewInvertible);",
            "using = profile::Skew, evidence = SkewInvertible);",
        ),
    );
    let stderr = expect_code(&check(&s), "E_METRIC");
    assert!(stderr.contains("certifies `Skew`"), "{stderr}");
}

#[test]
fn metric_operations_reject_wrong_objects_and_variances() {
    for (body, types) in [
        (
            "fn bad() -> Cotangent<Plane> { flat_skew(differential(g(), plane_at(1, 2))) }",
            "Cotangent<Plane>",
        ),
        (
            "fn bad() -> Tangent<Plane> { sharp_skew(vplane(plane_at(1, 2), 1, 0)) }",
            "Tangent<Plane>",
        ),
        (
            "indexed primitive vline = fiber_vector(Tangent, Smooth, Line);\nfn bad() -> Cotangent<Plane> { flat_skew(vline(line_at(1), 1)) }",
            "Tangent<Line>",
        ),
    ] {
        let stderr = rejects_metric(&with_metric(body), "E_ENDPOINT");
        assert!(stderr.contains(types), "{body}: {stderr}");
    }
    // flat returns a covector and sharp a vector.
    rejects_metric(
        &with_metric("fn bad() -> Tangent<Plane> { flat_skew(vplane(plane_at(1, 2), 1, 0)) }"),
        "E_TYPE",
    );
}

#[test]
fn metric_forms_select_protocol_nine_and_older_envelopes_reject_them() {
    let raw = request(&metric_fixture(METRIC_MAIN));
    assert_eq!(raw["version"], 9);
    assert_eq!(kernel(&raw, "emit")["ok"], true);
    for version in [7, 8] {
        let mut changed = raw.clone();
        changed["version"] = json!(version);
        assert_wire_rejected(&kernel(changed, "emit"), "E_PROTOCOL");
    }
}

#[test]
fn raw_wire_rejects_forged_metric_records() {
    let raw = request(&metric_fixture(METRIC_MAIN));
    let skew = declaration_pointer(&raw, "Skew");
    let euclid = declaration_pointer(&raw, "Euclid");
    let invertible = declaration_pointer(&raw, "SkewInvertible");
    let positive = declaration_pointer(&raw, "SkewPositive");
    let flat = declaration_pointer(&raw, "flat_skew");
    let sharp = declaration_pointer(&raw, "sharp_skew");
    assert_eq!(raw.pointer(&skew).unwrap()["kind"], "metric");
    assert_eq!(raw.pointer(&skew).unwrap()["gram"]["kind"], "gram");
    assert_eq!(raw.pointer(&euclid).unwrap()["gram"]["kind"], "euclidean");
    assert_eq!(
        raw.pointer(&invertible).unwrap()["evidence"],
        "nondegenerate"
    );
    assert_eq!(raw.pointer(&positive).unwrap()["evidence"], "riemannian");
    assert_eq!(raw.pointer(&flat).unwrap()["binding"]["op"], "flat");
    assert_eq!(raw.pointer(&sharp).unwrap()["binding"]["op"], "sharp");
    let identity = json!([["1", "0"], ["0", "1"]]);
    // Certificates and matrices never come from the wire.
    for (pointer, field) in [
        (invertible.clone(), "inverse"),
        (positive.clone(), "lower"),
        (positive.clone(), "pivots"),
        (skew.clone(), "inverse"),
        (format!("{euclid}/gram"), "rows"),
        (format!("{flat}/binding"), "gram"),
        (format!("{sharp}/binding"), "inverse"),
        (format!("{sharp}/binding"), "object"),
    ] {
        let mut extra = raw.clone();
        extra.pointer_mut(&pointer).unwrap()[field] = identity.clone();
        assert_wire_rejected(&kernel(extra, "emit"), "E_PROTOCOL");
    }
    let forged = |path: &str, value: Value| {
        let mut changed = raw.clone();
        *changed.pointer_mut(path).unwrap() = value;
        changed
    };
    for (path, value) in [
        (format!("{flat}/binding/op"), json!("gradient")),
        (format!("{flat}/binding/op"), json!("flat_")),
        (format!("{sharp}/binding/op"), json!("metric_sharp")),
        (format!("{invertible}/evidence"), json!("positive")),
        (format!("{euclid}/gram/kind"), json!("identity")),
        (format!("{skew}/gram/rows/0/0"), json!("2")),
    ] {
        assert_wire_rejected(&kernel(forged(&path, value), "emit"), "E_PROTOCOL");
    }
    // Consistent but wrong data is rejected by the checker with its own code.
    for (path, value, code) in [
        (
            format!("{skew}/gram/rows/1/0"),
            json!({"op": "natural", "value": "0"}),
            "E_METRIC",
        ),
        (
            format!("{positive}/metric/path"),
            json!(["Lorentz"]),
            "E_METRIC",
        ),
        (
            format!("{sharp}/binding/evidence/path"),
            json!(["SkewPositive"]),
            "E_METRIC",
        ),
        (
            format!("{sharp}/binding/evidence/path"),
            json!(["EuclidInvertible"]),
            "E_METRIC",
        ),
        (
            format!("{flat}/binding/metric/path"),
            json!(["Plane"]),
            "E_METRIC",
        ),
        (
            format!("{flat}/binding/tangent/path"),
            json!(["Cotangent"]),
            "E_SMOOTH",
        ),
    ] {
        assert_wire_rejected(&kernel(forged(&path, value), "emit"), code);
    }
}

/// A program that uses only the differential, with and without metric
/// declarations.
fn differential_program(with_metrics: bool) -> Scratch {
    let profile = if with_metrics {
        METRIC_PROFILE.to_string()
    } else {
        common::checked_replace(
            METRIC_PROFILE,
            "pub indexed family MetricForm(object(CInfAffine)) = metric_form constraints(canonical(0));\n",
            "",
        )
    };
    let metrics = if with_metrics {
        "use profile::MetricForm;
indexed metric Euclid: MetricForm<Plane> = euclidean;
indexed metric Skew: MetricForm<Plane> = gram((2, 1), (1, 1));
indexed evidence EuclidInvertible = nondegenerate(Euclid);
indexed evidence SkewInvertible = nondegenerate(Skew);
indexed evidence SkewPositive = riemannian(Skew);
indexed primitive flat_skew = flat(Tangent, Cotangent, using = Skew);
indexed primitive sharp_skew = sharp(Cotangent, Tangent, using = Skew, evidence = SkewInvertible);
indexed primitive sharp_euclid = sharp(Cotangent, Tangent, using = Euclid, evidence = EuclidInvertible);"
    } else {
        ""
    };
    let main = format!(
        "mod profile;
use profile::Smooth;
use profile::Cotangent;
use profile::Tangent;
use profile::Plane;
use profile::Line;
use profile::plane_at;
use profile::differential;
use profile::same_covector;
{metrics}
indexed primitive dplane = fiber_vector(Cotangent, Smooth, Plane);
indexed morphism g: Smooth<Plane, Line> = pullback(t -> x^2 + y);
fn main() -> Int {{
    if same_covector(differential(g(), plane_at(1, 2)), dplane(plane_at(1, 2), 2, 1)) {{ 42 }} else {{ 1 }}
}}
"
    );
    metric_fixture_with(&profile, &main)
}

#[test]
fn differential_is_unchanged_by_metric_declarations() {
    let free = differential_program(false);
    let metric = differential_program(true);
    let generated = |s: &Scratch| {
        let emitted = kernel(request(s), "emit");
        assert_eq!(emitted["ok"], true, "{emitted}");
        emitted["lean_source"].as_str().unwrap().to_owned()
    };
    let free_source = generated(&free);
    assert!(free_source.contains("(VastitasKernel.SmoothRuntime.differential "));
    assert_eq!(free_source, generated(&metric));
    assert_eq!(run(&free), b"42\n");
    assert_eq!(run(&metric), b"42\n");
}
