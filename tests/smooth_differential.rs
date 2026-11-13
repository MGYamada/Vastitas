//! Smooth objects and smooth maps through the public protocol-9 source path.
//! `Affine(n)[...]` declares a smooth real affine space; `Smooth<X, Y>` maps
//! are exact QQ polynomial maps. The kernel elaborates and checks every map;
//! these tests exercise acceptance, native execution, rejections, protocol
//! selection and forged wire. The last section runs the Stage 3 acceptance
//! program, `examples/packages/smooth-differential`.
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
fn objects_example_checks_builds_and_executes() {
    let s = fixture(MAIN);
    success(&check(&s));
    assert_eq!(run(&s), b"42\n");
}

#[test]
fn mutated_object_observations_change_the_native_result() {
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
fn object_forms_select_protocol_nine_and_older_envelopes_reject_them() {
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
        "smooth/affine/mod.vast",
        "metric/mod.vast",
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
fn a_right_intermediate_point_flips_the_failure_checks() {
    // With g(f(3)) = 18 and the right intermediate point, the detour succeeds:
    // codes 9 (it fails) and 21 (the identity keeps it a failure) flip.
    let main = common::checked_replace(
        COTANGENT_MAIN,
        "compose(f(), line_at(2)), dline(line_at(8), 1)",
        "compose(f(), line_at(3)), dline(line_at(18), 1)",
    );
    assert_eq!(run(&cotangent_fixture(&main)), b"72\n");
}

/// The lowered source of a program whose only pullback uses `binding`.
fn one_pullback_source(binding: &str) -> String {
    let main = format!(
        "mod profile;
use profile::Cotangent;
use profile::Smooth;
use profile::Line;
use profile::line_at;
use profile::lies_over;
use profile::{binding};
indexed primitive dline = fiber_vector(Cotangent, Smooth, Line);
indexed morphism sq: Smooth<Line, Line> = pullback(t -> t^2);
fn main() -> Int {{ if lies_over({binding}(sq(), line_at(3), dline(line_at(9), 1)), line_at(3)) {{ 42 }} else {{ 0 }} }}
"
    );
    let s = cotangent_fixture(&main);
    assert_eq!(run(&s), b"42\n");
    let emitted = kernel(request(&s), "emit");
    assert_eq!(emitted["ok"], true, "{emitted}");
    emitted["lean_source"].as_str().unwrap().to_string()
}

#[test]
fn each_pullback_binding_compiles_to_its_own_residual_policy() {
    // The kernel compiles the pullback along the declared map sq into Core
    // (#623): a generated backward function `f_1`, placed first among the
    // functions, with one Jacobian step. The module declares the map of sq
    // and its Jacobian table once, as `map_0` and `jacobian_0`, before its
    // functions. Saved, the caller evaluates sq(3) and passes both points
    // and the seed; recomputed, it passes the input point and the seed, and
    // the function evaluates sq(3) again. Neither runs the runtime reverse
    // pass.
    for (binding, parameters, caller_images, function_images) in
        [("pullback", 3, 1, 0), ("pullback_recomputed", 2, 0, 1)]
    {
        let source = one_pullback_source(binding);
        assert!(!source.contains("PullbackMode"), "{binding}: {source}");
        let definitions = common::lean_definitions(&source);
        let names: Vec<&str> = definitions.iter().map(|(name, _)| *name).collect();
        assert_eq!(
            names,
            ["map_0", "jacobian_0", "f_1", "f_0", "main"],
            "{binding}: {source}"
        );
        let (generated, caller) = (definitions[2].1, definitions[3].1);
        let header = generated.lines().next().unwrap();
        assert_eq!(header.matches(" (v_").count(), parameters, "{header}");
        assert_eq!(
            generated
                .matches("(VastitasKernel.SmoothRuntime.jacobianStep 1 jacobian_0 ")
                .count(),
            1,
            "{generated}"
        );
        assert_eq!(
            generated.matches("SmoothRuntime.applyPoint ").count(),
            function_images,
            "{binding}: {generated}"
        );
        assert_eq!(
            caller.matches("SmoothRuntime.applyPoint ").count(),
            caller_images,
            "{binding}: {caller}"
        );
        assert_eq!(caller.matches("(f_1 ").count(), 1, "{caller}");
    }
}

#[test]
fn cotangent_programs_lower_to_the_shared_smooth_runtime() {
    let raw = request(&cotangent_fixture(COTANGENT_MAIN));
    let emitted = kernel(&raw, "emit");
    assert_eq!(emitted["ok"], true, "{emitted}");
    let source = emitted["lean_source"].as_str().unwrap();
    for expected in [
        "import VastitasKernel.SmoothRuntime\n",
        // Every reverse pass is compiled into Core (#623): the forward images
        // and the Jacobian steps along the declared maps.
        "(VastitasKernel.SmoothRuntime.applyPoint ",
        "(VastitasKernel.SmoothRuntime.jacobianStep ",
        // The composite as one map is a step whose structure the compilation
        // does not open: the runtime reverse pass, with saved forward values.
        "(VastitasKernel.SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.saved ",
        "(VastitasKernel.SmoothRuntime.vector ",
        "(VastitasKernel.SmoothRuntime.component ",
        "(VastitasKernel.SmoothRuntime.pairing ",
        "(VastitasKernel.SmoothRuntime.fiberAt ",
        "(VastitasKernel.SmoothRuntime.fiberEqual ",
        ": (Option VastitasKernel.SmoothRuntime.Fiber)",
    ] {
        assert!(source.contains(expected), "{expected}\n{source}");
    }
    // No pass runs the routines that the compiled Core replaces.
    for absent in [
        "SmoothRuntime.PullbackMode.recomputed",
        "SmoothRuntime.differential ",
        "SmoothRuntime.linearize ",
        "SmoothRuntime.backward ",
    ] {
        assert!(!source.contains(absent), "{absent}\n{source}");
    }
}

// Stack safety of the smooth runtime (#630). A short program builds a chain of
// 2^18 `compose` nodes, a composite with an exponent of 2^18 or a composite of
// more than 10^5 terms. The runtime must run them in constant native stack: a
// recursion per node, per unit of the exponent or per term aborts with a
// stack overflow.

/// `{name}0` applies `step` to its parameter `p`, and `{name}{k}` applies
/// `{name}{k-1}` twice, so `{name}{k}` applies `step` 2^k times.
fn doubling(name: &str, step: &str, levels: usize) -> String {
    let kind = "Smooth<Line, Line>";
    let mut source = format!("fn {name}0(p: {kind}) -> {kind} {{ {step} }}\n");
    for level in 1..=levels {
        let half = format!("{name}{}", level - 1);
        source.push_str(&format!(
            "fn {name}{level}(p: {kind}) -> {kind} {{ {half}({half}(p)) }}\n"
        ));
    }
    source
}

/// A program over the cotangent profile with `items` before `main`.
fn stack_program(items: &str, main: &str) -> Scratch {
    cotangent_fixture(&format!(
        "mod profile;
use profile::SmoothR;
use profile::Smooth;
use profile::Cotangent;
use profile::Tape;
use profile::Pt;
use profile::Line;
use profile::Plane;
use profile::compose;
use profile::composite;
use profile::line_at;
use profile::pullback;
use profile::pullback_recomputed;
use profile::differential;
use profile::linearize;
use profile::backward;
use profile::lies_over;
use profile::same_covector;
indexed primitive same = smooth_equal(Smooth);
indexed primitive dline = fiber_vector(Cotangent, Smooth, Line);
indexed primitive dt = fiber_component(Cotangent, Line, t);
indexed morphism sq: Smooth<Line, Line> = pullback(t -> t^2);
indexed morphism idL: Smooth<Line, Line> = identity;
fn verdict(ok: Bool, code: Int) -> Int {{ if ok {{ 0 }} else {{ code }} }}
{items}
fn main() -> Int {{
{main}
}}
"
    ))
}

#[test]
fn a_chain_of_two_to_the_eighteen_nodes_runs_in_constant_native_stack() {
    // `before18(sq())` puts 2^18 identity nodes after sq, each new node the
    // `after` of a `compose`: the chain is deep in `before`. `after18(sq())`
    // puts them before sq: the chain is deep in `after`. The recomputing
    // reverse pass evaluates `before` again at every node, so it is quadratic
    // on a chain that is deep in `before`; it runs that shape with 2^10 nodes
    // only, and the deep-`after` chain, on which it is linear, with 2^18.
    let items = format!(
        "{}{}
// A tape that reaches `backward` through a function: no reverse site reads it,
// so the program calls the runtime `linearize` and `backward`.
fn tape_of(map: Smooth<Line, Line>, point: Smooth<Pt, Line>) -> Tape<Line, Line> {{ linearize(map, point) }}
fn through(tape: Tape<Line, Line>, seed: Cotangent<Line>) -> Cotangent<Line> {{ backward(tape, seed) }}",
        doubling("before", "compose(idL(), p)", 18),
        doubling("after", "compose(p, idL())", 18),
    );
    let main = "    let deepBefore: Smooth<Line, Line> = before18(sq());
    let deepAfter: Smooth<Line, Line> = after18(sq());
    let x: Smooth<Pt, Line> = line_at(3);
    // dt at sq(3) = 9; its pullback along either chain is 6 dt at 3.
    let seed: Cotangent<Line> = dline(line_at(9), 1);
    let six: Cotangent<Line> = dline(x, 6);
    pair_first(dt(pullback(deepBefore, x, seed)))
       // Forward evaluation of both shapes.
       + verdict(lies_over(dline(compose(deepBefore, x), 1), line_at(9)), 1)
       + verdict(lies_over(dline(compose(deepAfter, x), 1), line_at(9)), 2)
       // The saved mode, on both shapes.
       + verdict(same_covector(pullback(deepBefore, x, seed), six), 3)
       + verdict(same_covector(pullback(deepAfter, x, seed), six), 4)
       // The recomputing mode.
       + verdict(same_covector(pullback_recomputed(deepAfter, x, seed), six), 5)
       + verdict(same_covector(pullback_recomputed(before10(sq()), x, seed), six), 6)
       // The first-class tape and the differential.
       + verdict(same_covector(backward(linearize(deepBefore, x), seed), six), 7)
       + verdict(same_covector(through(tape_of(deepBefore, x), seed), six), 8)
       + verdict(same_covector(through(tape_of(deepAfter, x), seed), six), 9)
       + verdict(same_covector(differential(deepAfter, x), six), 10)
       // The map each chain denotes, and the composite as one map.
       + verdict(same(deepBefore, sq()), 11)
       + verdict(same(deepAfter, deepBefore), 12)
       + verdict(same(composite(deepBefore), sq()), 13)
       + verdict(same_covector(pullback(composite(deepAfter), x, seed), six), 14)";
    let s = stack_program(&items, main);
    success(&check(&s));
    // The chains are function results, so every pass over them is the runtime
    // routine: no compiled reverse Core replaces it.
    let emitted = kernel(request(&s), "emit");
    assert_eq!(emitted["ok"], true, "{emitted}");
    let source = emitted["lean_source"].as_str().unwrap();
    for expected in [
        "SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.saved ",
        "SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.recomputed ",
        "SmoothRuntime.applyPoint ",
        "SmoothRuntime.linearize ",
        "SmoothRuntime.backward ",
        "SmoothRuntime.same ",
        "SmoothRuntime.composite ",
    ] {
        assert!(source.contains(expected), "{expected}\n{source}");
    }
    assert_eq!(run(&s), b"6\n");
}

#[test]
fn a_composite_with_exponent_two_to_the_eighteen_runs_in_constant_native_stack() {
    // sq composed 18 times is t |-> t^262144. As one map, its value and its
    // derivative raise the coordinate to the powers 262144 and 262143.
    let power = (1..18).fold("sq()".to_string(), |inner, _| {
        format!("compose(sq(), {inner})")
    });
    let main = format!(
        "    let power: Smooth<Line, Line> = {power};
    let whole: Smooth<Line, Line> = composite(power);
    let one: Smooth<Pt, Line> = line_at(1);
    let two: Smooth<Pt, Line> = line_at(2);
    let top: Cotangent<Line> = dline(compose(power, two), 1);
    // At 1 the pullback of dt is the exponent.
    pair_first(dt(pullback(whole, one, dline(one, 1))))
       // At 2 the composite agrees with the 18 squarings pulled back one at a time.
       + verdict(same_covector(pullback(whole, two, top), pullback(power, two, top)), 1)
       + verdict(same_covector(pullback_recomputed(whole, two, top), pullback(power, two, top)), 2)
       + verdict(lies_over(dline(compose(whole, two), 1), compose(power, two)), 3)"
    );
    let s = stack_program("", &main);
    success(&check(&s));
    assert_eq!(run(&s), b"262144\n");
}

#[test]
fn nineteen_squarings_nested_on_the_left_denote_one_map_in_constant_native_stack() {
    // ((sq . sq) . sq) . ... substitutes t^2 into t^(2^k) at step k: the last
    // step raises t^2 to the power 2^18. Nested on the right, every step
    // squares instead.
    let left = (1..19).fold("sq()".to_string(), |inner, _| {
        format!("compose({inner}, sq())")
    });
    let right = (1..19).fold("sq()".to_string(), |inner, _| {
        format!("compose(sq(), {inner})")
    });
    let main = format!(
        "    let left: Smooth<Line, Line> = {left};
    let right: Smooth<Line, Line> = {right};
    42 + verdict(same(left, left), 1)
       + verdict(same(left, right), 2)
       + verdict(same(composite(left), right), 3)
       + verdict(!same(left, compose(right, sq())), 4)"
    );
    let s = stack_program("", &main);
    success(&check(&s));
    assert_eq!(run(&s), b"42\n");
}

/// The sum of the monomials of degree at most `degree` in three coordinates.
fn monomials(coordinates: [&str; 3], degree: u32) -> String {
    let mut terms = Vec::new();
    for first in 0..=degree {
        for second in 0..=degree - first {
            for third in 0..=degree - first - second {
                let factors: Vec<String> = coordinates
                    .iter()
                    .zip([first, second, third])
                    .filter(|(_, exponent)| *exponent > 0)
                    .map(|(coordinate, exponent)| format!("{coordinate}^{exponent}"))
                    .collect();
                terms.push(if factors.is_empty() {
                    "1".to_string()
                } else {
                    factors.join("*")
                });
            }
        }
    }
    terms.join(" + ")
}

#[test]
fn a_composite_with_more_than_a_hundred_thousand_terms_runs_in_constant_native_stack() {
    // The product of 286 monomials in a, b, c and 455 monomials in d, e, f has
    // 130130 terms, one per pair. Both factors are within the 512 terms of a
    // declared image; the composite as one map is not, and the runtime merges,
    // evaluates and differentiates it term by term.
    let items = format!(
        "indexed affine Space(SmoothR) = Affine(6)[a, b, c, d, e, f];
indexed primitive space_at = smooth_int_point(Smooth, Space, Pt);
indexed morphism factors: Smooth<Space, Plane> = pullback(x -> {}, y -> {});
indexed morphism times: Smooth<Plane, Line> = pullback(t -> x*y);
// The composite as one map against the two declared maps, at one point.
fn agrees(whole: Smooth<Space, Line>, product: Smooth<Space, Line>, p: Smooth<Pt, Space>) -> Bool {{
    let top: Cotangent<Line> = dline(compose(product, p), 1);
    same(whole, product)
        && lies_over(dline(compose(whole, p), 1), compose(product, p))
        && same_covector(pullback(whole, p, top), pullback(product, p, top))
}}",
        monomials(["a", "b", "c"], 10),
        monomials(["d", "e", "f"], 12),
    );
    let main = "    let product: Smooth<Space, Line> = compose(times(), factors());
    if agrees(composite(product), product, space_at(1, -1, 2, 1, 2, -1)) { 42 } else { 0 }";
    let s = stack_program(&items, main);
    success(&check(&s));
    assert_eq!(run(&s), b"42\n");
}

#[test]
fn cotangent_operations_reject_wrong_objects_variances_and_points() {
    // When no operand role is at fault, the endpoint error lists the operand
    // types. Role failures are covered by smooth_endpoint_errors_name_the_failing_role.
    for (label, body, types) in [
        (
            "a point whose source object is 1-dimensional",
            "fn bad() -> Bool { lies_over(pullback(sq(), sq(), dline(line_at(9), 1)), line_at(3)) }",
            "Smooth<Line, Line>, Smooth<Line, Line>, Cotangent<Line>",
        ),
        (
            "a covector in the point slot",
            "fn bad() -> Bool { lies_over(pullback(sq(), dline(line_at(3), 1), dline(line_at(9), 1)), line_at(3)) }",
            "Smooth<Line, Line>, Cotangent<Line>, Cotangent<Line>",
        ),
    ] {
        let stderr = rejects_cotangent(&with_cotangent(body), "E_ENDPOINT");
        assert!(stderr.contains(types), "{label}: {stderr}");
    }
    // An operand with one index in a slot from which the checker reads the
    // result's objects (the map of a pullback, the tape of a backward pass) is
    // a type error.
    for body in [
        "fn bad() -> Bool { lies_over(backward(dline(line_at(3), 1), dline(line_at(9), 1)), line_at(3)) }",
        "fn bad() -> Bool { lies_over(pullback(dline(line_at(3), 1), line_at(3), dline(line_at(9), 1)), line_at(3)) }",
    ] {
        let stderr = rejects_cotangent(&with_cotangent(body), "E_TYPE");
        assert!(
            stderr.contains("primitive operand shape mismatch"),
            "{body}: {stderr}"
        );
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
        // The module declares each distinct matrix once, in declaration
        // order (#629). Euclid's Gram matrix is its own inverse, so
        // flat_euclid and sharp_euclid name one declaration.
        "def matrix_0 : VastitasKernel.SmoothRuntime.Matrix :=\n  ([[(mkRat (1 : Int) 1), (mkRat (0 : Int) 1)], [(mkRat (0 : Int) 1), (mkRat (1 : Int) 1)]] : VastitasKernel.SmoothRuntime.Matrix)\n",
        // flat applies the declared Gram matrix of Skew.
        "def matrix_1 : VastitasKernel.SmoothRuntime.Matrix :=\n  ([[(mkRat (2 : Int) 1), (mkRat (1 : Int) 1)], [(mkRat (1 : Int) 1), (mkRat (1 : Int) 1)]] : VastitasKernel.SmoothRuntime.Matrix)\n",
        "(VastitasKernel.SmoothRuntime.flat matrix_1 ",
        // sharp applies the inverse that the kernel certified.
        "def matrix_2 : VastitasKernel.SmoothRuntime.Matrix :=\n  ([[(mkRat (1 : Int) 1), (mkRat (-1 : Int) 1)], [(mkRat (-1 : Int) 1), (mkRat (2 : Int) 1)]] : VastitasKernel.SmoothRuntime.Matrix)\n",
        "(VastitasKernel.SmoothRuntime.sharp matrix_2 ",
        "def matrix_3 : VastitasKernel.SmoothRuntime.Matrix :=\n  ([[(mkRat (1 : Int) 1), (mkRat (0 : Int) 1)], [(mkRat (0 : Int) 1), (mkRat (-1 : Int) 1)]] : VastitasKernel.SmoothRuntime.Matrix)\n",
        "(VastitasKernel.SmoothRuntime.sharp matrix_3 ",
        "(VastitasKernel.SmoothRuntime.sharp matrix_0 (VastitasKernel.SmoothRuntime.flat matrix_0 ",
        // The differential is compiled into Core (#623): a Jacobian step
        // along the declared g, and the runtime reverse pass along the parameter h
        // of each gradient function.
        "(VastitasKernel.SmoothRuntime.jacobianStep ",
    ] {
        assert!(source.contains(expected), "{expected}\n{source}");
    }
    // The five flat calls and the five sharp calls name four matrices, and
    // the calls of g name one map: no call repeats a literal.
    let count = |text: &str| source.matches(text).count();
    assert_eq!(count("(VastitasKernel.SmoothRuntime.flat matrix_"), 5);
    assert_eq!(count("(VastitasKernel.SmoothRuntime.sharp matrix_"), 5);
    assert_eq!(count(": VastitasKernel.SmoothRuntime.Matrix)"), 4);
    assert!(count("(VastitasKernel.SmoothRuntime.Program.primitive map_0)") > 1);
    assert_eq!(count("(VastitasKernel.AlgebraRuntime.Map.mk "), 1);
    assert!(!source.contains("SmoothRuntime.differential "), "{source}");
    assert_eq!(
        source
            .matches("(VastitasKernel.SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.saved ")
            .count(),
        3,
        "{source}"
    );
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
            "the metric `smooth_metric::Skew` is not symmetric",
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
            "the metric `smooth_metric::Lorentz` is not positive definite, so it has no Riemannian evidence",
        ),
        (
            "indexed evidence SkewInvertible = nondegenerate(Skew);",
            "indexed evidence SkewInvertible = nondegenerate(Plane);",
            "E_METRIC",
            "evidence names a metric, but `smooth_metric::profile::Plane` is not a metric",
        ),
        // sharp with another metric's evidence, or with the wrong kind.
        (
            "using = Skew, evidence = SkewInvertible",
            "using = Skew, evidence = EuclidInvertible",
            "E_METRIC",
            "`sharp` uses the metric `smooth_metric::Skew`, but the evidence `smooth_metric::EuclidInvertible` certifies `smooth_metric::Euclid`",
        ),
        (
            "using = Skew, evidence = SkewInvertible",
            "using = Skew, evidence = SkewPositive",
            "E_METRIC",
            "`sharp` needs nondegenerate evidence, but `smooth_metric::SkewPositive` is Riemannian evidence",
        ),
        (
            "flat(Tangent, Cotangent, using = Skew)",
            "flat(Tangent, Cotangent, using = SkewInvertible)",
            "E_METRIC",
            "`flat` needs a metric after `using =`, but `smooth_metric::SkewInvertible` is not a metric",
        ),
        (
            "flat(Tangent, Cotangent, using = Skew)",
            "flat(Cotangent, Cotangent, using = Skew)",
            "E_SMOOTH",
            "`flat` needs a tangent family, but `Cotangent` is a cotangent family",
        ),
        // A family that is not a tangent or cotangent family fails the
        // declaration audit.
        (
            "flat(Tangent, Cotangent, using = Skew)",
            "flat(Smooth, Cotangent, using = Skew)",
            "E_TYPE",
            "",
        ),
        (
            "indexed metric Euclid: MetricForm<Plane> = euclidean;",
            "indexed metric Euclid: Cotangent<Plane> = euclidean;",
            "E_METRIC",
            "a metric is declared at a `metric_form` family, but `smooth_metric::profile::Cotangent` is not one",
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
        stderr.contains(
            "the metric `smooth_metric::Diag10` is singular, so it has no nondegenerate evidence"
        ),
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
        stderr.contains(
            "the metric `smooth_metric::Foreign` is on `smooth_metric::QLine`, which is not a smooth object"
        ),
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

/// A 64-digit decimal literal.
const BIG: &str = "1000000000000000000000000000000000000000000000000000000000000007";

#[test]
fn oversized_gram_entries_are_rejected_before_any_certificate() {
    // (L^16)^16 has about 54,000 bits. The kernel bounds each entry before
    // it computes the inverse and the L D L^T factorization. The matrix
    // diag((L^16)^16, 0) is singular, and the example declares nondegenerate
    // and Riemannian evidence for it: a certificate computed before the
    // entry bound would report E_METRIC.
    let started = std::time::Instant::now();
    let stderr = rejects_metric(
        &replacing_metric(
            "gram((2, 1), (1, 1))",
            &format!("gram((({BIG}^16)^16, 0), (0, 0))"),
        ),
        "E_LIMIT",
    );
    assert!(
        stderr.contains("the Gram entry in row 1, column 1 has more than 512 bits"),
        "{stderr}"
    );
    assert!(started.elapsed() < std::time::Duration::from_secs(30));
    // The same singular matrix with a small entry reaches the certificate.
    let stderr = rejects_metric(
        &replacing_metric("gram((2, 1), (1, 1))", "gram((2, 0), (0, 0))"),
        "E_METRIC",
    );
    assert!(
        stderr.contains(
            "the metric `smooth_metric::Skew` is singular, so it has no nondegenerate evidence"
        ),
        "{stderr}"
    );
}

/// A dense symmetric 16 × 16 Gram matrix whose 136 independent entries have
/// pairwise distinct denominators. The entry in row i and column j ≥ i is a
/// product of `factors` fractions. Each has a denominator d of `digits`
/// digits, 10^(digits − 1) plus a small odd number of its own, and is
/// (9d + 1)/d on the diagonal and 1/d elsewhere. So the matrix is diagonally
/// dominant, and it is positive definite. With `singular`, row and column 15
/// repeat row and column 0.
fn distinct_gram(digits: usize, factors: usize, singular: bool) -> String {
    let fold = |i: usize| if singular && i == 15 { 0 } else { i };
    let pad = digits - 1;
    let rows: Vec<String> = (0..16)
        .map(|i| {
            let entries: Vec<String> = (0..16)
                .map(|j| {
                    let (low, high) = (fold(i).min(fold(j)), fold(i).max(fold(j)));
                    let fractions: Vec<String> = (0..factors)
                        .map(|factor| {
                            let odd = 2 * (16 * low + high) + 1 + 512 * factor;
                            if low == high {
                                format!("frac(9{:0pad$}, 1{odd:0pad$})", 9 * odd + 1)
                            } else {
                                format!("frac(1, 1{odd:0pad$})")
                            }
                        })
                        .collect();
                    fractions.join(" * ")
                })
                .collect();
            format!("({})", entries.join(", "))
        })
        .collect();
    format!("gram({})", rows.join(", "))
}

/// The object `Big` of dimension 16.
fn big_object() -> String {
    let coordinates: Vec<String> = (0..16).map(|i| format!("c{i}")).collect();
    format!(
        "indexed affine Big(profile::SmoothR) = Affine(16)[{}];",
        coordinates.join(", ")
    )
}

/// A metric `name` on `Big` with `copies` evidence declarations of each kind
/// in `kinds`.
fn metric_with_evidence(name: &str, gram: &str, kinds: &[&str], copies: usize) -> String {
    let mut declarations = format!("indexed metric {name}: MetricForm<Big> = {gram};");
    for kind in kinds {
        for copy in 0..copies {
            declarations.push_str(&format!(
                "\nindexed evidence {name}_{kind}_{copy} = {kind}({name});"
            ));
        }
    }
    declarations
}

const BOTH_KINDS: [&str; 2] = ["nondegenerate", "riemannian"];
const MATRIX_LIMIT: &str = "exceeds the matrix limit: the product of the norms of its rows, cleared of denominators, and of its largest row denominator has more than 16384 bits";

#[test]
fn a_dense_metric_on_sixteen_coordinates_is_certified_within_the_bound() {
    // Both matrices are diagonally dominant, so each is positive definite and
    // has both kinds of evidence.
    // `Shared` has L * L on the diagonal and 1 / L elsewhere. With one
    // denominator its certificates are small, and its matrix bound is 10,255
    // of the 16,384 bits of `metricMatrixBits`.
    let rows: Vec<String> = (0..16)
        .map(|i| {
            let entries: Vec<String> = (0..16)
                .map(|j| {
                    if i == j {
                        format!("{BIG} * {BIG}")
                    } else {
                        format!("frac(1, {BIG})")
                    }
                })
                .collect();
            format!("({})", entries.join(", "))
        })
        .collect();
    // `Distinct` has pairwise distinct 19-digit denominators, and its matrix
    // bound is 15,961 bits. Its certificates have entries of about that
    // size, so it is close to the largest work that the bound admits. The
    // check takes about 7 seconds on a development machine.
    let declarations = [
        big_object(),
        metric_with_evidence(
            "Shared",
            &format!("gram({})", rows.join(", ")),
            &BOTH_KINDS,
            1,
        ),
        metric_with_evidence("Distinct", &distinct_gram(19, 1, false), &BOTH_KINDS, 1),
    ]
    .join("\n");
    let started = std::time::Instant::now();
    success(&check(&metric_fixture(&with_metric(&declarations))));
    assert!(started.elapsed() < std::time::Duration::from_secs(120));
}

#[test]
fn a_dense_metric_beyond_the_matrix_bound_is_rejected_before_any_certificate() {
    // Every entry is within `metricEntryBits`, and both kinds of evidence are
    // declared. With products of two fractions with distinct 63-digit
    // denominators the matrix bound is 110,817 bits. Without that bound, the
    // two certificates of this matrix take about two minutes. With distinct
    // 20-digit denominators the matrix bound is 16,801 bits, one digit beyond
    // the matrix that the test above certifies.
    for (digits, factors) in [(63, 2), (20, 1)] {
        let declarations = [
            big_object(),
            metric_with_evidence(
                "Dense",
                &distinct_gram(digits, factors, false),
                &BOTH_KINDS,
                1,
            ),
        ]
        .join("\n");
        let started = std::time::Instant::now();
        let stderr = rejects_metric(&with_metric(&declarations), "E_LIMIT");
        assert!(
            stderr.contains(&format!(
                "the Gram matrix of the metric `smooth_metric::Dense` {MATRIX_LIMIT}"
            )),
            "{stderr}"
        );
        assert!(started.elapsed() < std::time::Duration::from_secs(30));
    }
}

#[test]
fn a_singular_metric_beyond_the_matrix_bound_is_a_limit_error_not_a_metric_error() {
    // Rows 1 and 16 are equal, so the matrix has no inverse. A certificate
    // computed before the matrix bound would report E_METRIC.
    let oversized = [
        big_object(),
        metric_with_evidence("Dense", &distinct_gram(63, 1, true), &["nondegenerate"], 1),
    ]
    .join("\n");
    let started = std::time::Instant::now();
    let stderr = rejects_metric(&with_metric(&oversized), "E_LIMIT");
    assert!(stderr.contains(MATRIX_LIMIT), "{stderr}");
    assert!(started.elapsed() < std::time::Duration::from_secs(30));
    // The same singular matrix with 5-digit denominators is within the
    // bound, and it reaches the certificate.
    let small = [
        big_object(),
        metric_with_evidence("Dense", &distinct_gram(5, 1, true), &["nondegenerate"], 1),
    ]
    .join("\n");
    let stderr = rejects_metric(&with_metric(&small), "E_METRIC");
    assert!(
        stderr.contains(
            "the metric `smooth_metric::Dense` is singular, so it has no nondegenerate evidence"
        ),
        "{stderr}"
    );
}

#[test]
fn repeated_evidence_shares_one_certificate_and_one_check() {
    // 48 evidence declarations of each kind for one dense metric with
    // distinct 12-digit denominators. The kernel computes one certificate for
    // each kind, and each audit of the declarations checks it once: the
    // check takes about 4 seconds on a development machine. With a
    // certificate and a check for each declaration it takes about 3 minutes.
    let declarations = [
        big_object(),
        metric_with_evidence("Dense", &distinct_gram(12, 1, false), &BOTH_KINDS, 48),
    ]
    .join("\n");
    let started = std::time::Instant::now();
    success(&check(&metric_fixture(&with_metric(&declarations))));
    assert!(started.elapsed() < std::time::Duration::from_secs(120));
}

#[test]
fn metric_selection_is_explicit_and_unambiguous() {
    // Two modules declare a metric named `Skew`: the profile's is Euclidean,
    // and `alt`'s has the Gram matrix ((2, 1), (1, 1)). Importing one selects
    // that one, so the gradient of x^2 + y at (1, 2) is (2, 1) or (1, 0).
    // Importing both makes `using = Skew` ambiguous, and it is rejected
    // before any metric is selected.
    let profile =
        format!("{METRIC_PROFILE}\npub indexed metric Skew: MetricForm<Plane> = euclidean;");
    let two_metrics = |imports: &str| {
        let main = common::checked_replace(
            METRIC_MAIN,
            "indexed metric Skew: MetricForm<Plane> = gram((2, 1), (1, 1));\n",
            "mod alt { pub indexed metric Skew: super::profile::MetricForm<super::profile::Plane> = gram((2, 1), (1, 1)); }\n",
        );
        let main = common::checked_replace(
            &main,
            "use profile::pairing;\n",
            &format!("use profile::pairing;\n{imports}"),
        );
        // The program prints the Skew gradient as 10 for (1, 0) or 21 for (2, 1).
        common::checked_replace(
            &main,
            "fn main() -> Int {",
            "fn main() -> Int {
    let probe: Tangent<Plane> = gradient_skew(g(), plane_at(1, 2));
    if reads(probe, 1, 0) { 10 } else { if reads(probe, 2, 1) { 21 } else { 0 } }
}

fn observations() -> Int {",
        )
    };
    assert_eq!(
        run(&metric_fixture_with(
            &profile,
            &two_metrics("use alt::Skew;\n")
        )),
        b"10\n"
    );
    assert_eq!(
        run(&metric_fixture_with(
            &profile,
            &two_metrics("use profile::Skew;\n")
        )),
        b"21\n"
    );
    let stderr = expect_code(
        &check(&metric_fixture_with(
            &profile,
            &two_metrics("use profile::Skew;\nuse alt::Skew;\n"),
        )),
        "E_DUPLICATE",
    );
    // The second `use` has the place of the error, and the first a note (#747).
    assert!(
        stderr.contains(
            "main.vast:19:1: E_DUPLICATE: 'Skew' is already the name of an import of this module"
        ) && stderr.contains("main.vast:18:1: note: first declaration is here"),
        "{stderr}"
    );
    // A metric named by path is that metric: evidence for the other metric
    // with the same short name does not certify it, and the message tells
    // the two apart by their full names.
    let s = metric_fixture_with(
        &profile,
        &common::checked_replace(
            METRIC_MAIN,
            "using = Skew, evidence = SkewInvertible);",
            "using = profile::Skew, evidence = SkewInvertible);",
        ),
    );
    let stderr = expect_code(&check(&s), "E_METRIC");
    assert!(
        stderr.contains(
            "`sharp` uses the metric `smooth_metric::profile::Skew`, but the evidence \
             `smooth_metric::SkewInvertible` certifies `smooth_metric::Skew`"
        ),
        "{stderr}"
    );
}

#[test]
fn metric_operations_reject_wrong_objects_and_variances() {
    // Wrong operand objects and variances are E_ENDPOINT role failures, covered
    // by smooth_endpoint_errors_name_the_failing_role. flat returns a covector,
    // so expecting a vector from it is a type error.
    rejects_metric(
        &with_metric("fn bad() -> Tangent<Plane> { flat_skew(vplane(plane_at(1, 2), 1, 0)) }"),
        "E_TYPE",
    );
}

/// The E_ENDPOINT explainer names the failing operand role of each smooth,
/// fiber and metric primitive: its family first, then its objects.
#[test]
fn smooth_endpoint_errors_name_the_failing_role() {
    for (body, message) in [
        (
            "fn bad() -> Bool { same(compose(f(), f()), gf()) }",
            "compose requires a second map with target Line (the first map's source), but the supplied second map has target Plane",
        ),
        (
            "fn bad() -> Bool { same(f(), g()) }",
            "same requires a second map with source Line (the first map's source), but the supplied second map has source Plane",
        ),
    ] {
        let stderr = rejects(&with(body), "E_ENDPOINT");
        assert!(stderr.contains(message), "{body}: {stderr}");
    }
    for (body, message) in [
        (
            "fn bad() -> Bool { lies_over(pullback(g(), plane_at(3, 9), dplane(plane_at(3, 9), 1, 0)), plane_at(3, 9)) }",
            "pullback requires a seed with object Line (the map's target), but the supplied seed has object Plane",
        ),
        (
            "indexed primitive vline = fiber_vector(Tangent, Smooth, Line);\nfn bad() -> Bool { lies_over(pullback(sq(), line_at(3), vline(line_at(9), 1)), line_at(3)) }",
            "pullback requires a seed of family Cotangent, but the supplied seed has family Tangent",
        ),
        (
            "fn bad() -> Bool { lies_over(pullback(f(), plane_at(3, 9), dplane(plane_at(3, 9), 1, 0)), line_at(3)) }",
            "pullback requires a point with target Line (the map's source), but the supplied point has target Plane",
        ),
        (
            "fn bad() -> Bool { lies_over(differential(f(), line_at(3)), line_at(3)) }",
            "differential requires a function with target Line (the primitive's declared line), but the supplied function has target Plane",
        ),
        (
            "fn bad() -> Bool { lies_over(differential(g(), line_at(3)), line_at(3)) }",
            "differential requires a point with target Plane (the function's source), but the supplied point has target Line",
        ),
        (
            "fn bad() -> Bool { lies_over(backward(linearize(f(), plane_at(3, 9)), dplane(plane_at(3, 9), 1, 0)), line_at(3)) }",
            "linearize requires a point with target Line (the map's source), but the supplied point has target Plane",
        ),
        (
            "fn bad() -> Bool { lies_over(backward(linearize(f(), line_at(3)), dline(line_at(3), 1)), line_at(3)) }",
            "backward requires a seed with object Plane (the tape's target), but the supplied seed has object Line",
        ),
        (
            "fn bad() -> Bool { lies_over(dline(line_at(3), 1), plane_at(3, 9)) }",
            "lies_over requires a point with target Line (the element's object), but the supplied point has target Plane",
        ),
        (
            "fn bad() -> Bool { lies_over(vplane(plane_at(1, 2), 1, 0), plane_at(1, 2)) }",
            "lies_over requires an element of family Cotangent, but the supplied element has family Tangent",
        ),
        (
            "fn bad() -> Bool { lies_over(dline(plane_at(3, 9), 1), line_at(3)) }",
            "dline requires a point with target Line (the primitive's declared object), but the supplied point has target Plane",
        ),
        (
            "fn bad() -> Bool { same_covector(vplane(plane_at(1, 2), 1, 0), vplane(plane_at(1, 2), 1, 0)) }",
            "same_covector requires a first element of family Cotangent, but the supplied first element has family Tangent",
        ),
        (
            "fn bad() -> Bool { same_covector(dline(line_at(3), 1), dplane(plane_at(3, 9), 1, 0)) }",
            "same_covector requires a second element with object Line (the first element's object), but the supplied second element has object Plane",
        ),
        (
            "fn bad() -> Int { pair_first(dx(dline(line_at(3), 1))) }",
            "dx requires an element with object Plane (the primitive's declared object), but the supplied element has object Line",
        ),
        (
            "fn bad() -> Int { pair_first(pairing(dline(line_at(1), 1), vplane(plane_at(1, 2), 1, 0))) }",
            "pairing requires a vector with object Line (the covector's object), but the supplied vector has object Plane",
        ),
        (
            "fn bad() -> Int { pair_first(pairing(differential(g(), plane_at(1, 2)), differential(g(), plane_at(1, 2)))) }",
            "pairing requires a vector of family Tangent, but the supplied vector has family Cotangent",
        ),
        (
            "fn bad() -> Int { pair_first(pairing(vplane(plane_at(1, 2), 3, 4), differential(g(), plane_at(1, 2)))) }",
            "pairing requires a covector of family Cotangent, but the supplied covector has family Tangent",
        ),
        (
            "fn bad() -> Int { pair_first(pairing(vplane(plane_at(1, 2), 3, 4), vplane(plane_at(1, 2), 3, 4))) }",
            "pairing requires a covector of family Cotangent, but the supplied covector has family Tangent",
        ),
        (
            "fn bad() -> Smooth<Line, Plane> { composite(linearize(f(), line_at(3))) }",
            "composite requires a map of family Smooth, but the supplied map has family Tape",
        ),
    ] {
        let stderr = rejects_cotangent(&with_cotangent(body), "E_ENDPOINT");
        assert!(stderr.contains(message), "{body}: {stderr}");
    }
    for (body, message) in [
        (
            "fn bad() -> Cotangent<Plane> { flat_skew(differential(g(), plane_at(1, 2))) }",
            "flat_skew requires a vector of family Tangent, but the supplied vector has family Cotangent",
        ),
        (
            "fn bad() -> Tangent<Plane> { sharp_skew(vplane(plane_at(1, 2), 1, 0)) }",
            "sharp_skew requires a covector of family Cotangent, but the supplied covector has family Tangent",
        ),
        (
            "indexed primitive vline = fiber_vector(Tangent, Smooth, Line);\nfn bad() -> Cotangent<Plane> { flat_skew(vline(line_at(1), 1)) }",
            "flat_skew requires a vector with object Plane (the metric's object), but the supplied vector has object Line",
        ),
        (
            "indexed primitive dline = fiber_vector(Cotangent, Smooth, Line);\nfn bad() -> Tangent<Plane> { sharp_skew(dline(line_at(1), 1)) }",
            "sharp_skew requires a covector with object Plane (the metric's object), but the supplied covector has object Line",
        ),
    ] {
        let stderr = rejects_metric(&with_metric(body), "E_ENDPOINT");
        assert!(stderr.contains(message), "{body}: {stderr}");
    }
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
    // A record without its metric, evidence or Gram matrix selects nothing
    // by default: it is rejected.
    for (pointer, field) in [
        (format!("{flat}/binding"), "metric"),
        (format!("{sharp}/binding"), "metric"),
        (format!("{sharp}/binding"), "evidence"),
        (skew.clone(), "gram"),
        (invertible.clone(), "metric"),
        (invertible.clone(), "evidence"),
    ] {
        let mut missing = raw.clone();
        let record = missing
            .pointer_mut(&pointer)
            .unwrap()
            .as_object_mut()
            .unwrap();
        assert!(record.remove(field).is_some(), "{pointer} has no {field}");
        assert_wire_rejected(&kernel(missing, "emit"), "E_PROTOCOL");
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
    // The differential is compiled into Core (#623): the unit covector at
    // g(1, 2), pulled back by the Jacobian table of g. No metric enters it.
    assert!(
        free_source.contains("(VastitasKernel.SmoothRuntime.jacobianStep "),
        "{free_source}"
    );
    assert!(
        !free_source.contains("SmoothRuntime.differential "),
        "{free_source}"
    );
    assert_eq!(free_source, generated(&metric));
    assert_eq!(run(&free), b"42\n");
    assert_eq!(run(&metric), b"42\n");
}

// The Stage 3 acceptance program (protocol 9). Each observation has its own
// failure code. Natively, it checks the roadmap identity and these #604 rows:
// C3, C4, C5, the runtime part of C6, C7, C9, C12 and the positive bullets of
// C13. Other tests and proofs cover the remaining rows:
// - C6's static part: cotangent_operations_reject_wrong_objects_variances_and_points
//   and acceptance_rejects_wrong_objects_and_a_gradient_primitive_statically.
// - C8 (proof): the oracle's smoothCompose_reifies (SmoothDeclarations.lean)
//   and core_cotangent_pullback (SmoothReverse.lean); the lowering tests
//   smooth_programs_lower_to_the_shared_smooth_runtime,
//   cotangent_programs_lower_to_the_shared_smooth_runtime and, for the
//   compiled reverse Core (#623), tests/reverse_core.rs.
// - C10 (bridge): pullback_eq_fderiv_adjoint and
//   pullback_getD_eq_fderiv_adjoint in lean-bridge Differential/Frechet.lean.
// - C11 (bridge): pullback_eq_kaehler_fiber and cot_compose_kaehler in
//   lean-bridge Differential/Kaehler.lean.
// - C12's metric independence: differential_is_unchanged_by_metric_declarations
//   and the oracle's smooth_differential_metric_free.
// - C13's rejections, and C14 (the S5 static rejections):
//   metric_declarations_reject_malformed_metrics_and_evidence_with_specific_codes
//   and metric_selection_is_explicit_and_unambiguous; for C14, also
//   posDef_of_riemannian, not_posDef_lorentz and isUnit_gram_of_nondegenerate
//   in lean-bridge Differential/Metric.lean.

const ACCEPTANCE_PROFILE: &str =
    include_str!("../examples/packages/smooth-differential/src/profile.vast");
const ACCEPTANCE_MAIN: &str =
    include_str!("../examples/packages/smooth-differential/src/main.vast");
/// The acceptance program's failure codes are exactly `1..=CODES`.
const CODES: u32 = 25;

fn acceptance_fixture(main: &str) -> Scratch {
    let s = Scratch::empty("smooth differential");
    s.write(
        "Vastitas.toml",
        include_str!("../examples/packages/smooth-differential/Vastitas.toml"),
    );
    s.write("src/main.vast", main);
    s.write("src/profile.vast", ACCEPTANCE_PROFILE);
    s
}

/// The acceptance program with extra items inserted before its helpers.
fn with_acceptance(extra: &str) -> String {
    assert!(ACCEPTANCE_MAIN.contains("fn verdict("));
    ACCEPTANCE_MAIN.replacen("fn verdict(", &format!("{extra}\nfn verdict("), 1)
}

#[track_caller]
fn rejects_acceptance(main: &str, code: &str) -> String {
    expect_code(&check(&acceptance_fixture(main)), code)
}

/// `source` with its only occurrence of `from` replaced by `to`.
#[track_caller]
fn mutate(source: &str, from: &str, to: &str) -> String {
    assert_eq!(source.matches(from).count(), 1, "{from:?} must occur once");
    source.replacen(from, to, 1)
}

/// The program with the failure code `k` of every `verdict` call replaced by
/// `2^(k - 1)`. Its native result `42 + m` then names exactly the failed
/// observations, as the bits of `m`, so two sets of failures never print the
/// same number. The codes must be exactly `1..=CODES`, each used once.
fn bitmask(main: &str) -> String {
    let mut masked = String::new();
    let mut codes = Vec::new();
    let mut rest = main;
    while let Some(at) = rest.find("verdict(") {
        let open = at + "verdict".len();
        masked.push_str(&rest[..open]);
        if rest[..at].ends_with("fn ") {
            // The helper's definition, not a call.
            rest = &rest[open..];
            continue;
        }
        // The code is the last argument, before the call's closing parenthesis.
        let (mut depth, mut comma, mut close) = (0, None, None);
        for (i, c) in rest[open..].char_indices() {
            match c {
                '(' => depth += 1,
                ')' if depth == 1 => {
                    close = Some(open + i);
                    break;
                }
                ')' => depth -= 1,
                ',' if depth == 1 => comma = Some(open + i),
                _ => {}
            }
        }
        let (comma, close) = (comma.unwrap(), close.unwrap());
        let code: u32 = rest[comma + 1..close].trim().parse().unwrap();
        codes.push(code);
        masked.push_str(&rest[open..=comma]);
        masked.push_str(&format!(" {}", 1u64 << (code - 1)));
        rest = &rest[close..];
    }
    masked.push_str(rest);
    codes.sort_unstable();
    assert_eq!(codes, (1..=CODES).collect::<Vec<_>>());
    masked
}

#[test]
fn smooth_example_checks_builds_and_executes() {
    let s = acceptance_fixture(ACCEPTANCE_MAIN);
    success(&check(&s));
    assert_eq!(run(&s), b"42\n");
}

/// A source mutation and the codes of the observations it falsifies.
type Mutation = (&'static str, &'static str, &'static [u32]);

#[test]
fn mutated_observations_change_the_native_result() {
    // Within a group, the mutations falsify disjoint observations. Every
    // code is falsified by some group.
    let groups: [(&[Mutation], u64); 4] = [
        (
            &[
                // 12 dt, not 13 dt.
                (
                    "reads(stepped, 12, 1), 1)",
                    "reads(stepped, 13, 1), 1)",
                    &[1],
                ),
                // The result does not lie over g(f(3)) = 18.
                (
                    "verdict(lies_over(stepped, x), 6)",
                    "verdict(lies_over(stepped, line_at(18)), 6)",
                    &[6],
                ),
                // A failure reads (0, 0), not the rational 0.
                ("reads(wrong, 0, 0), 11)", "reads(wrong, 0, 1), 11)", &[11]),
                // Recomputing from the seed 3 dt gives 36 dt.
                (
                    "pullback_recomputed(gAfterF, x, seed)",
                    "pullback_recomputed(gAfterF, x, dline(line_at(18), 3))",
                    &[12],
                ),
                // A after B instead of B after A.
                (
                    "pullback(compose(shearB(), shearA()), zero",
                    "pullback(compose(shearA(), shearB()), zero",
                    &[16],
                ),
                // diag(1, 2) for the Euclidean metric gives the gradient (2, 1/2).
                (
                    "Euclid: MetricForm<Plane> = euclidean;",
                    "Euclid: MetricForm<Plane> = gram((1, 0), (0, 2));",
                    &[19],
                ),
            ],
            298_059,
        ),
        (
            &[
                // Along the composite program, 2 dt pulls back to 24 dt.
                (
                    "pullback(gAfterF, x, seed)), 2)",
                    "pullback(gAfterF, x, dline(line_at(18), 2))), 2)",
                    &[2],
                ),
                (
                    "!lies_over(stepped, line_at(18)), 7)",
                    "!lies_over(stepped, x), 7)",
                    &[7],
                ),
                // A seed at 18 instead of 17 is accepted and reads 12.
                ("dline(line_at(17), 1)", "dline(line_at(18), 1)", &[8, 11]),
                // A tape from 2 rejects the seed at g(f(3)) = 18.
                (
                    "linearize(gAfterF, x)",
                    "linearize(gAfterF, line_at(2))",
                    &[13],
                ),
                (
                    "pullback(compose(shearA(), shearB()), zero",
                    "pullback(compose(shearB(), shearA()), zero",
                    &[17],
                ),
                // With the Euclidean Gram matrix, Lorentz no longer flips dy.
                ("gram((1, 0), (0, -1))", "gram((1, 0), (0, 1))", &[21]),
                // An outer map with value 324 at 18 and derivative 6 = sq'(3)
                // there: the recomputed pullback reads 72, as it would if
                // the recompute pass evaluated sq' at the input 3. The tape
                // from 3 (code 14) still rejects the seed at 16.
                (
                    "sq: Smooth<Line, Line> = pullback(t -> t^2);",
                    "sq: Smooth<Line, Line> = pullback(t -> 6*t + 216);",
                    &[25],
                ),
            ],
            17_896_684,
        ),
        (
            &[
                // Along the composite as one map, -dt pulls back to -12 dt.
                (
                    "pullback(composite(gAfterF), x, seed)",
                    "pullback(composite(gAfterF), x, dline(line_at(18), -1))",
                    &[3],
                ),
                // The right intermediate point f(3) and seed at 18: the
                // detour succeeds, also after the identity.
                (
                    "compose(f(), line_at(2)), dline(line_at(8), 1)",
                    "compose(f(), line_at(3)), dline(line_at(18), 1)",
                    &[9, 10],
                ),
                // A tape from 3 accepts a seed at sq(3) = 9.
                ("dline(line_at(16), 1)", "dline(line_at(9), 1)", &[14]),
                (
                    "reads_covector(dg, 2, 1), 18)",
                    "reads_covector(dg, 1, 2), 18)",
                    &[18],
                ),
                (
                    "gradient_euclid(g(), p), gradient_skew(g(), p)), 22)",
                    "gradient_euclid(g(), p), gradient_euclid(g(), p)), 22)",
                    &[22],
                ),
                // dg pairs with the Euclidean gradient (2, 1) to 5.
                (
                    "pair_first(pairing(dg, gradient_skew(g(), p))) == 2",
                    "pair_first(pairing(dg, gradient_euclid(g(), p))) == 2",
                    &[24],
                ),
            ],
            10_625_838,
        ),
        (
            &[
                // A declared map with gf(3) = 18 but derivative 6 at 3.
                ("pullback(t -> 2*t^2);", "pullback(t -> t^2 + 9);", &[4, 5]),
                // The identity keeps a covector that is not a failure.
                (
                    "pullback(idL(), x, detour)",
                    "pullback(idL(), x, stepped)",
                    &[10],
                ),
                // A map that fixes (1, 2) but is not the identity.
                (
                    "idP: Smooth<Plane, Plane> = identity;",
                    "idP: Smooth<Plane, Plane> = pullback(x -> x, y -> 2*y - 2);",
                    &[15],
                ),
                // Another Skew metric gives the gradient (3, -1), which pairs
                // with dg to 5.
                ("gram((2, 1), (1, 1))", "gram((1, 1), (1, 2))", &[20, 24]),
                // sharp under Skew after flat under Euclid.
                (
                    "sharp_skew(flat_skew(v))",
                    "sharp_skew(flat_euclid(v))",
                    &[23],
                ),
            ],
            13_124_162,
        ),
    ];
    let mut shown = std::collections::BTreeSet::new();
    for (index, (mutations, expected)) in groups.iter().enumerate() {
        let mut main = ACCEPTANCE_MAIN.to_string();
        let mut flipped = std::collections::BTreeSet::new();
        for (from, to, codes) in *mutations {
            main = mutate(&main, from, to);
            for code in *codes {
                assert!(flipped.insert(*code), "group {index} repeats code {code}");
            }
        }
        let bits: u64 = flipped.iter().map(|code| 1u64 << (code - 1)).sum();
        assert_eq!(*expected, 42 + bits, "group {index}: {flipped:?}");
        assert_eq!(
            String::from_utf8(run(&acceptance_fixture(&bitmask(&main)))).unwrap(),
            format!("{expected}\n"),
            "group {index}: {flipped:?}"
        );
        if index == 0 {
            // The shipped codes add up: 42 + 1 + 6 + 11 + 12 + 16 + 19.
            assert_eq!(run(&acceptance_fixture(&main)), b"107\n");
        }
        shown.extend(flipped);
    }
    assert_eq!(shown, (1..=CODES).collect());
}

#[test]
fn smooth_forms_select_protocol_nine_and_older_envelopes_reject_them() {
    let raw = request(&acceptance_fixture(ACCEPTANCE_MAIN));
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
fn acceptance_rejects_wrong_objects_and_a_gradient_primitive_statically() {
    // A seed over the plane for the composite program on the line. The
    // message names the seed's role and the expected and actual objects.
    let stderr = rejects_acceptance(
        &with_acceptance(
            "fn bad() -> Bool { lies_over(pullback(compose(g(), f()), line_at(3), dplane(plane_at(3, 9), 1, 0)), line_at(3)) }",
        ),
        "E_ENDPOINT",
    );
    assert!(
        stderr.contains("pullback requires a seed with object Line (the map's target), but the supplied seed has object Plane"),
        "{stderr}"
    );
    // The stepwise pullback's signature fixes the seed's object.
    let stderr = rejects_acceptance(
        &with_acceptance(
            "fn bad() -> Bool { lies_over(stepwise(line_at(3), dplane(plane_at(18, 0), 1, 0)), line_at(3)) }",
        ),
        "E_TYPE",
    );
    assert!(
        stderr.contains("expected Cotangent<Line>, found Cotangent<Plane>"),
        "{stderr}"
    );
    // There is no gradient primitive: a gradient is an ordinary function
    // that applies sharp, with a named metric and evidence, to the differential.
    let stderr = rejects_acceptance(
        &with_acceptance(
            "indexed primitive grad = gradient(Cotangent, Tangent, using = Skew, evidence = SkewInvertible);",
        ),
        "E_TYPE",
    );
    assert!(
        stderr.contains("unknown indexed primitive contract"),
        "{stderr}"
    );
}

/// JSON pointer to the result expression of a named function in the root module.
fn result_pointer(raw: &Value, name: &str) -> String {
    let functions = raw["packages"][0]["modules"][0]["functions"]
        .as_array()
        .unwrap();
    let f = functions.iter().position(|f| f["name"] == name).unwrap();
    format!("/packages/0/modules/0/functions/{f}/body/result")
}

#[test]
fn tampered_acceptance_bodies_are_rejected_by_the_kernel() {
    let raw = request(&acceptance_fixture(ACCEPTANCE_MAIN));
    let stepwise = result_pointer(&raw, "stepwise");
    let gradient = result_pointer(&raw, "gradient_skew");
    assert_eq!(raw.pointer(&stepwise).unwrap()["callee"], "pullback");
    assert_eq!(raw.pointer(&gradient).unwrap()["callee"], "sharp_skew");
    let forged = |path: &str, value: Value| {
        let mut changed = raw.clone();
        *changed.pointer_mut(path).unwrap() = value;
        changed
    };
    let mut swapped = raw.pointer(&format!("{stepwise}/args")).unwrap().clone();
    swapped.as_array_mut().unwrap().swap(1, 2);
    for (path, value, code) in [
        // The inner pullback along f instead of g.
        (
            format!("{stepwise}/args/2/args/0/callee"),
            json!("f"),
            "E_ENDPOINT",
        ),
        // The point and the seed swapped.
        (format!("{stepwise}/args"), swapped, "E_ENDPOINT"),
        // flat where the gradient applies sharp.
        (
            format!("{gradient}/callee"),
            json!("flat_skew"),
            "E_ENDPOINT",
        ),
        // A gradient operation that the program does not declare.
        (format!("{gradient}/callee"), json!("gradient"), "E_NAME"),
        (
            format!("{gradient}/args/0/callee"),
            json!("pullback"),
            "E_ARITY",
        ),
    ] {
        assert_wire_rejected(&kernel(forged(&path, value), "emit"), code);
    }
}
