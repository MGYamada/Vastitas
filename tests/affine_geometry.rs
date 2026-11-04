//! Historical Stage 2: presented affine objects through the public protocol-9
//! source path. The kernel expands, bounds and checks every polynomial; these
//! tests exercise acceptance, base chains, rejections and forged wire.
mod common;
use common::{Scratch, cli, kernel, success};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;

const PROFILE: &str = include_str!("../examples/packages/affine-geometry/src/profile.vast");
const MAIN: &str = include_str!("../examples/packages/affine-geometry/src/main.vast");

fn fixture(main: &str) -> Scratch {
    let s = Scratch::empty("affine geometry");
    s.write(
        "Vastitas.toml",
        include_str!("../examples/packages/affine-geometry/Vastitas.toml"),
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

fn rejects(main: &str, code: &str) -> String {
    let output = check(&fixture(main));
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(!output.status.success(), "accepted {main}");
    assert!(stderr.contains(code), "expected {code}: {stderr}");
    stderr
}

fn request(s: &Scratch) -> Value {
    let stub = s.write("capture", "#!/bin/sh\ncat > \"$(dirname \"$0\")/wire.json\"\nprintf '%s\\n' '{\"version\":9,\"ok\":false,\"diagnostics\":[{\"code\":\"E_CAPTURED\",\"message\":\"captured\"}]}'\nexit 1\n");
    std::fs::set_permissions(&stub, std::fs::Permissions::from_mode(0o755)).unwrap();
    let result = cli()
        .current_dir(&s.0)
        .env("VASTITAS_KERNEL", stub)
        .args(["check", "--manifest-path", "Vastitas.toml"])
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&result.stderr).contains("E_CAPTURED"),
        "{result:?}"
    );
    serde_json::from_slice(&std::fs::read(s.0.join("wire.json")).unwrap()).unwrap()
}

/// JSON pointer to a named declaration in the root module.
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

fn rejected_with(changed: Value, code: &str) {
    let result = kernel(changed, "emit");
    assert_eq!(result["ok"], false, "{result}");
    assert_eq!(result["diagnostics"][0]["code"], code, "{result}");
    assert!(result.get("lean_source").is_none(), "{result}");
}

#[test]
fn affine_example_checks_builds_and_executes() {
    let s = fixture(MAIN);
    success(&check(&s));
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
    assert_eq!(result.stdout, b"42\n");
}

#[test]
fn affine_forms_select_protocol_nine_and_older_envelopes_reject_them() {
    let raw = request(&fixture(MAIN));
    assert_eq!(raw["version"], 9);
    let accepted = kernel(&raw, "emit");
    assert_eq!(accepted["ok"], true, "{accepted}");
    for version in [7, 8] {
        let mut changed = raw.clone();
        changed["version"] = json!(version);
        rejected_with(changed, "E_PROTOCOL");
    }
    for version in 2..7 {
        let mut changed = raw.clone();
        changed["version"] = json!(version);
        let rejected = kernel(changed, "emit");
        assert_eq!(rejected["ok"], false, "version {version}: {rejected}");
    }
}

#[test]
fn structural_applications_follow_declared_base_chains() {
    for probe in [
        "fn probe(arrow: Over<X, X, S>) -> Int { 0 }",
        "fn probe(arrow: Over<DS, X, S>) -> Int { 0 }",
        "fn probe(arrow: Over<D, Line, SpecQQ>) -> Int { 0 }",
        "fn probe(arrow: Over<X, X, SpecQQ>) -> Int { 0 }",
    ] {
        success(&check(&fixture(&with(probe))));
    }
    for probe in [
        "fn probe(arrow: Over<X, D, S>) -> Int { 0 }",
        "fn probe(arrow: Over<S, X, X>) -> Int { 0 }",
        "fn probe(arrow: Over<Line, Line, S>) -> Int { 0 }",
    ] {
        rejects(&with(probe), "E_TYPE");
    }
}

#[test]
fn affine_source_rejections_are_specific() {
    for (declaration, code) in [
        (
            "indexed affine Bad(AffineQQ) = spec[t, x] relations(x^2 - t) over S;",
            "E_AFFINE_BASE",
        ),
        (
            "indexed affine Bad(AffineQQ) = spec[] over S by(t -> 0, u -> 0);",
            "E_AFFINE_BASE",
        ),
        (
            "indexed affine Bad(AffineQQ) = spec[e] over D by(e -> e);",
            "E_AFFINE_BASE",
        ),
        (
            "indexed affine Bad(AffineQQ) = spec[e] relations(x^2) over SpecQQ;",
            "E_AFFINE_COORDINATE",
        ),
        (
            "indexed affine Bad(AffineQQ) = spec[t, t] over SpecQQ;",
            "E_AFFINE_COORDINATE",
        ),
        (
            "indexed affine Bad(AffineQQ) = spec[e] relations(frac(1, 0)) over SpecQQ;",
            "E_AFFINE_COORDINATE",
        ),
        (
            "indexed affine Bad(AffineQQ) = spec[e] relations(e^17) over SpecQQ;",
            "E_LIMIT",
        ),
        (
            "indexed affine Bad(AffineQQ) = spec[e] relations(e^9 * e^8) over SpecQQ;",
            "E_LIMIT",
        ),
        (
            "indexed affine A(AffineQQ) = spec[a] over B by(b -> a);\nindexed affine B(AffineQQ) = spec[b] over A by(a -> b);",
            "E_AFFINE_BASE",
        ),
        (
            "indexed implementation Grid(profile::QQ, affine_descriptor) capabilities();\nindexed global G(Grid);\nindexed affine Bad(AffineQQ) = spec[] over G;",
            "E_AFFINE_BASE",
        ),
        ("indexed global Plain(AffineQQ);", "E_TYPE"),
        (
            "indexed family BadPoint(object(profile::AffineScheme), object(profile::AffineScheme)) = point constraints(same_base(0, 1));",
            "E_TYPE",
        ),
    ] {
        rejects(&with(declaration), code);
    }
    // Literal digits and nesting are bounded before the kernel sees them.
    let digits = "9".repeat(65);
    rejects(
        &with(&format!(
            "indexed affine Bad(AffineQQ) = spec[e] relations(e - {digits}) over SpecQQ;"
        )),
        "E_LIMIT",
    );
    let nested = format!("{}e{}", "(".repeat(70), ")".repeat(70));
    rejects(
        &with(&format!(
            "indexed affine Bad(AffineQQ) = spec[e] relations({nested}) over SpecQQ;"
        )),
        "E_LIMIT",
    );
    // `^` is only polynomial syntax.
    rejects("mod profile;\nfn main() -> Int { 2 ^ 3 }", "E_PARSE");
}

#[test]
fn degree_and_digit_boundaries_are_accepted() {
    let digits = "9".repeat(64);
    success(&check(&fixture(&with(&format!(
        "indexed affine Edge(AffineQQ) = spec[e] relations(e^16 - {digits} * e + frac(-3, 7)) over SpecQQ;"
    )))));
}

#[test]
fn raw_wire_rejects_forged_affine_records() {
    let raw = request(&fixture(MAIN));
    let x = declaration_pointer(&raw, "X");
    let origin = declaration_pointer(&raw, "Origin");
    let forged = |path: &str, value: Value| {
        let mut changed = raw.clone();
        *changed.pointer_mut(path).unwrap() = value;
        changed
    };
    let mut extra = raw.clone();
    extra.pointer_mut(&x).unwrap()["basis"] = json!([]);
    rejected_with(extra, "E_PROTOCOL");
    for (path, value) in [
        (
            format!("{x}/relations/0"),
            json!({"op": "sum", "terms": [{"op": "coordinate", "name": "x"}]}),
        ),
        (
            format!("{x}/relations/0"),
            json!({"op": "coordinate", "name": "x", "checked": true}),
        ),
        (
            format!("{x}/relations/0"),
            json!({"op": "natural", "value": "1e3"}),
        ),
        (
            format!("{x}/relations/0"),
            json!({"op": "natural", "value": "-1"}),
        ),
        (
            format!("{x}/relations/0"),
            json!({"op": "natural", "value": "9".repeat(65)}),
        ),
        (format!("{x}/relations/0"), json!({"op": "basis"})),
        (
            format!("{origin}/bindings/0"),
            json!({"name": "t", "image": {"op": "natural", "value": "0"}, "normal": []}),
        ),
    ] {
        rejected_with(forged(&path, value), "E_PROTOCOL");
    }
    // Consistent but mathematically wrong data is rejected by the checker.
    rejected_with(
        forged(
            &format!("{origin}/bindings/0/image"),
            json!({"op": "coordinate", "name": "t"}),
        ),
        "E_AFFINE_COORDINATE",
    );
    rejected_with(forged(&format!("{x}/base"), json!(null)), "E_AFFINE_BASE");
}

#[test]
fn morphism_declarations_reject_relation_variance_base_and_type_errors() {
    for (declaration, code) in [
        (
            "indexed morphism bad: Over<D, X, SpecQQ> = pullback(t -> 1, x -> e);",
            "E_AFFINE_RELATION",
        ),
        (
            "indexed morphism bad: Over<D, Line, SpecQQ> = pullback(e -> t);",
            "E_AFFINE_COORDINATE",
        ),
        (
            "indexed morphism bad: Over<D, Line, SpecQQ> = pullback(t -> t);",
            "E_AFFINE_COORDINATE",
        ),
        (
            "indexed morphism bad: Over<D, Line, SpecQQ> = identity;",
            "E_AFFINE_BASE",
        ),
        (
            "indexed morphism bad: Over<D, S, SpecQQ> = structure;",
            "E_AFFINE_BASE",
        ),
        (
            "indexed primitive bad = relative_coefficient(Over, D, Line, u, e);",
            "E_AFFINE_COORDINATE",
        ),
        (
            "indexed primitive bad = relative_coefficient(Over, D, Line, t, e + 1);",
            "E_AFFINE_COORDINATE",
        ),
        (
            "indexed implementation Grid(profile::QQ, affine_descriptor) capabilities();\nindexed classification Grids { parents(); domain(Grid); };\nindexed family Bad(object(Grids), object(Grids), object(Grids)) = relative constraints(structural(0, 2), structural(1, 2));",
            "E_TYPE",
        ),
        (
            "indexed family Bad(object(profile::AffineScheme), object(profile::AffineScheme), object(profile::AffineScheme)) = relative constraints(structural(0, 2));",
            "E_TYPE",
        ),
    ] {
        rejects(&with(declaration), code);
    }
    // A zero selector is not the constant monomial.
    for selector in ["0", "e - e"] {
        rejects(
            &with(&format!(
                "indexed primitive bad = relative_coefficient(Over, D, Line, t, {selector});"
            )),
            "E_AFFINE_COORDINATE",
        );
    }
    // Substitution is budgeted: small declarations whose expansions are huge
    // fail with E_LIMIT instead of exhausting the checker.
    let coordinates: Vec<String> = (0..16).map(|i| format!("x{i}")).collect();
    rejects(
        &with(&format!(
            "indexed affine Free(AffineQQ) = spec[{}] over SpecQQ;\nindexed affine T16(AffineQQ) = spec[t] relations(t^16) over SpecQQ;\nindexed morphism bad: Over<Free, T16, SpecQQ> = pullback(t -> {});",
            coordinates.join(", "),
            coordinates.join(" + ")
        )),
        "E_LIMIT",
    );
    let mut chain = String::from("indexed affine C0(AffineQQ) = spec[a0];\n");
    for k in 0..3 {
        chain += &format!(
            "indexed affine C{n}(AffineQQ) = spec[a{n}] over C{k} by(a{k} -> (a{n} + 1)^16);\n",
            n = k + 1
        );
    }
    rejects(
        &with(&(chain + "indexed morphism bad: Over<C3, C0, C0> = structure;")),
        "E_LIMIT",
    );
    // Composition and equality need matching endpoints and the same base.
    for body in [
        "fn bad() -> Bool { same(compose(toX(), p()), compose(toX(), p())) }",
        "fn bad() -> Bool { same(p(), sq()) }",
        "fn bad() -> Bool { same(compose(toS(), toX()), p()) }",
    ] {
        rejects(&with(body), "E_ENDPOINT");
    }
}

#[test]
fn mutated_observations_change_the_native_result() {
    let s = fixture(
        &MAIN
            .replace("verdict(!same(p(), q()), 1)", "verdict(same(p(), q()), 1)")
            .replace("== 9, 7)", "== 3, 7)"),
    );
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
    assert_eq!(result.stdout, b"50\n");
}

#[test]
fn relative_forms_reject_downgrade_and_forged_wire() {
    let raw = request(&fixture(MAIN));
    let p = declaration_pointer(&raw, "p");
    let to_x = declaration_pointer(&raw, "toX");
    let forged = |path: &str, value: Value| {
        let mut changed = raw.clone();
        *changed.pointer_mut(path).unwrap() = value;
        changed
    };
    for (path, value) in [
        (format!("{p}/definition"), json!({"kind": "pullback"})),
        (
            format!("{p}/definition"),
            json!({"kind": "cached", "images": []}),
        ),
        (
            format!("{p}/definition"),
            json!({"kind": "identity", "map": []}),
        ),
    ] {
        rejected_with(forged(&path, value), "E_PROTOCOL");
    }
    let mut extra = raw.clone();
    extra.pointer_mut(&p).unwrap()["map"] = json!({"images": []});
    rejected_with(extra, "E_PROTOCOL");
    // x |-> 1 sends x^2 - t to 1, which is not in the ideal (e^2).
    rejected_with(
        forged(
            &format!("{to_x}/definition/images/1/image"),
            json!({"op": "natural", "value": "1"}),
        ),
        "E_AFFINE_RELATION",
    );
}

#[test]
fn fiber_products_reject_unchosen_bases_non_isomorphisms_and_forged_squares() {
    for (declaration, code) in [
        (
            "indexed affine Bad(AffineQQ) = fiber(X, Origin2);",
            "E_AFFINE_BASE",
        ),
        (
            "indexed affine Bad(AffineQQ) = fiber(X, Origin2) via(t -> t^2) inverse(t -> t);",
            "E_AFFINE_RELATION",
        ),
        (
            "indexed morphism badBack: Over<Fiber, DS, S> = pullback(e -> 0);\nindexed cartesian bad = square(toX, toOrigin) through Fiber inverse badBack;",
            "E_AFFINE_RELATION",
        ),
        (
            "indexed cartesian bad = square(toOrigin, toX) through Fiber inverse back;",
            "E_AFFINE_BASE",
        ),
        (
            "indexed morphism bad: Over<X, S, S> = first;",
            "E_AFFINE_BASE",
        ),
        (
            "indexed primitive bad = relative_pair(Over, Fiber2);",
            "E_TYPE",
        ),
    ] {
        rejects(&with(declaration), code);
    }
    // `pair` needs both arrows over the fiber's base with one source.
    rejects(
        &with("fn bad() -> Bool { same(lift(toX(), toX()), lift(toX(), toOrigin())) }"),
        "E_ENDPOINT",
    );
}

#[test]
fn fiber_and_evidence_records_reject_forged_wire() {
    let raw = request(&fixture(MAIN));
    let fiber2 = declaration_pointer(&raw, "Fiber2");
    let square = declaration_pointer(&raw, "fiberIsDual");
    let mut extra = raw.clone();
    extra.pointer_mut(&fiber2).unwrap()["basis"] = json!([]);
    rejected_with(extra, "E_PROTOCOL");
    let mut extra = raw.clone();
    extra.pointer_mut(&square).unwrap()["comparison"] = json!([]);
    rejected_with(extra, "E_PROTOCOL");
    let mut changed = raw.clone();
    *changed.pointer_mut(&format!("{fiber2}/via")).unwrap() =
        json!({"forward": [], "inverse": [], "checked": true});
    rejected_with(changed, "E_PROTOCOL");
    // A consistent but non-invertible base map is a mathematical rejection.
    let mut changed = raw.clone();
    *changed
        .pointer_mut(&format!("{fiber2}/via/forward/0/image"))
        .unwrap() = json!({"op": "natural", "value": "0"});
    rejected_with(changed, "E_AFFINE_RELATION");
}

#[test]
fn principal_opens_and_restrictions_reject_non_preimages_and_non_isomorphisms() {
    for (declaration, code) in [
        (
            "indexed morphism bad: Over<Dt, Dt, SpecQQ> = restrict(sq);",
            "E_AFFINE_BASE",
        ),
        (
            "indexed morphism bad: Over<Line, Dt, SpecQQ> = restrict(sq);",
            "E_AFFINE_BASE",
        ),
        (
            "indexed morphism bad: Over<U1, U2, SpecQQ> = pullback(y -> xi, yi -> x^2);\nindexed iso badIso = forward bad inverse unglue;",
            "E_AFFINE_RELATION",
        ),
        (
            "indexed affine Bad(AffineQQ) = localize(Line, x) inverse w;",
            "E_AFFINE_COORDINATE",
        ),
        (
            "indexed affine Bad(AffineQQ) = localize(Line, t) inverse t;",
            "E_AFFINE_COORDINATE",
        ),
    ] {
        rejects(&with(declaration), code);
    }
    let raw = request(&fixture(MAIN));
    let open = declaration_pointer(&raw, "Dt");
    let mut extra = raw.clone();
    extra.pointer_mut(&open).unwrap()["basis"] = json!([]);
    rejected_with(extra, "E_PROTOCOL");
    let mut changed = raw.clone();
    changed["version"] = json!(8);
    rejected_with(changed, "E_PROTOCOL");
}
