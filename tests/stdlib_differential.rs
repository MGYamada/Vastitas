//! The smooth affine profile from the standard library (#604, S9a; C17).
//! A path package uses `std::geometry::smooth::affine`, `std::geometry::metric`
//! and `std::differential`. The tests run copies of
//! `examples/packages/stdlib-differential` against copies of the stdlib, and
//! check the name audit and the package boundaries of ADR 0001 §10.
mod common;
use common::{Scratch, cli, expect_code, success};
use serde_json::Value;
use std::path::Path;

const MAIN: &str = include_str!("../examples/packages/stdlib-differential/main.vast");
const MANIFEST: &str = include_str!("../examples/packages/stdlib-differential/Vastitas.toml");

/// A metric-free program: the pullback, the differential and a tape.
const METRIC_FREE: &str = r#"
use std::geometry::smooth::affine::SmoothR;
use std::geometry::smooth::affine::Smooth;
use std::geometry::smooth::affine::Cotangent;
use std::geometry::smooth::affine::Pt;
use std::geometry::smooth::affine::Line;
use std::geometry::smooth::affine::compose_smooth;
use std::geometry::smooth::affine::line_at;
use std::geometry::smooth::affine::same_covector;
use std::differential::pullback;
use std::differential::differential;
use std::differential::linearize;
use std::differential::backward;

indexed affine Plane(SmoothR) = Affine(2)[x, y];
indexed primitive plane_at = smooth_int_point(Smooth, Plane, Pt);
indexed morphism f: Smooth<Line, Plane> = pullback(x -> t, y -> t^2);
indexed morphism g: Smooth<Plane, Line> = pullback(t -> x^2 + y);
indexed primitive dline = fiber_vector(Cotangent, Smooth, Line);
indexed primitive dt = fiber_component(Cotangent, Line, t);
indexed primitive dx = fiber_component(Cotangent, Plane, x);

fn main() -> Int {
    let x: Smooth<Pt, Line> = line_at(3);
    let seed: Cotangent<Line> = dline(line_at(18), 1);
    let stepped: Cotangent<Line> = pullback(f(), x, pullback(g(), compose_smooth(f(), x), seed));
    let taped: Cotangent<Line> = backward(linearize(compose_smooth(g(), f()), x), seed);
    let dg: Cotangent<Plane> = differential(g(), plane_at(1, 2));
    if pair_first(dt(stepped)) == 12 && same_covector(stepped, taped) && pair_first(dx(dg)) == 2 {
        42
    } else {
        0
    }
}
"#;

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap()
}

/// The application `main` in `app/`, with a copy of the stdlib in `stdlib/`
/// as its `std` path dependency. `skip` lists stdlib directories to leave out.
fn fixture(main: &str, skip: &[&str]) -> Scratch {
    common::prepare_stdlib_package();
    let s = Scratch::empty("stdlib calculus");
    let stdlib = common::root().join("stdlib");
    s.write("stdlib/Vastitas.toml", &read(&stdlib.join("Vastitas.toml")));
    let mut stack = ["target/package", "src/geometry", "src/differential"]
        .map(|d| stdlib.join(d))
        .to_vec();
    while let Some(directory) = stack.pop() {
        for entry in std::fs::read_dir(&directory).unwrap() {
            let path = entry.unwrap().path();
            let relative = path
                .strip_prefix(&stdlib)
                .unwrap()
                .to_str()
                .unwrap()
                .to_owned();
            if skip.contains(&relative.as_str()) {
                continue;
            }
            if path.is_dir() {
                stack.push(path);
            } else if matches!(
                path.extension().and_then(|e| e.to_str()),
                Some("vast" | "toml")
            ) {
                s.write(&format!("stdlib/{relative}"), &read(&path));
            }
        }
    }
    s.write(
        "app/Vastitas.toml",
        &common::checked_replace(MANIFEST, "../../../stdlib", "../stdlib"),
    );
    s.write("app/main.vast", main);
    s
}

fn check_manifest(s: &Scratch, manifest: &str) -> std::process::Output {
    cli()
        .current_dir(&s.0)
        .args(["check", "--manifest-path", manifest])
        .output()
        .unwrap()
}

fn check(s: &Scratch) -> std::process::Output {
    check_manifest(s, "app/Vastitas.toml")
}

fn run(s: &Scratch) -> Vec<u8> {
    success(&check(s));
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
    result.stdout
}

/// The example with extra items inserted before its helpers.
fn with(extra: &str) -> String {
    common::checked_replace(MAIN, "fn verdict(", &format!("{extra}\nfn verdict("))
}

#[track_caller]
fn rejects(main: &str, code: &str) -> String {
    expect_code(&check(&fixture(main, &[])), code)
}

fn request(s: &Scratch) -> Value {
    let mut command = cli();
    command
        .current_dir(&s.0)
        .args(["check", "--manifest-path", "app/Vastitas.toml"]);
    common::captured_wire(command, 9)
}

fn package<'a>(wire: &'a Value, name: &str) -> &'a Value {
    wire["packages"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["name"] == name)
        .unwrap_or_else(|| panic!("no package {name}"))
}

/// Every string in `value`, in any position.
fn strings(value: &Value, out: &mut Vec<String>) {
    match value {
        Value::String(s) => out.push(s.clone()),
        Value::Array(items) => items.iter().for_each(|item| strings(item, out)),
        Value::Object(fields) => fields.values().for_each(|field| strings(field, out)),
        _ => {}
    }
}

#[test]
fn library_profile_checks_builds_and_runs_from_a_path_package() {
    let s = fixture(MAIN, &[]);
    assert_eq!(run(&s), b"42\n");
    // The library and the application share one protocol-9 closure.
    let wire = request(&s);
    for name in ["vastitas_geometry", "vastitas_differential", "vastitas_std"] {
        package(&wire, name);
    }
}

/// `value` without its source spans.
fn without_spans(value: &Value) -> Value {
    match value {
        Value::Object(fields) => Value::Object(
            fields
                .iter()
                .filter(|(key, _)| key.as_str() != "span")
                .map(|(key, field)| (key.clone(), without_spans(field)))
                .collect(),
        ),
        Value::Array(items) => Value::Array(items.iter().map(without_spans).collect()),
        other => other.clone(),
    }
}

/// Each public binding of the library is the documented operation over the
/// library's families. A binding with another mode or family, such as a
/// recomputing `pullback` or a `tangent_over` on covectors, fails here even
/// though it computes the same values in the example.
#[test]
fn library_bindings_are_the_documented_operations() {
    let wire = request(&fixture(MAIN, &[]));
    let path = |name: &str| serde_json::json!({ "path": [name] });
    let expected = [
        (
            "vastitas_geometry",
            vec!["smooth", "affine"],
            "compose_smooth",
            serde_json::json!({ "op": "smooth_compose", "family": path("Smooth") }),
        ),
        (
            "vastitas_geometry",
            vec!["smooth", "affine"],
            "composite",
            serde_json::json!({ "op": "smooth_composite", "family": path("Smooth") }),
        ),
        (
            "vastitas_geometry",
            vec!["smooth", "affine"],
            "same_smooth",
            serde_json::json!({ "op": "smooth_equal", "family": path("Smooth") }),
        ),
        (
            "vastitas_geometry",
            vec!["smooth", "affine"],
            "line_at",
            serde_json::json!({ "op": "smooth_int_point", "family": path("Smooth"), "object": path("Line"), "point": path("Pt") }),
        ),
        (
            "vastitas_geometry",
            vec!["smooth", "affine"],
            "lies_over",
            serde_json::json!({ "op": "fiber_at", "family": path("Cotangent"), "map_family": path("Smooth") }),
        ),
        (
            "vastitas_geometry",
            vec!["smooth", "affine"],
            "tangent_over",
            serde_json::json!({ "op": "fiber_at", "family": path("Tangent"), "map_family": path("Smooth") }),
        ),
        (
            "vastitas_geometry",
            vec!["smooth", "affine"],
            "same_covector",
            serde_json::json!({ "op": "fiber_equal", "family": path("Cotangent") }),
        ),
        (
            "vastitas_geometry",
            vec!["smooth", "affine"],
            "same_vector",
            serde_json::json!({ "op": "fiber_equal", "family": path("Tangent") }),
        ),
        (
            "vastitas_geometry",
            vec!["smooth", "affine"],
            "pairing",
            serde_json::json!({ "op": "fiber_pairing", "cotangent": path("Cotangent"), "tangent": path("Tangent") }),
        ),
        (
            "vastitas_differential",
            vec![],
            "pullback",
            serde_json::json!({ "op": "cotangent_pullback", "map_family": path("Smooth"), "cotangent": path("Cotangent"), "mode": "saved" }),
        ),
        (
            "vastitas_differential",
            vec![],
            "differential",
            serde_json::json!({ "op": "differential", "map_family": path("Smooth"), "cotangent": path("Cotangent"), "line": path("Line") }),
        ),
        (
            "vastitas_differential",
            vec![],
            "linearize",
            serde_json::json!({ "op": "linearize", "map_family": path("Smooth"), "tape": path("Tape") }),
        ),
        (
            "vastitas_differential",
            vec![],
            "backward",
            serde_json::json!({ "op": "cotangent_backward", "tape": path("Tape"), "cotangent": path("Cotangent") }),
        ),
    ];
    for (library, module, name, binding) in expected {
        let module = package(&wire, library)["modules"]
            .as_array()
            .unwrap()
            .iter()
            .find(|m| m["path"] == serde_json::json!(module))
            .unwrap_or_else(|| panic!("{library}: no module {module:?}"));
        let declaration = module["indexed_declarations"]
            .as_array()
            .unwrap()
            .iter()
            .find(|d| d["name"] == name)
            .unwrap_or_else(|| panic!("{library}: no declaration {name}"));
        assert_eq!(declaration["kind"], "primitive", "{library}::{name}");
        assert_eq!(declaration["public"], true, "{library}::{name}");
        assert_eq!(
            without_spans(&declaration["binding"]),
            binding,
            "{library}::{name}"
        );
    }
}

/// The library's other operations work from an application: `tangent_over`,
/// `composite`, `same_smooth` and the `Tape` family. Each check has its own
/// code, so the program prints 42 only when all of them hold.
#[test]
fn library_fiber_and_map_operations_work_from_an_application() {
    let main = common::checked_replace(
        MAIN,
        "use std::geometry::metric::MetricForm;",
        "use std::geometry::metric::MetricForm;\nuse std::geometry::smooth::affine::Tape;\nuse std::geometry::smooth::affine::tangent_over;\nuse std::geometry::smooth::affine::composite;\nuse std::geometry::smooth::affine::same_smooth;",
    );
    let main = common::checked_replace(
        &main,
        "indexed morphism g: Smooth<Plane, Line> = pullback(t -> x^2 + y);",
        "indexed morphism g: Smooth<Plane, Line> = pullback(t -> x^2 + y);\nindexed morphism twice_square: Smooth<Line, Line> = pullback(t -> 2*t^2);\nindexed morphism square: Smooth<Line, Line> = pullback(t -> t^2);",
    );
    let main = common::checked_replace(
        &main,
        "    42 + verdict(",
        concat!(
            "    let tape: Tape<Line, Line> = linearize(gAfterF, x);\n",
            "    42 + verdict(tangent_over(grad, p), 12)\n",
            "       + verdict(!tangent_over(vplane(plane_at(0, 0), 1, 0), p), 13)\n",
            "       + verdict(same_smooth(composite(gAfterF), twice_square()), 14)\n",
            "       + verdict(same_smooth(gAfterF, twice_square()), 15)\n",
            "       + verdict(!same_smooth(gAfterF, square()), 16)\n",
            "       + verdict(same_covector(backward(tape, seed), stepped), 17)\n",
            "       + verdict(",
        ),
    );
    assert_eq!(run(&fixture(&main, &[])), b"42\n");
    // Each new check can fail: a vector at (1, 2) does not lie over (0, 0),
    // and the composite is not t^2.
    let failing = common::checked_replace(
        &main,
        "verdict(tangent_over(grad, p), 12)",
        "verdict(tangent_over(grad, plane_at(0, 0)), 12)",
    );
    let failing = common::checked_replace(
        &failing,
        "verdict(same_smooth(gAfterF, twice_square()), 15)",
        "verdict(same_smooth(gAfterF, square()), 15)",
    );
    assert_eq!(run(&fixture(&failing, &[])), b"69\n");
}

#[test]
fn mutated_observations_change_the_native_result() {
    // 13 dt is wrong (code 1). The seed at 18 is right, so the failure check
    // fails (6). Under sharp with Euclid, the gradient (2, 1) is not (1, 0)
    // (8 and 11), flat under Skew maps it to (5, 3), not dg (9), and it pairs
    // with dg to 5 (10). The metric selection decides the gradient.
    let main = common::checked_replace(
        MAIN,
        "reads(dt(stepped), 12, 1)",
        "reads(dt(stepped), 13, 1)",
    );
    let main = common::checked_replace(&main, "dline(line_at(17), 1)", "dline(line_at(18), 1)");
    let main = common::checked_replace(
        &main,
        "sharp(Cotangent, Tangent, using = Skew, evidence = SkewInvertible)",
        "sharp(Cotangent, Tangent, using = Euclid, evidence = EuclidInvertible)",
    );
    let main = common::checked_replace(
        &main,
        "indexed evidence SkewInvertible",
        "indexed metric Euclid: MetricForm<Plane> = euclidean;\nindexed evidence EuclidInvertible = nondegenerate(Euclid);\nindexed evidence SkewInvertible",
    );
    assert_eq!(run(&fixture(&main, &[])), b"87\n");
}

#[test]
fn gradient_is_ordinary_code_over_the_metric_free_differential() {
    let wire = request(&fixture(MAIN, &[]));
    // No binding in the closure is a gradient operation.
    for p in wire["packages"].as_array().unwrap() {
        for module in p["modules"].as_array().unwrap() {
            for declaration in module["indexed_declarations"]
                .as_array()
                .into_iter()
                .flatten()
            {
                assert_ne!(declaration["binding"]["op"], "gradient", "{declaration}");
            }
        }
    }
    let app = package(&wire, "stdlib_differential_demo");
    let functions = app["modules"][0]["functions"].as_array().unwrap();
    assert!(functions.iter().any(|f| f["name"] == "gradient"));
    // sharp is bound next to the metric it names, not in the library.
    let library_strings = |name: &str| {
        let mut out = Vec::new();
        strings(package(&wire, name), &mut out);
        out
    };
    for name in ["vastitas_geometry", "vastitas_differential"] {
        let library = library_strings(name);
        assert!(
            !library.iter().any(|s| s == "sharp" || s == "flat"),
            "{name}"
        );
    }
    // The kernel admits no gradient primitive either.
    rejects(
        &with(
            "indexed primitive grad = gradient(Smooth, Cotangent, Tangent, using = Skew, evidence = SkewInvertible);",
        ),
        "E_TYPE",
    );
}

/// Why `std::differential` exports no `gradient` function: a library function
/// can name neither the application's object nor its `sharp`.
#[test]
fn a_library_gradient_can_take_neither_the_object_nor_sharp() {
    // The smooth families take declared objects only, never an object parameter.
    let object =
        "X: Object<std::geometry::smooth::affine::CInfAffine, std::geometry::smooth::CInfReal>";
    for (body, label) in [
        (
            format!("fn grad_at({object}, h: Smooth<X, Line>, p: Smooth<Pt, X>) -> Int {{ 0 }}"),
            "Smooth<X, Line>",
        ),
        (
            format!("fn grad_at({object}, c: Cotangent<X>) -> Int {{ 0 }}"),
            "Cotangent<X>",
        ),
    ] {
        let stderr = rejects(&with(&body), "E_TYPE");
        assert!(
            stderr.contains(&format!("invalid indexed annotation {label}")),
            "{stderr}"
        );
    }
    // sharp is not a function value, and Fn values carry scalars only.
    for (body, code, message) in [
        (
            "fn probe() -> Int { let s = sharp_skew; 0 }",
            "E_TYPE",
            "`sharp_skew` names a primitive, which is not a value; call it with its operands",
        ),
        (
            "fn probe() -> Int { let s = gradient; 0 }",
            "E_TYPE",
            "Fn values require scalar/Fn signatures; indexed and Pair functions are direct-call only",
        ),
        (
            "fn probe() -> Int { let s = fn(c: Cotangent<Plane>) -> Tangent<Plane> { sharp_skew(c) }; 0 }",
            "E_TYPE",
            "lambda signatures require scalar/Fn types",
        ),
        (
            "fn apply_sharp(s: Fn<Cotangent<Plane>, Tangent<Plane>>, c: Cotangent<Plane>) -> Tangent<Plane> { s(c) }",
            "E_PROTOCOL",
            "Fn signatures contain only scalars and recursive Fn types",
        ),
    ] {
        let stderr = rejects(&with(body), code);
        assert!(stderr.contains(message), "{stderr}");
    }
}

#[test]
fn smooth_operations_are_not_ambiguous_with_stage_one_geometry() {
    // The smooth module declares no compose, identity or equality of its own
    // under the Stage 1 names.
    for name in ["compose", "id", "same", "apply", "Morphism"] {
        let stderr = rejects(
            &with(&format!("use std::geometry::smooth::affine::{name};")),
            "E_NAME",
        );
        assert!(
            stderr.contains(&format!("undefined name '{name}'")),
            "{stderr}"
        );
    }
    // Each spelling names one operation, and each operation takes one family.
    for (body, message) in [
        (
            "fn bad() -> Int { let h = std::geometry::compose(g(), f()); 0 }",
            "compose requires a first map of family Morphism, but the supplied first map has family Smooth",
        ),
        // The legacy bare `compose` is std::geometry::compose.
        (
            "fn bad() -> Int { let h = compose(g(), f()); 0 }",
            "compose requires a first map of family Morphism, but the supplied first map has family Smooth",
        ),
        (
            "fn bad() -> Int { let X = std::geometry::smooth::Affine(2); let h = compose_smooth(std::geometry::smooth::id(X), std::geometry::smooth::id(X)); 0 }",
            "compose_smooth requires a first map of family Smooth, but the supplied first map has family Morphism",
        ),
        (
            "indexed morphism idL: Smooth<Line, Line> = identity;\nfn bad() -> Bool { std::geometry::smooth::affine::same_smooth(idL(), std::geometry::smooth::id(std::geometry::smooth::Affine(1))) }",
            "same_smooth requires a second map of family Smooth, but the supplied second map has family Morphism",
        ),
    ] {
        let stderr = rejects(&with(body), "E_ENDPOINT");
        assert!(stderr.contains(message), "{stderr}");
    }
    // Both compositions in one program, each on its own family.
    let main = common::checked_replace(
        MAIN,
        "use std::differential::pullback;",
        "use std::geometry::compose;\nuse std::geometry::smooth::id;\nuse std::differential::pullback;",
    );
    let main = common::checked_replace(
        &main,
        "    42 + verdict(",
        "    let X = std::geometry::smooth::Affine(2);\n    let m: std::geometry::Morphism<X, X> = compose(id(X), id(X));\n    42 + verdict(",
    );
    assert_eq!(run(&fixture(&main, &[])), b"42\n");
}

#[test]
fn library_objects_keep_their_identity_and_classification() {
    // A line declared by the application is not the library's line.
    let stderr = rejects(
        &with(
            "indexed affine MyLine(SmoothR) = Affine(1)[t];\nindexed morphism k: Smooth<Plane, MyLine> = pullback(t -> x^2 + y);\nfn bad() -> Bool { lies_over(differential(k(), plane_at(1, 2)), plane_at(1, 2)) }",
        ),
        "E_ENDPOINT",
    );
    assert!(
        stderr.contains("but the supplied function has target MyLine"),
        "{stderr}"
    );
    // Smooth affine objects index neither Stage 1 families nor the reverse.
    for body in [
        "fn probe(p: std::geometry::Point<Line, std::geometry::smooth::BaseSmooth>) -> Int { 0 }",
        "fn probe(m: Smooth<std::geometry::smooth::BaseSmooth, Line>) -> Int { 0 }",
    ] {
        rejects(&with(body), "E_TYPE");
    }
    // MetricForm is distinct from the protocol-8 Metric and from MetricSpace.
    for name in ["Metric", "MetricSpace"] {
        rejects(
            &with(&format!("use std::geometry::metric::{name};")),
            "E_NAME",
        );
    }
    let stderr = rejects(
        &with("indexed metric Bad: MetricForm<std::geometry::smooth::BaseSmooth> = euclidean;"),
        "E_METRIC",
    );
    assert!(stderr.contains("which is not a smooth object"), "{stderr}");
}

#[test]
fn geometry_package_does_not_depend_on_differential() {
    let s = fixture(MAIN, &[]);
    assert!(!read(&s.0.join("stdlib/src/geometry/Vastitas.toml")).contains("[dependencies]"));
    let wire = request(&s);
    assert_eq!(
        package(&wire, "vastitas_geometry")["dependencies"],
        serde_json::json!([])
    );
    let dependencies = package(&wire, "vastitas_differential")["dependencies"]
        .as_array()
        .unwrap();
    assert_eq!(dependencies.len(), 1);
    assert_eq!(dependencies[0]["alias"], "geometry");
    assert!(
        dependencies[0]["target"]
            .as_str()
            .unwrap()
            .ends_with("src/geometry/Vastitas.toml")
    );
    // The geometry package checks on its own.
    success(&check_manifest(&s, "stdlib/src/geometry/Vastitas.toml"));
    // A geometry package that depends on differential forms a cycle.
    let manifest = read(&s.0.join("stdlib/src/geometry/Vastitas.toml"))
        + "\n[dependencies]\ndifferential = { path = \"../differential\" }\n";
    s.write("stdlib/src/geometry/Vastitas.toml", &manifest);
    expect_code(&check(&s), "E_CYCLE");
}

#[test]
fn metric_free_programs_need_no_metric_module() {
    // The pullback and the differential name no metric declaration.
    let wire = request(&fixture(METRIC_FREE, &[]));
    let mut library = Vec::new();
    strings(package(&wire, "vastitas_differential"), &mut library);
    for word in [
        "metric",
        "MetricForm",
        "metric_form",
        "flat",
        "sharp",
        "evidence",
    ] {
        assert!(!library.iter().any(|s| s == word), "{word}");
    }
    // Without the metric module, the metric-free program still runs, and a
    // program that names MetricForm cannot resolve it.
    let s = fixture(METRIC_FREE, &["src/geometry/metric"]);
    let root = read(&s.0.join("stdlib/src/geometry/mod.vast"));
    s.write(
        "stdlib/src/geometry/mod.vast",
        &common::checked_replace(&root, "pub mod metric;\n", ""),
    );
    assert!(!s.0.join("stdlib/src/geometry/metric").exists());
    assert_eq!(run(&s), b"42\n");
    s.write("app/main.vast", MAIN);
    expect_code(&check(&s), "E_NAME");
}
