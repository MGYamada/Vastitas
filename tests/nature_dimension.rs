//! `nature::dimension` from a path package (Stage 4, #759; C17, C18, C19,
//! C20, C21). An application that depends on copies of the stdlib and of the
//! `nature` package declares a chart with a length and a time coordinate, a
//! std metric with its evidence, a reading, scales and physical
//! interpretations. The tests check what the kernel accepts and rejects, run
//! the gradient natively, compare the generated Lean with and without the
//! nature declarations, and audit the module's public names (ADR 0002).
mod common;
use common::{Scratch, expect_code, kernel, read, success};
use serde_json::{Value, json};

/// The nature declarations of `MAIN`: a reading, two scales and the physical
/// interpretation of the std metric G = diag(1/9, 1/4) by them.
const NATURE: &str = "indexed reading phys: Reading<C> = (x: Length, t: Time);
indexed scale l0 = 3 of Length;
indexed scale t0 = 2 of Time;
indexed physical PG: PhysicalMetric<C> = interpret(G, reading = phys, gram((l0^-2, 0), (0, t0^-2)));
";

/// The chart C = Affine(2)[x, t] with the std metric G = diag(1/9, 1/4) and
/// its evidence, and the gradient of h(x, t) = x + t under G at (1, 2), which
/// is (9, 4). `main` prints 100 times its x component plus its t component.
const MAIN: &str = "use std::geometry::smooth::affine::SmoothR;
use std::geometry::smooth::affine::Smooth;
use std::geometry::smooth::affine::Tangent;
use std::geometry::smooth::affine::Cotangent;
use std::geometry::smooth::affine::Pt;
use std::geometry::smooth::affine::Line;
use std::geometry::metric::MetricForm;
use std::differential::differential;
use nature::dimension::Reading;
use nature::dimension::PhysicalMetric;
use nature::dimension::Length;
use nature::dimension::Time;

indexed affine C(SmoothR) = Affine(2)[x, t];
indexed metric G: MetricForm<C> = gram((frac(1, 9), 0), (0, frac(1, 4)));
indexed evidence GInvertible = nondegenerate(G);
indexed primitive sharp_g = sharp(Cotangent, Tangent, using = G, evidence = GInvertible);
indexed primitive chart_at = smooth_int_point(Smooth, C, Pt);
indexed primitive vx = fiber_component(Tangent, C, x);
indexed primitive vt = fiber_component(Tangent, C, t);
indexed morphism h: Smooth<C, Line> = pullback(t -> x + t);

indexed reading phys: Reading<C> = (x: Length, t: Time);
indexed scale l0 = 3 of Length;
indexed scale t0 = 2 of Time;
indexed physical PG: PhysicalMetric<C> = interpret(G, reading = phys, gram((l0^-2, 0), (0, t0^-2)));

// The gradient under G: sharp applied to the metric-free differential.
fn gradient(f: Smooth<C, Line>, p: Smooth<Pt, C>) -> Tangent<C> {
    sharp_g(differential(f, p))
}

fn main() -> Int {
    let grad: Tangent<C> = gradient(h(), chart_at(1, 2));
    if pair_second(vx(grad)) == 1 && pair_second(vt(grad)) == 1 {
        100 * pair_first(vx(grad)) + pair_first(vt(grad))
    } else {
        0
    }
}
";

const APP_MANIFEST: &str = "[package]\nname = \"nature_dimension_demo\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n\n[dependencies]\nstd = { path = \"../stdlib\" }\nnature = { path = \"../nature\" }\n";

/// The application `main` in `app/` with copies of the stdlib in `stdlib/`
/// and of the nature package in `nature/`, as in the repository. The app and
/// the nature package both depend on `../stdlib`.
fn fixture(main: &str) -> Scratch {
    let s = common::stdlib_app("nature dimension", APP_MANIFEST, main, &[]);
    s.copy_nature();
    s
}

fn check(s: &Scratch) -> std::process::Output {
    s.check_manifest("app/Vastitas.toml")
}

fn run(s: &Scratch) -> Vec<u8> {
    s.check_build_and_run("app/Vastitas.toml")
}

/// `MAIN` with extra items inserted before `gradient`.
fn with(extra: &str) -> String {
    common::checked_replace(
        MAIN,
        "// The gradient under G",
        &format!("{extra}\n// The gradient under G"),
    )
}

#[track_caller]
fn rejects(main: &str, code: &str) -> String {
    expect_code(&check(&fixture(main)), code)
}

fn request(s: &Scratch) -> Value {
    s.captured("app/Vastitas.toml", 9)
}

fn packages<'a>(wire: &'a Value, name: &str) -> Vec<&'a Value> {
    wire["packages"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|p| p["name"] == name)
        .collect()
}

/// The scaled metric is accepted, and its gradient through the Stage 3
/// `sharp` is (9, 4): the gradient depends on the units through the Gram
/// matrix (C18).
#[test]
fn the_scaled_metric_is_accepted_and_its_gradient_is_nine_four() {
    assert_eq!(run(&fixture(MAIN)), b"904\n");
}

/// The application and the package of `nature::dimension` reach one std
/// package, so the reading of the application's chart is a reading of a
/// `CInfAffine` object of the one std package (C21). The root package of
/// `nature` depends on the dimension package alone and re-exports it.
#[test]
fn nature_and_the_application_share_one_std_package() {
    let wire = request(&fixture(MAIN));
    let [std] = packages(&wire, "vastitas_std").try_into().unwrap();
    let [nature] = packages(&wire, "vastitas_nature").try_into().unwrap();
    let [dimension] = packages(&wire, "vastitas_dimension").try_into().unwrap();
    let [app] = packages(&wire, "nature_dimension_demo").try_into().unwrap();
    for package in [dimension, app] {
        let std_dependency: Vec<&Value> = package["dependencies"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|d| d["alias"] == "std")
            .collect();
        assert_eq!(std_dependency.len(), 1, "{package}");
        assert_eq!(std_dependency[0]["target"], std["source"]);
    }
    // The dimension package depends on std alone, and the root of nature on
    // the dimension package alone.
    assert_eq!(dimension["dependencies"].as_array().unwrap().len(), 1);
    assert_eq!(
        nature["dependencies"],
        json!([{ "alias": "dimension_library", "target": dimension["source"] }])
    );
    // No std package depends on nature or on its dimension package.
    for name in ["vastitas_std", "vastitas_geometry", "vastitas_differential"] {
        for package in packages(&wire, name) {
            for dependency in package["dependencies"].as_array().unwrap() {
                assert_ne!(dependency["target"], nature["source"], "{name}");
                assert_ne!(dependency["target"], dimension["source"], "{name}");
            }
        }
    }
}

/// The Euclidean metric of the chart read as (Length, Time) is rejected:
/// dx² has dimension L² and dt² has dimension T² (C17). The plain std metric
/// with its evidence and `sharp` stays valid.
#[test]
fn euclid_under_length_and_time_is_rejected_naming_l2_and_t2() {
    let euclid = "indexed metric E: MetricForm<C> = euclidean;
indexed evidence EInvertible = nondegenerate(E);
indexed primitive sharp_e = sharp(Cotangent, Tangent, using = E, evidence = EInvertible);";
    success(&check(&fixture(&with(euclid))));
    let stderr = rejects(
        &with(&format!(
            "{euclid}\nindexed physical PE: PhysicalMetric<C> = interpret(E, reading = phys, euclidean);"
        )),
        "E_DIMENSION",
    );
    let message = common::message_text(&stderr);
    assert!(
        message.contains("L^2") && message.contains("T^2"),
        "{stderr}"
    );
}

/// A magnitude mismatch and a scale of the wrong dimension are rejected, and
/// dx² − c²dt² with a speed scale c is accepted (C18). The mismatch has
/// consistent dimensions, (1/2)·t0⁻² = 1/8 in place of 1/4, so only the
/// magnitude check rejects it.
#[test]
fn scaled_interpretations_must_match_the_metric_and_its_dimensions() {
    let stderr = rejects(
        &with(
            "indexed physical Off: PhysicalMetric<C> = interpret(G, reading = phys, gram((l0^-2, 0), (0, frac(1, 2) * t0^-2)));",
        ),
        "E_DIMENSION",
    );
    let message = common::message_text(&stderr);
    assert!(
        message.contains("Off")
            && message.contains("the magnitude 1/8")
            && message.contains("has 1/4 there"),
        "{stderr}"
    );
    let stderr = rejects(
        &with(
            "indexed scale t3 = 3 of Time;\nindexed physical Wrong: PhysicalMetric<C> = interpret(G, reading = phys, gram((t3^-2, 0), (0, t0^-2)));",
        ),
        "E_DIMENSION",
    );
    assert!(stderr.contains("Wrong"), "{stderr}");
    let minkowski = with(concat!(
        "use nature::dimension::Speed;\n",
        "indexed scale c = 3 of Speed;\n",
        "indexed metric M: MetricForm<C> = gram((1, 0), (0, -9));\n",
        "indexed physical PM: PhysicalMetric<C> = interpret(M, reading = phys, gram((1, 0), (0, -1 * c^2)));",
    ));
    success(&check(&fixture(&minkowski)));
}

/// Kinds are nominal: `normalized` with a `Wavelength` scale on the `Length`
/// coordinate is rejected although the dimensions agree, and so is a `Torque`
/// scale on an `Energy` coordinate (C19).
#[test]
fn normalized_needs_the_kind_of_each_coordinate() {
    success(&check(&fixture(&with(
        "indexed physical PN: PhysicalMetric<C> = interpret(G, reading = phys, normalized(x: l0, t: t0));",
    ))));
    let stderr = rejects(
        &with(concat!(
            "use nature::dimension::Wavelength;\n",
            "indexed scale w0 = 3 of Wavelength;\n",
            "indexed physical PW: PhysicalMetric<C> = interpret(G, reading = phys, normalized(x: w0, t: t0));",
        )),
        "E_DIMENSION",
    );
    assert!(stderr.contains("Wavelength"), "{stderr}");
    let energy = concat!(
        "use nature::dimension::Energy;\n",
        "use nature::dimension::Torque;\n",
        "indexed affine Q(SmoothR) = Affine(1)[e];\n",
        "indexed metric GQ: MetricForm<Q> = gram((1));\n",
        "indexed reading energy: Reading<Q> = (e: Energy);\n",
        "indexed scale e0 = 1 of Energy;\n",
        "indexed scale tau = 1 of Torque;\n",
    );
    success(&check(&fixture(&with(&format!(
        "{energy}indexed physical PQ: PhysicalMetric<Q> = interpret(GQ, reading = energy, normalized(e: e0));"
    )))));
    let stderr = rejects(
        &with(&format!(
            "{energy}indexed physical PT: PhysicalMetric<Q> = interpret(GQ, reading = energy, normalized(e: tau));"
        )),
        "E_DIMENSION",
    );
    assert!(stderr.contains("Torque"), "{stderr}");
}

/// The generated Lean of the program is byte identical with and without its
/// nature declarations, and without the nature package at all (C17).
#[test]
fn generated_code_is_byte_identical_without_the_nature_declarations() {
    let generated = |s: &Scratch| {
        let emitted = kernel(request(s), "emit");
        assert_eq!(emitted["ok"], true, "{emitted}");
        emitted["lean_source"].as_str().unwrap().to_owned()
    };
    let with_nature = fixture(MAIN);
    let source = generated(&with_nature);
    let without = fixture(&common::checked_replace(MAIN, NATURE, ""));
    assert_eq!(source, generated(&without));
    // Without the dependency on nature and its imports.
    let imports: String = MAIN
        .lines()
        .filter(|line| line.starts_with("use nature::"))
        .map(|line| format!("{line}\n"))
        .collect();
    assert_eq!(imports.lines().count(), 4);
    let alone = fixture(&common::checked_replace(
        &common::checked_replace(MAIN, NATURE, ""),
        &imports,
        "",
    ));
    alone.write(
        "app/Vastitas.toml",
        &common::checked_replace(APP_MANIFEST, "nature = { path = \"../nature\" }\n", ""),
    );
    let wire = request(&alone);
    assert!(packages(&wire, "vastitas_nature").is_empty());
    assert!(packages(&wire, "vastitas_dimension").is_empty());
    assert_eq!(source, generated(&alone));
    assert_eq!(run(&with_nature), b"904\n");
    assert_eq!(run(&alone), b"904\n");
}

/// The module exports exactly the two families, the three base dimensions
/// and the seven quantity kinds, and nothing else (C21). It is the root module
/// of the package `vastitas_dimension`, and the one module of the root of
/// `nature` re-exports it as `nature::dimension`.
#[test]
fn dimension_module_exports_exactly_its_names() {
    let wire = request(&fixture(MAIN));
    let [nature] = packages(&wire, "vastitas_nature").try_into().unwrap();
    let [package] = packages(&wire, "vastitas_dimension").try_into().unwrap();
    let [root] = nature["modules"].as_array().unwrap().as_slice() else {
        panic!("{nature}");
    };
    let [dimension] = package["modules"].as_array().unwrap().as_slice() else {
        panic!("{package}");
    };
    assert_eq!(root["path"], json!([]));
    assert_eq!(dimension["path"], json!([]));
    let mut imports = root["imports"].clone();
    imports
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .for_each(common::remove_spans);
    assert_eq!(
        imports,
        json!([{ "path": ["dimension_library"], "alias": "dimension", "public": true }])
    );
    for items in ["functions", "generics", "methods"] {
        assert_eq!(root[items], json!([]), "{items}");
    }
    for items in ["imports", "functions", "generics", "methods"] {
        assert_eq!(dimension[items], json!([]), "{items}");
    }
    assert_eq!(dimension["public"], true);
    assert_eq!(
        root["indexed_declarations"].as_array().map_or(0, Vec::len),
        0
    );
    let declarations: Vec<(&str, &str)> = dimension["indexed_declarations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|d| {
            assert_eq!(d["public"], true, "{d}");
            (d["name"].as_str().unwrap(), d["kind"].as_str().unwrap())
        })
        .collect();
    assert_eq!(
        declarations,
        [
            ("Reading", "family"),
            ("PhysicalMetric", "family"),
            ("L", "base_dimension"),
            ("T", "base_dimension"),
            ("M", "base_dimension"),
            ("Length", "quantity"),
            ("Time", "quantity"),
            ("Mass", "quantity"),
            ("Speed", "quantity"),
            ("Wavelength", "quantity"),
            ("Energy", "quantity"),
            ("Torque", "quantity"),
        ]
    );
    // The families index std's smooth affine objects.
    let mut families = dimension["indexed_declarations"].as_array().unwrap()[..2].to_vec();
    families.iter_mut().for_each(common::remove_spans);
    let object = json!([{ "kind": "object",
        "domain": { "path": ["std", "geometry", "smooth", "affine", "CInfAffine"] } }]);
    for (family, representation) in families.iter().zip(["reading", "physical_metric"]) {
        assert_eq!(family["parameters"], object, "{family}");
        assert_eq!(family["representation"], representation, "{family}");
        assert_eq!(
            family["constraints"],
            json!([{ "kind": "canonical", "object": 0 }])
        );
    }
    // The package declares no reading, scale, interpretation or metric: those
    // are the application's.
    let kinds: Vec<&str> = declarations.iter().map(|(_, kind)| *kind).collect();
    for kind in ["reading", "scale", "physical_metric", "metric", "frame"] {
        assert!(!kinds.contains(&kind), "{kind}");
    }
    for name in [
        "Dimension",
        "Velocity",
        "Ratio",
        "Angle",
        "Celsius",
        "Metre",
    ] {
        let stderr = rejects(&with(&format!("use nature::dimension::{name};")), "E_NAME");
        assert!(
            stderr.contains(&format!("undefined name '{name}'")),
            "{stderr}"
        );
    }
}

/// The module is reachable by item imports, full paths, an alias and a
/// plain `use nature::dimension;`, since `dimension` is an ordinary name
/// (#778). `dim`, the geometric operation, is no alias.
#[test]
fn the_dimension_module_is_reachable_by_items_paths_and_an_alias() {
    success(&check(&fixture(&with(concat!(
        "use nature::dimension as units;\n",
        "indexed scale s1 = 1 of units::Length;\n",
        "indexed scale s2 = 2 of nature::dimension::Mass;",
    )))));
    success(&check(&fixture(&with(concat!(
        "use nature::dimension;\n",
        "indexed scale s1 = 1 of dimension::Length;",
    )))));
    rejects(&with("use nature::dimension as dim;"), "E_RESERVED");
}

/// A std manifest that depends on nature forms a cycle, since nature depends
/// on std (C20; `scripts/check_boundaries.py` rejects the edge by itself).
#[test]
fn a_std_manifest_that_depends_on_nature_forms_a_cycle() {
    let s = fixture(MAIN);
    let manifest = read(&s.0.join("stdlib/src/geometry/Vastitas.toml"))
        + "\n[dependencies]\nnature = { path = \"../../../nature\" }\n";
    s.write("stdlib/src/geometry/Vastitas.toml", &manifest);
    expect_code(&check(&s), "E_CYCLE");
}
