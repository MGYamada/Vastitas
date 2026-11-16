//! `std::linalg::spectral` from a path package (Stage 5, #806; C12, C17). An
//! application that depends on a copy of the stdlib declares free modules,
//! endomorphism fields, spectra and a branch on its own objects with the
//! library's families, declares the invariants and observations that name
//! them, and observes their values natively. The tests also audit the public
//! names of the package `vastitas_linalg` and its family contracts (ADR 0001
//! §12).
mod common;
use common::{Run, Scratch, exits, expect_code};
use serde_json::{Value, json};

/// The plane with three fields: L = (x + y) of rank 1, whose one eigenvalue
/// x + y is simple everywhere, so its chart is the whole plane with the
/// witness 1; D = diag(x, y, x + y, 1) of rank 4, the limit, with
/// chi = (s - x)(s - y)(s - x - y)(s - 1); and the zero field Z. The fiber
/// coordinate is s. At p = (1, 2) the branch point is (p, 3), where the
/// eigenvalue has the differential (1, 1) and the eigenprojector 1. Each
/// observation has its own failure bit, 2^(k−1) for the code k, so `main`
/// returns 42 only when all of them hold, and the bits above 42 name every
/// observation that fails.
const MAIN: &str = r#"
use std::geometry::smooth::affine::SmoothR;
use std::geometry::smooth::affine::Smooth;
use std::geometry::smooth::affine::Cotangent;
use std::geometry::smooth::affine::Pt;
use std::geometry::smooth::affine::Line;
use std::geometry::smooth::affine::same_smooth;
use std::geometry::smooth::affine::line_at;
use std::geometry::smooth::affine::same_covector;
use std::linalg::spectral::FreeModule;
use std::linalg::spectral::Endomorphism;
use std::linalg::spectral::Spectrum;
use std::linalg::spectral::Branch;
use std::differential::differential;

indexed affine Plane(SmoothR) = Affine(2)[x, y];
indexed free_module U: FreeModule<Plane> = basis(u);
indexed endomorphism L: Endomorphism<Plane> = rows((x + y)) of U symmetric;
indexed spectrum SL: Spectrum<Plane> = eigen(L, s);
indexed branch BL: Branch<Plane> = simple(SL, localize = 1, witness = 1, exponent = 1);
indexed free_module V4: FreeModule<Plane> = basis(e1, e2, e3, e4);
indexed endomorphism D: Endomorphism<Plane> = rows((x, 0, 0, 0), (0, y, 0, 0), (0, 0, x + y, 0), (0, 0, 0, 1)) of V4 symmetric;
indexed spectrum SD: Spectrum<Plane> = eigen(D, s);
indexed free_module V: FreeModule<Plane> = basis(e1, e2);
indexed endomorphism Z: Endomorphism<Plane> = rows((0, 0), (0, 0)) of V symmetric;
indexed spectrum SZ: Spectrum<Plane> = eigen(Z, s);

indexed morphism trd3: Smooth<Plane, Line> = trace_power(D, 3);
indexed morphism refd3: Smooth<Plane, Line> = pullback(t -> x^3 + y^3 + (x + y)^3 + 1);
indexed morphism cd0: Smooth<Plane, Line> = char_coefficient(SD, 0);
indexed morphism refd0: Smooth<Plane, Line> = pullback(t -> x*y*(x + y));
indexed morphism trz: Smooth<Plane, Line> = trace_power(Z, 2);

indexed primitive plane_at = smooth_int_point(Smooth, Plane, Pt);
indexed primitive dplane = fiber_vector(Cotangent, Smooth, Plane);
indexed primitive on_l = on_branch(Smooth, Line, branch = BL);
indexed primitive dl = branch_differential(Smooth, Cotangent, Line, branch = BL);
indexed primitive pl = branch_projector(Smooth, Line, branch = BL, u, u);
indexed primitive ann_d = annihilates(Smooth, spectrum = SD, element = (s - x) * (s - y) * (s - x - y) * (s - 1));
indexed primitive act_d = action_entry(Smooth, spectrum = SD, element = s^2, e3, e3);
indexed primitive ann_z = annihilates(Smooth, spectrum = SZ, element = s);

fn verdict(ok: Bool, code: Int) -> Int { if ok { 0 } else { code } }

// An entry reads n / d.
fn reads(value: Pair<Int>, n: Int, d: Int) -> Bool {
    pair_first(value) == n && pair_second(value) == d
}

fn main() -> Int {
    let p: Smooth<Pt, Plane> = plane_at(1, 2);
    // The rank-1 branch: x + y = 3 at p, with d(x + y) = (1, 1) and P = 1.
    42 + verdict(on_l(p, line_at(3)) && !on_l(p, line_at(2)), 1)
       + verdict(same_covector(dl(p, line_at(3)), dplane(p, 1, 1)), 2)
       + verdict(reads(pl(p, line_at(3)), 1, 1), 4)
       // The rank-4 field: tr(D^3) and det(D) as smooth maps, chi(D) = 0, and
       // the entry (e3, e3) of D^2 is (x + y)^2 = 9 at p.
       + verdict(same_smooth(trd3(), refd3()) && same_smooth(cd0(), refd0()), 8)
       + verdict(ann_d(p) && reads(act_d(p), 9, 1), 16)
       // The zero field: s annihilates it, and tr(Z^2) = 0 has the zero differential.
       + verdict(ann_z(p) && same_covector(differential(trz(), p), dplane(p, 0, 0)), 32)
}
"#;

/// The application `main` in `app/`, with a copy of the stdlib in `stdlib/`
/// as its `std` path dependency.
fn fixture(main: &str) -> Scratch {
    common::stdlib_app(
        "stdlib spectral",
        "[package]\nname = \"stdlib_spectral_demo\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n\n[dependencies]\nstd = { path = \"../stdlib\" }\n",
        main,
        &[],
    )
}

fn check(s: &Scratch) -> std::process::Output {
    s.check_manifest("app/Vastitas.toml")
}

fn run(s: &Scratch) -> Run {
    s.check_build_and_run("app/Vastitas.toml")
}

/// `MAIN` with extra items inserted before its helpers.
fn with(extra: &str) -> String {
    common::checked_replace(MAIN, "fn verdict(", &format!("{extra}\nfn verdict("))
}

#[track_caller]
fn rejects(main: &str, code: &str) -> String {
    expect_code(&check(&fixture(main)), code)
}

fn request(s: &Scratch) -> Value {
    s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL)
}

/// The module of a package in the wire.
fn module<'a>(wire: &'a Value, package: &str, path: &[&str]) -> &'a Value {
    wire["packages"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["name"] == package)
        .unwrap_or_else(|| panic!("no package {package}"))["modules"]
        .as_array()
        .unwrap()
        .iter()
        .find(|m| m["path"] == json!(path))
        .unwrap_or_else(|| panic!("{package}: no module {path:?}"))
}

/// `value` without its source spans.
fn without_spans(value: &Value) -> Value {
    let mut value = value.clone();
    common::remove_spans(&mut value);
    value
}

/// A rank-1 field, a field of rank 4 at the limit and the zero field check,
/// build and run from a path package (C12).
#[test]
fn spectral_families_from_the_library_check_build_and_run_from_a_path_package() {
    assert_eq!(run(&fixture(MAIN)), exits(42));
}

/// Each observation can fail, and each mutation below falsifies exactly its
/// own observation: another eigenvalue (bit 1), another covector for the
/// differential (2), another entry of the projector (4), another reference
/// for the trace power (8), the entry of D rather than D^2 (16) and the
/// negated annihilation by s of the zero field (32). With every mutation the
/// program exits with 42 + 63, and the bits name every code.
#[test]
fn mutated_spectral_observations_change_the_native_result() {
    let mutations = [
        ("on_l(p, line_at(3)) &&", "on_l(p, line_at(4)) &&"),
        ("dplane(p, 1, 1)), 2)", "dplane(p, 1, 2)), 2)"),
        (
            "reads(pl(p, line_at(3)), 1, 1)",
            "reads(pl(p, line_at(3)), 1, 2)",
        ),
        ("(x + y)^3 + 1)", "(x + y)^3 + 2)"),
        ("element = s^2, e3, e3", "element = s, e3, e3"),
        ("verdict(ann_z(p) &&", "verdict(!ann_z(p) &&"),
    ];
    let main = mutations.iter().fold(MAIN.to_string(), |main, (from, to)| {
        common::checked_replace(&main, from, to)
    });
    assert_eq!(run(&fixture(&main)), exits(42 + 63));
}

/// The package `vastitas_linalg` has the root module, which exports the
/// module `spectral` alone, and `spectral` exports exactly the four families,
/// and nothing else (C17). It depends on the geometry package alone.
#[test]
fn linalg_exports_exactly_the_spectral_module_and_its_four_families() {
    let wire = request(&fixture(MAIN));
    let package = wire["packages"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["name"] == "vastitas_linalg")
        .unwrap();
    let aliases: Vec<&str> = package["dependencies"]
        .as_array()
        .unwrap()
        .iter()
        .map(|d| d["alias"].as_str().unwrap())
        .collect();
    assert_eq!(aliases, ["geometry"]);
    let paths: Vec<&Value> = package["modules"]
        .as_array()
        .unwrap()
        .iter()
        .map(|m| &m["path"])
        .collect();
    assert_eq!(paths, [&json!([]), &json!(["spectral"])]);
    let root = module(&wire, "vastitas_linalg", &[]);
    assert_eq!(root["public"], true);
    for items in ["imports", "functions", "generics", "methods"] {
        assert_eq!(root[items], json!([]), "{items}");
    }
    assert!(
        root["indexed_declarations"]
            .as_array()
            .is_none_or(|d| d.is_empty()),
        "{root}"
    );
    let spectral = module(&wire, "vastitas_linalg", &["spectral"]);
    assert_eq!(spectral["public"], true);
    for items in ["imports", "functions", "generics", "methods"] {
        assert_eq!(spectral[items], json!([]), "{items}");
    }
    // The families and their contracts: each indexes one smooth affine object
    // of std::geometry::smooth::affine, canonically.
    let family = |name: &str, representation: &str| {
        json!({ "name": name, "kind": "family", "public": true,
                "parameters": [{ "kind": "object",
                    "domain": { "path": ["geometry", "smooth", "affine", "CInfAffine"] } }],
                "constraints": [{ "kind": "canonical", "object": 0 }],
                "representation": representation })
    };
    assert_eq!(
        without_spans(&spectral["indexed_declarations"]),
        json!([
            family("FreeModule", "free_module"),
            family("Endomorphism", "endomorphism"),
            family("Spectrum", "spectrum"),
            family("Branch", "branch"),
        ])
    );
    // The library declares no module, field, spectrum, branch, invariant or
    // observation: the application declares them.
    let kinds = ["free_module", "endomorphism", "spectrum", "branch"];
    let ops = [
        "annihilates",
        "action_entry",
        "on_branch",
        "branch_differential",
        "branch_projector",
    ];
    for p in wire["packages"].as_array().unwrap() {
        if p["name"] == "stdlib_spectral_demo" {
            continue;
        }
        for m in p["modules"].as_array().unwrap() {
            for d in m["indexed_declarations"].as_array().into_iter().flatten() {
                assert!(!kinds.contains(&d["kind"].as_str().unwrap()), "{d}");
                let op = d["binding"]["op"].as_str().unwrap_or("");
                assert!(!ops.contains(&op), "{d}");
                let definition = d["definition"]["kind"].as_str().unwrap_or("");
                assert!(
                    !["trace_power", "char_coefficient"].contains(&definition),
                    "{d}"
                );
            }
        }
    }
    // No other name resolves in the module or at the root of the package.
    for name in [
        "spectral::FreeModuleOf",
        "spectral::Matrix",
        "spectral::Eigen",
        "spectral::basis",
        "spectral::rows",
        "spectral::eigen",
        "spectral::simple",
        "spectral::trace_power",
        "spectral::char_coefficient",
        "spectral::annihilates",
        "spectral::on_branch",
        "FreeModule",
        "Endomorphism",
        "geometry",
    ] {
        let leaf = name.rsplit("::").next().unwrap();
        let stderr = rejects(
            &with(&format!("use std::linalg::{name} as probe;")),
            "E_NAME",
        );
        assert!(
            stderr.contains(&format!("undefined name '{leaf}'")),
            "{name}: {stderr}"
        );
    }
}

/// A free module of `BaseSmooth`, a global object of the smooth grid and no
/// smooth affine object, is rejected before its family is consulted.
#[test]
fn a_free_module_of_an_object_that_is_not_smooth_is_rejected() {
    let stderr = rejects(
        &with(
            "indexed free_module bad: FreeModule<std::geometry::smooth::BaseSmooth> = basis(b1);",
        ),
        "E_SPECTRAL",
    );
    assert!(
        stderr.contains(
            "E_SPECTRAL: the free module `stdlib_spectral_demo::bad` is on \
             `vastitas_geometry::smooth::BaseSmooth`, which is not a smooth object; it needs a \
             smooth object declared with `Affine(n)[…]`"
        ),
        "{stderr}"
    );
}

/// A smooth affine object `Q` of another classification, `Other`, with local
/// families of `Other` that declare a free module, a field and a spectrum on
/// `Q`. The library's families index `CInfAffine` only.
const OTHER: &str = "indexed marker R2;
indexed implementation SmoothR2(R2, smooth_affine) capabilities();
indexed classification Other { parents(); domain(SmoothR2); };
indexed affine Q(SmoothR2) = Affine(1)[q];
indexed family FM2(object(Other)) = free_module constraints(canonical(0));
indexed family EN2(object(Other)) = endomorphism constraints(canonical(0));
indexed family SP2(object(Other)) = spectrum constraints(canonical(0));
indexed free_module W: FM2<Q> = basis(b1);
indexed endomorphism K: EN2<Q> = rows((q)) of W;
indexed spectrum SK: SP2<Q> = eigen(K, s);
";

/// A free module of the smooth affine object `Q` of `OTHER`, outside
/// `CInfAffine`, is rejected: it is on `Q`, which its family does not accept.
/// So is a field, a spectrum and a branch on `Q` at the library's family,
/// while the same declarations at the local families of `Other` are
/// accepted.
#[test]
fn a_free_module_of_an_object_outside_cinf_affine_is_rejected() {
    assert_eq!(
        run(&fixture(&with(&format!(
            "{OTHER}indexed family BR2(object(Other)) = branch constraints(canonical(0));\n\
             indexed branch BK: BR2<Q> = simple(SK, localize = 1, witness = 1, exponent = 1);"
        )))),
        exits(42)
    );
    for (kind, family, declaration) in [
        (
            "free module",
            "FreeModule",
            "indexed free_module bad: FreeModule<Q> = basis(b1);",
        ),
        (
            "endomorphism",
            "Endomorphism",
            "indexed endomorphism bad: Endomorphism<Q> = rows((q)) of W;",
        ),
        (
            "spectrum",
            "Spectrum",
            "indexed spectrum bad: Spectrum<Q> = eigen(K, s);",
        ),
        (
            "branch",
            "Branch",
            "indexed branch bad: Branch<Q> = simple(SK, localize = 1, witness = 1, exponent = 1);",
        ),
    ] {
        let stderr = rejects(&with(&format!("{OTHER}{declaration}")), "E_SPECTRAL");
        assert!(
            stderr.contains(&format!(
                "E_SPECTRAL: the {kind} `stdlib_spectral_demo::bad` is on `stdlib_spectral_demo::Q`, \
                 which its family `vastitas_linalg::spectral::{family}` does not accept"
            )),
            "{kind}: {stderr}"
        );
    }
}
