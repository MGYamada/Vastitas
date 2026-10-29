mod common;
use common::{Scratch, cli, kernel, success};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;

const LIBRARY: &[(&str, &str)] = &[
    ("lib.vast", include_str!("../stdlib/geometry/src/lib.vast")),
    (
        "scheme.vast",
        include_str!("../stdlib/geometry/src/scheme.vast"),
    ),
    (
        "smooth.vast",
        include_str!("../stdlib/geometry/src/smooth.vast"),
    ),
];
const ENTRYPOINT: &str = include_str!("../stdlib/indexed/src/lib.vast");
const MANIFEST: &str = include_str!("../stdlib/geometry/Vastitas.toml");
const DEMO: &str = include_str!("../examples/packages/stdlib-geometry/main.vast");

fn fixture(source: &str, rewrite: impl Fn(&str) -> String) -> Scratch {
    let s = Scratch::empty("stdlib geometry");
    s.write("geo/Vastitas.toml", MANIFEST);
    for (name, source) in LIBRARY {
        s.write(&format!("geo/src/{name}"), &rewrite(source));
    }
    s.write("standard/src/lib.vast", ENTRYPOINT);
    s.write("standard/Vastitas.toml", &format!("[package]\nname='vastitas_std_indexed'\nversion='0.1.0'\nroot='src/lib.vast'\n[dependencies]\ngeometry_library={{path='../geo'}}\narithmetic_library={{path='{}'}}\n", common::root().join("stdlib").display()));
    s.write("app/Vastitas.toml", "[package]\nname='app'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\nstd={path='../standard'}\ngeo={path='../geo'}\nsame={path='../geo'}\n");
    s.write("app/main.vast", source);
    s
}

fn check(s: &Scratch) -> std::process::Output {
    cli()
        .current_dir(&s.0)
        .args(["check", "--manifest-path", "app/Vastitas.toml"])
        .output()
        .unwrap()
}

fn reject(source: &str, code: &str) {
    let result = check(&fixture(source, str::to_owned));
    assert!(!result.status.success(), "accepted {source}");
    assert!(
        String::from_utf8_lossy(&result.stderr).contains(code),
        "{result:?}"
    );
}

fn native(s: &Scratch) {
    native_result(s, b"42\n");
}

fn native_result(s: &Scratch, expected: &[u8]) {
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
    assert_eq!(result.stdout, expected);
}

#[test]
fn pointed_and_smooth_workflows_migrate_without_erasing_abstract_annotations() {
    native(&fixture(
        include_str!("../examples/packages/stdlib-geometry/pointed/main.vast"),
        str::to_owned,
    ));
    native_result(
        &fixture(
            include_str!("../examples/packages/stdlib-geometry/smooth/main.vast"),
            str::to_owned,
        ),
        b"2\n",
    );
}

#[test]
fn ordinary_and_smooth_stdlib_packages_preserve_points_and_run() {
    native(&fixture(DEMO, str::to_owned));
    native(&fixture(
        &DEMO.replace("scheme::apply", "same::scheme::apply"),
        str::to_owned,
    ));
}

#[test]
fn coherent_renaming_retains_contracts_without_privileged_geometry_names() {
    let rename = |text: &str| {
        text.replace("Scheme", "Space")
            .replace("QQ", "Rational")
            .replace("CInfReal", "SmoothScalar")
            .replace("Point", "Position")
            .replace("Morphism", "Arrow")
    };
    native(&fixture(&rename(DEMO), rename));
}

#[test]
fn domains_coefficients_and_base_objects_are_separate() {
    reject(
        "fn main() -> Int { let X: Object<geo::scheme::Scheme, geo::scheme::QQ> = geo::smooth::Affine(2); 0 }",
        "E_TYPE",
    );
    reject(
        "fn main() -> Int { let X = geo::scheme::Affine(2); let p: geo::Point<X, geo::scheme::QQ> = geo::scheme::origin(X); 0 }",
        "E_TYPE",
    );
    reject(
        "fn main() -> Int { let X = geo::scheme::Affine(2); let Y = geo::smooth::Affine(2); let p: geo::Point<X, Y> = geo::scheme::origin(X); 0 }",
        "E_TYPE",
    );
    reject(
        "fn main() -> Int { let X = geo::scheme::Affine(2); let d = geo::smooth::dimension(X); 0 }",
        "E_ENDPOINT",
    );
}

#[test]
fn generated_objects_and_opened_witnesses_do_not_collapse() {
    reject(
        "fn main() -> Int { let X = geo::scheme::Affine(2); let Y = geo::scheme::Affine(2); let p = geo::scheme::origin(X); let q: geo::Point<Y, geo::scheme::BaseQQ> = p; 0 }",
        "E_TYPE",
    );
    reject(
        "fn main() -> Int { let a = geo::scheme::pointed(2); let b = geo::scheme::pointed(2); unpack a as { witness: X, fields: [p] }; unpack b as { witness: Y, fields: [q] }; let wrong: geo::Point<Y, geo::scheme::BaseQQ> = p; 0 }",
        "E_TYPE",
    );
}

#[test]
fn copying_the_library_package_does_not_copy_its_nominal_identity() {
    let s = fixture(
        "fn main() -> Int { let X: Object<geo::scheme::Scheme, geo::scheme::QQ> = other::scheme::Affine(2); 0 }",
        str::to_owned,
    );
    s.write("other/Vastitas.toml", MANIFEST);
    for (name, source) in LIBRARY {
        s.write(&format!("other/src/{name}"), source);
    }
    let path = s.0.join("app/Vastitas.toml");
    let manifest = std::fs::read_to_string(&path).unwrap() + "other={path='../other'}\n";
    s.write("app/Vastitas.toml", &manifest);
    let result = check(&s);
    assert!(!result.status.success());
    assert!(
        String::from_utf8_lossy(&result.stderr).contains("E_TYPE"),
        "{result:?}"
    );
}

#[test]
fn geometry_and_arithmetic_share_the_checked_protocol_seven_closure() {
    let s = fixture(
        "fn main() -> Int { let X = geo::scheme::Affine(20); arithmetic::arithmetic::generic::add(int(geo::scheme::dimension(X)), 22) }",
        str::to_owned,
    );
    let path = s.0.join("app/Vastitas.toml");
    let manifest = std::fs::read_to_string(path).unwrap()
        + &format!(
            "arithmetic={{path='{}'}}\n",
            common::root().join("stdlib").display()
        );
    s.write("app/Vastitas.toml", &manifest);
    native(&s);
}

#[test]
fn dependent_morphism_calls_retain_the_point_test_object_through_repacking() {
    let source = r#"
fn act(X: Object<geo::scheme::Scheme, geo::scheme::QQ>, Y: Object<geo::scheme::Scheme, geo::scheme::QQ>, S: Object<geo::scheme::Scheme, geo::scheme::QQ>, f: geo::Morphism<X, Y>, p: geo::Point<X, S>) -> geo::Point<Y, S> {
    geo::apply(f, p)
}
fn main() -> Int {
    let X = geo::scheme::Affine(42);
    let S = geo::scheme::base();
    let p = act(X, X, S, geo::scheme::id(X), geo::scheme::origin(X));
    let packed = pack geo::Pointed<geo::scheme::Scheme, geo::scheme::QQ> { witness: X, fields: [p] };
    unpack packed as { witness: Y, fields: [q] };
    int(geo::scheme::dimension(Y))
}
"#;
    native(&fixture(source, str::to_owned));
}

#[test]
fn classification_does_not_manufacture_missing_implementation_capabilities() {
    for capabilities in ["origin", "dimension", ""] {
        let result = check(&fixture("fn main() -> Int { 42 }", |source| {
            source.replace(
                "capabilities(origin, dimension)",
                &format!("capabilities({capabilities})"),
            )
        }));
        assert!(
            !result.status.success(),
            "accepted incomplete implementation: {capabilities}"
        );
        assert!(
            String::from_utf8_lossy(&result.stderr).contains("E_TYPE"),
            "{result:?}"
        );
    }
}

#[test]
fn public_reexports_retain_family_and_arithmetic_function_identity() {
    let s = fixture(
        r#"
use std::geometry::scheme as scheme;
use std::geometry::smooth as smooth;
fn main() -> Int {
    let X = scheme::Affine(20);
    let p: geo::Point<X, scheme::BaseQQ> = scheme::origin(X);
    let q: smooth::Point<X, scheme::BaseQQ> = same::scheme::apply(scheme::id(X), p);
    let add = if true { std::arithmetic::integers::int_add } else { arithmetic::arithmetic::integers::int_add };
    add(int(scheme::dimension(X)), 22)
}
"#,
        str::to_owned,
    );
    let manifest = std::fs::read_to_string(s.0.join("app/Vastitas.toml")).unwrap()
        + &format!(
            "arithmetic={{path='{}'}}\n",
            common::root().join("stdlib").display()
        );
    s.write("app/Vastitas.toml", &manifest);
    native(&s);
}

#[test]
fn private_support_and_future_geometry_namespaces_are_not_public() {
    reject(
        "pub use geo::Objects as Exposed; fn main() -> Int { 0 }",
        "E_VISIBILITY",
    );
    for module in ["complex", "symplectic", "variety", "kahler"] {
        reject(
            &format!("use std::geometry::{module} as future; fn main() -> Int {{ 0 }}"),
            "E_NAME",
        );
    }
    reject(
        "method std::arithmetic::generic::add(x: Int, y: Int) -> Int { 0 } fn main() -> Int { 0 }",
        "E_OWNER",
    );
}

#[test]
fn original_arithmetic_entrypoint_still_accepts_legacy_geometry() {
    let s = Scratch::empty("legacy std geometry");
    s.write("app/Vastitas.toml", &format!("[package]\nname='app'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\nstd={{path='{}'}}\n", common::root().join("stdlib").display()));
    s.write("app/main.vast", "fn main() -> Int { let X = Affine(QQ, 20); std::arithmetic::generic::add(int(dimension(X)), 22) }");
    native(&s);
}

#[test]
fn kernel_reconstructs_module_visibility_and_geometry_contracts_from_wire() {
    let s = fixture(DEMO, str::to_owned);
    let stub = s.write("capture", "#!/bin/sh\ncat > wire.json\nprintf '%s\\n' '{\"version\":7,\"ok\":false,\"diagnostics\":[{\"code\":\"E_CAPTURED\",\"message\":\"captured\"}]}'\nexit 1\n");
    std::fs::set_permissions(&stub, std::fs::Permissions::from_mode(0o755)).unwrap();
    let output = cli()
        .current_dir(&s.0)
        .env("VASTITAS_KERNEL", stub)
        .args(["check", "--manifest-path", "app/Vastitas.toml"])
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("E_CAPTURED"),
        "{output:?}"
    );
    let original: Value =
        serde_json::from_slice(&std::fs::read(s.0.join("wire.json")).unwrap()).unwrap();
    assert_eq!(original["version"], 7);
    assert_eq!(kernel(&original, "check")["ok"], true);
    assert_eq!(kernel(&original, "emit")["ok"], true);
    let geo = original["packages"]
        .as_array()
        .unwrap()
        .iter()
        .position(|p| p["name"] == "vastitas_geometry")
        .unwrap();
    let scheme = original["packages"][geo]["modules"]
        .as_array()
        .unwrap()
        .iter()
        .position(|m| m["path"] == json!(["scheme"]))
        .unwrap();
    for mutation in [
        "private module",
        "wrong base",
        "forged owner",
        "missing capability",
    ] {
        let mut raw = original.clone();
        let module = &mut raw["packages"][geo]["modules"][scheme];
        match mutation {
            "private module" => module["public"] = json!(false),
            "wrong base" => {
                let origin = module["indexed_declarations"]
                    .as_array_mut()
                    .unwrap()
                    .iter_mut()
                    .find(|d| d["name"] == "origin")
                    .unwrap();
                origin["binding"]["base_object"]["path"] =
                    json!(["package", "smooth", "BaseSmooth"]);
            }
            "forged owner" => module["indexed_declarations"][0]["owner"] = json!("stdlib"),
            _ => {
                let implementation = module["indexed_declarations"]
                    .as_array_mut()
                    .unwrap()
                    .iter_mut()
                    .find(|d| d["name"] == "GridQQ")
                    .unwrap();
                implementation["capabilities"] = json!([]);
            }
        }
        for mode in ["check", "emit"] {
            let result = kernel(&raw, mode);
            assert_eq!(result["ok"], false, "{mutation}/{mode}: {result}");
            assert!(result.get("lean_source").is_none(), "{result}");
        }
    }
}
