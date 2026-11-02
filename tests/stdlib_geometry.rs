mod common;
use common::{Scratch, cli, kernel, success};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;

const LIBRARY: &[(&str, &str)] = &[
    ("mod.vast", include_str!("../stdlib/src/geometry/mod.vast")),
    (
        "scheme/mod.vast",
        include_str!("../stdlib/src/geometry/scheme/mod.vast"),
    ),
    (
        "smooth/mod.vast",
        include_str!("../stdlib/src/geometry/smooth/mod.vast"),
    ),
];
const MANIFEST: &str = include_str!("../stdlib/src/geometry/Vastitas.toml");
const DEMO: &str = include_str!("../examples/packages/stdlib-geometry/main.vast");

fn fixture(source: &str, rewrite: impl Fn(&str) -> String) -> Scratch {
    common::prepare_stdlib_package();
    let s = Scratch::empty("stdlib geometry");
    s.write("geo/Vastitas.toml", &rewrite(MANIFEST));
    for (name, source) in LIBRARY {
        s.write(&format!("geo/{name}"), &rewrite(source));
    }
    for name in [
        "lib.vast",
        "arithmetic.vast",
        "arithmetic/integers.vast",
        "arithmetic/naturals.vast",
        "arithmetic/generic.vast",
    ] {
        s.write(
            &format!("standard/{name}"),
            &std::fs::read_to_string(common::root().join("stdlib/target/package").join(name))
                .unwrap(),
        );
    }
    s.write("standard/Vastitas.toml", "[package]\nname='vastitas_std'\nversion='0.1.0'\nroot='lib.vast'\n[dependencies]\ngeometry_library={path='../geo'}\n");
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
fn unchanged_legacy_examples_use_the_declared_stdlib_profile() {
    native(&fixture(
        include_str!("../examples/pointed.vast"),
        str::to_owned,
    ));
    native_result(
        &fixture(include_str!("../examples/smooth.vast"), str::to_owned),
        b"2\n",
    );
}

#[test]
fn legacy_and_declared_types_share_endpoints_packages_and_primitives() {
    native(&fixture(
        r#"
fn act(X: Scheme, S: Scheme, f: geo::Morphism<X, X>, p: Point<X, S>) -> geo::Point<X, S> {
    apply(f, p)
}
fn main() -> Int {
    let X: Scheme = geo::scheme::Affine(42);
    let S = Base(QQ);
    let p = act(X, S, id(X), geo::scheme::origin(X));
    let boxed: geo::Pointed<geo::scheme::Scheme, geo::scheme::QQ> = pack { scheme: X, point: p };
    unpack boxed as { witness: Y, fields: [q] };
    let again: Pointed<Scheme, QQ> = pack geo::Pointed<geo::scheme::Scheme, geo::scheme::QQ> { witness: Y, fields: [apply(geo::scheme::id(Y), q)] };
    unpack again as { scheme: Z, point: z };
    int(geo::scheme::dimension(Z))
}
"#,
        str::to_owned,
    ));
}

#[test]
fn legacy_profile_paths_can_be_coherently_renamed() {
    native(&fixture(include_str!("../examples/pointed.vast"), |text| {
        text.replace("Scheme", "Space")
            .replace("QQ", "Rational")
            .replace("Point", "Position")
            .replace("Morphism", "Arrow")
    }));
}

#[test]
fn legacy_geometry_inside_independent_lambdas_is_checked() {
    native(&fixture(
        r#"
fn run(f: Fn<Nat, Int>, n: Nat) -> Int { f(n) }
fn main() -> Int {
    run(fn(n: Nat) -> Int { let X: Scheme = Affine(QQ, n); int(dimension(X)) }, 42)
}
"#,
        str::to_owned,
    ));
    reject(
        "fn main() -> Int { let X = Affine(QQ, 2); let f = fn(n: Int) -> Int { let p: Point<X, Base(QQ)> = origin(X); n }; 0 }",
        "E_CAPTURE",
    );
    reject(
        "fn unused(f: Fn<Int, Int>) -> Int { let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let p = apply(id(X), origin(Y)); f(0) } fn main() -> Int { 0 }",
        "E_ENDPOINT",
    );
}

#[test]
fn legacy_alias_branches_and_anonymous_outer_endpoints_survive_library_lowering() {
    native(&fixture(
        r#"
fn main() -> Int {
    let X = Affine(QQ, 42);
    let Y = X;
    let Z = if false { X } else { Y };
    let p: Point<Z, Base(QQ)> = apply(compose(id(X), id(Y)), origin(X));
    let anonymous = origin(Affine(QQ, 2));
    let kept = { anonymous };
    let boxed = pack { scheme: Z, point: p };
    unpack boxed as { scheme: W, point: q };
    int(dimension(W))
}
"#,
        str::to_owned,
    ));
}

#[test]
fn legacy_endpoint_base_and_scope_failures_preserve_existing_output() {
    let cases = [
        (
            "let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let p = apply(id(X), origin(Y));",
            "E_ENDPOINT",
        ),
        (
            "let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let f = compose(id(X), id(Y));",
            "E_ENDPOINT",
        ),
        (
            "let X = Affine(QQ, 2); let p: Point<X, Base(CInfReal)> = origin(X);",
            "E_BASE",
        ),
        (
            "let X = Affine(QQ, 2); let p: Point<X, QQ> = origin(X);",
            "E_TYPE",
        ),
        (
            "let X = Affine(QQ, 2); let S = Affine(QQ, 0); let p: Point<X, S> = origin(X);",
            "E_TYPE",
        ),
        (
            "let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let p = pack { scheme: X, point: origin(Y) };",
            "E_ENDPOINT",
        ),
        ("let p = { let X = Affine(QQ, 2); origin(X) };", "E_ESCAPE"),
        ("let f = { let X = Affine(QQ, 2); id(X) };", "E_ESCAPE"),
        (
            "let p = { let X = Affine(QQ, 2); let a = pack { scheme: X, point: origin(X) }; unpack a as { scheme: Y, point: q }; q };",
            "E_ESCAPE",
        ),
        (
            "let X = Affine(QQ, 2); let a: Pointed<CInfScheme, CInfReal> = pack { scheme: X, point: origin(X) };",
            "E_TYPE",
        ),
        (
            "let X = Affine(QQ, 2); let Y = same_object(X); let p: Point<Y, Base(QQ)> = origin(X);",
            "E_TYPE",
        ),
        (
            "let X = Affine(QQ, 2); let a = pack { scheme: X, point: origin(X) }; unpack a as { scheme: Y, point: p }; unpack a as { scheme: Z, point: q }; let bad: Point<Y, Base(QQ)> = q;",
            "E_TYPE",
        ),
        (
            "let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let Z = if true { X } else { Y }; let p: Point<Z, Base(QQ)> = origin(X);",
            "E_TYPE",
        ),
    ];
    for (body, code) in cases {
        let s = fixture(
            &format!("fn same_object(X: Scheme) -> Scheme {{ X }} fn main() -> Int {{ {body} 0 }}"),
            str::to_owned,
        );
        s.write("program", "preserve this output");
        for mode in ["check", "build"] {
            let mut command = cli();
            command
                .current_dir(&s.0)
                .args([mode, "--manifest-path", "app/Vastitas.toml"]);
            if mode == "build" {
                command.args(["-o", "program"]);
            }
            let output = command.output().unwrap();
            assert!(!output.status.success(), "accepted {body}");
            let error = String::from_utf8_lossy(&output.stderr);
            assert!(error.contains(&format!(": {code}: ")), "{error}");
            assert_eq!(
                std::fs::read(s.0.join("program")).unwrap(),
                b"preserve this output"
            );
        }
    }
}

#[test]
fn missing_or_ambiguous_profiles_do_not_supply_legacy_meaning() {
    let source = "fn main() -> Int { let X = Affine(QQ, 42); int(dimension(X)) }";
    let s = fixture(source, str::to_owned);
    s.write(
        "geo/Vastitas.toml",
        MANIFEST.split("[geometry_compat]").next().unwrap(),
    );
    assert!(!check(&s).status.success());
    s.write(
        "app/main.vast",
        "fn main() -> Int { let X = geo::scheme::Affine(42); int(geo::scheme::dimension(X)) }",
    );
    native(&s);
    s.write("geo/Vastitas.toml", MANIFEST);
    s.write("other/Vastitas.toml", MANIFEST);
    for (name, source) in LIBRARY {
        s.write(&format!("other/{name}"), source);
    }
    let manifest = std::fs::read_to_string(s.0.join("app/Vastitas.toml")).unwrap()
        + "other={path='../other'}\n";
    s.write("app/Vastitas.toml", &manifest);
    native(&s); // two independent libraries work through explicit names
    s.write("app/main.vast", source);
    let output = check(&s);
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("exactly one"));
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
        s.write(&format!("other/{name}"), source);
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
    let manifest = std::fs::read_to_string(path).unwrap() + "arithmetic={path='../standard'}\n";
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
        + "arithmetic={path='../standard'}\n";
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

fn captured_wire(s: &Scratch) -> Value {
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
    original
}

#[test]
fn kernel_reconstructs_module_visibility_and_geometry_contracts_from_wire() {
    let s = fixture(DEMO, str::to_owned);
    let original = captured_wire(&s);
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

#[test]
fn raw_compatibility_roles_and_old_wire_downgrades_are_rejected() {
    let s = fixture(include_str!("../examples/pointed.vast"), str::to_owned);
    let original = captured_wire(&s);
    assert_eq!(kernel(&original, "check")["ok"], true);
    let geo = original["packages"]
        .as_array()
        .unwrap()
        .iter()
        .position(|p| p["name"] == "vastitas_geometry")
        .unwrap();
    for mutation in [
        "missing profile",
        "wrong base",
        "wrong origin",
        "same marker",
        "wrong point",
        "unknown field",
        "null profile",
    ] {
        let mut raw = original.clone();
        let package = &mut raw["packages"][geo];
        match mutation {
            "missing profile" => {
                package.as_object_mut().unwrap().remove("geometry_compat");
            }
            "wrong base" => {
                package["geometry_compat"]["scheme"]["base_object"] =
                    json!("self::smooth::BaseSmooth")
            }
            "wrong origin" => {
                package["geometry_compat"]["scheme"]["origin"] = json!("self::scheme::dimension")
            }
            "same marker" => {
                package["geometry_compat"]["smooth"]["marker"] = json!("self::scheme::QQ")
            }
            "wrong point" => package["geometry_compat"]["point"] = json!("self::Morphism"),
            "unknown field" => package["geometry_compat"]["trusted"] = json!(true),
            _ => package["geometry_compat"] = Value::Null,
        }
        for mode in ["check", "emit"] {
            let output = kernel(&raw, mode);
            assert_eq!(output["ok"], false, "{mutation}/{mode}: {output}");
            assert!(output.get("lean_source").is_none());
        }
    }
    for version in 3..=6 {
        let mut raw = original.clone();
        raw["version"] = json!(version);
        if version == 3 {
            raw.as_object_mut().unwrap().remove("input");
        }
        for pkg in raw["packages"].as_array_mut().unwrap() {
            for module in pkg["modules"].as_array_mut().unwrap() {
                module
                    .as_object_mut()
                    .unwrap()
                    .remove("indexed_declarations");
            }
        }
        let output = kernel(&raw, "emit");
        assert_eq!(output["ok"], false, "downgrade {version}: {output}");
        assert!(
            output["diagnostics"][0]["message"]
                .as_str()
                .unwrap()
                .contains("geometry_compat"),
            "{output}"
        );
    }
    let mut flat = common::request("fn main() -> Int { 42 }", "flat.vast");
    flat["geometry_compat"] = original["packages"][geo]["geometry_compat"].clone();
    assert_eq!(kernel(&flat, "emit")["ok"], false);
}
