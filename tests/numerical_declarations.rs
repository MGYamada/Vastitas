mod common;
use common::{Scratch, cli, kernel, success};
use serde_json::{Value, json};

const PROFILES: &str =
    include_str!("../examples/packages/numerical-declarations/src/profiles/mod.vast");

fn fixture(profiles: &str) -> Scratch {
    let s = Scratch::empty("numerical declarations");
    s.write(
        "Vastitas.toml",
        include_str!("../examples/packages/numerical-declarations/Vastitas.toml"),
    );
    s.write(
        "src/main.vast",
        include_str!("../examples/packages/numerical-declarations/src/main.vast"),
    );
    s.write("src/profiles/mod.vast", profiles);
    s
}

fn check(s: &Scratch) -> std::process::Output {
    cli()
        .current_dir(&s.0)
        .args(["check", "--manifest-path", "Vastitas.toml"])
        .output()
        .unwrap()
}

fn request(s: &Scratch) -> Value {
    common::captured_wire(
        cli()
            .current_dir(&s.0)
            .args(["check", "--manifest-path", "Vastitas.toml"]),
        8,
    )
}

fn rejects(source: &str, code: &str) {
    let output = check(&fixture(source));
    assert!(!output.status.success(), "accepted {source}");
    common::expect_code(&output, code);
}

#[test]
fn declared_numerical_profiles_compose_with_pure_check_build_and_execution() {
    let s = fixture(PROFILES);
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
    // An unrelated, unused ordinary body still passes through the full checker.
    s.write(
        "src/main.vast",
        "mod profiles; fn unused() -> Int { true } fn main() -> Int { 42 }",
    );
    let output = check(&s);
    assert!(!output.status.success());
    common::expect_code(&output, "E_TYPE");
}

#[test]
fn numerical_declarations_require_version_eight_without_any_resource_function() {
    let raw = request(&fixture(PROFILES));
    assert_eq!(raw["version"], 8);
    let result = kernel(&raw, "emit");
    assert_eq!(result["ok"], true, "{result}");
    assert_ne!(result["storage_runtime"], true);
    for version in 2..8 {
        let mut changed = raw.clone();
        changed["version"] = json!(version);
        common::assert_wire_rejected(&kernel(changed, "emit"), "E_PROTOCOL");
    }
}

#[test]
fn complete_environment_rejects_wrong_base_coefficient_and_capabilities() {
    for (before, after) in [
        (
            "linear_descriptor(SmoothBase, real)",
            "linear_descriptor(RealCoefficients, real)",
        ),
        (
            "linear_descriptor(SmoothBase, real)",
            "linear_descriptor(SmoothScalar, real)",
        ),
        ("scalar_base(smooth, real)", "scalar_base(smooth, complex)"),
        (
            "linear_descriptor(RealBase, real)",
            "linear_descriptor(ComplexBase, real)",
        ),
        (
            "linear_descriptor(ComplexBase, complex)",
            "linear_descriptor(RealBase, complex)",
        ),
        (
            "RealSmooth(RealCoefficients",
            "RealSmooth(ComplexCoefficients",
        ),
        ("capabilities();", "capabilities(origin);"),
        ("scalar_base(scheme, complex)", "scalar_base(scheme, real)"),
    ] {
        rejects(&PROFILES.replace(before, after), "E_TYPE");
    }
    rejects(
        &format!(
            "{PROFILES}\npub indexed implementation Unused(RealCoefficients, scalar_base(scheme, complex)) capabilities();"
        ),
        "E_TYPE",
    );
}

/// A declaration that breaks a rule of the implementations is reported at
/// that declaration, with the rule that it breaks (#704). The old place was the
/// first character of the root manifest, with one text for every rule.
#[test]
fn a_broken_implementation_rule_is_reported_at_the_declaration() {
    const P: &str = "numerical_declarations::profiles";
    let with_marker = format!("{PROFILES}\npub indexed marker Other;\n");
    // `ComplexSmooth` ahead of the implementation of its base.
    let complex_first = {
        let line = "pub indexed implementation ComplexSmooth(ComplexCoefficients, linear_descriptor(SmoothBase, complex)) capabilities();\n";
        let rest = common::checked_replace(PROFILES, line, "");
        common::checked_replace(
            &format!("{line}{rest}"),
            "ComplexSmooth(ComplexCoefficients",
            "ComplexSmooth(RealCoefficients",
        )
    };
    let cases: [(&str, &str, &str, &str, String); 15] = [
        (
            PROFILES,
            "linear_descriptor(SmoothBase, real)",
            "linear_descriptor(RealCoefficients, real)",
            "7:5",
            format!(
                "the base of the `linear_descriptor` implementation `{P}::RealSmooth` must be an `indexed global` of a `scalar_base` implementation, but `{P}::RealCoefficients` is not one"
            ),
        ),
        (
            PROFILES,
            "linear_descriptor(SmoothBase, real)",
            "linear_descriptor(SmoothScalar, real)",
            "7:5",
            format!(
                "the base of the `linear_descriptor` implementation `{P}::RealSmooth` must be an `indexed global` of a `scalar_base` implementation, but `{P}::SmoothScalar` is not one"
            ),
        ),
        (
            PROFILES,
            "scalar_base(smooth, real)",
            "scalar_base(smooth, complex)",
            "5:5",
            format!(
                "the `scalar_base` implementation `{P}::SmoothScalar` has the setting `smooth`, which must have the kind `real`"
            ),
        ),
        (
            PROFILES,
            "linear_descriptor(RealBase, real)",
            "linear_descriptor(ComplexBase, real)",
            "12:5",
            format!(
                "the linear implementation `{P}::RealLinear` over the `scheme` base `{P}::ComplexBase` must have the kind `complex` of the implementation of its base, but it has the kind `real`"
            ),
        ),
        (
            PROFILES,
            "linear_descriptor(ComplexBase, complex)",
            "linear_descriptor(RealBase, complex)",
            "16:5",
            format!(
                "the linear implementation `{P}::ComplexLinear` over the `scheme` base `{P}::RealBase` must have the kind `real` of the implementation of its base, but it has the kind `complex`"
            ),
        ),
        (
            &with_marker,
            "RealLinear(RealCoefficients",
            "RealLinear(Other",
            "12:5",
            format!(
                "the linear implementation `{P}::RealLinear` over the `scheme` base `{P}::RealBase` must have the marker `{P}::RealCoefficients` of the implementation of its base, but it has the marker `{P}::Other`"
            ),
        ),
        (
            PROFILES,
            "RealSmooth(RealCoefficients",
            "RealSmooth(ComplexCoefficients",
            "7:5",
            format!(
                "the `real` linear implementation `{P}::RealSmooth` over the `smooth` base `{P}::SmoothBase` must have the marker `{P}::RealCoefficients` of the implementation of its base, but it has the marker `{P}::ComplexCoefficients`"
            ),
        ),
        (
            &complex_first,
            "",
            "",
            "1:5",
            format!(
                "the `complex` linear implementation `{P}::ComplexSmooth` over the `smooth` base `{P}::SmoothBase` must have another marker than `{P}::RealCoefficients`, the marker of the implementation of its base"
            ),
        ),
        // The same error where the implementation of the base comes first:
        // that implementation is the first of two kinds of one marker.
        (
            PROFILES,
            "ComplexSmooth(ComplexCoefficients",
            "ComplexSmooth(RealCoefficients",
            "5:5",
            format!(
                "the implementations of the marker `{P}::RealCoefficients` must have one coefficient kind, but `{P}::SmoothScalar` has the kind `real` and `{P}::ComplexSmooth` has the kind `complex`"
            ),
        ),
        (
            PROFILES,
            "scalar_base(scheme, complex)",
            "scalar_base(scheme, real)",
            "8:5",
            format!(
                "the implementations of the marker `{P}::ComplexCoefficients` must have one coefficient kind, but `{P}::ComplexSmooth` has the kind `complex` and `{P}::ComplexScalar` has the kind `real`"
            ),
        ),
        (
            PROFILES,
            "linear_descriptor(RealBase, real)) capabilities();",
            "linear_descriptor(RealBase, real)) capabilities(origin);",
            "12:5",
            format!(
                "the `linear_descriptor` implementation `{P}::RealLinear` must have an empty capability list"
            ),
        ),
        (
            PROFILES,
            "scalar_base(scheme, real)) capabilities();",
            "scalar_base(scheme, real)) capabilities(dimension);",
            "10:5",
            format!(
                "the `scalar_base` implementation `{P}::RealScalar` must have an empty capability list"
            ),
        ),
        (
            PROFILES,
            "linear_descriptor(RealBase, real)) capabilities();",
            "linear_descriptor(RealBase, real)) capabilities(origin, origin);",
            "12:5",
            format!(
                "the capability list of the implementation `{P}::RealLinear` names a capability twice"
            ),
        ),
        (
            PROFILES,
            "RealLinear(RealCoefficients",
            "RealLinear(RealScalar",
            "12:5",
            format!(
                "the marker of the implementation `{P}::RealLinear` must be an `indexed marker`, but `{P}::RealScalar` is not one"
            ),
        ),
        // Another declaration that the same check rejects has its own place
        // and its own rule (#736).
        (
            PROFILES,
            "pub indexed global RealBase(RealScalar);",
            "pub indexed global RealBase(RealScalar);\nindexed primitive Bad = descriptor(RealSmooth);",
            "12:1",
            format!(
                "the implementation `{P}::RealSmooth` of the `descriptor` primitive `{P}::Bad` must have the representation `affine_descriptor`"
            ),
        ),
    ];
    for (profiles, before, after, place, message) in cases {
        let source = if before.is_empty() {
            profiles.to_string()
        } else {
            common::checked_replace(profiles, before, after)
        };
        let output = check(&fixture(&source));
        let error = common::expect_code(&output, "E_TYPE");
        assert!(
            error.ends_with(&format!(
                "src/profiles/mod.vast:{place}: E_TYPE: {message}\n"
            )),
            "{after}: {error}"
        );
        assert_eq!(error.lines().count(), 1, "{error}");
        assert!(!error.contains("Vastitas.toml"), "{error}");
    }
    // An implementation that nothing uses counts for the kinds of its marker.
    let unused = format!(
        "{PROFILES}\npub indexed implementation Unused(RealCoefficients, scalar_base(scheme, complex)) capabilities();"
    );
    let error = common::expect_code(&check(&fixture(&unused)), "E_TYPE");
    assert!(
        error.ends_with(&format!(
            "src/profiles/mod.vast:5:5: E_TYPE: the implementations of the marker `{P}::RealCoefficients` must have one coefficient kind, but `{P}::SmoothScalar` has the kind `real` and `{P}::Unused` has the kind `complex`\n"
        )),
        "{error}"
    );
}

#[test]
fn numerical_profiles_do_not_acquire_legacy_geometry_operations() {
    for declaration in [
        "indexed primitive Bad = descriptor(RealSmooth);",
        "indexed primitive Bad = global(SmoothBase);",
        "indexed family Bad(object(RealSmooth), object(RealSmooth)) = point constraints(same_base(0, 1));",
        "indexed family Bad(object(ComplexLinear), object(ComplexLinear)) = morphism constraints(same_base(0, 1));",
    ] {
        rejects(&format!("{PROFILES}\n{declaration}"), "E_TYPE");
    }
}

#[test]
fn raw_wire_cannot_forge_profile_base_or_bypass_representation_schema() {
    let raw = request(&fixture(PROFILES));
    let modules = raw["packages"][0]["modules"].as_array().unwrap();
    let profile_module = modules
        .iter()
        .position(|m| m["path"] == json!(["profiles"]))
        .unwrap();
    let declarations = modules[profile_module]["indexed_declarations"]
        .as_array()
        .unwrap();
    let declaration = declarations
        .iter()
        .position(|d| d["name"] == "RealSmooth")
        .unwrap();
    let pointer = format!(
        "/packages/0/modules/{profile_module}/indexed_declarations/{declaration}/representation"
    );
    for (representation, code) in [
        (
            json!({"linear_descriptor": {"base": {"path": ["RealCoefficients"], "span": {"start": 0, "end": 0, "line": 1, "column": 1}}, "coefficient": "real"}}),
            "E_TYPE",
        ),
        (
            json!({"linear_descriptor": {"base": {"path": ["SmoothBase"], "span": {"start": 0, "end": 0, "line": 1, "column": 1}}, "coefficient": "f64"}}),
            "E_PROTOCOL",
        ),
        (
            json!({"scalar_base": {"setting": "smooth", "coefficient": "real", "checked": true}}),
            "E_PROTOCOL",
        ),
        (
            json!({"scalar_base": {"setting": "scheme", "coefficient": "real"}, "linear_descriptor": {"base": "SmoothBase", "coefficient": "real"}}),
            "E_PROTOCOL",
        ),
    ] {
        let mut changed = raw.clone();
        *changed.pointer_mut(&pointer).unwrap() = representation;
        let result = kernel(changed, "emit");
        assert_eq!(result["ok"], false, "{result}");
        assert_eq!(result["diagnostics"][0]["code"], code, "{result}");
        assert!(result.get("lean_source").is_none());
    }
}

#[test]
fn base_path_obeys_module_visibility_and_kind_even_when_unused() {
    let s =
        fixture(&PROFILES.replace("pub indexed global SmoothBase", "indexed global SmoothBase"));
    s.write("src/main.vast", "mod profiles; indexed implementation Bad(profiles::RealCoefficients, linear_descriptor(profiles::SmoothBase, real)) capabilities(); fn main() -> Int { 0 }");
    let output = check(&s);
    assert!(!output.status.success());
    common::expect_code(&output, "E_VISIBILITY");
    rejects(
        &PROFILES.replace(
            "linear_descriptor(SmoothBase, real)",
            "linear_descriptor(Absent, real)",
        ),
        "E_NAME",
    );
}
