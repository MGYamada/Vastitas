mod common;
use common::{Scratch, cli, kernel, success};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;

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
    let stub = s.write("capture", "#!/bin/sh\ncat > \"$(dirname \"$0\")/wire.json\"\nprintf '%s\\n' '{\"version\":8,\"ok\":false,\"diagnostics\":[{\"code\":\"E_CAPTURED\",\"message\":\"captured\"}]}'\nexit 1\n");
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

fn rejects(source: &str, code: &str) {
    let output = check(&fixture(source));
    assert!(!output.status.success(), "accepted {source}");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(code),
        "{output:?}"
    );
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
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("E_TYPE"),
        "{output:?}"
    );
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
        let rejected = kernel(changed, "emit");
        assert_eq!(rejected["ok"], false, "version {version}: {rejected}");
        assert!(rejected.get("lean_source").is_none());
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
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("E_VISIBILITY"),
        "{output:?}"
    );
    rejects(
        &PROFILES.replace(
            "linear_descriptor(SmoothBase, real)",
            "linear_descriptor(Absent, real)",
        ),
        "E_NAME",
    );
}
