mod common;
use common::{Scratch, assert_rejected, cli, kernel, success};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;
use std::process::Command;

const REAL: &str = include_str!("../examples/packages/generative-owned-map/src/real/mod.vast");
const COMPLEX: &str =
    include_str!("../examples/packages/generative-owned-map/src/complex/mod.vast");

fn fixture(real: &str, complex: &str) -> Scratch {
    let s = Scratch::empty("generative owned maps");
    for (name, source) in [
        (
            "Vastitas.toml",
            include_str!("../examples/packages/generative-owned-map/Vastitas.toml"),
        ),
        (
            "src/main.vast",
            include_str!("../examples/packages/generative-owned-map/src/main.vast"),
        ),
        (
            "src/profiles/mod.vast",
            include_str!("../examples/packages/generative-owned-map/src/profiles/mod.vast"),
        ),
        ("src/real/mod.vast", real),
        ("src/complex/mod.vast", complex),
    ] {
        s.write(name, source);
    }
    s
}
fn command(s: &Scratch, mode: &str) -> Command {
    let mut c = cli();
    c.current_dir(&s.0)
        .args([mode, "--manifest-path", "Vastitas.toml"]);
    c
}
fn capture(s: &Scratch) -> Value {
    let stub = s.write("capture", "#!/bin/sh\ncat > \"$(dirname \"$0\")/wire.json\"\nprintf '%s\\n' '{\"version\":8,\"ok\":false,\"diagnostics\":[{\"code\":\"E_CAPTURED\",\"message\":\"captured\"}]}'\nexit 1\n");
    std::fs::set_permissions(&stub, std::fs::Permissions::from_mode(0o755)).unwrap();
    let output = command(s, "check")
        .env("VASTITAS_KERNEL", stub)
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("E_CAPTURED"),
        "{output:?}"
    );
    serde_json::from_slice(&std::fs::read(s.0.join("wire.json")).unwrap()).unwrap()
}
fn functions(raw: &mut Value) -> &mut Vec<Value> {
    raw["packages"][0]["modules"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|m| m["path"] == json!(["real"]))
        .unwrap()["resource_functions"]
        .as_array_mut()
        .unwrap()
}
fn function<'a>(raw: &'a mut Value, name: &str) -> &'a mut Value {
    functions(raw)
        .iter_mut()
        .find(|f| f["name"] == name)
        .unwrap()
}
fn reject(real: &str, expected: &str) {
    let s = fixture(real, COMPLEX);
    let output = command(&s, "check").output().unwrap();
    assert!(!output.status.success(), "invalid package accepted");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(expected),
        "expected {expected}: {output:?}"
    );
}

#[test]
fn owned_packages_preserve_public_contracts_and_reject_forged_wire() {
    let s = fixture(REAL, COMPLEX);
    success(&command(&s, "check").output().unwrap());
    let raw = capture(&s);
    let response = kernel(&raw, "emit");
    assert_eq!(response["ok"], true, "{response}");
    let source = response["lean_source"].as_str().unwrap();
    assert_eq!(source.matches("allocate arena").count(), 2);
    assert!(!source.contains("copy arena"));
    assert!(!source.contains("VastitasGemmNative"));
    for version in 2..=7 {
        let mut forged = raw.clone();
        forged["version"] = json!(version);
        assert_rejected(forged, "E_PROTOCOL");
    }
    let mut forged = raw.clone();
    function(&mut forged, "create")["results"][0]["type"]["dimension"] = json!(2);
    assert_rejected(forged, "E_NUMERICAL_TYPE");
    let mut forged = raw.clone();
    function(&mut forged, "create")["results"][0]["type"]["source"] = json!("bw");
    assert_rejected(forged, "E_RESOURCE_NAME");
    let mut forged = raw.clone();
    function(&mut forged, "create")["results"][0]["type"]["checked"] = json!(true);
    assert_rejected(forged, "E_PROTOCOL");
    let mut forged = raw.clone();
    function(&mut forged, "relay")["parameters"][2]["dimension"] = json!(4);
    assert_rejected(forged, "E_NUMERICAL_TYPE");
    let mut forged = raw.clone();
    function(&mut forged, "relay")["body"][0]["operation"]["space"] = json!("u");
    assert_rejected(forged, "E_DUPLICATE");
    let mut forged = raw.clone();
    function(&mut forged, "relay")["body"][0]["operation"]["allocation"] = json!(0);
    assert_rejected(forged, "E_PROTOCOL");
}

#[test]
fn owned_packages_enforce_affine_scope_and_actual_nominal_arguments() {
    for (before, after, code) in [
        (
            "move updated -> moved;",
            "borrow illicit = read(updated, layout(8, 3, 2, 4, false)); move updated -> moved;",
            "E_NUMERICAL_PACKAGE",
        ),
        (
            "move updated -> moved;",
            "map illicit = owned(updated, layout(8, 3, 2, 4, false), bu, bu); move updated -> moved;",
            "E_NUMERICAL_PACKAGE",
        ),
        (
            "unpack moved as (w, bw, result);",
            "unpack moved as (w, bw, result); unpack moved as (w2, bw2, result2);",
            "E_NUMERICAL_PACKAGE",
        ),
        (
            "move updated -> moved;",
            "move updated -> moved; drop(updated);",
            "E_RESOURCE_MOVE",
        ),
        (
            "fill(initialize, f64_bits(4611686018427387904));",
            "",
            "E_RESOURCE_INIT",
        ),
        ("release(initialize);", "", "E_RESOURCE_LOAN"),
        (
            "map boxed = pack(result);",
            "borrow outstanding = read(result); map boxed = pack(result);",
            "E_RESOURCE_LOAN",
        ),
        (
            "call relay(u, bu, created)",
            "basis wrong = basis(u); call relay(u, wrong, created)",
            "E_NUMERICAL_TYPE",
        ),
        (
            "returns (boxed: OwnedMapTo<bu, 3>)",
            "returns (boxed: Owned<F64, 10> initialized [layout(8, 3, 2, 4, false)])",
            "E_NUMERICAL_PACKAGE",
        ),
        (
            "returns (boxed: OwnedMapTo<bu, 3>)",
            "returns (result: OwnedMap<bu, bw>)",
            "E_RESOURCE_NAME",
        ),
        (
            "unpack moved as (w, bw, result);",
            "if true { unpack moved as (w, bw, result); drop(result); } else { drop(moved); }",
            "E_RESOURCE_NAME",
        ),
        (
            "call inspect(u, bu, w, bw, result)",
            "call create(u, bu) -> (other); unpack other as (w2, bw2, result2); call inspect(u, bu, w, bw, result2)",
            "E_NUMERICAL_TYPE",
        ),
        (
            "call inspect(u, bu, w, bw, result)",
            "map repacked = pack(result); unpack repacked as (w2, bw2, result2); call inspect(u, bu, w, bw, result2)",
            "E_NUMERICAL_TYPE",
        ),
    ] {
        assert!(REAL.contains(before));
        reject(&REAL.replace(before, after), code);
    }
    // Opaque storage cannot be erased by a helper contract, including unused bodies.
    let erased = format!(
        "{}\nresource fn erase(input: Owned<F64, 10>) -> Unit {{ drop(input); value {{ () }} }}",
        REAL.replace(
            "move updated -> moved;",
            "call erase(updated) -> (); move updated -> moved;"
        )
    );
    reject(&erased, "E_NUMERICAL_PACKAGE");
    // A hidden derived target requires a richer closed provenance contract.
    let derived = REAL.replace("space w = linear(super::profiles::RealSmooth, 3);\n    basis bw = basis(w);", "space p = linear(super::profiles::RealSmooth, 3); basis bp = basis(p); space w = dual(p); basis bw = derived(bp, w);");
    reject(&derived, "E_NUMERICAL_PACKAGE");
    let unused = format!(
        "{REAL}\nresource fn unused(u: Space<super::profiles::RealSmooth, 2>, bu: Basis<u>, input: OwnedMapTo<bu, 3>) -> Unit {{ borrow illicit = read(input, layout(8, 3, 2, 4, false)); release(illicit); drop(input); value {{ () }} }}"
    );
    reject(&unused, "E_NUMERICAL_PACKAGE");
}

#[test]
fn owned_packages_build_and_execute_without_openblas() {
    for variant in 0..3 {
        let transform = |source: &str, width: u64| match variant {
            1 => source
                .replace(
                    &format!("layout({width}, 3, 2, 4, false)"),
                    &format!("layout({width}, 2, 3, 4, true)"),
                )
                .replace("[10]", "[12]"),
            2 => source
                .replace("<bu, 3>", "<bu, 0>")
                .replace(", 3>", ", 0>")
                .replace(", 3);", ", 0);")
                .replace(
                    &format!("layout({width}, 3, 2, 4, false)"),
                    &format!("layout({width}, 0, 2, 4, false)"),
                )
                .lines()
                .filter(|line| !line.trim().starts_with("expect("))
                .collect::<Vec<_>>()
                .join("\n"),
            _ => source.to_owned(),
        };
        let s = fixture(&transform(REAL, 8), &transform(COMPLEX, 16));
        success(
            &command(&s, "build")
                .args(["-o", "program"])
                .output()
                .unwrap(),
        );
        let output = Command::new(s.0.join("program")).output().unwrap();
        success(&output);
        assert_eq!(output.stdout, b"42\n");
    }
}
