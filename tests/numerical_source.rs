mod common;
use common::{Scratch, assert_rejected, cli, kernel, success};
use serde_json::{Value, json};
use std::os::unix::fs::{PermissionsExt, symlink};
use std::process::Command;

const MAIN: &str = include_str!("../examples/packages/numerical/src/main.vast");
const REAL: &str = include_str!("../examples/packages/numerical/src/real/mod.vast");
const COMPLEX: &str = include_str!("../examples/packages/numerical/src/complex/mod.vast");
const PROFILES: &str = include_str!("../examples/packages/numerical/src/profiles/mod.vast");

fn fixture(real: &str) -> Scratch {
    let s = Scratch::empty("public numerical");
    s.write(
        "Vastitas.toml",
        include_str!("../examples/packages/numerical/Vastitas.toml"),
    );
    s.write("src/main.vast", MAIN);
    s.write("src/real/mod.vast", real);
    s.write("src/complex/mod.vast", COMPLEX);
    s.write("src/profiles/mod.vast", PROFILES);
    s
}
fn command(s: &Scratch, mode: &str) -> Command {
    let mut command = cli();
    command
        .current_dir(&s.0)
        .args([mode, "--manifest-path", "Vastitas.toml"]);
    command
}
fn captured(s: &Scratch) -> Value {
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
fn rejection(s: &Scratch, code: &str) {
    let output = command(s, "check").output().unwrap();
    assert!(!output.status.success(), "unexpected acceptance");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(code),
        "expected {code}: {output:?}"
    );
}
fn module<'a>(raw: &'a mut Value, name: &str) -> &'a mut Value {
    raw["packages"][0]["modules"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|m| m["path"] == json!([name]))
        .unwrap()
}
fn numerical_body<'a>(raw: &'a mut Value, name: &str) -> &'a mut Vec<Value> {
    module(raw, name)["resource_functions"][0]["body"]
        .as_array_mut()
        .unwrap()
}
fn local_operation<'a>(body: &'a mut [Value], name: &str) -> &'a mut Value {
    &mut body
        .iter_mut()
        .find(|statement| statement["operation"]["name"] == name)
        .unwrap()["operation"]
}

#[test]
fn public_numerical_check_and_emit_do_not_require_openblas() {
    let s = fixture(REAL);
    success(&command(&s, "check").output().unwrap());
    let raw = captured(&s);
    let response = kernel(&raw, "emit");
    assert_eq!(response["ok"], true, "{response}");
    assert_eq!(response["storage_runtime"], true);
    assert_eq!(response["numerical_runtime"], true);
    let generated = response["lean_source"].as_str().unwrap();
    assert_eq!(
        generated.matches("VastitasGemmNative.gemm arena").count(),
        4
    );
    let artifact = s.write("program", "existing artifact");
    let output = command(&s, "build")
        .args(["-o", "program"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("--openblas-prefix"),
        "{output:?}"
    );
    assert_eq!(std::fs::read(artifact).unwrap(), b"existing artifact");
    // Unused numerical bodies are still checked, but do not force a native
    // numerical dependency into a pure executable.
    s.write(
        "src/main.vast",
        "mod profiles; mod real; mod complex; fn main() -> Int { 42 }",
    );
    let response = kernel(captured(&s), "emit");
    assert_eq!(response["ok"], true, "{response}");
    assert_eq!(response["numerical_runtime"], false);
    success(&command(&s, "build").args(["-o", "pure"]).output().unwrap());
    let output = Command::new(s.0.join("pure")).output().unwrap();
    success(&output);
    assert_eq!(output.stdout, b"42\n");
    s.write(
        "src/real/mod.vast",
        &REAL.replace(
            "map destination = view(output, bu, bw)",
            "map destination = view(output, bw, bw)",
        ),
    );
    rejection(&s, "E_NUMERICAL_TYPE");
}

#[test]
fn public_products_reject_nominal_resource_and_scope_errors() {
    for (before, after, code) in [
        (
            "map destination = view(output, bu, bw)",
            "map destination = view(output, bw, bw)",
            "E_NUMERICAL_TYPE",
        ),
        (
            "map right = view(input_b, bu, bv)",
            "basis another = basis(v); map right = view(input_b, bu, another)",
            "E_NUMERICAL_TYPE",
        ),
        (
            "map right = view(input_b, bu, bv)",
            "space other = linear(super::profiles::RealSmooth, 3); basis another = basis(other); map right = view(input_b, bu, another)",
            "E_NUMERICAL_TYPE",
        ),
        (
            "super::profiles::RealSmooth",
            "super::profiles::ComplexSmooth",
            "E_NUMERICAL_TYPE",
        ),
        (
            "super::profiles::RealSmooth",
            "super::profiles::RealCoefficients",
            "E_NUMERICAL_TYPE",
        ),
        (
            "map left = view(input_a, bv, bw)",
            "map left = view(input_a, bu, bw)",
            "E_NUMERICAL_TYPE",
        ),
        (
            "gemm(left, right, destination, overwrite",
            "transpose(input_a); gemm(left, right, destination, overwrite",
            "E_NUMERICAL_TYPE",
        ),
        (
            "gemm(left, right, destination, overwrite",
            "transpose(output); gemm(left, right, destination, overwrite",
            "E_NUMERICAL_TYPE",
        ),
        (
            "gemm(left, right, destination, overwrite",
            "release(input_a); gemm(left, right, destination, overwrite",
            "E_NUMERICAL_TYPE",
        ),
        (
            "gemm(left, right, destination, overwrite",
            "borrow child = read(input_a, layout(0, 2, 3, 2, false)); gemm(left, right, destination, overwrite",
            "E_NUMERICAL_TYPE",
        ),
        (
            "gemm(left, right, destination, overwrite",
            "gemm(left, right, destination, accumulate",
            "E_RESOURCE_GEMM",
        ),
        (
            "gemm(left, right, destination, overwrite",
            "gemm(input_a, right, destination, overwrite",
            "E_NUMERICAL_TYPE",
        ),
        (
            "basis bu = basis(u);",
            "if true { basis bu = basis(u); } else {}",
            "E_RESOURCE_NAME",
        ),
        ("basis bu = basis(u);", "basis u = basis(u);", "E_DUPLICATE"),
        (
            "value { () }",
            "value { let f = fn(x: Int) -> Int { u }; () }",
            "E_CAPTURE",
        ),
        (
            "gemm(left, right, destination, overwrite, NativeFast);",
            "if false { gemm(right, left, destination, overwrite, NativeFast); } else {}",
            "E_NUMERICAL_TYPE",
        ),
    ] {
        rejection(&fixture(&REAL.replace(before, after)), code);
    }
    // Exact object/basis composition does not prove physical separation, even
    // when one read/write loan is explicitly interpreted in both map roles.
    let alias = "pub resource fn product() -> Unit {
        space u = linear(super::profiles::RealSmooth, 2);
        basis b = basis(u);
        allocate a: F64[4];
        borrow init = write(a, layout(0, 2, 2, 2, false));
        fill(init, f64_bits(0));
        release(init);
        borrow both = read_write(a, layout(0, 2, 2, 2, false));
        map m = view(both, b, b);
        gemm(m, m, m, overwrite, NativeFast);
        release(both);
        drop(a);
        value { () }
    }";
    rejection(&fixture(alias), "E_RESOURCE_GEMM");
    let s = fixture(REAL);
    s.write(
        "src/main.vast",
        &format!("{MAIN}\nfn unused() -> Int {{ true }}"),
    );
    rejection(&s, "E_TYPE");
}

#[test]
fn numerical_paths_are_resolved_with_actual_visibility_and_alias_identity() {
    let s = fixture(&REAL.replace("super::profiles::RealSmooth", "super::profiles::Chosen"));
    s.write(
        "src/profiles/mod.vast",
        &format!("{PROFILES}\npub use RealSmooth as Chosen;"),
    );
    success(&command(&s, "check").output().unwrap());
    s.write(
        "src/profiles/mod.vast",
        &PROFILES.replace(
            "pub indexed implementation RealSmooth",
            "indexed implementation RealSmooth",
        ),
    );
    s.write("src/real/mod.vast", REAL);
    rejection(&s, "E_VISIBILITY");
    s.write("src/profiles/mod.vast", PROFILES);
    let mut raw = captured(&s);
    raw["packages"][0]["modules"]
        .as_array_mut()
        .unwrap()
        .reverse();
    assert_eq!(kernel(raw, "check")["ok"], true);
}

#[test]
fn raw_numerical_bodies_recheck_nominal_identity_and_live_loans_even_when_unused() {
    // Mutate an accepted frontend request, then call Lean directly. Source-only
    // rejections cannot demonstrate that the independent checker enforces these
    // contracts. Exercise both coefficients and the separate all-body probes.
    let s = fixture(REAL);
    for main in [
        MAIN,
        "mod profiles; mod real; mod complex; fn main() -> Int { 42 }",
    ] {
        s.write("src/main.vast", main);
        let raw = captured(&s);
        let response = kernel(&raw, "emit");
        assert_eq!(response["ok"], true, "{response}");
        assert_eq!(response["numerical_runtime"], main == MAIN);
        for name in ["real", "complex"] {
            // u and w both have dimension two but different object identities.
            let mut changed = raw.clone();
            local_operation(numerical_body(&mut changed, name), "destination")["source"] =
                json!("bw");
            assert_rejected(changed, "E_NUMERICAL_TYPE");

            for distinct_space in [false, true] {
                let mut changed = raw.clone();
                let body = numerical_body(&mut changed, name);
                let basis_index = body
                    .iter()
                    .position(|statement| statement["operation"]["name"] == "bv")
                    .unwrap();
                let mut basis = body[basis_index].clone();
                basis["operation"]["name"] = json!("other_basis");
                if distinct_space {
                    let mut space = body
                        .iter()
                        .find(|statement| statement["operation"]["name"] == "v")
                        .unwrap()
                        .clone();
                    space["operation"]["name"] = json!("other_space");
                    basis["operation"]["space"] = json!("other_space");
                    body.insert(basis_index, space);
                }
                body.insert(basis_index + 1, basis);
                local_operation(body, "right")["target"] = json!("other_basis");
                assert_rejected(changed, "E_NUMERICAL_TYPE");
            }

            for action in [
                // Square output: dimensions still agree, but the exact layout
                // snapshot does not. A shape-only stale-view check would pass.
                json!({"op": "transpose", "loan": "output"}),
                json!({"op": "release", "loan": "input_a"}),
                json!({"op": "borrow", "name": "child", "source": "input_a",
                    "layout": {"offset": 0, "rows": 2, "columns": 3,
                        "leading": 2, "transposed": false}, "access": "read"}),
            ] {
                let mut changed = raw.clone();
                let body = numerical_body(&mut changed, name);
                let gemm = body
                    .iter()
                    .position(|statement| statement["operation"]["op"] == "gemm")
                    .unwrap();
                let span = body[gemm]["span"].clone();
                body.insert(
                    gemm,
                    json!({"kind": "action", "action": action, "span": span}),
                );
                assert_rejected(changed, "E_NUMERICAL_TYPE");
            }
        }
    }
}

#[test]
fn raw_numerical_profiles_resolve_against_the_actual_declarations() {
    let raw = captured(&fixture(REAL));
    assert_eq!(kernel(&raw, "check")["ok"], true);
    for (name, profile, marker) in [
        ("real", "RealSmooth", "RealCoefficients"),
        ("complex", "ComplexSmooth", "ComplexCoefficients"),
    ] {
        let mut changed = raw.clone();
        let declaration = module(&mut changed, "profiles")["indexed_declarations"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|declaration| declaration["name"] == profile)
            .unwrap();
        declaration["public"] = json!(false);
        assert_rejected(changed, "E_VISIBILITY");

        // The declaration is valid and public, but it is not a linear profile.
        let mut changed = raw.clone();
        local_operation(numerical_body(&mut changed, name), "u")["implementation"]["path"] =
            json!(["super", "profiles", marker]);
        assert_rejected(changed, "E_NUMERICAL_TYPE");

        // A malformed declaration cannot be hidden behind an otherwise valid
        // numerical body or an old frontend acceptance of this same path.
        let mut changed = raw.clone();
        let declaration = module(&mut changed, "profiles")["indexed_declarations"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|declaration| declaration["name"] == profile)
            .unwrap();
        declaration["representation"]["linear_descriptor"]["base"]["path"] = json!([marker]);
        assert_rejected(changed, "E_TYPE");
    }
}

#[test]
fn raw_numerical_wire_rejects_forged_ids_flags_and_old_envelopes() {
    let raw = captured(&fixture(REAL));
    for version in 2..8 {
        let mut old = raw.clone();
        old["version"] = json!(version);
        let response = kernel(old, "emit");
        assert_eq!(response["ok"], false, "{response}");
        assert!(response.get("lean_source").is_none());
    }
    for (op, key, value) in [
        ("space", "implementation", json!(0)),
        ("space", "owner", json!("trusted")),
        ("space", "dimension", json!(-1)),
        ("space", "checked", json!(true)),
        ("basis", "brand", json!(0)),
        ("map", "allocation", json!(0)),
        ("map", "source", json!(0)),
        ("gemm", "certificate", json!({"checked": true})),
        ("gemm", "conjugate_left", json!(true)),
        ("gemm", "policy", json!("exact")),
        ("gemm", "mode", json!("unknown")),
    ] {
        let mut changed = raw.clone();
        let operation = &mut numerical_body(&mut changed, "real")
            .iter_mut()
            .find(|s| s["operation"]["op"] == op)
            .unwrap()["operation"];
        operation[key] = value;
        let response = kernel(changed, "emit");
        assert_eq!(response["ok"], false, "{op}/{key}: {response}");
        assert_eq!(
            response["diagnostics"][0]["code"], "E_PROTOCOL",
            "{response}"
        );
        assert!(response.get("lean_source").is_none());
    }
    // Nested paths have their own strict decoder. A checked ID or proof tag
    // cannot be smuggled beside the otherwise valid unresolved path.
    for key in ["checked_id", "proof"] {
        let mut changed = raw.clone();
        local_operation(numerical_body(&mut changed, "real"), "u")["implementation"][key] =
            json!("trusted");
        assert_rejected(changed, "E_PROTOCOL");
    }
    let mut changed = raw;
    let operation = &mut numerical_body(&mut changed, "real")
        .iter_mut()
        .find(|s| s["operation"]["op"] == "gemm")
        .unwrap()["operation"];
    operation["left"] = json!("input_a");
    assert_eq!(
        kernel(changed, "check")["diagnostics"][0]["code"],
        "E_NUMERICAL_TYPE"
    );
}

#[test]
fn numerical_build_flags_are_explicit_and_failure_preserves_existing_output() {
    let s = fixture(REAL);
    s.write("program", "existing artifact");
    for args in [
        vec!["--openblas-prefix"],
        vec!["--native-cc"],
        vec![
            "--openblas-prefix",
            "missing",
            "--openblas-prefix",
            "missing",
        ],
        vec!["--native-cc", "cc", "--native-cc", "cc"],
        vec!["--openblas-prefix", "missing"],
    ] {
        let output = command(&s, "build")
            .args(["-o", "program"])
            .args(args)
            .output()
            .unwrap();
        assert!(!output.status.success(), "{output:?}");
        assert_eq!(
            std::fs::read(s.0.join("program")).unwrap(),
            b"existing artifact"
        );
    }
    assert!(
        !command(&s, "check")
            .args(["--openblas-prefix", "missing"])
            .output()
            .unwrap()
            .status
            .success()
    );
    let stub = s.write("backend", "#!/bin/sh\ncat >/dev/null\ncat \"$RESPONSE\"\n");
    std::fs::set_permissions(&stub, std::fs::Permissions::from_mode(0o755)).unwrap();
    for (storage, numerical) in [(json!(false), json!(true)), (json!(true), json!("yes"))] {
        let response = s.write("response.json", &json!({"version":8,"ok":true,"lean_source":"", "storage_runtime":storage, "numerical_runtime":numerical}).to_string());
        let output = command(&s, "build")
            .env("VASTITAS_KERNEL", &stub)
            .env("RESPONSE", response)
            .args(["-o", "program"])
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("E_PROTOCOL"));
        assert_eq!(
            std::fs::read(s.0.join("program")).unwrap(),
            b"existing artifact"
        );
    }
}

#[test]
#[ignore = "requires the explicit pinned OpenBLAS prefix; both numerical CI jobs run this test"]
fn public_real_complex_products_build_execute_and_keep_output_protection() {
    let prefix =
        std::env::var_os("VASTITAS_TEST_OPENBLAS_PREFIX").expect("explicit numerical test prefix");
    let s = fixture(REAL);
    // Spaces and quotes in the dependency path exercise generated Lake data
    // escaping, not shell evaluation.
    let linked = s.0.join("BLAS \"quoted\" prefix");
    std::fs::create_dir(&linked).unwrap();
    let prefix = std::fs::canonicalize(prefix).unwrap();
    symlink(prefix.join("include"), linked.join("include")).unwrap();
    symlink(prefix.join("lib"), linked.join("lib")).unwrap();
    let build = |output: &str| {
        let mut command = command(&s, "build");
        command
            .args(["-o", output, "--openblas-prefix"])
            .arg(&linked);
        if let Some(cc) = std::env::var_os("VASTITAS_TEST_NATIVE_CC") {
            command.arg("--native-cc").arg(cc);
        }
        command.output().unwrap()
    };
    success(&build("program"));
    let result = Command::new(s.0.join("program")).output().unwrap();
    success(&result);
    assert_eq!(result.stdout, b"42\n");
    s.write(
        "src/real/mod.vast",
        &REAL.replace(
            "expect(updated, 0, 0, f64_bits(4633359591634108416))",
            "expect(updated, 0, 0, f64_bits(0))",
        ),
    );
    success(&build("failure"));
    let result = Command::new(s.0.join("failure")).output().unwrap();
    assert!(!result.status.success());
    assert!(
        String::from_utf8_lossy(&result.stderr).contains("E_NATIVE_EXPECT"),
        "{result:?}"
    );
    assert!(result.stdout.is_empty());
    let existing = std::fs::read(s.0.join("program")).unwrap();
    s.write(
        "src/real/mod.vast",
        &REAL.replace("view(output, bu, bw)", "view(output, bw, bw)"),
    );
    let result = build("program");
    assert!(!result.status.success());
    assert_eq!(std::fs::read(s.0.join("program")).unwrap(), existing);
}
