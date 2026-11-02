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

// Exercise two activation levels and both destination modes using the same
// real/complex numerical payloads as the direct-call fixture.
fn with_interfaces(source: &str, profile: &str) -> String {
    let header = format!(
        "u: Space<super::profiles::{profile}, 2>, v: Space<super::profiles::{profile}, 3>, \
         w: Space<super::profiles::{profile}, 2>, bu: Basis<u>, bv: Basis<v>, bw: Basis<w>, \
         left: ReadMap<bv, bw>, right: ReadMap<bu, bv>"
    );
    let source = source
        .replace(
            "gemm(left, right, destination, overwrite, NativeFast);",
            "call forward(u, v, w, bu, bv, bw, left, right, destination) -> ();",
        )
        .replace(
            "gemm(left, right, accumulated, accumulate, NativeFast);",
            "call add_product(u, v, w, bu, bv, bw, left, right, accumulated) -> ();",
        );
    format!(
        "{source}\nresource fn forward({header}, destination: WriteMap<bu, bw> initializes) -> Unit {{
            call multiply_into(u, v, w, bu, bv, bw, left, right, destination) -> ();
            value {{ () }}
        }}
        resource fn multiply_into({header}, destination: WriteMap<bu, bw> initializes) -> Unit {{
            gemm(left, right, destination, overwrite, NativeFast);
            value {{ () }}
        }}
        resource fn add_product({header}, accumulated: ReadWriteMap<bu, bw>) -> Unit {{
            gemm(left, right, accumulated, accumulate, NativeFast);
            value {{ () }}
        }}"
    )
}

fn owned_result_source(complex: bool) -> String {
    let profile = if complex {
        "ComplexSmooth"
    } else {
        "RealSmooth"
    };
    let scalar = if complex { "Complex<F64>" } else { "F64" };
    let width = if complex { 16 } else { 8 };
    let literal = |real: f64, imaginary: f64| {
        if complex {
            format!("complex_bits({}, {})", real.to_bits(), imaginary.to_bits())
        } else {
            format!("f64_bits({})", real.to_bits())
        }
    };
    let initial = literal(2.0, 3.0);
    let changed = literal(4.0, 5.0);
    let one = literal(1.0, 0.0);
    let header = format!(
        "u: Space<super::profiles::{profile}, 1>, bu: Basis<u>, w: Space<super::profiles::{profile}, 1>, bw: Basis<w>"
    );
    format!(
        "pub resource fn product() -> Unit {{
            space u = linear(super::profiles::{profile}, 1); basis bu = basis(u);
            space w = linear(super::profiles::{profile}, 1); basis bw = basis(w);
            call create(u, bu, w, bw) -> (created);
            call relay(u, bu, w, bw, created) -> (updated);
            move updated -> moved;
            borrow result = read(moved, layout({width}, 1, 1, 3, false));
            expect(result, 0, 0, {changed}); map left = view(result, moved);
            allocate identity: {scalar}[1];
            borrow initialize = write(identity, layout(0, 1, 1, 1, false));
            fill(initialize, {one}); release(initialize);
            borrow input = read(identity, layout(0, 1, 1, 1, false));
            map right = view(input, bu, bu);
            allocate output: {scalar}[1]; borrow destination = write(output, layout(0, 1, 1, 1, false));
            map target = view(destination, bu, bw);
            gemm(left, right, target, overwrite, NativeFast);
            release(destination); release(input); release(result); drop(moved); drop(identity);
            borrow final = read(output, layout(0, 1, 1, 1, false));
            expect(final, 0, 0, {changed}); release(final); drop(output); value {{ () }}
        }}
        resource fn create({header}) returns (result: OwnedMap<bu, bw>) -> Unit {{
            allocate buffer: {scalar}[5];
            borrow write = write(buffer, layout({width}, 1, 1, 3, false));
            fill(write, {initial}); release(write);
            map result = owned(buffer, layout({width}, 1, 1, 3, false), bu, bw);
            value {{ () }}
        }}
        resource fn relay({header}, input: OwnedMap<bu, bw>) returns (result: OwnedMap<bu, bw>) -> Unit {{
            call update(u, bu, w, bw, input) -> (result); value {{ () }}
        }}
        resource fn update({header}, input: OwnedMap<bu, bw>) returns (input: OwnedMap<bu, bw>) -> Unit {{
            borrow change = read_write(input);
            map coordinates = view(change, input);
            fill(change, {changed}); release(change); value {{ () }}
        }}"
    )
}

#[test]
fn owned_numerical_results_preserve_identity_storage_and_reject_forged_contracts() {
    let source = owned_result_source(false);
    let s = fixture(&source);
    s.write("src/complex/mod.vast", &owned_result_source(true));
    success(&command(&s, "check").output().unwrap());
    let raw = captured(&s);
    let response = kernel(&raw, "emit");
    assert_eq!(response["ok"], true, "{response}");
    let generated = response["lean_source"].as_str().unwrap();
    assert_eq!(generated.matches("allocate arena").count(), 6);
    assert_eq!(
        generated.matches("VastitasGemmNative.gemm arena").count(),
        2
    );
    assert!(!generated.contains("copy arena"));
    for (before, after, code) in [
        (
            "returns (result: OwnedMap<bu, bw>)",
            "returns (result: OwnedMap<bw, bu>)",
            "E_NUMERICAL_TYPE",
        ),
        (
            "fill(write, f64_bits(4611686018427387904));",
            "",
            "E_RESOURCE_INIT",
        ),
        (
            "fill(write, f64_bits(4611686018427387904)); release(write);",
            "fill(write, f64_bits(4611686018427387904));",
            "E_RESOURCE_LOAN",
        ),
        (
            "call relay(u, bu, w, bw, created)",
            "call relay(w, bw, u, bu, created)",
            "E_NUMERICAL_TYPE",
        ),
        (
            "move updated -> moved;",
            "drop(created); move updated -> moved;",
            "E_RESOURCE_MOVE",
        ),
        (
            "layout(8, 1, 1, 3, false));\n            expect(result",
            "layout(0, 1, 1, 3, false));\n            expect(result",
            "E_RESOURCE_INIT",
        ),
        (
            "map left = view(result, moved);",
            "transpose(result); map left = view(result, moved);",
            "E_NUMERICAL_TYPE",
        ),
        (
            "value { () }\n        }\n        resource fn relay",
            "drop(buffer); value { () }\n        }\n        resource fn relay",
            "E_RESOURCE_MOVE",
        ),
        (
            "returns (input: OwnedMap<bu, bw>)",
            "returns (input: OwnedMap<bu, bw>, input: OwnedMap<bu, bw>)",
            "E_RESOURCE_TYPE",
        ),
        (
            "fill(change, f64_bits(4616189618054758400)); release(change);",
            "fill(change, f64_bits(4616189618054758400));",
            "E_RESOURCE_ESCAPE",
        ),
    ] {
        assert!(source.contains(before), "ineffective mutation: {before}");
        rejection(&fixture(&source.replace(before, after)), code);
    }
    for replacement in [
        json!({"kind":"owned_map", "source":"bu", "target":"bw", "checked":true}),
        json!({"kind":"owned_map", "source":"bu", "target":"input"}),
        json!({"kind":"owned_map", "source":"bu", "target":"missing"}),
        json!({"kind":"owned_map", "source":"bu", "target":"bw", "allocation":0}),
    ] {
        let mut altered = raw.clone();
        module(&mut altered, "real")["resource_functions"][3]["results"][0]["type"] = replacement;
        let response = kernel(&altered, "emit");
        assert_eq!(response["ok"], false, "{response}");
        assert!(response.get("lean_source").is_none());
    }
    let local_basis = source.replace(
        "map result = owned(buffer, layout(8, 1, 1, 3, false), bu, bw);",
        "basis local = basis(w); map result = owned(buffer, layout(8, 1, 1, 3, false), bu, local);",
    );
    rejection(&fixture(&local_basis), "E_NUMERICAL_TYPE");
    rejection(
        &fixture(&local_basis.replace(
            "returns (result: OwnedMap<bu, bw>)",
            "returns (result: OwnedMap<bu, local>)",
        )),
        "E_RESOURCE_NAME",
    );
    let duplicate_input = source.replace(
        "call relay(u, bu, w, bw, created)",
        "call duplicated(u, bu, w, bw, created, created)",
    )
        + "\nresource fn duplicated(u: Space<super::profiles::RealSmooth, 1>, bu: Basis<u>,
         w: Space<super::profiles::RealSmooth, 1>, bw: Basis<w>,
         input: OwnedMap<bu, bw>, other: OwnedMap<bu, bw>) -> Unit {
            drop(input); drop(other); value { () }
         }";
    rejection(&fixture(&duplicate_input), "E_RESOURCE_MOVE");
}

#[test]
fn owned_numerical_results_build_without_openblas() {
    let without_gemm = |complex| {
        owned_result_source(complex).replace(
            "gemm(left, right, target, overwrite, NativeFast);",
            "copy(result, destination);",
        )
    };
    let s = fixture(&without_gemm(false));
    s.write("src/complex/mod.vast", &without_gemm(true));
    let response = kernel(captured(&s), "emit");
    assert_eq!(response["ok"], true, "{response}");
    assert!(
        !response["lean_source"]
            .as_str()
            .unwrap()
            .contains("VastitasGemmNative")
    );
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

#[test]
#[ignore = "requires the explicit pinned OpenBLAS prefix; both numerical CI jobs run this test"]
fn owned_numerical_results_build_execute_real_complex_transfers() {
    let prefix =
        std::env::var_os("VASTITAS_TEST_OPENBLAS_PREFIX").expect("explicit numerical test prefix");
    let s = fixture(&owned_result_source(false));
    s.write("src/complex/mod.vast", &owned_result_source(true));
    let mut build = command(&s, "build");
    build
        .args(["-o", "program", "--openblas-prefix"])
        .arg(prefix);
    if let Some(cc) = std::env::var_os("VASTITAS_TEST_NATIVE_CC") {
        build.arg("--native-cc").arg(cc);
    }
    success(&build.output().unwrap());
    let output = Command::new(s.0.join("program")).output().unwrap();
    success(&output);
    assert_eq!(output.stdout, b"42\n");
}

fn coefficient_source(complex: bool) -> String {
    let profile = if complex {
        "ComplexSmooth"
    } else {
        "RealSmooth"
    };
    let scalar = if complex { "Complex<F64>" } else { "F64" };
    let literal = |real: f64, imaginary: f64| {
        if complex {
            format!("complex_bits({}, {})", real.to_bits(), imaginary.to_bits())
        } else {
            format!("f64_bits({})", real.to_bits())
        }
    };
    let a = literal(if complex { 1.0 } else { 2.0 }, 1.0);
    let b = literal(if complex { 2.0 } else { 0.25 }, 0.0);
    let two = literal(2.0, 0.0);
    let half = literal(0.5, 0.0);
    let changed = literal(if complex { 0.0 } else { 2.0 }, 1.0);
    let first = literal(if complex { 2.0 } else { 0.75 }, 10.0);
    let second = literal(if complex { -1.0 } else { 1.375 }, 7.0);
    format!(
        "pub resource fn product() -> Unit {{
            space u = linear(super::profiles::{profile}, 1); basis bu = basis(u);
            allocate a: {scalar}[1]; allocate b: {scalar}[1];
            allocate c: {scalar}[1]; allocate factor: {scalar}[1];
            borrow wa = write(a, layout(0, 1, 1, 1, false)); fill(wa, {a}); release(wa);
            borrow wb = write(b, layout(0, 1, 1, 1, false)); fill(wb, {b}); release(wb);
            borrow ra = read(a, layout(0, 1, 1, 1, false));
            borrow rb = read(b, layout(0, 1, 1, 1, false));
            map left = view(ra, bu, bu); map right = view(rb, bu, bu);
            borrow wf = write(factor, layout(0, 1, 1, 1, false));
            map computed = view(wf, bu, bu);
            gemm(left, right, computed, overwrite, NativeFast); release(wf);
            borrow wc = write(c, layout(0, 1, 1, 1, false));
            map destination = view(wc, bu, bu);
            gemm(left, right, destination, overwrite, NativeFast, alpha={two}); release(wc);
            borrow rf = read(factor, layout(0, 1, 1, 1, false));
            borrow updated = read_write(c, layout(0, 1, 1, 1, false));
            map accumulator = view(updated, bu, bu);
            call update(u, bu, left, right, accumulator, rf) -> ();
            expect(updated, 0, 0, {first}); release(rf);
            borrow change = write(factor, layout(0, 1, 1, 1, false));
            fill(change, {changed}); release(change);
            borrow rf_again = read(factor, layout(0, 1, 1, 1, false));
            call update(u, bu, left, right, accumulator, rf_again) -> ();
            expect(updated, 0, 0, {second});
            release(rf_again); release(updated); release(rb); release(ra);
            drop(factor); drop(c); drop(b); drop(a); value {{ () }}
        }}
        resource fn update(u: Space<super::profiles::{profile}, 1>, bu: Basis<u>,
            left: ReadMap<bu, bu>, right: ReadMap<bu, bu>, output: ReadWriteMap<bu, bu>,
            factor: Read<{scalar}, 1, 1>) -> Unit {{
            gemm(left, right, output, accumulate, NativeFast, alpha=coefficient(factor), beta={half});
            value {{ () }}
        }}"
    )
}

fn exact_coefficient_source(complex: bool) -> String {
    coefficient_source(complex)
        .replace("f64_bits(4611686018427387904)", "f64(0x1p1)")
        .replace("f64_bits(4602678819172646912)", "f64(0.5)")
        .replace("complex_bits(4611686018427387904, 0)", "complex(0x1p1, 0)")
        .replace(
            "complex_bits(4602678819172646912, 0)",
            "complex(0.5, 0x0p0)",
        )
}

#[test]
fn exact_gemm_coefficients_keep_the_existing_real_and_complex_wire() {
    let s = fixture(&exact_coefficient_source(false));
    s.write("src/complex/mod.vast", &exact_coefficient_source(true));
    success(&command(&s, "check").output().unwrap());
    let mut exact = captured(&s);
    assert_eq!(kernel(&exact, "emit")["ok"], true);
    s.write("src/real/mod.vast", &coefficient_source(false));
    s.write("src/complex/mod.vast", &coefficient_source(true));
    let mut explicit = captured(&s);
    common::remove_spans(&mut exact);
    common::remove_spans(&mut explicit);
    assert_eq!(exact, explicit);
}

fn half_accumulated(source: &str, complex: bool) -> String {
    let literal = |real: f64, imaginary: f64| {
        if complex {
            format!("complex_bits({}, {})", real.to_bits(), imaginary.to_bits())
        } else {
            format!("f64_bits({})", real.to_bits())
        }
    };
    let mut result = source.replace(
        "gemm(left, right, accumulated, accumulate, NativeFast);",
        &format!(
            "gemm(left, right, accumulated, accumulate, NativeFast, beta={});",
            literal(0.5, 0.0)
        ),
    );
    let products = if complex {
        [[(1.0, 2.0), (0.0, 3.0)], [(2.0, 0.0), (2.0, 0.0)]]
    } else {
        [[(58.0, 0.0), (64.0, 0.0)], [(139.0, 0.0), (154.0, 0.0)]]
    };
    for (i, row) in products.iter().enumerate() {
        for (j, &(real, imaginary)) in row.iter().enumerate() {
            let old = format!(
                "expect(updated, {i}, {j}, {});",
                literal(2.0 * real, 2.0 * imaginary)
            );
            assert!(result.contains(&old));
            result = result.replace(
                &old,
                &format!(
                    "expect(updated, {i}, {j}, {});",
                    literal(1.5 * real, 1.5 * imaginary)
                ),
            );
        }
    }
    result
}

#[test]
fn numerical_coefficients_check_actual_computed_scalar_loans_and_strict_wire() {
    let s = fixture(&coefficient_source(false));
    s.write("src/complex/mod.vast", &coefficient_source(true));
    success(&command(&s, "check").output().unwrap());
    let raw = captured(&s);
    let response = kernel(&raw, "emit");
    assert_eq!(response["ok"], true, "{response}");
    let generated = response["lean_source"].as_str().unwrap();
    assert_eq!(generated.matches("gemmScaled arena").count(), 6);
    assert_eq!(generated.matches("allocate arena").count(), 8);
    assert!(!generated.contains("copy arena"));
    for value in [
        json!(null),
        json!({"kind":"loan", "loan":"output"}),
        json!({"kind":"literal", "value":{"kind":"complex_f64", "real":0, "imaginary":0}}),
        json!({"kind":"loan", "loan":"factor", "checked":true}),
    ] {
        let mut altered = raw.clone();
        module(&mut altered, "real")["resource_functions"][1]["body"][0]["operation"]["alpha"] =
            value;
        let response = kernel(altered, "emit");
        assert_eq!(response["ok"], false, "{response}");
        assert!(response.get("lean_source").is_none());
    }
    let source = coefficient_source(false);
    for (before, after, code) in [
        (
            "alpha=coefficient(factor)",
            "alpha=coefficient(output)",
            "E_RESOURCE_LOAN",
        ),
        (
            "alpha=coefficient(factor)",
            "alpha=complex_bits(0, 0)",
            "E_RESOURCE_COEFFICIENT",
        ),
        (
            "NativeFast, alpha=f64_bits",
            "NativeFast, beta=f64_bits",
            "E_RESOURCE_COEFFICIENT",
        ),
        (
            "alpha=coefficient(factor)",
            "alpha=f64_bits(0), alpha=f64_bits(0)",
            "E_DUPLICATE",
        ),
        (
            "call update(u, bu, left, right, accumulator, rf)",
            "gemm(left, right, accumulator, accumulate, NativeFast, alpha=coefficient(updated)); call update(u, bu, left, right, accumulator, rf)",
            "E_RESOURCE_COEFFICIENT",
        ),
    ] {
        assert!(source.contains(before));
        rejection(&fixture(&source.replace(before, after)), code);
    }
}

#[test]
fn numerical_inputs_preserve_nominal_contracts_and_emit_without_extra_storage() {
    let s = fixture(&with_interfaces(REAL, "RealSmooth"));
    s.write(
        "src/complex/mod.vast",
        &with_interfaces(COMPLEX, "ComplexSmooth"),
    );
    success(&command(&s, "check").output().unwrap());
    let response = kernel(captured(&s), "emit");
    assert_eq!(response["ok"], true, "{response}");
    let generated = response["lean_source"].as_str().unwrap();
    assert_eq!(
        generated.matches("VastitasGemmNative.gemm arena").count(),
        4
    );
    assert_eq!(generated.matches("allocate arena").count(), 6);
    assert!(!generated.contains("copy arena"));
    // Even a library/pure entry checks each original numerical contract/body.
    s.write(
        "src/main.vast",
        "mod profiles; mod real; mod complex; fn main() -> Int { 42 }",
    );
    let response = kernel(captured(&s), "emit");
    assert_eq!(response["ok"], true, "{response}");
    assert_eq!(response["numerical_runtime"], false);
    assert_eq!(response["storage_runtime"], false);
}

#[test]
fn numerical_input_source_rejects_wrong_dependencies_permissions_and_postconditions() {
    let source = with_interfaces(REAL, "RealSmooth");
    for (before, after, code) in [
        (
            "call forward(u, v, w",
            "call forward(w, v, w",
            "E_NUMERICAL_TYPE",
        ),
        ("bu: Basis<u>", "bu: Basis<w>", "E_NUMERICAL_TYPE"),
        ("bu: Basis<u>", "bu: Basis<bu>", "E_RESOURCE_NAME"),
        (
            "u: Space<super::profiles::RealSmooth, 2>",
            "u: Space<super::profiles::RealSmooth, 3>",
            "E_NUMERICAL_TYPE",
        ),
        (
            "v: Space<super::profiles::RealSmooth, 3>",
            "v: Basis<u>",
            "E_NUMERICAL_TYPE",
        ),
        (
            "right: ReadMap<bu, bv>",
            "right: ReadMap<bv, bu>",
            "E_NUMERICAL_TYPE",
        ),
        (
            "left: ReadMap<bv, bw>",
            "left: WriteMap<bv, bw>",
            "E_RESOURCE_ACCESS",
        ),
        (
            "gemm(left, right, destination, overwrite, NativeFast);",
            "",
            "E_RESOURCE_INIT",
        ),
        (
            "gemm(left, right, destination, overwrite, NativeFast);",
            "fill(destination, f64_bits(0));",
            "E_RESOURCE_LOAN",
        ),
        (
            "call forward(u, v, w",
            "transpose(output); call forward(u, v, w",
            "E_NUMERICAL_TYPE",
        ),
    ] {
        assert!(source.contains(before), "missing mutation {before}");
        let s = fixture(&source.replace(before, after));
        rejection(&s, code);
    }
}

#[test]
fn numerical_input_wire_rechecks_headers_and_rejects_forged_metadata() {
    let s = fixture(&with_interfaces(REAL, "RealSmooth"));
    let raw = captured(&s);
    assert_eq!(kernel(&raw, "check")["ok"], true);
    for unused in [false, true] {
        let mut raw = raw.clone();
        if unused {
            s.write(
                "src/main.vast",
                "mod profiles; mod real; mod complex; fn main() -> Int { 42 }",
            );
            raw = captured(&s);
        }
        for (index, key, value, code) in [
            (0, "dimension", json!(3), "E_NUMERICAL_TYPE"),
            (3, "space", json!("w"), "E_NUMERICAL_TYPE"),
            (3, "space", json!("bu"), "E_RESOURCE_NAME"),
            (6, "source", json!("bu"), "E_NUMERICAL_TYPE"),
            (6, "access", json!("write"), "E_RESOURCE_ACCESS"),
            (6, "checked_id", json!(7), "E_PROTOCOL"),
            (8, "proof", json!(true), "E_PROTOCOL"),
        ] {
            let mut altered = raw.clone();
            module(&mut altered, "real")["resource_functions"][2]["parameters"][index][key] = value;
            assert_rejected(altered, code);
        }
        let mut altered = raw.clone();
        module(&mut altered, "real")["resource_functions"][2]["parameters"][0]["implementation"]
            ["checked_id"] = json!(12);
        assert_rejected(altered, "E_PROTOCOL");
    }
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
fn numerical_coefficients_build_execute_computed_real_complex_scalars() {
    let prefix =
        std::env::var_os("VASTITAS_TEST_OPENBLAS_PREFIX").expect("explicit numerical test prefix");
    for (real, complex) in [
        (coefficient_source(false), coefficient_source(true)),
        (
            exact_coefficient_source(false),
            exact_coefficient_source(true),
        ),
        (
            half_accumulated(REAL, false),
            half_accumulated(COMPLEX, true),
        ),
    ] {
        let s = fixture(&real);
        s.write("src/complex/mod.vast", &complex);
        let mut build = command(&s, "build");
        build
            .args(["-o", "program", "--openblas-prefix"])
            .arg(&prefix);
        if let Some(cc) = std::env::var_os("VASTITAS_TEST_NATIVE_CC") {
            build.arg("--native-cc").arg(cc);
        }
        success(&build.output().unwrap());
        let output = Command::new(s.0.join("program")).output().unwrap();
        success(&output);
        assert_eq!(output.stdout, b"42\n");
    }
}

#[test]
#[ignore = "requires the explicit pinned OpenBLAS prefix; both numerical CI jobs run this test"]
fn numerical_inputs_build_execute_nested_real_complex_products() {
    let prefix =
        std::env::var_os("VASTITAS_TEST_OPENBLAS_PREFIX").expect("explicit numerical test prefix");
    let s = fixture(&with_interfaces(REAL, "RealSmooth"));
    s.write(
        "src/complex/mod.vast",
        &with_interfaces(COMPLEX, "ComplexSmooth"),
    );
    let mut build = command(&s, "build");
    build
        .args(["-o", "program", "--openblas-prefix"])
        .arg(prefix);
    if let Some(cc) = std::env::var_os("VASTITAS_TEST_NATIVE_CC") {
        build.arg("--native-cc").arg(cc);
    }
    success(&build.output().unwrap());
    let output = Command::new(s.0.join("program")).output().unwrap();
    success(&output);
    assert_eq!(output.stdout, b"42\n");
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

const TRANSFORMS: &str = include_str!("../examples/packages/linear-transforms/src/main.vast");

fn transform_fixture(source: &str) -> Scratch {
    let s = Scratch::empty("typed linear transforms");
    s.write(
        "Vastitas.toml",
        include_str!("../examples/packages/linear-transforms/Vastitas.toml"),
    );
    s.write("src/main.vast", source);
    s.write(
        "src/profiles/mod.vast",
        include_str!("../examples/packages/linear-transforms/src/profiles/mod.vast"),
    );
    s
}

fn transform_body(raw: &mut Value) -> &mut Vec<Value> {
    raw["packages"][0]["modules"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|module| module["path"] == json!([]))
        .unwrap()["resource_functions"][0]["body"]
        .as_array_mut()
        .unwrap()
}

fn real_transforms() -> String {
    TRANSFORMS
        .replace("ComplexSmooth", "RealSmooth")
        .replace("Complex<F64>", "F64")
        .replace(
            "complex_bits(0, 4607182418800017408)",
            "f64_bits(4611686018427387904)",
        )
        .replace(
            "complex_bits(0, 13830554455654793216)",
            "f64_bits(4611686018427387904)",
        )
        .replace(
            "complex_bits(4607182418800017408, 0)",
            "f64_bits(4607182418800017408)",
        )
}

#[test]
fn typed_linear_transforms_check_preserve_views_and_reject_bad_authority() {
    for source in [TRANSFORMS.to_owned(), real_transforms()] {
        let s = transform_fixture(&source);
        success(&command(&s, "check").output().unwrap());
        let response = kernel(captured(&s), "emit");
        assert_eq!(response["ok"], true, "{response}");
        let generated = response["lean_source"].as_str().unwrap();
        assert_eq!(generated.matches("allocate arena").count(), 3);
        assert_eq!(
            generated.matches("VastitasGemmNative.gemm arena").count(),
            3
        );
        assert!(!generated.contains("copy arena"));
    }
    for (old, new, code) in [
        (
            "space vd = dual(v);",
            "space vd = conjugate(v, sigma);",
            "E_NUMERICAL_TYPE",
        ),
        ("derived(bv, vd)", "basis(vd)", "E_NUMERICAL_TYPE"),
        ("derived(bv, vd)", "derived(bw, vd)", "E_NUMERICAL_TYPE"),
        (
            "dual(input, bwd, bvd)",
            "dual(input, bvd, bwd)",
            "E_NUMERICAL_TYPE",
        ),
        (
            "conjugate(input, bvc, bwc, sigma)",
            "dual(input, bvc, bwc)",
            "E_NUMERICAL_TYPE",
        ),
        (
            "adjoint(input, hv, hw)",
            "adjoint(input, hv, input)",
            "E_NUMERICAL_TYPE",
        ),
        (
            "adjoint(input, hv, hw)",
            "adjoint(input, hw, hv)",
            "E_NUMERICAL_TYPE",
        ),
        (
            "orthonormal(bv, sigma)",
            "scaled_identity(bv, sigma, 2)",
            "E_NUMERICAL_TYPE",
        ),
        (
            "orthonormal(bv, sigma)",
            "scaled_identity(bv, sigma, 0)",
            "E_NUMERICAL_TYPE",
        ),
        (
            "diagonal(bw, sigma, [1])",
            "diagonal(bw, sigma, [1, 1])",
            "E_NUMERICAL_TYPE",
        ),
        (
            "diagonal(bw, sigma, [1])",
            "diagonal(bw, sigma, [0])",
            "E_NUMERICAL_TYPE",
        ),
        (
            "hv: OrthonormalMetric<bv, sigma>",
            "hv: Metric<bv, sigma>",
            "E_NUMERICAL_TYPE",
        ),
        (
            "involution sigma = canonical(v);",
            "space real_base = linear(profiles::RealSmooth, 1); involution sigma = canonical(real_base);",
            "E_NUMERICAL_TYPE",
        ),
        (
            "map transformed = dual(input, bwd, bvd);",
            "map transformed = dual(input, bwd, bvd); release(input);",
            "E_RESOURCE_LOAN",
        ),
        (
            "release(transformed);",
            "release(transformed); release(transformed);",
            "E_RESOURCE_LOAN",
        ),
        ("release(transformed);", "", "E_RESOURCE_LOAN"),
    ] {
        let changed = TRANSFORMS.replace(old, new);
        assert_ne!(changed, TRANSFORMS, "ineffective source mutation: {old}");
        rejection(&transform_fixture(&changed), code);
    }
}

#[test]
fn typed_linear_transform_wire_rejects_forged_evidence_and_old_protocols() {
    let raw = captured(&transform_fixture(TRANSFORMS));
    for version in 2..8 {
        let mut changed = raw.clone();
        changed["version"] = json!(version);
        let response = kernel(changed, "emit");
        assert_eq!(response["ok"], false, "{response}");
        assert!(response.get("lean_source").is_none());
    }
    for (name, key, value, expected) in [
        ("vd", "parent", json!("w"), "E_NUMERICAL_TYPE"),
        ("bvd", "parent", json!("bw"), "E_NUMERICAL_TYPE"),
        ("vc", "involution", json!("v"), "E_NUMERICAL_TYPE"),
        (
            "hv",
            "gram",
            json!({"kind":"scaled_identity", "entry":"2"}),
            "E_NUMERICAL_TYPE",
        ),
        (
            "hv",
            "gram",
            json!({"kind":"scaled_identity", "entry":"NaN"}),
            "E_PROTOCOL",
        ),
        (
            "hv",
            "gram",
            json!({"kind":"identity", "orthonormal":true}),
            "E_PROTOCOL",
        ),
        ("hv", "checked", json!(true), "E_PROTOCOL"),
        ("sigma", "coefficient", json!("complex"), "E_PROTOCOL"),
    ] {
        let mut changed = raw.clone();
        local_operation(transform_body(&mut changed), name)[key] = value;
        let response = kernel(changed, "emit");
        assert_eq!(response["ok"], false, "{name}/{key}: {response}");
        assert_eq!(response["diagnostics"][0]["code"], expected, "{response}");
        assert!(response.get("lean_source").is_none());
    }
    for field in ["conjugate", "allocation", "origin", "checked"] {
        let mut changed = raw.clone();
        let functions = changed["packages"][0]["modules"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|m| m["path"] == json!([]))
            .unwrap()["resource_functions"]
            .as_array_mut()
            .unwrap();
        let helper = functions
            .iter_mut()
            .find(|f| f["name"] == "adjoint_into")
            .unwrap();
        helper["body"][0]["operation"]["operation"][field] = json!(true);
        let response = kernel(changed, "emit");
        assert_eq!(response["ok"], false, "{response}");
        assert_eq!(
            response["diagnostics"][0]["code"], "E_PROTOCOL",
            "{response}"
        );
        assert!(response.get("lean_source").is_none());
    }
}

#[test]
fn typed_transform_metadata_builds_without_openblas_and_checks_unused_helpers() {
    let start = TRANSFORMS.find("    allocate a:").unwrap();
    let end = TRANSFORMS.find("\nresource fn dual_into").unwrap();
    let source = format!(
        "{}    value {{ 42 }}\n}}\n{}",
        &TRANSFORMS[..start],
        &TRANSFORMS[end..]
    );
    let s = transform_fixture(&source);
    success(
        &command(&s, "build")
            .args(["-o", "program"])
            .output()
            .unwrap(),
    );
    let output = Command::new(s.0.join("program")).output().unwrap();
    success(&output);
    assert_eq!(output.stdout, b"42\n");
    // Removing calls does not bypass independent checking of invalid bodies.
    s.write(
        "src/main.vast",
        &source.replace("dual(input, bwd, bvd)", "dual(input, bvd, bwd)"),
    );
    let original = std::fs::read(s.0.join("program")).unwrap();
    let failed = command(&s, "build")
        .args(["-o", "program"])
        .output()
        .unwrap();
    assert!(!failed.status.success());
    assert_eq!(std::fs::read(s.0.join("program")).unwrap(), original);
}

fn rectangular_transform_source(complex: bool, kind: &str) -> String {
    let profile = if complex {
        "ComplexSmooth"
    } else {
        "RealSmooth"
    };
    let scalar = if complex { "Complex<F64>" } else { "F64" };
    let width = if complex { 16 } else { 8 };
    let literal = |re: f64, im: f64| {
        if complex {
            format!("complex_bits({}, {})", re.to_bits(), im.to_bits())
        } else {
            format!("f64_bits({})", re.to_bits())
        }
    };
    let transpose = kind != "conjugate";
    let conjugate = kind != "dual";
    let (input_space, output_space, input_basis, output_basis, operation) = match kind {
        "dual" => ("wd", "vd", "bwd", "bvd", "dual(original, bwd, bvd)"),
        "conjugate" => (
            "vc",
            "wc",
            "bvc",
            "bwc",
            "conjugate(original, bvc, bwc, sigma)",
        ),
        "adjoint" => ("w", "v", "bw", "bv", "adjoint(original, hv, hw)"),
        _ => panic!("unknown transform"),
    };
    let (rows, columns) = if transpose { (3, 2) } else { (2, 3) };
    let input = format!("layout({width}, 2, 3, 4, false)");
    let identity = format!(
        "layout({width}, {columns}, {columns}, {}, false)",
        columns + 2
    );
    let output = format!("layout({width}, {rows}, {columns}, {}, false)", rows + 2);
    let mut source = format!("mod profiles; resource fn main() -> Int {{
        space v = linear(profiles::{profile}, 3); space w = linear(profiles::{profile}, 2);
        basis bv = basis(v); basis bw = basis(w); involution sigma = canonical(v);
        space vd = dual(v); space wd = dual(w); basis bvd = derived(bv, vd); basis bwd = derived(bw, wd);
        space vc = conjugate(v, sigma); space wc = conjugate(w, sigma);
        basis bvc = derived(bv, vc); basis bwc = derived(bw, wc);
        metric hv = orthonormal(bv, sigma); metric hw = orthonormal(bw, sigma);
        allocate a: {scalar}[13]; allocate b: {scalar}[{}]; allocate c: {scalar}[{}];
        borrow wa = write(a, {input});", 1+(columns+2)*columns, 1+(rows+2)*columns);
    for i in 0..2 {
        for j in 0..3 {
            let re = (i * 3 + j + 1) as f64;
            source += &format!("store(wa, {i}, {j}, {});", literal(re, re + 6.0));
        }
    }
    source += &format!("release(wa); borrow wb = write(b, {identity});");
    for i in 0..columns {
        for j in 0..columns {
            source += &format!(
                "store(wb, {i}, {j}, {});",
                literal(if i == j { 1.0 } else { 0.0 }, 0.0)
            );
        }
    }
    source += &format!("release(wb); borrow ra = read(a, {input}); borrow rb = read(b, {identity});
        borrow wc_out = write(c, {output}); map original = view(ra, bv, bw); map transformed = {operation};
        map unit = view(rb, {input_basis}, {input_basis}); map destination = view(wc_out, {input_basis}, {output_basis});
        call multiply({input_space}, {output_space}, {input_basis}, {output_basis}, transformed, unit, destination) -> ();
        release(transformed); release(wc_out); borrow result = read(c, {output});");
    for i in 0..rows {
        for j in 0..columns {
            let (r, c) = if transpose { (j, i) } else { (i, j) };
            let re = (r * 3 + c + 1) as f64;
            source += &format!(
                "expect(result, {i}, {j}, {});",
                literal(re, (re + 6.0) * if conjugate { -1.0 } else { 1.0 })
            );
        }
    }
    source += &format!("release(result); release(ra); release(rb); drop(a); drop(b); drop(c); value {{ 42 }} }}
        resource fn multiply(u: Space<profiles::{profile}, {columns}>, z: Space<profiles::{profile}, {rows}>,
            bu: Basis<u>, bz: Basis<z>, left: ReadMap<bu, bz>, right: ReadMap<bu, bu>,
            output: WriteMap<bu, bz> initializes) -> Unit {{
            gemm(left, right, output, overwrite, NativeFast); value {{ () }} }}");
    source
}

#[test]
fn typed_rectangular_transforms_check_all_endpoint_directions() {
    for complex in [false, true] {
        for kind in ["dual", "conjugate", "adjoint"] {
            let source = rectangular_transform_source(complex, kind);
            success(
                &command(&transform_fixture(&source), "check")
                    .output()
                    .unwrap(),
            );
        }
    }
    let owned = owned_transform_source();
    success(
        &command(&transform_fixture(&owned), "check")
            .output()
            .unwrap(),
    );
    rejection(
        &transform_fixture(&owned.replace("made: OwnedMap<bu, bz>", "made: OwnedMap<bz, bu>")),
        "E_NUMERICAL_TYPE",
    );
}

fn owned_transform_source() -> String {
    // Materialize the transformed map in a callee-owned padded destination,
    // then return its exact caller-selected dual bases and allocation.
    let mut source = rectangular_transform_source(true, "dual");
    for (old, new) in [
        ("allocate c: Complex<F64>[11];", ""),
        ("borrow wc_out = write(c, layout(16, 3, 2, 5, false));", ""),
        ("map destination = view(wc_out, bwd, bvd);", ""),
        (
            "call multiply(wd, vd, bwd, bvd, transformed, unit, destination) -> ();",
            "call multiply(wd, vd, bwd, bvd, transformed, unit) -> (made);",
        ),
        (
            "release(wc_out); borrow result = read(c, layout(16, 3, 2, 5, false));",
            "borrow result = read(made);",
        ),
        ("drop(c);", "drop(made);"),
        (
            "right: ReadMap<bu, bu>,\n            output: WriteMap<bu, bz> initializes) -> Unit",
            "right: ReadMap<bu, bu>) returns(made: OwnedMap<bu, bz>) -> Unit",
        ),
        (
            "gemm(left, right, output, overwrite, NativeFast);",
            "allocate c: Complex<F64>[11]; borrow wc_out = write(c, layout(16, 3, 2, 5, false));
          map output = view(wc_out, bu, bz); gemm(left, right, output, overwrite, NativeFast);
          release(wc_out); map made = owned(c, layout(16, 3, 2, 5, false), bu, bz);",
        ),
    ] {
        assert!(
            source.contains(old),
            "ineffective owned transform source edit: {old}"
        );
        source = source.replace(old, new);
    }
    source
}

#[test]
#[ignore = "requires the explicit pinned OpenBLAS prefix; both numerical CI jobs run this test"]
fn typed_linear_transforms_build_execute_real_complex_and_rectangular_calls() {
    let prefix =
        std::env::var_os("VASTITAS_TEST_OPENBLAS_PREFIX").expect("explicit numerical test prefix");
    let mut sources = vec![TRANSFORMS.to_owned(), real_transforms()];
    sources.push(owned_transform_source());
    for complex in [false, true] {
        for kind in ["dual", "conjugate", "adjoint"] {
            sources.push(rectangular_transform_source(complex, kind));
        }
    }
    for source in sources {
        let s = transform_fixture(&source);
        let mut build = command(&s, "build");
        build
            .args(["-o", "program", "--openblas-prefix"])
            .arg(&prefix);
        if let Some(cc) = std::env::var_os("VASTITAS_TEST_NATIVE_CC") {
            build.arg("--native-cc").arg(cc);
        }
        success(&build.output().unwrap());
        let result = Command::new(s.0.join("program")).output().unwrap();
        success(&result);
        assert_eq!(result.stdout, b"42\n");
    }
}

const NETWORK_REAL: &str = include_str!("../examples/packages/finite_network/src/real/mod.vast");
const NETWORK_COMPLEX: &str =
    include_str!("../examples/packages/finite_network/src/complex/mod.vast");

fn network_statement<'a>(raw: &'a mut Value, name: &str) -> &'a mut Value {
    numerical_body(raw, name)
        .iter_mut()
        .find(|s| s["kind"] == "network")
        .unwrap()
}

fn network_reuse(complex: bool) -> String {
    let profile = if complex {
        "ComplexSmooth"
    } else {
        "RealSmooth"
    };
    let scalar = if complex { "Complex<F64>" } else { "F64" };
    let input = if complex {
        format!("complex_bits({}, {})", 2.0_f64.to_bits(), 3.0_f64.to_bits())
    } else {
        format!("f64_bits({})", 2.0_f64.to_bits())
    };
    // (2+3i)^2 = -5+12i, not the Hermitian result 13.
    let expected = if complex {
        format!(
            "complex_bits({}, {})",
            (-5.0_f64).to_bits(),
            12.0_f64.to_bits()
        )
    } else {
        format!("f64_bits({})", 4.0_f64.to_bits())
    };
    format!(
        "pub resource fn product() -> Unit {{
        space v = linear(super::profiles::{profile}, 1); basis bv = basis(v);
        allocate a: {scalar}[1]; allocate c: {scalar}[1];
        borrow init = write(a, layout(0, 1, 1, 1, false)); fill(init, {input}); release(init);
        borrow read = read(a, layout(0, 1, 1, 1, false)); map same = view(read, bv, bv);
        borrow write = write(c, layout(0, 1, 1, 1, false)); map destination = view(write, bv, bv);
        contract(destination, NativeFast) {{
            occurrence a = same; occurrence b = same;
            edge(a.input, b.output); input(b.input); output(a.output);
        }}
        release(write); release(read);
        borrow result = read(c, layout(0, 1, 1, 1, false)); expect(result, 0, 0, {expected});
        release(result); drop(a); drop(c); value {{ () }}
    }}"
    )
}

#[test]
fn finite_network_public_source_has_deterministic_gemm_and_no_port_allocations() {
    let s = fixture(NETWORK_REAL);
    s.write("src/complex/mod.vast", NETWORK_COMPLEX);
    success(&command(&s, "check").output().unwrap());
    let raw = captured(&s);
    let response = kernel(&raw, "emit");
    assert_eq!(response["ok"], true, "{response}");
    let generated = response["lean_source"].as_str().unwrap();
    assert_eq!(generated.matches("allocate arena").count(), 6);
    assert_eq!(
        generated.matches("VastitasGemmNative.gemm arena").count(),
        2
    );
    assert!(!generated.contains("copy arena"));
    let mut reordered = raw.clone();
    network_statement(&mut reordered, "real")["graph"]["occurrences"]
        .as_array_mut()
        .unwrap()
        .reverse();
    assert_eq!(
        kernel(&reordered, "emit")["lean_source"],
        response["lean_source"]
    );
    {
        let (real, complex) = (network_reuse(false), network_reuse(true));
        let reuse = fixture(&real);
        reuse.write("src/complex/mod.vast", &complex);
        success(&command(&reuse, "check").output().unwrap());
        let emission = kernel(captured(&reuse), "emit");
        assert_eq!(emission["ok"], true, "{emission}");
        let code = emission["lean_source"].as_str().unwrap();
        assert_eq!(code.matches("allocate arena").count(), 4);
        assert!(!code.contains("copy arena"));
    }
}

#[test]
fn finite_network_source_rejects_invalid_ports_and_unlicensed_identifications() {
    for (before, after) in [
        ("occurrence b = right;", "occurrence a = right;"),
        ("input(b.input);", "input(a.input);"),
        ("output(a.output);", ""),
        ("output(a.output);", "output(unknown.output);"),
        ("edge(a.input, b.output);", "edge(a.output, b.output);"),
        ("edge(a.input, b.output);", "edge(a.input, b.input);"),
        (
            "input(b.input);\n        output(a.output);",
            "input(a.output); output(b.input);",
        ),
        (
            "map right = view(input_b, bu, bv);",
            "space other = linear(super::profiles::RealSmooth, 3); basis bo = basis(other); map right = view(input_b, bu, bo);",
        ),
        (
            "map right = view(input_b, bu, bv);",
            "basis bo = basis(v); map right = view(input_b, bu, bo);",
        ),
        (
            "map right = view(input_b, bu, bv);",
            "space dv = dual(v); basis bdv = derived(bv, dv); map right = view(input_b, bu, bdv);",
        ),
        (
            "map right = view(input_b, bu, bv);",
            "involution sigma = canonical(v); space cv = conjugate(v, sigma); basis bcv = derived(bv, cv); map right = view(input_b, bu, bcv);",
        ),
    ] {
        assert!(NETWORK_REAL.contains(before));
        rejection(&fixture(&NETWORK_REAL.replace(before, after)), "E_NETWORK");
    }
    // Exact destination endpoints and live storage still use existing checkers.
    rejection(
        &fixture(&NETWORK_REAL.replace(
            "map destination = view(output, bu, bw);",
            "map destination = view(output, bw, bu);",
        )),
        "E_NUMERICAL_TYPE",
    );
    rejection(
        &fixture(&NETWORK_REAL.replace(
            "contract(destination",
            "release(input_a); contract(destination",
        )),
        "E_NUMERICAL_TYPE",
    );
    rejection(
        &fixture(&network_reuse(false).replace("contract(destination", "contract(same")),
        "E_RESOURCE_ACCESS",
    );
    let unused = fixture(&NETWORK_REAL.replace("input(b.input);", "input(a.input);"));
    unused.write(
        "src/main.vast",
        "mod real; mod complex; mod profiles; fn main() -> Int { 42 }",
    );
    rejection(&unused, "E_NETWORK");
    let branch = NETWORK_REAL.replace("    contract(destination, NativeFast) {", "    if true { gemm(left, right, destination, overwrite, NativeFast); } else { contract(destination, NativeFast) {")
        .replace("output(a.output);\n    }", "output(a.output);\n    } }")
        .replace("input(b.input);", "input(a.input);");
    rejection(&fixture(&branch), "E_NETWORK");
}

#[test]
fn finite_network_wire_is_independently_checked_and_fails_closed() {
    let s = fixture(NETWORK_REAL);
    let raw = captured(&s);
    for field in [
        "conjugate",
        "metric",
        "dual_conversion",
        "certificate",
        "schedule",
    ] {
        let mut changed = raw.clone();
        network_statement(&mut changed, "real")[field] = json!(true);
        assert_rejected(changed, "E_PROTOCOL");
    }
    for path in ["graph", "occurrence", "edge", "port"] {
        let mut changed = raw.clone();
        let graph = &mut network_statement(&mut changed, "real")["graph"];
        let target = match path {
            "graph" => graph,
            "occurrence" => &mut graph["occurrences"][0],
            "edge" => &mut graph["edges"][0],
            _ => &mut graph["edges"][0]["dual"],
        };
        target["conjugate"] = json!(true);
        assert_rejected(changed, "E_PROTOCOL");
    }
    for (field, value) in [
        ("inputs", json!([])),
        ("occurrences", json!([])),
        ("edges", json!([])),
    ] {
        let mut changed = raw.clone();
        network_statement(&mut changed, "real")["graph"][field] = value;
        assert_rejected(changed, "E_PROTOCOL");
    }
    for role in ["dual", "conjugate", "adjoint"] {
        let mut changed = raw.clone();
        network_statement(&mut changed, "real")["graph"]["edges"][0]["dual"]["role"] = json!(role);
        assert_rejected(changed, "E_PROTOCOL");
    }
    let mut changed = raw.clone();
    network_statement(&mut changed, "real")["graph"]["inputs"][0]["occurrence"] = json!("a");
    assert_rejected(changed, "E_NETWORK");
    let mut changed = raw.clone();
    local_operation(numerical_body(&mut changed, "real"), "right")["target"] = json!("bw");
    assert_rejected(changed, "E_NUMERICAL_TYPE");
    for version in [2, 3, 4, 5, 6, 7] {
        let mut changed = raw.clone();
        changed["version"] = json!(version);
        assert_eq!(kernel(&changed, "check")["ok"], false);
    }
}

#[test]
#[ignore = "requires the explicit pinned OpenBLAS prefix; both numerical CI jobs run this test"]
fn finite_network_build_execute_rectangular_complex_reuse_and_calls() {
    let prefix =
        std::env::var_os("VASTITAS_TEST_OPENBLAS_PREFIX").expect("explicit numerical test prefix");
    let nested = |source: &str, profile: &str| {
        with_interfaces(source, profile)
        .replace("gemm(left, right, destination, overwrite, NativeFast);", "contract(destination, NativeFast) { occurrence a = left; occurrence b = right; edge(a.input, b.output); input(b.input); output(a.output); }")
    };
    let branched_real = NETWORK_REAL
        .replace("    contract(destination, NativeFast) {", "    if true { contract(destination, NativeFast) {")
        .replace("output(a.output);\n    }", "output(a.output);\n    } } else { gemm(left, right, destination, overwrite, NativeFast); }");
    let branched_complex = NETWORK_COMPLEX
        .replace("    contract(destination, NativeFast) {", "    if false { gemm(left, right, destination, overwrite, NativeFast); } else { contract(destination, NativeFast) {")
        .replace("output(a.output);\n    }", "output(a.output);\n    } }");
    for (real, complex) in [
        (NETWORK_REAL.to_owned(), NETWORK_COMPLEX.to_owned()),
        (branched_real, branched_complex),
        (network_reuse(false), network_reuse(true)),
        (nested(REAL, "RealSmooth"), nested(COMPLEX, "ComplexSmooth")),
    ] {
        let s = fixture(&real);
        s.write("src/complex/mod.vast", &complex);
        success(&command(&s, "check").output().unwrap());
        let mut build = command(&s, "build");
        build
            .args(["-o", "program", "--openblas-prefix"])
            .arg(&prefix);
        if let Some(cc) = std::env::var_os("VASTITAS_TEST_NATIVE_CC") {
            build.arg("--native-cc").arg(cc);
        }
        success(&build.output().unwrap());
        let output = Command::new(s.0.join("program")).output().unwrap();
        success(&output);
        assert_eq!(output.stdout, b"42\n");
    }
}

#[test]
fn finite_network_unused_bodies_keep_ordinary_build_independent_of_blas() {
    let s = fixture(NETWORK_REAL);
    s.write("src/complex/mod.vast", NETWORK_COMPLEX);
    s.write(
        "src/main.vast",
        "mod real; mod complex; mod profiles; fn main() -> Int { 42 }",
    );
    success(&command(&s, "check").output().unwrap());
    let emission = kernel(captured(&s), "emit");
    assert_eq!(emission["ok"], true, "{emission}");
    assert_eq!(emission["numerical_runtime"], false);
    success(
        &command(&s, "build")
            .args(["-o", "ordinary"])
            .output()
            .unwrap(),
    );
    let output = Command::new(s.0.join("ordinary")).output().unwrap();
    success(&output);
    assert_eq!(output.stdout, b"42\n");
}

#[test]
fn finite_network_preserves_explicit_transformed_map_authority() {
    for kind in ["dual", "conjugate", "adjoint"] {
        let source = rectangular_transform_source(true, kind).replace(
            "gemm(left, right, output, overwrite, NativeFast);",
            "contract(output, NativeFast) { occurrence a = left; occurrence b = right; edge(a.input, b.output); input(b.input); output(a.output); }",
        );
        success(
            &command(&transform_fixture(&source), "check")
                .output()
                .unwrap(),
        );
    }
}

const EVALUATION: &str = include_str!("../examples/packages/vector-evaluation/src/main.vast");

fn evaluation_fixture(source: &str) -> Scratch {
    let s = Scratch::empty("bilinear vector evaluation");
    s.write(
        "Vastitas.toml",
        include_str!("../examples/packages/vector-evaluation/Vastitas.toml"),
    );
    s.write("src/main.vast", source);
    s.write(
        "src/profiles/mod.vast",
        include_str!("../examples/packages/vector-evaluation/src/profiles/mod.vast"),
    );
    s
}

fn evaluation_source(complex: bool, dimension: usize, transposed: bool) -> String {
    let layout = if transposed {
        format!("layout(16, 1, {dimension}, 2, true)")
    } else {
        format!("layout(16, {dimension}, 1, {}, false)", dimension + 2)
    };
    let mut source = EVALUATION
        .replace("ComplexSmooth, 1)", &format!("ComplexSmooth, {dimension})"))
        .replace("ComplexSmooth, 1>", &format!("ComplexSmooth, {dimension}>"))
        .replace(
            "input: Complex<F64>[4]",
            &format!("input: Complex<F64>[{}]", 2 * dimension + 2),
        )
        .replace(
            "write(input, layout(16, 1, 1, 3, false))",
            &format!("write(input, {layout})"),
        )
        .replace(
            "read(input, layout(16, 1, 1, 3, false))",
            &format!("read(input, {layout})"),
        );
    let literal = |n: f64| {
        if complex {
            format!("complex_bits({}, 0)", n.to_bits())
        } else {
            format!("f64_bits({})", n.to_bits())
        }
    };
    // The zero-inner convention writes positive zero, including for an empty dual evaluation.
    let dual = if complex && dimension != 0 {
        -(dimension as f64)
    } else {
        4.0 * dimension as f64
    };
    let hermitian = if complex {
        dimension as f64
    } else {
        4.0 * dimension as f64
    };
    source = source
        .replace("complex_bits(13830554455654793216, 0)", &literal(dual))
        .replace("complex_bits(4607182418800017408, 0)", &literal(hermitian));
    if !complex {
        source = source
            .replace("ComplexSmooth", "RealSmooth")
            .replace("Complex<F64>", "F64")
            .replace(
                "complex_bits(0, 4607182418800017408)",
                "f64_bits(4611686018427387904)",
            );
    }
    source
}

fn evaluation_extra_sources() -> [String; 4] {
    let mixed = EVALUATION
        .replace(
            "complex_bits(0, 4607182418800017408)",
            "complex_bits(4607182418800017408, 4611686018427387904)",
        )
        .replace(
            "complex_bits(13830554455654793216, 0)",
            "complex_bits(13837309855095848960, 4616189618054758400)",
        )
        .replace(
            "complex_bits(4607182418800017408, 0)",
            "complex_bits(4617315517961601024, 0)",
        );
    let accumulated = EVALUATION.replace("    call hermitian_value(v, bv", "    evaluate(phi, x, checked_out, accumulate, NativeFast, alpha=complex_bits(0, 4607182418800017408), beta=complex_bits(4611686018427387904, 0));\n    expect(checked_out, 0, 0, complex_bits(13835058055282163712, 13830554455654793216));\n    call hermitian_value(v, bv");
    let combined = |condition| {
        EVALUATION.replace(
            "    call algebraic(v, bv, vd, bvd, phi, x, out) -> ();",
            &format!(
                r#"    map tensor = view(read_input, bv, bv);
    map destination = view(out, bv, bv);
    if {condition} {{
        contract(destination, NativeFast) {{
            occurrence a = tensor; occurrence b = tensor;
            edge(a.input, b.output); input(b.input); output(a.output);
        }}
        call algebraic(v, bv, vd, bvd, phi, x, out) -> ();
    }} else {{
        call algebraic(v, bv, vd, bvd, phi, x, out) -> ();
        contract(destination, NativeFast) {{
            occurrence a = tensor; occurrence b = tensor;
            edge(a.input, b.output); input(b.input); output(a.output);
        }}
    }}"#
            ),
        )
    };
    [mixed, accumulated, combined(true), combined(false)]
}

#[test]
fn vector_evaluation_checks_nominal_roles_loans_and_all_shapes() {
    for complex in [false, true] {
        for dimension in [0, 1, 3] {
            for transposed in [false, true] {
                let s = evaluation_fixture(&evaluation_source(complex, dimension, transposed));
                success(&command(&s, "check").output().unwrap());
                let response = kernel(captured(&s), "emit");
                assert_eq!(response["ok"], true, "{response}");
                let generated = response["lean_source"].as_str().unwrap();
                assert_eq!(generated.matches("allocate arena").count(), 2);
                assert_eq!(
                    generated.matches("VastitasGemmNative.gemm arena").count(),
                    2
                );
                assert!(!generated.contains("copy arena"));
            }
        }
    }
    for (old, new) in [
        (
            "evaluate(phi, x, output, overwrite",
            "evaluate(x, x, output, overwrite",
        ),
        (
            "space vd = dual(v)",
            "space vd = linear(profiles::ComplexSmooth, 1)",
        ),
        ("basis bvd = derived(bv, vd)", "basis bvd = basis(vd)"),
        (
            "vector phi = view(read_input, bvd)",
            "vector phi = view(read_input, bv)",
        ),
        (
            "vector phi = view(read_input, bvd)",
            "vector phi = view(read_input, bvc)",
        ),
        ("conjugate(x, bvc, sigma)", "conjugate(x, bv, sigma)"),
        (
            "hermitian(x, y, output, h, overwrite",
            "evaluate(x, y, output, overwrite",
        ),
        ("h: OrthonormalMetric<bv, sigma>", "h: Metric<bv, sigma>"),
        (
            "metric h = orthonormal(bv, sigma)",
            "metric h = scaled_identity(bv, sigma, 2)",
        ),
        (
            "hermitian(x, y, output, h, overwrite",
            "hermitian(x, y, output, x, overwrite",
        ),
        (
            "evaluate(phi, x, output, overwrite",
            "evaluate(phi, x, output, accumulate",
        ),
        ("release(conjugated);", ""),
        ("release(conjugated);", "release(x); release(conjugated);"),
        ("fill(init, complex_bits(0, 4607182418800017408));", ""),
        ("phi, x, out) -> ()", "phi, x, read_input) -> ()"),
    ] {
        let changed = EVALUATION.replace(old, new);
        assert_ne!(changed, EVALUATION, "ineffective mutation: {old}");
        let result = command(&evaluation_fixture(&changed), "check")
            .output()
            .unwrap();
        assert!(
            !result.status.success(),
            "accepted invalid evaluation: {old} -> {new}"
        );
    }
    for source in evaluation_extra_sources() {
        success(
            &command(&evaluation_fixture(&source), "check")
                .output()
                .unwrap(),
        );
    }
    let aliased_coefficient = evaluation_extra_sources()[1].replace(
        "alpha=complex_bits(0, 4607182418800017408)",
        "alpha=coefficient(checked_out)",
    );
    rejection(
        &evaluation_fixture(&aliased_coefficient),
        "E_RESOURCE_COEFFICIENT",
    );
}

#[test]
fn vector_evaluation_wire_rejects_injected_authority_and_downgrades() {
    let raw = captured(&evaluation_fixture(EVALUATION));
    for version in 2..8 {
        let mut changed = raw.clone();
        changed["version"] = json!(version);
        let response = kernel(changed, "emit");
        assert_eq!(response["ok"], false, "{response}");
        assert!(response.get("lean_source").is_none());
    }
    for (name, key, value) in [
        ("phi", "basis", json!("bv")),
        ("x", "conjugate", json!(true)),
        ("x", "origin", json!({"kind":"dual"})),
        ("x", "allocation", json!(0)),
        ("x", "checked", json!(true)),
    ] {
        let mut changed = raw.clone();
        local_operation(transform_body(&mut changed), name)[key] = value;
        let response = kernel(changed, "emit");
        assert_eq!(response["ok"], false, "{name}/{key}: {response}");
        assert!(response.get("lean_source").is_none());
    }
    for field in ["conjugate_left", "loan", "checked", "metric"] {
        let mut changed = raw.clone();
        let root = changed["packages"][0]["modules"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|m| m["path"] == json!([]))
            .unwrap();
        let function = root["resource_functions"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|f| f["name"] == "algebraic")
            .unwrap();
        function["body"][0]["operation"]["operation"][field] = json!(true);
        let response = kernel(changed, "emit");
        assert_eq!(response["ok"], false, "{response}");
        assert_eq!(
            response["diagnostics"][0]["code"], "E_PROTOCOL",
            "{response}"
        );
    }
}

#[test]
fn vector_evaluation_unused_helpers_need_no_blas_but_remain_checked() {
    let start = EVALUATION.find("    allocate input:").unwrap();
    let end = EVALUATION.find("\nresource fn algebraic").unwrap();
    let source = format!(
        "{}    value {{ 42 }}\n}}\n{}",
        &EVALUATION[..start],
        &EVALUATION[end..]
    );
    let s = evaluation_fixture(&source);
    success(
        &command(&s, "build")
            .args(["-o", "program"])
            .output()
            .unwrap(),
    );
    let result = Command::new(s.0.join("program")).output().unwrap();
    success(&result);
    assert_eq!(result.stdout, b"42\n");
    let binary = std::fs::read(s.0.join("program")).unwrap();
    s.write(
        "src/main.vast",
        &source.replace("evaluate(phi, x, output", "evaluate(x, x, output"),
    );
    assert!(
        !command(&s, "build")
            .args(["-o", "program"])
            .output()
            .unwrap()
            .status
            .success()
    );
    assert_eq!(std::fs::read(s.0.join("program")).unwrap(), binary);
}

#[test]
#[ignore = "requires the explicit pinned OpenBLAS prefix; both numerical CI jobs run this test"]
fn vector_evaluation_builds_executes_real_complex_empty_and_transposed() {
    let prefix =
        std::env::var_os("VASTITAS_TEST_OPENBLAS_PREFIX").expect("explicit numerical test prefix");
    let mut sources = evaluation_extra_sources().to_vec();
    for complex in [false, true] {
        for dimension in [0, 1, 3] {
            for transposed in [false, true] {
                sources.push(evaluation_source(complex, dimension, transposed));
            }
        }
    }
    for source in sources {
        let s = evaluation_fixture(&source);
        let mut build = command(&s, "build");
        build
            .args(["-o", "program", "--openblas-prefix"])
            .arg(&prefix);
        if let Some(cc) = std::env::var_os("VASTITAS_TEST_NATIVE_CC") {
            build.arg("--native-cc").arg(cc);
        }
        success(&build.output().unwrap());
        let result = Command::new(s.0.join("program")).output().unwrap();
        success(&result);
        assert_eq!(result.stdout, b"42\n");
    }
}

#[test]
#[ignore = "requires the explicit pinned OpenBLAS prefix; both numerical CI jobs run this test"]
fn generated_owned_packages_feed_real_complex_gemm_without_copying() {
    let prefix =
        std::env::var_os("VASTITAS_TEST_OPENBLAS_PREFIX").expect("explicit numerical test prefix");
    let source = |complex: bool| {
        let (source, scalar, zero, one, result) = if complex {
            (
                include_str!("../examples/packages/generative-owned-map/src/complex/mod.vast"),
                "Complex<F64>",
                "complex_bits(0, 0)",
                "complex_bits(4607182418800017408, 0)",
                "complex_bits(4616189618054758400, 4617315517961601024)",
            )
        } else {
            (
                include_str!("../examples/packages/generative-owned-map/src/real/mod.vast"),
                "F64",
                "f64_bits(0)",
                "f64_bits(4607182418800017408)",
                "f64_bits(4616189618054758400)",
            )
        };
        source.replace("pub resource fn run()", "pub resource fn product()")
            .replace("drop(final);", &format!(
                "borrow left_data = read(final); map left = view(left_data, final);
                 allocate identity: {scalar}[4];
                 borrow initialize = write(identity, layout(0, 2, 2, 2, false));
                 fill(initialize, {zero}); store(initialize, 0, 0, {one}); store(initialize, 1, 1, {one}); release(initialize);
                 borrow right_data = read(identity, layout(0, 2, 2, 2, false)); map right = view(right_data, bu, bu);
                 allocate output: {scalar}[6]; borrow output_data = write(output, layout(0, 3, 2, 3, false));
                 map destination = view(output_data, bu, bw); gemm(left, right, destination, overwrite, NativeFast);
                 release(output_data); release(right_data); release(left_data); drop(final); drop(identity);
                 borrow answer = read(output, layout(0, 3, 2, 3, false));
                 expect(answer, 0, 0, {result}); expect(answer, 2, 1, {result}); release(answer); drop(output);"))
    };
    let s = fixture(&source(false));
    s.write("src/complex/mod.vast", &source(true));
    success(&command(&s, "check").output().unwrap());
    let response = kernel(captured(&s), "emit");
    assert_eq!(response["ok"], true, "{response}");
    let generated = response["lean_source"].as_str().unwrap();
    assert_eq!(generated.matches("allocate arena").count(), 6);
    assert!(!generated.contains("copy arena"));
    let mut build = command(&s, "build");
    build
        .args(["-o", "program", "--openblas-prefix"])
        .arg(prefix);
    if let Some(cc) = std::env::var_os("VASTITAS_TEST_NATIVE_CC") {
        build.arg("--native-cc").arg(cc);
    }
    success(&build.output().unwrap());
    let output = Command::new(s.0.join("program")).output().unwrap();
    success(&output);
    assert_eq!(output.stdout, b"42\n");
}
