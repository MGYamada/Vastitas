mod common;
use common::{Scratch, assert_rejected, cli, kernel, success};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;
use std::process::Command;

const REAL: &str = include_str!("../examples/packages/tensor-packing/src/real/mod.vast");
const COMPLEX: &str = include_str!("../examples/packages/tensor-packing/src/complex/mod.vast");

fn fixture(real: &str, complex: &str) -> Scratch {
    let s = Scratch::empty("tensor packing");
    s.write(
        "Vastitas.toml",
        include_str!("../examples/packages/tensor-packing/Vastitas.toml"),
    );
    s.write(
        "src/main.vast",
        include_str!("../examples/packages/tensor-packing/src/main.vast"),
    );
    s.write(
        "src/profiles/mod.vast",
        include_str!("../examples/packages/tensor-packing/src/profiles/mod.vast"),
    );
    s.write("src/real/mod.vast", real);
    s.write("src/complex/mod.vast", complex);
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
fn operation<'a>(raw: &'a mut Value, name: &str) -> &'a mut Value {
    &mut raw["packages"][0]["modules"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|module| module["path"] == json!(["real"]))
        .unwrap()["resource_functions"][0]["body"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|statement| statement["operation"]["name"] == name)
        .unwrap()["operation"]
}
fn rejection(source: &str) {
    let result = command(&fixture(source, COMPLEX), "check")
        .output()
        .unwrap();
    assert!(
        !result.status.success(),
        "accepted invalid tensor source: {source}"
    );
}
fn branched(source: &str, condition: bool) -> String {
    source.replace("    pack3(t, destination);", &format!("    if {condition} {{ pack3(t, destination); }} else {{ pack3(t, destination); }}"))
        .replace("    contract3(packed, b, c, NativeFast);", &format!("    if {condition} {{ contract3(packed, b, c, NativeFast); }} else {{ contract3(packed, b, c, NativeFast); }}"))
}

fn through_calls(source: &str, complex: bool) -> String {
    let profile = if complex {
        "ComplexSmooth"
    } else {
        "RealSmooth"
    };
    let scalar = if complex { "Complex<F64>" } else { "F64" };
    let pack_header = format!(
        "u: Space<super::profiles::{profile}, 2>, bu: Basis<u>, v: Space<super::profiles::{profile}, 3>, bv: Basis<v>, vd: DualSpace<v>, bvd: DerivedBasis<bv, vd>, w: Space<super::profiles::{profile}, 2>, bw: Basis<w>, source: Read<{scalar}, 2, 6>, destination: Write<{scalar}, 4, 3> initializes"
    );
    let product_header = format!(
        "u: Space<super::profiles::{profile}, 2>, bu: Basis<u>, v: Space<super::profiles::{profile}, 3>, bv: Basis<v>, vd: DualSpace<v>, bvd: DerivedBasis<bv, vd>, w: Space<super::profiles::{profile}, 2>, bw: Basis<w>, x: Space<super::profiles::{profile}, 2>, bx: Basis<x>, xd: DualSpace<x>, bxd: DerivedBasis<bx, xd>, source: Read<{scalar}, 4, 3>, right: Read<{scalar}, 3, 2>, destination: Write<{scalar}, 4, 2> initializes"
    );
    let source = source.replace("pack3(t, destination);", "call pack_forward(u, bu, v, bv, vd, bvd, w, bw, input_t, packing) -> ();")
        .replace("contract3(packed, b, c, NativeFast);", "call contract_into(u, bu, v, bv, vd, bvd, w, bw, x, bx, xd, bxd, packed_read, input_b, output) -> ();");
    format!("{source}
      resource fn pack_forward({pack_header}) -> Unit {{
        call pack_into(u, bu, v, bv, vd, bvd, w, bw, source, destination) -> (); value {{ () }}
      }}
      resource fn pack_into({pack_header}) -> Unit {{
        tensor t = view3(source, bu, bvd, bw, axes(0,1,2), 1);
        tensor p = view3(destination, bu, bvd, bw, axes(0,2,1), 2); pack3(t, p); value {{ () }}
      }}
      resource fn contract_into({product_header}) -> Unit {{
        tensor t = view3(source, bu, bvd, bw, axes(0,2,1), 2);
        tensor b = view2(right, bv, bxd); tensor c = view3(destination, bu, bw, bxd, axes(0,1,2), 2);
        contract3(t, b, c, NativeFast); value {{ () }}
      }}")
}

#[test]
fn tensor_source_checks_real_axes_explicit_packing_and_ordered_boundaries() {
    let s = fixture(REAL, COMPLEX);
    success(&command(&s, "check").output().unwrap());
    let emission = kernel(captured(&s), "emit");
    assert_eq!(emission["ok"], true, "{emission}");
    let native = emission["lean_source"].as_str().unwrap();
    assert_eq!(native.matches("pack3 arena").count(), 2);
    assert_eq!(native.matches("VastitasGemmNative.gemm arena").count(), 2);
    assert_eq!(native.matches("allocate arena").count(), 8);
    assert!(!native.contains("copy arena"));
    success(
        &command(
            &fixture(&through_calls(REAL, false), &through_calls(COMPLEX, true)),
            "check",
        )
        .output()
        .unwrap(),
    );
    for condition in [false, true] {
        success(
            &command(
                &fixture(&branched(REAL, condition), &branched(COMPLEX, condition)),
                "check",
            )
            .output()
            .unwrap(),
        );
    }
    rejection(
        &REAL
            .replace(
                "basis bv = basis(v);",
                "basis bv = basis(v); basis other = basis(v);",
            )
            .replace("view2(input_b, bv, bxd)", "view2(input_b, other, bxd)"),
    );
    let already_grouped = |complex| {
        constant_source(complex, [2, 3, 2, 2]).replace(
            "pack3(t, p);",
            if complex {
                "fill(packing, complex_bits(0, 4607182418800017408));"
            } else {
                "fill(packing, f64_bits(4607182418800017408));"
            },
        )
    };
    let grouped = fixture(&already_grouped(false), &already_grouped(true));
    let emission = kernel(captured(&grouped), "emit");
    assert_eq!(emission["ok"], true, "{emission}");
    assert!(
        !emission["lean_source"]
            .as_str()
            .unwrap()
            .contains("pack3 arena")
    );
    for (old, new) in [
        ("view3(output, bu, bw, bxd", "view3(output, bw, bu, bxd"),
        ("view3(input_t, bu, bvd, bw", "view3(input_t, bu, bv, bw"),
        (
            "space vd = dual(v);",
            "involution sigma = canonical(v); space vd = conjugate(v, sigma);",
        ),
        ("axes(0, 2, 1), 2", "axes(0, 0, 1), 2"),
        ("pack3(t, destination);", ""),
        ("release(packing);", ""),
        (
            "pack3(t, destination);",
            "release(input_t); pack3(t, destination);",
        ),
        (
            "contract3(packed, b, c, NativeFast);",
            "contract3(t, b, c, NativeFast);",
        ),
        (
            "write(scratch, layout(8, 4, 3, 5, false))",
            "write(original, layout(8, 4, 3, 5, false))",
        ),
    ] {
        assert!(REAL.contains(old), "ineffective mutation: {old}");
        rejection(&REAL.replace(old, new));
    }
}

#[test]
fn tensor_wire_rejects_forged_axes_groupings_authority_and_old_envelopes() {
    let raw = captured(&fixture(REAL, COMPLEX));
    for (field, forged) in [
        ("checked", json!(true)),
        ("allocation", json!(0)),
        ("conjugate", json!(true)),
    ] {
        let mut changed = raw.clone();
        operation(&mut changed, "t")[field] = forged;
        assert_rejected(changed, "E_PROTOCOL");
    }
    for (field, forged) in [
        ("order", json!([0, 0, 2])),
        ("split", json!(0)),
        ("split", json!(3)),
    ] {
        let mut changed = raw.clone();
        operation(&mut changed, "t")["grouping"][field] = forged;
        assert_rejected(changed, "E_TENSOR");
    }
    let mut changed = raw.clone();
    operation(&mut changed, "c")["axes"] = json!(["bw", "bu", "bxd"]);
    assert_rejected(changed, "E_TENSOR");
    let mut changed = raw.clone();
    operation(&mut changed, "t")["grouping"]["order"] = json!([0, 1, 2, 3]);
    assert_rejected(changed, "E_PROTOCOL");
    for version in 2..8 {
        let mut changed = raw.clone();
        changed["version"] = json!(version);
        assert_eq!(kernel(changed, "emit")["ok"], false);
    }
}

#[test]
fn unused_tensors_are_audited_and_do_not_require_numerical_runtime() {
    let s = fixture(REAL, COMPLEX);
    s.write(
        "src/main.vast",
        "mod profiles; mod real; mod complex; fn main() -> Int { 42 }",
    );
    let emission = kernel(captured(&s), "emit");
    assert_eq!(emission["ok"], true, "{emission}");
    assert_eq!(emission["numerical_runtime"], false);
    success(
        &command(&s, "build")
            .args(["-o", "ordinary"])
            .output()
            .unwrap(),
    );
    let run = Command::new(s.0.join("ordinary")).output().unwrap();
    success(&run);
    assert_eq!(run.stdout, b"42\n");
    s.write(
        "src/real/mod.vast",
        &REAL.replace("view3(output, bu, bw, bxd", "view3(output, bw, bu, bxd"),
    );
    assert!(!command(&s, "check").output().unwrap().status.success());
}

fn constant_source(complex: bool, [i, k, j, n]: [usize; 4]) -> String {
    let profile = if complex {
        "ComplexSmooth"
    } else {
        "RealSmooth"
    };
    let scalar = if complex { "Complex<F64>" } else { "F64" };
    let width = if complex { 16 } else { 8 };
    let input = if complex {
        "complex_bits(0, 4607182418800017408)"
    } else {
        "f64_bits(4607182418800017408)"
    };
    let output = if complex {
        format!("complex_bits({}, 0)", (-(k as f64)).to_bits())
    } else {
        format!("f64_bits({})", (k as f64).to_bits())
    };
    let output = if k == 0 && complex {
        "complex_bits(0, 0)".into()
    } else {
        output
    };
    let mut source = format!("pub resource fn product() -> Unit {{
      space u = linear(super::profiles::{profile}, {i}); basis bu = basis(u);
      space v = linear(super::profiles::{profile}, {k}); basis bv = basis(v);
      space w = linear(super::profiles::{profile}, {j}); basis bw = basis(w);
      space x = linear(super::profiles::{profile}, {n}); basis bx = basis(x);
      space vd = dual(v); basis bvd = derived(bv, vd); space xd = dual(x); basis bxd = derived(bx, xd);");
    for (name, rows, columns) in [
        ("original", i, k * j),
        ("right", k, n),
        ("scratch", i * j, k),
        ("result", i * j, n),
    ] {
        source.push_str(&format!(
            "allocate {name}: {scalar}[{}];",
            2 + (rows + 1) * columns
        ));
    }
    for (name, owner, rows, columns) in [("t", "original", i, k * j), ("b", "right", k, n)] {
        source.push_str(&format!("borrow init_{name} = write({owner}, layout({}, {rows}, {columns}, {}, false)); fill(init_{name}, {input}); release(init_{name}); borrow read_{name} = read({owner}, layout({}, {rows}, {columns}, {}, false));", 2*width, rows+1, 2*width, rows+1));
    }
    source.push_str(&format!("tensor t = view3(read_t, bu, bvd, bw, axes(0,1,2), 1); tensor b = view2(read_b, bv, bxd);
      borrow packing = write(scratch, layout({}, {}, {k}, {}, false));
      tensor p = view3(packing, bu, bvd, bw, axes(0,2,1), 2); pack3(t, p); release(packing);
      borrow packed_read = read(scratch, layout({}, {}, {k}, {}, false));
      tensor packed = view3(packed_read, bu, bvd, bw, axes(0,2,1), 2);
      borrow output = write(result, layout({}, {}, {n}, {}, false));
      tensor c = view3(output, bu, bw, bxd, axes(0,1,2), 2); contract3(packed, b, c, NativeFast); release(output);
      borrow checked = read(result, layout({}, {}, {n}, {}, false));", 2*width,i*j,i*j+1,2*width,i*j,i*j+1,2*width,i*j,i*j+1,2*width,i*j,i*j+1));
    for column in 0..n {
        for row in 0..i * j {
            source.push_str(&format!("expect(checked, {row}, {column}, {output});"));
        }
    }
    source.push_str("release(checked); release(packed_read); release(read_b); release(read_t); drop(result); drop(scratch); drop(right); drop(original); value { () } }");
    source
}

#[test]
#[ignore = "requires explicit pinned OpenBLAS prefix; numerical CI runs this test"]
fn tensor_native_executes_rank_three_permutation_bilinear_products_and_empty_axes() {
    let prefix =
        std::env::var_os("VASTITAS_TEST_OPENBLAS_PREFIX").expect("explicit numerical test prefix");
    let mut cases = vec![
        (REAL.to_owned(), COMPLEX.to_owned()),
        (through_calls(REAL, false), through_calls(COMPLEX, true)),
    ];
    cases.push((
        constant_source(false, [2, 3, 2, 2]).replace(
            "pack3(t, p);",
            "fill(packing, f64_bits(4607182418800017408));",
        ),
        constant_source(true, [2, 3, 2, 2]).replace(
            "pack3(t, p);",
            "fill(packing, complex_bits(0, 4607182418800017408));",
        ),
    ));
    for condition in [false, true] {
        cases.push((branched(REAL, condition), branched(COMPLEX, condition)));
    }
    for dimensions in [
        [2, 3, 2, 2],
        [0, 3, 2, 2],
        [2, 0, 2, 2],
        [2, 3, 0, 2],
        [2, 3, 2, 0],
        [1, 1, 1, 1],
    ] {
        cases.push((
            constant_source(false, dimensions),
            constant_source(true, dimensions),
        ));
    }
    for (real, complex) in cases {
        let s = fixture(&real, &complex);
        success(&command(&s, "check").output().unwrap());
        let mut build = command(&s, "build");
        build
            .args(["-o", "program", "--openblas-prefix"])
            .arg(&prefix);
        if let Some(cc) = std::env::var_os("VASTITAS_TEST_NATIVE_CC") {
            build.arg("--native-cc").arg(cc);
        }
        success(&build.output().unwrap());
        let run = Command::new(s.0.join("program")).output().unwrap();
        success(&run);
        assert_eq!(run.stdout, b"42\n");
    }
}
