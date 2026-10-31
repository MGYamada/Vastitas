mod common;
use common::{Scratch, assert_rejected, cli, kernel, success};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;
use std::process::Command;

const REAL: &str = include_str!("../examples/packages/cached-tensor-packing/src/real/mod.vast");
const COMPLEX: &str =
    include_str!("../examples/packages/cached-tensor-packing/src/complex/mod.vast");

fn fixture(real: &str, complex: &str) -> Scratch {
    let s = Scratch::empty("cached packing");
    s.write(
        "Vastitas.toml",
        include_str!("../examples/packages/cached-tensor-packing/Vastitas.toml"),
    );
    s.write(
        "src/main.vast",
        include_str!("../examples/packages/cached-tensor-packing/src/main.vast"),
    );
    s.write(
        "src/profiles/mod.vast",
        include_str!("../examples/packages/cached-tensor-packing/src/profiles/mod.vast"),
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
fn rejection(source: &str, code: &str) {
    let output = command(&fixture(source, COMPLEX), "check")
        .output()
        .unwrap();
    assert!(!output.status.success(), "accepted stale cache");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(code),
        "{output:?}"
    );
}
fn moved(source: &str) -> String {
    source
        .replace(
            "release(input_t);",
            "release(input_t); move original -> moved_original;",
        )
        .replace("drop(original);", "drop(moved_original);")
        .replace(
            "release(packing);",
            "release(packing); move scratch -> moved_scratch;",
        )
        .replace("read(scratch,", "read(moved_scratch,")
        .replace("drop(scratch);", "drop(moved_scratch);")
}
fn branched(source: &str, condition: bool) -> String {
    let (header, body) = source
        .split_once("pub resource fn product() -> Unit {")
        .unwrap();
    let (body, _) = body.rsplit_once("    value { () }").unwrap();
    format!(
        "{header}pub resource fn product() -> Unit {{ if {condition} {{ {body} }} else {{ {body} }} value {{ () }} }}"
    )
}
fn empty_source(complex: bool) -> String {
    let profile = if complex {
        "ComplexSmooth"
    } else {
        "RealSmooth"
    };
    let scalar = if complex { "Complex<F64>" } else { "F64" };
    format!(
        "pub resource fn product() -> Unit {{
      space u = linear(super::profiles::{profile}, 0); basis bu = basis(u);
      space d = dual(u); basis bd = derived(bu, d);
      allocate original: {scalar}[0]; allocate scratch: {scalar}[0]; allocate result: {scalar}[0];
      borrow input = read(original, layout(0, 0, 0, 1, false));
      borrow packing = write(scratch, layout(0, 0, 0, 1, false));
      tensor t = view3(input, bu, bd, bu, axes(0,1,2), 1);
      tensor b = view2(input, bu, bd);
      tensor destination = view3(packing, bu, bd, bu, axes(0,2,1), 2);
      cache saved = pack3(t, destination); release(packing);
      borrow packed_read = read(scratch, layout(0, 0, 0, 1, false));
      tensor packed = view3(packed_read, bu, bd, bu, axes(0,2,1), 2);
      borrow output = write(result, layout(0, 0, 0, 1, false));
      tensor c = view3(output, bu, bu, bd, axes(0,1,2), 2);
      contract3_cached(saved, packed, b, c, NativeFast);
      contract3_cached(saved, packed, b, c, NativeFast);
      release(output); release(packed_read); release(input);
      drop(result); drop(scratch); drop(original); value {{ () }} }}"
    )
}
fn refreshed(source: &str, complex: bool) -> String {
    let width = if complex { 16 } else { 8 };
    let value = if complex {
        "complex_bits(0, 4607182418800017408)"
    } else {
        "f64_bits(4607182418800017408)"
    };
    source.replace("release(input_t);", &format!("release(input_t); borrow changed = write(original, layout({width}, 2, 6, 3, false)); store(changed, 0, 0, {value}); release(changed); borrow fresh_input = read(original, layout({width}, 2, 6, 3, false)); tensor fresh_tensor = view3(fresh_input, bu, bvd, bw, axes(0, 1, 2), 1); cache refreshed = pack3(fresh_tensor, destination); release(fresh_input);"))
        .replace("contract3_cached(saved,", "contract3_cached(refreshed,")
}
#[test]
fn cached_pack_has_actual_repeated_consumer_and_erases_without_extra_copy() {
    for (real, complex, branches) in [
        (REAL.to_owned(), COMPLEX.to_owned(), 1),
        (moved(REAL), moved(COMPLEX), 1),
        (branched(REAL, true), branched(COMPLEX, false), 2),
    ] {
        let s = fixture(&real, &complex);
        success(&command(&s, "check").output().unwrap());
        let emission = kernel(captured(&s), "emit");
        assert_eq!(emission["ok"], true, "{emission}");
        let native = emission["lean_source"].as_str().unwrap();
        assert_eq!(native.matches("pack3 arena").count(), 2 * branches);
        assert_eq!(
            native.matches("VastitasGemmNative.gemm arena").count(),
            4 * branches
        );
        assert_eq!(native.matches("allocate arena").count(), 8 * branches);
        for erased in [
            "captureDependency",
            "requireDependency",
            "forgetDependency",
            "copy arena",
        ] {
            assert!(!native.contains(erased), "{native}");
        }
    }
}
#[test]
fn stale_dependencies_fail_but_ordinary_snapshots_remain_valid() {
    success(
        &command(&fixture(&empty_source(false), &empty_source(true)), "check")
            .output()
            .unwrap(),
    );
    success(
        &command(
            &fixture(&refreshed(REAL, false), &refreshed(COMPLEX, true)),
            "check",
        )
        .output()
        .unwrap(),
    );
    let branch_consumer = REAL.replace("    contract3_cached(saved, packed, b, c, NativeFast);\n    contract3_cached(saved, packed, b, c, NativeFast);", "    if true { contract3_cached(saved, packed, b, c, NativeFast); } else { contract3_cached(saved, packed, b, c, NativeFast); }");
    success(
        &command(&fixture(&branch_consumer, COMPLEX), "check")
            .output()
            .unwrap(),
    );
    let mutated = REAL.replace("release(input_t);", "release(input_t); borrow changed = write(original, layout(8, 2, 6, 3, false)); fill(changed, f64_bits(0)); release(changed);");
    rejection(&mutated, "E_TENSOR");
    let ordinary = mutated.replace("contract3_cached(saved,", "contract3(");
    success(
        &command(&fixture(&ordinary, COMPLEX), "check")
            .output()
            .unwrap(),
    );
    for source in [
        REAL.replace("release(packing);", "fill(packing, f64_bits(0)); release(packing);"),
        REAL.replace("release(input_t);", "release(input_t); drop(original);"),
        REAL.replace("release(input_t);", "release(input_t); if true { } else { }"),
        REAL.replace("release(input_t);", "release(input_t); borrow gap = write(original, layout(0, 1, 1, 1, false)); fill(gap, f64_bits(0)); release(gap);"),
        REAL.replace("release(input_t);", "release(input_t); call change(original) -> (changed_original);").replace("drop(original);", "drop(changed_original);") + "\nresource fn change(buffer: Owned<F64, 20>) returns (buffer: Owned<F64, 20>) -> Unit { borrow r = write(buffer, layout(8, 2, 6, 3, false)); fill(r, f64_bits(0)); release(r); value { () } }",
    ] { rejection(&source, "E_TENSOR"); }
    rejection(
        &REAL.replace("contract3_cached(saved,", "contract3_cached(destination,"),
        "E_TENSOR_CACHE",
    );
    rejection(
        &REAL
            .replace(
                "basis bw = basis(w);",
                "basis bw = basis(w); basis other = basis(w);",
            )
            .replace(
                "view3(packed_read, bu, bvd, bw",
                "view3(packed_read, bu, bvd, other",
            )
            .replace("view3(output, bu, bw, bxd", "view3(output, bu, other, bxd"),
        "E_TENSOR",
    );
    let unused = mutated.replace("pub resource fn product()", "resource fn unused_bad()");
    rejection(&(REAL.to_owned() + &unused), "E_TENSOR");
}
#[test]
fn cache_wire_reconstructs_versions_and_disallows_raw_packing_claims() {
    let s = fixture(REAL, COMPLEX);
    let raw = captured(&s);
    for version in 2..=7 {
        let mut invalid = raw.clone();
        invalid["version"] = json!(version);
        assert_rejected(invalid, "E_PROTOCOL");
    }
    fn body(value: &mut Value) -> &mut Vec<Value> {
        value["packages"][0]["modules"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|m| m["path"] == json!(["real"]))
            .unwrap()["resource_functions"][0]["body"]
            .as_array_mut()
            .unwrap()
    }
    for field in ["version", "allocation", "dependency", "checked", "axes"] {
        let mut invalid = raw.clone();
        let statement = body(&mut invalid)
            .iter_mut()
            .find(|s| s["operation"]["op"] == "cached_pack")
            .unwrap();
        statement["operation"][field] = json!(0);
        assert_rejected(invalid, "E_PROTOCOL");
    }
    let mut invalid = raw.clone();
    let statement = body(&mut invalid)
        .iter_mut()
        .find(|s| s["operation"]["op"] == "cached_pack")
        .unwrap();
    statement["kind"] = json!("action");
    statement["operation"] =
        json!({"op":"capture_dependency","name":"saved","source":"input_t","target":"packing"});
    assert_rejected(invalid, "E_PROTOCOL");
}
#[test]
fn unused_cached_numerical_body_does_not_link_openblas() {
    let s = fixture(REAL, COMPLEX);
    s.write(
        "src/main.vast",
        "mod profiles; mod real; mod complex; fn main() -> Int { 42 }",
    );
    success(
        &command(&s, "build")
            .args(["-o", "ordinary"])
            .env_remove("VASTITAS_OPENBLAS_PREFIX")
            .output()
            .unwrap(),
    );
    let run = Command::new(s.0.join("ordinary")).output().unwrap();
    success(&run);
    assert_eq!(run.stdout, b"42\n");
}
#[test]
#[ignore = "requires pinned OpenBLAS; numerical CI runs this test"]
fn cached_native_real_complex_reuse_and_source_destination_lifetimes() {
    let prefix =
        std::env::var_os("VASTITAS_TEST_OPENBLAS_PREFIX").expect("explicit numerical test prefix");
    let overwrite_source = |s: &str| {
        s.replace("    contract3_cached(saved, packed, b, c, NativeFast);\n    contract3_cached(saved, packed, b, c, NativeFast);", "    contract3_cached(saved, packed, b, c, NativeFast);")
        .replace("write(result,", "write(original,").replace("read(result,", "read(original,")
    };
    for (real, complex) in [
        (REAL.to_owned(), COMPLEX.to_owned()),
        (moved(REAL), moved(COMPLEX)),
        (refreshed(REAL, false), refreshed(COMPLEX, true)),
        (overwrite_source(REAL), overwrite_source(COMPLEX)),
        (empty_source(false), empty_source(true)),
        (branched(REAL, true), branched(COMPLEX, false)),
    ] {
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
