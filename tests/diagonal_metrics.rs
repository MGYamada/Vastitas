mod common;
use common::{Scratch, assert_rejected, cli, kernel, success};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;
use std::process::Command;

const REAL: &str = include_str!("../examples/packages/diagonal-metrics/src/real/mod.vast");
const COMPLEX: &str = include_str!("../examples/packages/diagonal-metrics/src/complex/mod.vast");

fn fixture(real: &str, complex: &str) -> Scratch {
    let s = Scratch::empty("diagonal metrics");
    s.write(
        "Vastitas.toml",
        include_str!("../examples/packages/diagonal-metrics/Vastitas.toml"),
    );
    s.write(
        "src/main.vast",
        include_str!("../examples/packages/diagonal-metrics/src/main.vast"),
    );
    s.write(
        "src/profiles/mod.vast",
        include_str!("../examples/packages/diagonal-metrics/src/profiles/mod.vast"),
    );
    s.write("src/real/mod.vast", real);
    s.write("src/complex/mod.vast", complex);
    s
}
fn command(s: &Scratch, mode: &str) -> Command {
    let mut c = cli();
    c.current_dir(&s.0)
        .args([mode, "--manifest-path", "Vastitas.toml"]);
    c
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
    assert!(
        !output.status.success(),
        "accepted invalid diagonal operation"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(code),
        "{output:?}"
    );
}
fn adjoint_only(source: &str) -> String {
    format!(
        "{}    value {{ () }}\n}}\n",
        source.split_once("    space vc =").unwrap().0
    )
}
fn branched(source: &str) -> String {
    let body = source
        .strip_prefix("pub resource fn exercise() -> Unit {\n")
        .unwrap()
        .strip_suffix("    value { () }\n}\n")
        .unwrap();
    format!(
        "pub resource fn exercise() -> Unit {{ if false {{ {body} }} else {{ {body} }} value {{ () }} }}"
    )
}
fn empty(complex: bool, scale: &str) -> String {
    let scalar = if complex { "Complex<F64>" } else { "F64" };
    let profile = if complex {
        "ComplexSmooth"
    } else {
        "RealSmooth"
    };
    let literal = if complex {
        "complex_bits(0,0)"
    } else {
        "f64_bits(0)"
    };
    format!("pub resource fn exercise() -> Unit {{
        space v = linear(super::profiles::{profile},0); basis bv = basis(v);
        involution sigma = canonical(v); metric h = scaled_identity(bv,sigma,{scale});
        space vc = conjugate(v,sigma); basis bvc = derived(bv,vc);
        allocate input: {scalar}[0]; allocate output: {scalar}[0];
        allocate scratch_owner: {scalar}[0]; allocate scalar_result: {scalar}[1];
        borrow r = read(input,layout(0,0,0,1,false));
        borrow w = write(output,layout(0,0,0,1,false));
        map a = view(r,bv,bv); map b = view(w,bv,bv);
        adjoint_into(a,b,h,h,NativeFast); release(r); release(w);
        borrow x = read(input,layout(0,0,1,1,false));
        vector vx = view(x,bv); vector cx = view(x,bvc);
        borrow out = write(scalar_result,layout(0,1,1,1,false));
        hermitian_diagonal(cx,vx,out,h,scratch(scratch_owner,layout(0,0,1,1,false)),overwrite,NativeFast);
        release(out); borrow result = read(scalar_result,layout(0,1,1,1,false));
        expect(result,0,0,{literal}); release(result); release(x);
        drop(input); drop(output); drop(scratch_owner); drop(scalar_result); value {{ () }} }}")
}

fn boundary(complex: bool, scale: &str) -> String {
    let (scalar, profile, input, expected) = if complex {
        (
            "Complex<F64>",
            "ComplexSmooth",
            "complex_bits(4607182418800017408,4607182418800017408)",
            "complex_bits(4607182418800017408,13830554455654793216)",
        )
    } else {
        (
            "F64",
            "RealSmooth",
            "f64_bits(4607182418800017408)",
            "f64_bits(4607182418800017408)",
        )
    };
    format!("pub resource fn exercise() -> Unit {{
      space v = linear(super::profiles::{profile},1); basis b = basis(v);
      involution sigma = canonical(v); metric h = scaled_identity(b,sigma,{scale});
      allocate a: {scalar}[1]; allocate out: {scalar}[1];
      borrow init = write(a,layout(0,1,1,1,false)); fill(init,{input}); release(init);
      borrow r = read(a,layout(0,1,1,1,false)); borrow w = write(out,layout(0,1,1,1,false));
      map input = view(r,b,b); map output = view(w,b,b); adjoint_into(input,output,h,h,NativeFast);
      release(r); release(w); borrow verify = read(out,layout(0,1,1,1,false)); expect(verify,0,0,{expected});
      release(verify); drop(a); drop(out); value {{ () }} }}")
}

#[test]
fn diagonal_metrics_check_actual_real_complex_operations_and_branches() {
    for (real, complex, repeats) in [
        (REAL.to_owned(), COMPLEX.to_owned(), 1),
        (branched(REAL), branched(COMPLEX), 2),
    ] {
        let s = fixture(&real, &complex);
        success(&command(&s, "check").output().unwrap());
        let emitted = kernel(captured(&s), "emit");
        assert_eq!(emitted["ok"], true, "{emitted}");
        let source = emitted["lean_source"].as_str().unwrap();
        assert_eq!(
            source
                .matches("VastitasStorageNative.diagonalAdjoint arena")
                .count(),
            2 * repeats
        );
        assert_eq!(
            source
                .matches("VastitasGemmNative.diagonalPair arena")
                .count(),
            4 * repeats
        );
        assert!(!source.contains("VastitasStorageNative.diagonalScale arena"));
        assert!(!source.contains("copy arena") && !source.contains("pack3 arena"));
    }
    for scale in ["0", "9007199254740993"] {
        success(
            &command(&fixture(&empty(false, scale), &empty(true, scale)), "check")
                .output()
                .unwrap(),
        );
    }
    let helper = REAL.replace(
        "adjoint_into(input,output,hv,hw,NativeFast);",
        "call materialize(v,w,bv,bw,sigma,hv,hw,input,output) -> ();",
    ) + "\nresource fn materialize(v: Space<super::profiles::RealSmooth,2>,w: Space<super::profiles::RealSmooth,3>,bv: Basis<v>,bw: Basis<w>,sigma: Involution<v>,hv: Metric<bv,sigma>,hw: Metric<bw,sigma>,a: ReadMap<bv,bw>,out: WriteMap<bw,bv> initializes) -> Unit { adjoint_into(a,out,hv,hw,NativeFast); value { () } }";
    success(
        &command(&fixture(&helper, COMPLEX), "check")
            .output()
            .unwrap(),
    );
    let pair_helper = REAL.replace(
        "hermitian_diagonal(xc,vy,result0,hv,scratch(scratch_owner,layout(8,2,1,3,false)),overwrite,NativeFast);",
        "call pair_into(v,bv,sigma,hv,vc,bvc,xc,vy,result0,scratch_owner) -> (scratch0);",
    ).replace(
        "hermitian_diagonal(xc,vy,result1,hv,scratch(scratch_owner,layout(8,2,1,3,false)),overwrite,NativeFast);",
        "call pair_into(v,bv,sigma,hv,vc,bvc,xc,vy,result1,scratch0) -> (scratch1);",
    ).replace("drop(scratch_owner)","drop(scratch1)")
    + "\nresource fn pair_into(v: Space<super::profiles::RealSmooth,2>,bv: Basis<v>,sigma: Involution<v>,h: Metric<bv,sigma>,vc: ConjugateSpace<v,sigma>,bvc: DerivedBasis<bv,vc>,x: ReadVector<bvc>,y: ReadVector<bv>,out: Write<F64,1,1> initializes,s: Owned<F64,3>) returns (s: Owned<F64,3>) -> Unit { hermitian_diagonal(x,y,out,h,scratch(s,layout(8,2,1,3,false)),overwrite,NativeFast); value { () } }";
    success(
        &command(&fixture(&pair_helper, COMPLEX), "check")
            .output()
            .unwrap(),
    );
}

#[test]
fn diagonal_metrics_reject_wrong_forms_access_and_unrealizable_entries() {
    for (from, to, code) in [
        ("[2, -4]", "[2, 0]", "E_NUMERICAL_TYPE"),
        ("[2, -4]", "[2]", "E_NUMERICAL_TYPE"),
        ("[2, -4]", "[9007199254740993, -4]", "E_NUMERICAL_METRIC"),
        (
            "input,output,hv,hw",
            "input,output,hw,hv",
            "E_NUMERICAL_METRIC",
        ),
        (
            "input,output,hv,hw",
            "input,output,input,hw",
            "E_NUMERICAL_METRIC",
        ),
        (
            "scratch(scratch_owner,layout(8,2,1,3,false))",
            "scratch(scratch_owner,layout(8,1,1,3,false))",
            "E_RESOURCE_DIAGONAL",
        ),
        (
            "    hermitian_diagonal(xc,vy,result0",
            "    borrow busy = write(scratch_owner,layout(8,2,1,3,false)); hermitian_diagonal(xc,vy,result0",
            "E_RESOURCE_LOAN",
        ),
        (
            "hermitian_diagonal(xc,vy,result0,hv",
            "hermitian_diagonal(xc,vy,result0,hw",
            "E_NUMERICAL_METRIC",
        ),
        (
            "write(scalar_result,layout(8,1,1,2,false))",
            "write(y,layout(8,1,1,2,false))",
            "E_RESOURCE_ALIAS",
        ),
    ] {
        rejection(&REAL.replace(from, to), code);
    }
    let opaque = REAL.replace("allocate scratch_owner: F64[3];", "space hidden = linear(super::profiles::RealSmooth,1); basis hidden_basis = basis(hidden); allocate scratch_buffer: F64[3]; borrow initialize = write(scratch_buffer,layout(8,1,2,1,false)); fill(initialize,f64_bits(0)); release(initialize); map scratch_map = owned(scratch_buffer,layout(8,1,2,1,false),bv,hidden_basis); map scratch_owner = pack(scratch_map);");
    rejection(&opaque, "E_NUMERICAL_PACKAGE");
    let unused = REAL
        .replace("pub resource fn exercise()", "resource fn unused_bad()")
        .replace("[2, -4]", "[9007199254740993, -4]");
    rejection(&(REAL.to_owned() + &unused), "E_NUMERICAL_METRIC");
}

#[test]
fn diagonal_wire_never_accepts_raw_gram_certificates() {
    let raw = captured(&fixture(REAL, COMPLEX));
    for version in 2..=7 {
        let mut invalid = raw.clone();
        invalid["version"] = json!(version);
        assert_rejected(invalid, "E_PROTOCOL");
    }
    for operation in ["adjoint_into", "hermitian_diagonal"] {
        for field in [
            "diagonal",
            "bits",
            "checked",
            "allocation",
            "inverse",
            "conjugate",
        ] {
            let mut invalid = raw.clone();
            let module = invalid["packages"][0]["modules"]
                .as_array_mut()
                .unwrap()
                .iter_mut()
                .find(|m| m["path"] == json!(["real"]))
                .unwrap();
            let statement = module["resource_functions"][0]["body"]
                .as_array_mut()
                .unwrap()
                .iter_mut()
                .find(|s| s["operation"]["op"] == operation)
                .unwrap();
            statement["operation"][field] = json!(true);
            assert_rejected(invalid, "E_PROTOCOL");
        }
    }
}

#[test]
fn materialized_diagonal_adjoint_builds_without_openblas() {
    for (real, complex) in [
        (adjoint_only(REAL), adjoint_only(COMPLEX)),
        (
            boundary(false, "9007199254740992"),
            boundary(true, "-9007199254740992"),
        ),
    ] {
        let s = fixture(&real, &complex);
        let emitted = kernel(captured(&s), "emit");
        assert_eq!(emitted["numerical_runtime"], false, "{emitted}");
        let output = s.0.join("program");
        success(
            &command(&s, "build")
                .arg("-o")
                .arg(&output)
                .output()
                .unwrap(),
        );
        let result = Command::new(output).output().unwrap();
        success(&result);
        assert_eq!(String::from_utf8_lossy(&result.stdout).trim(), "42");
    }
}

#[test]
#[ignore = "requires pinned sequential LP64 OpenBLAS 0.3.34"]
fn diagonal_pairing_builds_executes_real_complex_and_empty_forms() {
    let prefix = std::env::var("VASTITAS_TEST_OPENBLAS_PREFIX").expect("pinned OpenBLAS prefix");
    for (real, complex) in [
        (REAL.to_owned(), COMPLEX.to_owned()),
        (empty(false, "0"), empty(true, "9007199254740993")),
    ] {
        let s = fixture(&real, &complex);
        let output = s.0.join("program");
        let mut build = command(&s, "build");
        build
            .arg("-o")
            .arg(&output)
            .arg("--openblas-prefix")
            .arg(&prefix);
        if let Ok(cc) = std::env::var("VASTITAS_TEST_NATIVE_CC") {
            build.arg("--native-cc").arg(cc);
        }
        success(&build.output().unwrap());
        let result = Command::new(output).output().unwrap();
        success(&result);
        assert_eq!(String::from_utf8_lossy(&result.stdout).trim(), "42");
    }
}
