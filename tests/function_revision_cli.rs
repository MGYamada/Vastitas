mod common;

use common::{Scratch, expect_code, success};
use serde_json::Value;
use std::{fs, os::unix::fs::symlink, process::Command};

#[test]
fn build_rechecks_the_captured_assembly_and_preserves_output_on_mismatch() {
    let s = Scratch::empty("revision replay");
    s.write_package(
        "base",
        "pub fn f(x: Int) -> Int { x } pub grant edit : f to ext { domain (Int); }",
        "",
    );
    s.write_package("ext", "pub contribution inc : base::f { fn base::f(x: Int) requires (HasOrder) -> Int { x + 1 } }", "base={path='../base'}");
    let source = "use base::f as chosen; assemble chosen { borrow base::edit { apply ext::inc; } } fn main() -> Int { chosen(41) }";
    s.write_package("app", source, "base={path='../base'}\next={path='../ext'}");
    let manifest = "app/Vastitas.toml";
    let printed = s
        .command("check", manifest)
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&printed);
    let revision: Value = serde_json::from_slice(&printed.stdout).unwrap();
    assert_eq!(revision["schema"], 1);
    fs::write(s.0.join("r.json"), printed.stdout).unwrap();
    let replay = || {
        s.command("build", manifest)
            .args(["--expect-function-revision", "r.json", "-o", "prog"])
            .output()
            .unwrap()
    };
    success(&replay());
    assert_eq!(
        Command::new(s.0.join("prog")).status().unwrap().code(),
        Some(42)
    );
    let old_binary = fs::read(s.0.join("prog")).unwrap();
    s.write("app/main.vast", &source.replace("apply ext::inc;", ""));
    expect_code(&replay(), "E_FUNCTION_REVISION");
    assert_eq!(old_binary, fs::read(s.0.join("prog")).unwrap());
}

#[test]
fn malformed_or_aliased_revision_files_cannot_replace_inputs() {
    let s = Scratch::empty("bad revision");
    s.write("main.vast", "fn main() -> Int { 0 }");
    let receipt = s.write("r.json", "{}");
    symlink(&receipt, s.0.join("out")).unwrap();
    expect_code(
        &s.cli()
            .args([
                "build",
                "main.vast",
                "-o",
                "out",
                "--expect-function-revision",
                "r.json",
            ])
            .output()
            .unwrap(),
        "E_OUTPUT",
    );
    assert_eq!(fs::read_to_string(receipt).unwrap(), "{}");
    for (text, code) in [
        ("{}", "E_FUNCTION_REVISION"),
        ("{},\"packages\":[]", "E_FUNCTION_REVISION"),
        ("{\"schema\":1,\"schema\":1}", "E_PROTOCOL"),
    ] {
        s.write("r.json", text);
        expect_code(
            &s.cli()
                .args(["check", "main.vast", "--expect-function-revision", "r.json"])
                .output()
                .unwrap(),
            code,
        );
    }
}

#[test]
fn nested_accepted_terms_roundtrip_without_decoding_the_receipt_in_rust() {
    let s = Scratch::empty("deep revision");
    let args = "f(".repeat(61) + "1" + &")".repeat(61);
    s.write(
        "main.vast",
        &format!("fn f(x: Int) -> Int {{ x }} fn main() -> Int {{ {args} }}"),
    );
    let result = s
        .cli()
        .args(["check", "main.vast", "--print-function-revision"])
        .output()
        .unwrap();
    success(&result);
    fs::write(s.0.join("r.json"), result.stdout).unwrap();
    success(
        &s.cli()
            .args(["check", "main.vast", "--expect-function-revision", "r.json"])
            .output()
            .unwrap(),
    );
}

#[test]
fn unchanged_llvm_bytes_do_not_authorize_an_edited_library_or_manifest() {
    let s = Scratch::empty("physical revision");
    let entry = "fn main() -> Int { helper(21) }";
    let helper = "fn helper(x: Int) -> Int { x + x } // λ1";
    s.write("main.vast", entry);
    s.write("lib.vast", helper);
    let flat = ["main.vast", "--lib", "lib.vast"];
    s.write_package(
        "pkg",
        "pub fn main() -> Int { dep::helper(21) }",
        "dep={path='../dep'}",
    );
    s.write_package("dep", &format!("pub {helper}"), "");
    let manifest = ["--manifest-path", "pkg/Vastitas.toml"];
    let run = |inputs: &[&str], options: &[&str]| {
        s.cli()
            .arg("check")
            .args(inputs)
            .args(options)
            .output()
            .unwrap()
    };
    let preview = [
        "--llvm-preview",
        "--target-triple",
        "aarch64-apple-darwin",
        "--data-layout",
        "e-m:o-i64:64-n32:64-S128",
    ];
    for (inputs, file, original, changed) in [
        (
            flat.as_slice(),
            "lib.vast",
            helper.to_owned(),
            helper.replace("λ1", "λ2"),
        ),
        (
            manifest.as_slice(),
            "dep/main.vast",
            format!("pub {helper}"),
            format!("pub {helper}").replace("λ1", "λ2"),
        ),
        (
            manifest.as_slice(),
            "dep/Vastitas.toml",
            std::fs::read_to_string(s.0.join("dep/Vastitas.toml")).unwrap() + "\n# revision A",
            std::fs::read_to_string(s.0.join("dep/Vastitas.toml")).unwrap() + "\n# revision B",
        ),
    ] {
        s.write(file, &original);
        let receipt = run(inputs, &["--print-function-revision"]);
        success(&receipt);
        s.write(
            "receipt.json",
            std::str::from_utf8(&receipt.stdout).unwrap(),
        );
        let before = run(inputs, &preview);
        success(&before);
        let mut replay = preview.to_vec();
        replay.extend(["--expect-function-revision", "receipt.json"]);
        success(&run(inputs, &replay));
        s.write(file, &changed);
        let after = run(inputs, &preview);
        success(&after);
        assert_eq!(before.stdout, after.stdout, "{file}");
        let rejected = run(inputs, &replay);
        expect_code(&rejected, "E_FUNCTION_REVISION");
        assert!(rejected.stdout.is_empty());
    }
}

#[test]
#[cfg(target_os = "linux")]
fn different_non_utf8_library_paths_have_distinct_revisions() {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;
    let s = Scratch::empty("native path bytes");
    s.write("main.vast", "fn main() -> Int { helper() }");
    let first = OsStr::from_bytes(b"lib-\xff.vast");
    let second = OsStr::from_bytes(b"lib-\xfe.vast");
    for path in [first, second] {
        fs::write(s.0.join(path), "fn helper() -> Int { 42 }").unwrap();
    }
    let run = |path: &OsStr, opts: &[&str]| {
        s.cli()
            .args(["check", "main.vast", "--lib"])
            .arg(path)
            .args(opts)
            .output()
            .unwrap()
    };
    let receipt = run(first, &["--print-function-revision"]);
    success(&receipt);
    let value: Value = serde_json::from_slice(&receipt.stdout).unwrap();
    assert_eq!(
        value["input"]["root_source"]["files"][1]["path"],
        serde_json::json!(first.as_bytes())
    );
    fs::write(s.0.join("r.json"), receipt.stdout).unwrap();
    success(&run(first, &["--expect-function-revision", "r.json"]));
    expect_code(
        &run(second, &["--expect-function-revision", "r.json"]),
        "E_FUNCTION_REVISION",
    );
}
