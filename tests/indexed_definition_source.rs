//! Physical implementation and classification declarations through protocol 10.
mod common;

use common::{CURRENT_PROTOCOL, Scratch, assert_wire_rejected, checked_replace, kernel_with_args};
use serde_json::{Value, json};

const TRIPLE: &str = "arm64-apple-darwin27.2.0";
const LAYOUT: &str = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32";
const ROOT: &str = "mod defs;
indexed implementation Local(defs::MarkA, linear_descriptor(defs::BaseA, real)) capabilities();
indexed classification Choice {
    parents(defs::RootA, defs::RootB,);
    domain(defs::GridA, defs::GridB,);
};
fn main() -> Int { 10 }
";
const DEFINITIONS: &str = "pub indexed marker MarkA;
pub indexed marker MarkB;
pub indexed marker Complex;
pub indexed implementation GridA(MarkA, affine_descriptor) capabilities(origin, dim,);
pub indexed implementation GridB(MarkA, affine_descriptor) capabilities();
pub indexed implementation Scalar(MarkA, scalar_base(scheme, real)) capabilities();
pub indexed global BaseA(Scalar);
pub indexed global BaseB(Scalar);
pub indexed implementation CScalar(Complex, scalar_base(scheme, complex)) capabilities();
pub indexed implementation Smooth(MarkA, smooth_affine) capabilities();
pub indexed implementation Presented(MarkA, presented_affine(rational)) capabilities();
pub indexed classification RootA { parents(); domain(GridA, GridB); };
pub indexed classification RootB { parents(); domain(GridB, GridA); };
";

fn request(s: &Scratch, root: &str, definitions: &str) -> Value {
    s.write_package("app", root, "");
    s.write("app/defs.vast", definitions);
    s.captured("app/Vastitas.toml", CURRENT_PROTOCOL)
}

fn file_mut<'a>(wire: &'a mut Value, name: &str) -> &'a mut Value {
    wire["root_source"]["files"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|f| f["path"].as_str().unwrap().ends_with(name))
        .unwrap()
}

fn decl_mut<'a>(wire: &'a mut Value, name: &str) -> &'a mut Value {
    wire["packages"][0]["modules"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .flat_map(|m| m["indexed_declarations"].as_array_mut().unwrap())
        .find(|d| d["name"] == name)
        .unwrap()
}

fn assert_physical_rejection(wire: &Value, before_token: &str) {
    let line = before_token.bytes().filter(|&c| c == b'\n').count() + 1;
    let column = before_token.rsplit('\n').next().unwrap().chars().count() + 1;
    for args in [
        &["check"][..],
        &["emit"],
        &["function-revision"],
        &["llvm-check", TRIPLE, LAYOUT],
        &["llvm-build", TRIPLE, LAYOUT],
    ] {
        let result = kernel_with_args(wire, args);
        assert_wire_rejected(&result, "E_MODULE_SOURCE");
        let span = &result["diagnostics"][0]["span"];
        assert_eq!(
            (span["line"].as_u64(), span["column"].as_u64()),
            (Some(line as u64), Some(column as u64)),
            "{result}"
        );
        assert!(result.get("llvm").is_none() && result.get("function_revision").is_none());
    }
}

fn assert_folded(wire: &Value) {
    let checked = kernel_with_args(wire, &["llvm-check", TRIPLE, LAYOUT]);
    assert_eq!(checked["ok"], true, "{checked}");
    assert_eq!(
        checked["llvm"]["ir"],
        include_str!("../llvm/src/folded-arithmetic.ll")
    );
}

#[test]
fn implementation_and_classification_edits_bind_the_source_revision_and_complete_bytes() {
    let s = Scratch::empty("indexed definition source");
    let original = request(&s, ROOT, DEFINITIONS);
    let revision = kernel_with_args(&original, &["function-revision"])["function_revision"].clone();
    assert!(revision.is_object(), "{revision}");
    assert_folded(&original);
    for (file, from, to, token) in [
        ("defs.vast", "GridA(MarkA", "GridA(MarkB", "MarkB"),
        ("defs.vast", "origin, dim,", "dim, origin,", "dim"),
        (
            "defs.vast",
            "scalar_base(scheme, real)",
            "scalar_base(smooth, real)",
            "smooth",
        ),
        (
            "main.vast",
            "linear_descriptor(defs::BaseA",
            "linear_descriptor(defs::BaseB",
            "defs::BaseB",
        ),
        (
            "main.vast",
            "parents(defs::RootA, defs::RootB,)",
            "parents(defs::RootB, defs::RootA,)",
            "defs::RootB",
        ),
        (
            "main.vast",
            "domain(defs::GridA, defs::GridB,)",
            "domain(defs::GridB, defs::GridA,)",
            "defs::GridB",
        ),
    ] {
        let is_root = file == "main.vast";
        let source = if is_root { ROOT } else { DEFINITIONS };
        let edited = checked_replace(source, from, to);
        assert_eq!(source.len(), edited.len());
        let changed = if is_root {
            request(&s, &edited, DEFINITIONS)
        } else {
            request(&s, ROOT, &edited)
        };
        assert_folded(&changed);
        let mut replay = changed.clone();
        replay["expected_function_revision"] = revision.clone();
        let rejected = kernel_with_args(&replay, &["llvm-check", TRIPLE, LAYOUT]);
        assert_wire_rejected(&rejected, "E_FUNCTION_REVISION");
        assert!(rejected.get("llvm").is_none());
        let mut stale = original.clone();
        stale["root_source"] = changed["root_source"].clone();
        let offset = source.find(from).unwrap() + to.find(token).unwrap();
        let prefix = &edited[..offset];
        assert_physical_rejection(&stale, prefix);
    }
}

#[test]
fn a_dependency_alias_resolves_definition_fields_in_their_declaring_package() {
    let s = Scratch::empty("indexed definition dependency owner");
    s.write_package("owner", DEFINITIONS, "");
    let app = ROOT.strip_prefix("mod defs;\n").unwrap();
    s.write_package("app", app, "defs={path='../owner'}");
    let original = s.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    let reordered = checked_replace(
        DEFINITIONS,
        "domain(GridA, GridB);",
        "domain(GridB, GridA);",
    );
    s.write_package("owner", &reordered, "");
    let edited = s.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    assert_folded(&original);
    assert_folded(&edited);
    let mut stale = original;
    stale["root_source"] = edited["root_source"].clone();
    let start = reordered.find("domain(GridB, GridA);").unwrap() + "domain(".len();
    assert_physical_rejection(&stale, &reordered[..start]);
}

#[test]
fn scalar_and_affine_representation_tokens_and_reference_spans_are_checked() {
    let s = Scratch::empty("indexed definition operands");
    let original = request(&s, ROOT, DEFINITIONS);
    for (from, to, bad) in [
        (
            "scalar_base(scheme, complex)",
            "scalar_base(scheme, complez)",
            "complez",
        ),
        ("smooth_affine", "smooth_affinx", "smooth_affinx"),
        (
            "presented_affine(rational)",
            "presented_affine(national)",
            "national",
        ),
        (
            "affine_descriptor) capabilities(origin",
            "afine_descriptor ) capabilities(origin",
            "afine_descriptor",
        ),
    ] {
        let edited = checked_replace(DEFINITIONS, from, to);
        assert_eq!(edited.len(), DEFINITIONS.len());
        let mut stale = original.clone();
        file_mut(&mut stale, "defs.vast")["text"] = json!(edited);
        let prefix = &edited[..edited.find(bad).unwrap()];
        assert_physical_rejection(&stale, prefix);
    }
    for (name, pointer, physical) in [
        ("Local", "/marker/span", "defs::MarkA"),
        (
            "Local",
            "/representation/linear_descriptor/base/span",
            "defs::BaseA",
        ),
        ("Choice", "/parents/1/span", "defs::RootB"),
        ("Choice", "/domain/1/span", "defs::GridB"),
    ] {
        let mut stale = original.clone();
        let span = decl_mut(&mut stale, name).pointer_mut(pointer).unwrap();
        let col = span["column"].as_u64().unwrap();
        span["column"] = json!(col + 1);
        let prefix = &ROOT[..ROOT.find(physical).unwrap()];
        assert_physical_rejection(&stale, prefix);
    }
}

#[test]
fn used_linear_implementation_and_tensor_buffers_agree_on_the_gemm_abi() {
    let s = Scratch::empty("physical implementation in a tensor contraction");
    let manifest = "Vastitas.toml";
    s.write(
        manifest,
        include_str!("../llvm/fixtures/tensor-column/Vastitas.toml"),
    );
    s.write(
        "src/main.vast",
        include_str!("../llvm/fixtures/tensor-column/src/main.vast"),
    );
    let profile = include_str!("../llvm/fixtures/tensor-column/src/profiles/mod.vast");
    let product = include_str!("../llvm/fixtures/tensor-column/src/product/mod.vast");
    s.write("src/profiles/mod.vast", profile);
    s.write("src/product/mod.vast", product);
    let preview = || {
        s.command("check", manifest)
            .args([
                "--llvm-preview",
                "--target-triple",
                TRIPLE,
                "--data-layout",
                LAYOUT,
            ])
            .output()
            .unwrap()
    };

    let original = preview();
    common::success(&original);
    assert_eq!(
        original.stdout,
        include_bytes!("../llvm/src/tensor-column.ll")
    );
    let real = checked_replace(
        profile,
        "ComplexSmooth(ComplexCoefficients, linear_descriptor(SmoothBase, complex))",
        "ComplexSmooth(RealCoefficients, linear_descriptor(SmoothBase, real))",
    );
    s.write("src/profiles/mod.vast", &real);
    let mismatched = preview();
    common::expect_code(&mismatched, "E_TENSOR");
    assert!(mismatched.stdout.is_empty());

    let real_product = product
        .replace("F32<CC>", "F32<RR>")
        .replace("complex32(1,2)", "f32_bits(1065353216)")
        .replace("complex32(3,-4)", "f32_bits(1077936128)")
        .replace("complex32(33,6)", "f32_bits(1091567616)");
    s.write("src/product/mod.vast", &real_product);
    let real = preview();
    common::success(&real);
    for (output, tag) in [(original, "3"), (real, "2")] {
        let text = std::str::from_utf8(&output.stdout).unwrap();
        let mut calls = text
            .lines()
            .filter_map(|line| line.split_once("call i32 @vq_storage_gemm(ptr %arena, i64 "));
        assert_eq!(calls.next().unwrap().1.split(',').next(), Some(tag));
        assert!(calls.next().is_none());
    }
}
