//! Physical indexed definitions through protocol 10.
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

const FAMILIES: &str = "pub indexed classification Chart { parents(); domain(Smooth); };
pub indexed family FrameA(object(Chart)) = frame constraints(canonical(0 ));
pub indexed family FrameB(object(Chart)) = frame constraints(canonical(0 ));
pub indexed family Coordinates(frame(FrameA ),) = frame_vector  ;
pub indexed family Dual(frame(FrameA)) = frame_covector constraints( );
pub indexed family Maps(frame(FrameA), frame(FrameB)) = frame_map;
pub indexed family Empty() = token constraints();
";
const PROFILE_FAMILY: &str = "indexed family Profile(domain, marker, natural, object(defs::RootA), object(defs::RootB),)
    = token constraints(over(3,1), same_object(3,4), same_base(4,3), structural(3,4), canonical(3),);
";

#[test]
fn ordered_family_parameters_constraints_and_representation_bind_the_revision() {
    let s = Scratch::empty("indexed family definition");
    let root = format!("{ROOT}{PROFILE_FAMILY}");
    let defs = format!("{DEFINITIONS}{FAMILIES}");
    let original = request(&s, &root, &defs);
    assert_folded(&original);
    let rev = kernel_with_args(&original, &["function-revision"])["function_revision"].clone();
    assert!(rev.is_object());
    for (in_root, from, to, first_difference) in [
        (
            true,
            "domain, marker, natural",
            "natural, marker, domain",
            "natural",
        ),
        (
            true,
            "object(defs::RootA)",
            "object(defs::RootB)",
            "defs::RootB",
        ),
        (true, "same_object(3,4)", "same_object(4,3)", "4"),
        (
            true,
            "same_base(4,3), structural(3,4)",
            "structural(3,4), same_base(4,3)",
            "structural",
        ),
        (
            false,
            "Coordinates(frame(FrameA ",
            "Coordinates(frame(FrameB ",
            "FrameB",
        ),
        (
            false,
            "= frame_vector  ;",
            "= frame_covector;",
            "frame_covector",
        ),
    ] {
        let source = if in_root { &root } else { &defs };
        let edited = checked_replace(source, from, to);
        let changed = if in_root {
            request(&s, &edited, &defs)
        } else {
            request(&s, &root, &edited)
        };
        assert_folded(&changed);
        let mut stale = original.clone();
        stale["root_source"] = changed["root_source"].clone();
        let offset = edited.find(to).unwrap() + to.find(first_difference).unwrap();
        assert_physical_rejection(&stale, &edited[..offset]);
        let mut replay = changed;
        replay["expected_function_revision"] = rev.clone();
        assert_wire_rejected(
            &kernel_with_args(&replay, &["llvm-check", TRIPLE, LAYOUT]),
            "E_FUNCTION_REVISION",
        );
    }
}

#[test]
fn family_replay_checks_empty_lists_nested_punctuation_and_decimal_slots() {
    let s = Scratch::empty("indexed family grammar");
    let padded = format!("{}0", "0".repeat(70));
    let defs = format!(
        "{DEFINITIONS}{FAMILIES}pub indexed family Long(object(RootA)) = token constraints(canonical({padded}));\n"
    );
    let original = request(&s, ROOT, &defs);
    assert_folded(&original);
    for (from, to, token) in [
        ("= token constraints();", "= token              ;", ";"),
        (" constraints( );", " constraints(,);", ","),
        ("frame(FrameA ),)", "frame(FrameA,),)", ","),
        ("canonical(0 ));", "canonical(0,));", ","),
    ] {
        let start = defs.find(from).unwrap();
        let edited = defs.replacen(from, to, 1);
        let mut stale = original.clone();
        file_mut(&mut stale, "defs.vast")["text"] = json!(edited);
        assert_physical_rejection(&stale, &edited[..start + to.find(token).unwrap()]);
    }
    let mut stale = original;
    let edited = checked_replace(&defs, &padded, &format!("{}1", "0".repeat(70)));
    file_mut(&mut stale, "defs.vast")["text"] = json!(edited);
    assert_physical_rejection(&stale, &edited[..defs.find(&padded).unwrap()]);
}

#[test]
fn the_written_index_kinds_check_an_uncalled_function_signature() {
    let package = "examples/packages/geometry/indexed-objects";
    let s = common::example_package("indexed family signature", package, &[]);
    common::success(&s.check_manifest("Vastitas.toml"));
    let shapes = include_str!("../examples/packages/geometry/indexed-objects/shapes.vast");
    let swapped = checked_replace(
        shapes,
        "object(Shape), marker, natural",
        "object(Shape), natural, marker",
    );
    s.write(
        "shapes.vast",
        &checked_replace(&swapped, "over(0, 1)", "over(0, 2)"),
    );
    let result = s.check_manifest("Vastitas.toml");
    let diagnostics = common::expect_code(&result, "E_TYPE");
    assert!(diagnostics.contains("main.vast"), "{diagnostics}");
    let main = include_str!("../examples/packages/geometry/indexed-objects/main.vast");
    s.write(
        "main.vast",
        &checked_replace(main, "Label<X, shapes::QQ, 7>", "Label<X, 7, shapes::QQ>"),
    );
    common::success(&s.check_manifest("Vastitas.toml"));
}

#[test]
fn package_cases_replay_witness_types_and_ordered_bound_fields() {
    let s = Scratch::empty("indexed package case source");
    let declarations = "
indexed family Entry(domain, marker, natural, object(defs::RootA), object(defs::Scalar)) = token constraints();
indexed family Empty() = token constraints();
indexed package Hidden {
    case(defs::RootA, defs::MarkA) {
        Entry(domain(defs::RootA), marker(defs::MarkA), 00018446744073709551616, witness, global(defs::BaseA),);
        Empty();
    }
    case(defs::RootB, defs::MarkA) { }
};
";
    let root = format!("{ROOT}{declarations}");
    let original = request(&s, &root, DEFINITIONS);
    assert_folded(&original);
    let revision = kernel_with_args(&original, &["function-revision"])["function_revision"].clone();
    assert!(revision.is_object());
    for (from, to, token) in [
        ("case(defs::RootA", "case(defs::RootB", "defs::RootB"),
        ("defs::MarkA) { }", "defs::MarkB) { }", "defs::MarkB"),
        ("Entry(domain(", "Empty(domain(", "Empty"),
        ("domain(defs::RootA)", "marker(defs::RootA)", "marker"),
        ("marker(defs::MarkA)", "marker(defs::MarkB)", "defs::MarkB"),
        (
            "00018446744073709551616",
            "00018446744073709551617",
            "00018446744073709551617",
        ),
        ("witness, global", "unknown, global", "unknown"),
        ("global(defs::BaseA)", "global(defs::BaseB)", "defs::BaseB"),
        ("Empty();", "Empty(,)", ","),
    ] {
        let edited = checked_replace(&root, from, to);
        let mut stale = original.clone();
        stale["root_source"]["text"] = json!(edited);
        let offset = root.find(from).unwrap() + to.find(token).unwrap();
        assert_physical_rejection(&stale, &edited[..offset]);
    }
    let mut changed = request(
        &s,
        &checked_replace(&root, "global(defs::BaseA)", "global(defs::BaseB)"),
        DEFINITIONS,
    );
    assert_folded(&changed);
    changed["expected_function_revision"] = revision;
    assert_wire_rejected(
        &kernel_with_args(&changed, &["llvm-check", TRIPLE, LAYOUT]),
        "E_FUNCTION_REVISION",
    );
    let mut moved = original.clone();
    let case = &mut decl_mut(&mut moved, "Hidden")["cases"][0];
    case["fields"][0]["indices"][0]["declaration"]["span"] =
        case["witness_type"]["domain"]["span"].clone();
    let field = root.find("Entry(domain(defs::RootA)").unwrap();
    assert_physical_rejection(&moved, &root[..field + "Entry(domain(".len()]);
    let mut reversed = original.clone();
    decl_mut(&mut reversed, "Hidden")["cases"]
        .as_array_mut()
        .unwrap()
        .swap(0, 1);
    let case = root.find("case(defs::RootA").unwrap();
    assert_physical_rejection(&reversed, &root[..case + "case(".len()]);
    let mut swapped = original;
    decl_mut(&mut swapped, "Hidden")["cases"][0]["fields"]
        .as_array_mut()
        .unwrap()
        .swap(0, 1);
    assert_physical_rejection(&swapped, &root[..field]);
}

#[test]
fn an_uncalled_pack_body_requires_the_written_field_index() {
    let s = Scratch::empty("indexed package payload");
    let root = "mod defs;
indexed family Tag(natural) = token constraints();
indexed package Tagged { case(defs::GridA, defs::MarkA) { Tag(7); } };
fn wrap(X: Object<defs::GridA, defs::MarkA>, t: Tag<7>) -> Tagged<defs::GridA, defs::MarkA> {
    pack Tagged<defs::GridA, defs::MarkA> { witness: X, fields: [t] }
}
fn main() -> Int { 10 }";
    s.write_package("app", root, "");
    s.write("app/defs.vast", DEFINITIONS);
    common::success(&s.check_manifest("app/Vastitas.toml"));
    let changed = checked_replace(root, "Tag(7);", "Tag(8);");
    s.write("app/main.vast", &changed);
    let output = s.check_manifest("app/Vastitas.toml");
    let diagnostic = common::expect_code(&output, "E_ENDPOINT");
    assert!(
        diagnostic.contains("main.vast:5:5") && diagnostic.contains("Tag<7>"),
        "{diagnostic}"
    );
    s.write(
        "app/main.vast",
        &checked_replace(&changed, "t: Tag<7>", "t: Tag<8>"),
    );
    common::success(&s.check_manifest("app/Vastitas.toml"));
}

#[test]
fn every_registered_primitive_has_a_physical_program_accepted_by_the_public_checker() {
    use std::collections::BTreeSet;

    let mut observed = BTreeSet::new();
    for package in [
        "examples/packages/geometry/frames",
        "stdlib/src/geometry",
        "tests/emit_corpus/spectral-primitives",
        "examples/packages/stdlib/stdlib-affine",
        "examples/packages/geometry/smooth-cotangent",
    ] {
        let manifest = common::root().join(package).join("Vastitas.toml");
        let wire = common::captured_wire(
            common::manifest_command("check", manifest),
            CURRENT_PROTOCOL,
        );
        let reply = kernel_with_args(&wire, &["check"]);
        assert_eq!(reply["ok"], true, "{package}: {reply}");
        for package in wire["packages"].as_array().unwrap() {
            for module in package["modules"].as_array().unwrap() {
                let Some(declarations) = module.get("indexed_declarations") else {
                    continue;
                };
                for d in declarations.as_array().unwrap() {
                    if d["kind"] == "primitive" {
                        observed.insert(d["binding"]["op"].as_str().unwrap().to_owned());
                    }
                }
            }
        }
    }
    let registry = vastitas::indexed::primitive_families()
        .iter()
        .map(|f| f.op.to_owned())
        .collect();
    assert_eq!(observed, registry);
}

#[test]
fn a_primitive_binds_its_qualified_argument_and_revision_even_when_unused() {
    let s = Scratch::empty("indexed primitive source");
    let root = format!("{ROOT}indexed primitive base = descriptor(defs::GridA);\n");
    let changed = checked_replace(&root, "descriptor(defs::GridA)", "descriptor(defs::GridB)");
    let original = request(&s, &root, DEFINITIONS);
    let mut current = request(&s, &changed, DEFINITIONS);
    for wire in [&original, &current] {
        assert_folded(wire);
    }
    current["expected_function_revision"] =
        kernel_with_args(&original, &["function-revision"])["function_revision"].clone();
    assert_wire_rejected(
        &kernel_with_args(&current, &["llvm-check", TRIPLE, LAYOUT]),
        "E_FUNCTION_REVISION",
    );
    let mut stale = original.clone();
    stale["root_source"] = current["root_source"].clone();
    assert_physical_rejection(&stale, &changed[..changed.rfind("defs::GridB").unwrap()]);
    let mut forged = original;
    let path = &mut decl_mut(&mut forged, "base")["binding"]["implementation"]["span"];
    path["end"] = json!(path["end"].as_u64().unwrap() - 1);
    assert_physical_rejection(&forged, &root[..root.rfind("defs::GridA").unwrap()]);
}

#[test]
fn a_written_frame_component_selects_the_executed_coordinate() {
    let s = common::example_package(
        "primitive frame coordinate",
        "examples/packages/geometry/frames",
        &[],
    );
    let declarations = include_str!("../examples/packages/geometry/frames/src/main.vast")
        .split_once("fn main() -> Int {")
        .unwrap()
        .0;
    let source = format!(
        "{declarations}fn main() -> Int {{ pair_first(first(in_b(plane_at(1, 2), 7, 19))) }}\n"
    );
    s.write("src/main.vast", &source);
    assert_eq!(s.check_build_and_run("Vastitas.toml"), common::exits(7));
    let wire = s.captured("Vastitas.toml", CURRENT_PROTOCOL);
    let from = "primitive first = frame_component(Coords, 0)";
    let changed = checked_replace(
        &source,
        from,
        "primitive first = frame_component(Coords, 1)",
    );
    let index = source.find(from).unwrap() + from.find('0').unwrap();
    let mut stale = wire.clone();
    stale["root_source"]["text"] = json!(changed);
    assert_physical_rejection(&stale, &source[..index]);
    s.write("src/main.vast", &changed);
    assert_eq!(s.check_build_and_run("Vastitas.toml"), common::exits(19));

    // Padded values still count every decimal digit against the frontend bound.
    let padded = checked_replace(
        &source,
        from,
        &from.replace('0', &format!("{}0", " ".repeat(64))),
    );
    s.write("src/main.vast", &padded);
    let mut wire = s.captured("Vastitas.toml", CURRENT_PROTOCOL);
    assert_eq!(kernel_with_args(&wire, &["check"])["ok"], true);
    wire["root_source"]["text"] =
        json!(padded.replacen(&format!("{}0", " ".repeat(64)), &"0".repeat(65), 1));
    assert_physical_rejection(&wire, &padded[..index]);
}

#[test]
fn primitive_selectors_coordinates_polynomials_and_pullback_modes_replay() {
    for (package, file, from, to, token) in [
        (
            "frames",
            "main.vast",
            "flat(Tangent, Cotangent, using = Skew)",
            "flat(Tangent, Cotangent, other = Skew)",
            "other",
        ),
        (
            "frames",
            "main.vast",
            "source = b, target = l",
            "source = c, target = l",
            "c,",
        ),
        (
            "frames",
            "profile.vast",
            "Cotangent, saved)",
            "Cotangent, saves)",
            "saves",
        ),
        (
            "affine-geometry",
            "main.vast",
            "DS, Fiber, X::x, e",
            "DS, Fiber, X::y, e",
            "X::y",
        ),
        (
            "affine-geometry",
            "main.vast",
            "DS, Fiber, X::x, e",
            "DS, Fiber, X::x, x",
            "x)",
        ),
        (
            "spectral-observations",
            "main.vast",
            "spectrum = STwoI, element = t - 2, f1, f2",
            "spectrum = STwoI, element = t + 2, f1, f2",
            "t + 2",
        ),
        (
            "spectral-observations",
            "main.vast",
            "p12 = branch_projector(Smooth, Line, branch = B, e1, e2)",
            "p12 = branch_projector(Smooth, Line, branch = B, e1, e1)",
            "e1)",
        ),
        (
            "indexed-objects",
            "shapes.vast",
            "dim((Measured, QQ))",
            "dim((Measured, QP))",
            "QP",
        ),
    ] {
        let manifest = common::root()
            .join("examples/packages/geometry")
            .join(package)
            .join("Vastitas.toml");
        let mut wire = common::captured_wire(
            common::manifest_command("check", manifest),
            CURRENT_PROTOCOL,
        );
        let is_root = file == "main.vast";
        let field = if is_root {
            &mut wire["root_source"]["text"]
        } else {
            &mut file_mut(&mut wire, file)["text"]
        };
        let source = field.as_str().unwrap();
        let offset = source.find(from).unwrap();
        let edited = source.replacen(from, to, 1);
        let pos = offset + edited[offset..].find(token).unwrap();
        *field = json!(edited);
        assert_physical_rejection(&wire, &edited[..pos]);
    }
}

const TENSOR_FIXTURE: &str = "llvm/fixtures/tensor-column";
const PROFILE: &str = include_str!("../llvm/fixtures/tensor-column/src/profiles/mod.vast");
const PRODUCT: &str = include_str!("../llvm/fixtures/tensor-column/src/product/mod.vast");

fn real_profile() -> String {
    checked_replace(
        PROFILE,
        "ComplexSmooth(ComplexCoefficients, linear_descriptor(SmoothBase, complex))",
        "ComplexSmooth(RealCoefficients, linear_descriptor(SmoothBase, real))",
    )
}

fn real_product() -> String {
    PRODUCT
        .replace("F32<CC>", "F32<RR>")
        .replace("complex32(1,2)", "f32_bits(1065353216)")
        .replace("complex32(3,-4)", "f32_bits(1077936128)")
        .replace("complex32(33,6)", "f32_bits(1091567616)")
}

#[test]
fn used_linear_implementation_and_tensor_buffers_agree_on_the_gemm_abi() {
    let s = common::example_package(
        "physical implementation in a tensor contraction",
        TENSOR_FIXTURE,
        &[],
    );
    let preview = || {
        s.command("check", "Vastitas.toml")
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
    s.write("src/profiles/mod.vast", &real_profile());
    let mismatched = preview();
    common::expect_code(&mismatched, "E_TENSOR");
    assert!(mismatched.stdout.is_empty());

    s.write("src/product/mod.vast", &real_product());
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

#[test]
#[ignore = "requires pinned sequential LP64 OpenBLAS"]
fn native_cells_follow_the_written_linear_implementation() {
    let s = common::example_package("native physical tensor representation", TENSOR_FIXTURE, &[]);
    let real_profile = real_profile();
    let real_product = real_product();
    let options = common::numerical_build_options(None);
    let check = |backend: &[&str]| {
        for (profile, product, expected, wrong, observed) in [
            (
                PROFILE,
                PRODUCT,
                "complex32(33,6)",
                "complex32(33,0)",
                "complex32_bits(1107558400, 1086324736)",
            ),
            (
                real_profile.as_str(),
                real_product.as_str(),
                "f32_bits(1091567616)",
                "f32_bits(0)",
                "f32_bits(1091567616)",
            ),
        ] {
            s.write("src/profiles/mod.vast", profile);
            let bad = checked_replace(
                product,
                &format!("expect(r,1,0,{expected})"),
                &format!("expect(r,1,0,{wrong})"),
            );
            for (source, status) in [(product, 0), (bad.as_str(), 1)] {
                s.write("src/product/mod.vast", source);
                common::success(
                    &s.command("build", "Vastitas.toml")
                        .args(backend)
                        .args(&options)
                        .args(["-o", "product"])
                        .output()
                        .unwrap(),
                );
                let output = std::process::Command::new(s.0.join("product"))
                    .output()
                    .unwrap();
                assert_eq!(output.status.code(), Some(status), "{output:?}");
                if status == 1 {
                    common::expect_code(&output, "E_NATIVE_EXPECT");
                    let message = String::from_utf8_lossy(&output.stderr);
                    assert!(
                        message.contains(&format!("cell (1, 0): holds {observed}")),
                        "{message}"
                    );
                }
            }
        }
    };
    check(&[]);
    #[cfg(feature = "llvm-native")]
    check(&["--llvm-preview"]);
}
