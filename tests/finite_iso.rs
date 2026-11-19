mod common;

use common::{Scratch, assert_wire_rejected, checked_replace, expect_code, kernel};
use serde_json::json;

const GROUP: &str = include_str!("../llvm/fixtures/finite-iso/main.vast");
const MANIFEST: &str = "app/Vastitas.toml";

fn app() -> Scratch {
    let p = Scratch::empty("finite isomorphism");
    p.copy_stdlib(&common::STDLIB_PACKAGES, &[]);
    p.write_package("app", GROUP, "std={path='../stdlib'}");
    p
}

#[test]
fn both_isomorphism_projections_are_executable_in_their_own_hom_fibers() {
    let p = app();
    assert_eq!(p.check_build_and_run(MANIFEST), common::exits(42));
    let ir = p
        .command("check", MANIFEST)
        .args([
            "--llvm-preview",
            "--target-triple",
            "x86_64-unknown-linux-gnu",
            "--data-layout",
            "e-p:64:64",
        ])
        .output()
        .unwrap();
    common::success(&ir);
    assert!(
        String::from_utf8(ir.stdout)
            .unwrap()
            .contains("define i32 @main ( )")
    );

    #[cfg(feature = "llvm-native")]
    {
        let build = p
            .command("build", MANIFEST)
            .args(["--llvm-preview", "-o", "iso-native"])
            .output()
            .unwrap();
        common::success(&build);
        let status = std::process::Command::new(p.0.join("iso-native"))
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(42));
    }

    for (from, to, code) in [
        ("C, A, B, go, back", "C, A, B, go, go", "E_ISO"),
        ("C, A, B, go, back", "C, B, A, go, back", "E_ISO"),
        ("C, A, B, go, back", "C, A, B, ids, back", "E_ISO"),
        ("I : Iso", "I : Category", "E_ISO"),
        (
            "finite::lookup::<I::forward>()",
            "finite::lookup::<go>()",
            "E_TYPE",
        ),
        (
            "finite::lookup::<I::inverse>()",
            "finite::lookup::<I::forward>()",
            "E_TYPE",
        ),
    ] {
        p.write("app/main.vast", &checked_replace(GROUP, from, to));
        expect_code(&p.check_manifest(MANIFEST), code);
    }

    // The two copies deliberately use exactly the same tables.
    let graph = "indexed instance C : Category = finite_graph(Obj, Arr, s, t, ids, comp);";
    let other = checked_replace(
        GROUP,
        graph,
        &format!("{graph}\n{}", graph.replace(" C :", " D :")),
    );
    p.write(
        "app/main.vast",
        &checked_replace(&other, "finite_iso(C,", "finite_iso(D,"),
    );
    expect_code(&p.check_manifest(MANIFEST), "E_TYPE");
}

#[test]
fn a_one_sided_inverse_is_rejected_even_when_the_instance_is_unused() {
    let p = app();
    let (decls, _) = GROUP.split_once("fn forwardArrow").unwrap();
    // Two objects and a retraction. The extra endomorphism of b is the
    // idempotent go after back, distinct from b's identity.
    let mut retraction = decls.to_owned();
    for (from, to) in [
        ("aa; ab; ba; bb;", "aa; ab; ba; bb; proj;"),
        ("(bb) => b; }", "(bb) => b; (proj) => b; }"),
        ("(ab, ba) => bb;", "(ab, ba) => proj;"),
        (
            "(bb, bb) => bb;",
            "(bb, bb) => bb; (proj, ab) => ab; (ba, proj) => ba; (bb, proj) => proj; (proj, bb) => proj; (proj, proj) => proj;",
        ),
    ] {
        assert!(retraction.contains(from));
        retraction = retraction.replace(from, to);
    }
    let unused_main = "fn main() -> Int { 0 }";
    let (category_only, _) = retraction.split_once("indexed instance I :").unwrap();
    p.write("app/main.vast", &format!("{category_only}{unused_main}"));
    common::success(&p.check_manifest(MANIFEST));
    for (selection, failed_composite) in [
        (
            "C, A, B, go, back",
            "forward after inverse must be the identity of the target",
        ),
        (
            "C, B, A, back, go",
            "inverse after forward must be the identity of the source",
        ),
    ] {
        let altered = retraction.replace("C, A, B, go, back", selection);
        p.write("app/main.vast", &format!("{altered}{unused_main}"));
        assert!(expect_code(&p.check_manifest(MANIFEST), "E_ISO").contains(failed_composite));
    }
}

#[test]
fn the_wire_rechecks_the_named_inverse_and_rejects_supplied_law_evidence() {
    let p = app();
    let wire = p.captured(MANIFEST, 10);
    for (field, code) in [("inverse", "E_ISO"), ("laws", "E_PROTOCOL")] {
        let mut forged = wire.clone();
        let d = forged["packages"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .flat_map(|p| p["modules"].as_array_mut().unwrap())
            .filter_map(|m| m.get_mut("indexed_declarations")?.as_array_mut())
            .flatten()
            .find(|d| d["name"] == "I")
            .unwrap();
        if field == "inverse" {
            assert_eq!(d["iso"][field]["path"], json!(["back"]));
            d["iso"][field]["path"] = json!(["go"]);
        } else {
            d["iso"][field] = json!(true);
        }
        assert_wire_rejected(&kernel(forged, "emit"), code);
    }
    let revision = kernel(&wire, "function-revision")["function_revision"].clone();
    let other = checked_replace(
        GROUP,
        "indexed instance I :",
        "indexed table otherBack() -> Arr { () => ba; }\nindexed instance I :",
    );
    p.write(
        "app/main.vast",
        &checked_replace(&other, "B, go, back);", "B, go, otherBack);"),
    );
    let mut changed = p.captured(MANIFEST, 10);
    assert_eq!(kernel(&changed, "check")["ok"], true);
    changed["expected_function_revision"] = revision;
    assert_wire_rejected(&kernel(changed, "emit"), "E_FUNCTION_REVISION");
}
