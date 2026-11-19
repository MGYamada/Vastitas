mod common;

use common::{Scratch, assert_wire_rejected, checked_replace, exits, expect_code, kernel};
use serde_json::json;

const S3: &str = include_str!("../llvm/fixtures/opposite-s3/main.vast");
const CHAIN: &str = include_str!("fixtures/finite-chain.vast");
const MANIFEST: &str = "app/Vastitas.toml";

#[test]
fn inversion_uses_the_covariant_functor_checker_on_the_opposite_of_s3() {
    let p = Scratch::empty("noncommuting opposite");
    p.copy_stdlib(&common::STDLIB_PACKAGES, &[]);
    p.write_package("app", S3, "std={path='../stdlib'}");
    assert_eq!(p.check_build_and_run(MANIFEST), exits(42));
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
        let result = p
            .command("build", MANIFEST)
            .args(["--llvm-preview", "-o", "opposite"])
            .output()
            .unwrap();
        common::success(&result);
        assert_eq!(
            std::process::Command::new(p.0.join("opposite"))
                .status()
                .unwrap()
                .code(),
            Some(42)
        );
    }
    // A graph slot accepts a table ID. Dropping the orientation at this
    // boundary would turn an opposite composition into its original operation.
    let copy = "indexed instance Copy : Category = finite_graph(R::objects, R::arrows, R::source, R::target, R::identities, R::composition);";
    let raw = S3.replace("fn main()", &format!("{copy}\nfn main()"));
    p.write("app/main.vast", &raw);
    assert!(expect_code(&p.check_manifest(MANIFEST), "E_CATEGORY").contains("named view"));
    p.write(
        "app/main.vast",
        &raw.replace(copy, &copy.replace("R::", "RR::")),
    );
    common::success(&p.check_manifest(MANIFEST));

    // Every S3 arrow has the same endpoints. Each mutation must fail the composition law.
    for changed in [
        checked_replace(S3, "finite_functor(R, S3", "finite_functor(S3, S3"),
        checked_replace(
            S3,
            "(p120) => p201; (p201) => p120;",
            "(p120) => p120; (p201) => p201;",
        ),
    ] {
        p.write("app/main.vast", &changed);
        assert!(expect_code(&p.check_manifest(MANIFEST), "E_FUNCTOR").contains("composition"));
    }
}

#[test]
fn the_opposite_swaps_endpoints_and_keeps_the_selected_category_nominal() {
    let p = Scratch::empty("opposite of a chain");
    let decls = CHAIN.split_once("fn main").unwrap().0;
    let source = format!(
        "{decls}
indexed instance R : Small = Opposite<C>;
indexed schema MapOf = finite_functor;
indexed schema Cell = finite_nat_trans;
indexed schema Iso = finite_iso;
indexed table objId(Obj) -> Obj {{ (lo) => lo; (hi) => hi; }}
indexed table arrId(Arr) -> Arr {{ (up) => up; (leftId) => leftId; (rightId) => rightId; }}
indexed instance IdR : MapOf = finite_functor(R, R, objId, arrId);
indexed instance UnitR : Cell = finite_nat_trans(IdR, IdR, R::identities);
indexed table L() -> Obj {{ () => lo; }}
indexed table LId() -> Arr {{ () => leftId; }}
indexed instance Trivial : Iso = finite_iso(R, L, L, LId, LId);
fn up() -> Hom<R, R::objects::hi, Obj::lo> {{ R::up }}
fn main() -> Int {{
    let result = finite::lookup::<R::composition>(up(), R::rightId);
    if result == R::up && finite::lookup::<R::source>(Arr::up) == Obj::hi &&
       finite::lookup::<R::target>(Arr::up) == Obj::lo &&
       finite::lookup::<UnitR::components>(Obj::hi) == Arr::rightId &&
       finite::lookup::<Trivial::inverse>() == R::leftId {{ 42 }} else {{ 7 }}
}}"
    );
    p.write_package("app", &source, "");
    assert_eq!(p.check_build_and_run(MANIFEST), exits(42));
    for (from, to, code) in [
        ("R::objects::hi, Obj::lo", "Obj::lo, Obj::hi", "E_TYPE"),
        ("up(), R::rightId", "up(), C::rightId", "E_TYPE"),
        ("Opposite<C>", "Opposite<R>", "E_CYCLE"),
        ("Opposite<C>", "Opposite<Arr>", "E_CATEGORY"),
        (
            "indexed instance R : Small",
            "indexed schema Other = finite_category;\nindexed instance R : Other",
            "E_CATEGORY",
        ),
    ] {
        p.write("app/main.vast", &checked_replace(&source, from, to));
        expect_code(&p.check_manifest(MANIFEST), code);
    }

    p.write("app/main.vast", &source);
    let wire = p.captured(MANIFEST, 10);
    let revision = kernel(&wire, "function-revision")["function_revision"].clone();
    let mut forged = wire;
    let view = forged["packages"][0]["modules"][0]["indexed_declarations"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|d| d["name"] == "R")
        .unwrap();
    view["trusted_laws"] = json!(true);
    assert_wire_rejected(&kernel(forged, "emit"), "E_PROTOCOL");

    let changed = checked_replace(&source, "indexed instance R :", "indexed instance D : Small = finite_graph(Obj, Arr, s, t, ids, comp);\nindexed instance R :").replace("Opposite<C>", "Opposite<D>");
    p.write("app/main.vast", &changed);
    let mut wire = p.captured(MANIFEST, 10);
    assert_eq!(kernel(&wire, "check")["ok"], true);
    wire["expected_function_revision"] = revision;
    assert_wire_rejected(&kernel(wire, "emit"), "E_FUNCTION_REVISION");
}
