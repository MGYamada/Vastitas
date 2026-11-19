mod common;
use common::{Scratch, exits, expect_code, native, reject};

#[test]
fn named_and_glyph_exact_methods_agree_on_all_integer_keys() {
    let source = "
fn main() -> Int {
    let n: Nat = 5; let z: Nat = 0; let a: Int = -7;
    if std::operator::add(n,n) == n+n && std::operator::sub(z,n) == z-n
        && std::operator::mul(a,a) == a*a && std::operator::neg(a) == -a
        && std::operator::sub(a,2) == a-2 && std::operator::mul(n,n) == n*n
        && std::operator::add(a,2) == a+2
        && div(n,n) == n/n && div(a,n) == -2 && div(n,a) == 0
        && div(a,a) == 1 && div(a,z) == 0 && div(z,z) == z
        && std::operator::div(a,n) == a/n && 24 / 3 * 2 / 4 == 4
        && -7 / -3 == 3 { 42 } else { 0 }
}";
    native(source, &[], exits(42), "exact-operators.vast");
}

#[test]
fn imported_operator_alias_and_same_spelling_local_family_are_distinct() {
    let s = Scratch::empty("canonical operators");
    s.write_package("app", "use std::operator::sub as cut; fn sub(a: Int, b: Int) -> Int { 90 } fn main() -> Int { let n: Nat = 1; if self::sub(0,1) == 90 && cut(n,2) == n-2 && cut(0,1) == n-n && cut(0,1) == -1 { 42 } else { 0 } }", "");
    assert_eq!(s.check_build_and_run("app/Vastitas.toml"), exits(42));
    s.write_package("other", "pub fn sub(a: Int,b: Int) -> Int { 99 }", "");
    s.write_package(
        "app",
        "fn main() -> Int { std::operator::sub(1,2) }",
        "std={path='../other'}",
    );
    expect_code(&s.check_manifest("app/Vastitas.toml"), "E_NAME");
}

#[test]
fn division_promotion_does_not_admit_other_mixed_keys_or_nat_negation() {
    reject("fn f() -> Int { 7 % 2 }", "E_UNSUPPORTED", "rem.vast");
    reject("fn f() -> Int { fdiv(7,2) }", "E_NAME", "floor.vast");
    reject(
        "fn div(x:Int,y:Int) -> Int { 99 } fn main() -> Int { div(3,2) }",
        "E_NAME",
        "ambiguous.vast",
    );
    reject(
        "fn f(n: Nat, i: Int) -> Int { std::operator::mul(n,i) }",
        "E_TYPE",
        "mixed.vast",
    );
    reject(
        "fn f(n: Nat) -> Int { std::operator::neg(n) }",
        "E_TYPE",
        "neg.vast",
    );
    reject(
        "fn f() -> Int { std::operator::div(true,true) }",
        "E_OPERATOR",
        "bool.vast",
    );
    reject(
        "fn f() -> Int { std::operator::div(1) }",
        "E_ARITY",
        "arity.vast",
    );
    reject(
        "fn f() -> Int { 4 /* 2 */ }",
        "E_UNSUPPORTED",
        "comment.vast",
    );
}

#[test]
fn returned_revision_binds_spelling_and_both_mixed_division_keys() {
    let s = Scratch::empty("operator revision");
    s.write_package(
        "app",
        "
use std::operator::div as quotient;
fn f(n: Nat, i: Int) -> Int {
    let a = n / i; let b = quotient(n,i); let c = i / n; let d = div(i,n);
    let e = n / n; let g = i / i; a
}
fn main() -> Int { f(1,2) }",
        "",
    );
    let mut request = s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    let response = common::kernel(&request, "function-revision");
    let revision = &response["function_revision"];
    let sites = revision["pure"]["operator_sites"]
        .as_array()
        .expect("checked Core operators");
    assert_eq!(sites.len(), 6, "{sites:?}");
    assert_eq!(sites[0], sites[1]);
    assert_eq!(sites[2], sites[3]);
    let signatures: Vec<_> = sites
        .iter()
        .map(|site| {
            assert_eq!(site["id"]["package"]["source"], "vastitas:compat:operators");
            assert_eq!(site["id"]["name"], "div");
            site["key"].clone()
        })
        .collect();
    assert_eq!(
        serde_json::json!(signatures),
        serde_json::json!([
            ["Nat", "Int"],
            ["Nat", "Int"],
            ["Int", "Nat"],
            ["Int", "Nat"],
            ["Nat", "Nat"],
            ["Int", "Int"]
        ])
    );
    request["expected_function_revision"] = revision.clone();
    assert_eq!(
        common::kernel(&request, "check")["function_revision_matched"],
        true
    );
    request["expected_function_revision"]["pure"]["operator_sites"][0]["key"] =
        serde_json::json!(["Int", "Int"]);
    assert_eq!(common::kernel(&request, "emit")["ok"], false);
}

#[test]
fn a_lifted_lambda_cannot_capture_or_reinterpret_a_div_binding() {
    let s = Scratch::empty("division capture");
    let source = "fn main() -> Int { let div = fn(x:Int,y:Int)->Int { 99 }; let f = fn()->Int { div(7,2) }; f() }";
    s.write_package("app", source, "");
    let raw = s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    expect_code(&s.check_manifest("app/Vastitas.toml"), "E_CAPTURE");
    for mode in ["check", "emit", "function-revision"] {
        common::assert_wire_rejected(&common::kernel(&raw, mode), "E_CAPTURE");
    }
    s.write_package(
        "app",
        &source.replace("{ div(7,2)", "{ std::operator::div(7,2)"),
        "",
    );
    assert_eq!(s.check_build_and_run("app/Vastitas.toml"), exits(3));
}

#[test]
fn exact_operator_families_are_static_values_with_checked_method_bodies() {
    let s = Scratch::empty("operator Fn values");
    let program = "
use std::operator::sub as minus;
fn get() -> Fn<(Int,Nat),Int> { std::operator::div }
fn higher(f: Fn<(Nat,Int),Int>, n:Nat) -> Int { f(n,-2) }
fn main() -> Int {
    let op = minus; let n:Nat = 5; let z:Nat=0; let unbound = div;
    if op(n,8) == 0 && op(2,5) == z && get()(-7,n) == -2 && higher(unbound,n) == -2 { 42 } else { 1 }
}";
    s.write_package("app", program, "");
    assert_eq!(s.check_build_and_run("app/Vastitas.toml"), exits(42));
    let mut request = s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    let result = common::kernel(&request, "function-revision");
    let revision = &result["function_revision"];
    let families = revision["families"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|r| r["id"]["package"]["source"] == "vastitas:compat:operators")
        .collect::<Vec<_>>();
    assert_eq!(families.len(), 2);
    assert!(
        families
            .iter()
            .any(|r| r["id"]["name"] == "sub" && r["dispatch"].as_array().unwrap().len() == 2)
    );
    assert!(
        families
            .iter()
            .any(|r| r["id"]["name"] == "div" && r["dispatch"].as_array().unwrap().len() == 4)
    );
    assert!(
        revision["pure"]["static_uses"]
            .as_array()
            .unwrap()
            .iter()
            .any(|u| u["selection"]["id"]["name"] == "div")
    );
    request["expected_function_revision"] = revision.clone();
    assert_eq!(
        common::kernel(&request, "emit")["function_revision_matched"],
        true
    );
    let bad = program.replace("Fn<(Int,Nat),Int>", "Fn<(Int,Nat),Bool>");
    s.write_package("app", &bad, "");
    expect_code(&s.check_manifest("app/Vastitas.toml"), "E_TYPE");
    native(
        "fn main()->Int { let minus = std::operator::neg; minus(-42) }",
        &[],
        exits(42),
        "flat-operator.vast",
    );
}

#[test]
fn all_prelude_calls_and_values_select_the_canonical_owner() {
    let s = Scratch::empty("arithmetic prelude");
    let source = "fn main() -> Int {
      let a = add; let s = sub; let m = mul; let n = neg; let d = div;
      if add(4,3) == a(4,3) && sub(4,3) == s(4,3) && mul(4,3) == m(4,3)
        && neg(4) == n(4) && div(4,3) == d(4,3) && a(4,3) == 4+3
        && s(4,3) == 4-3 && m(4,3) == 4*3 && n(4) == -4 && d(4,3) == 4/3 { 42 } else { 0 } }";
    s.write_package("app", source, "");
    assert_eq!(s.check_build_and_run("app/Vastitas.toml"), exits(42));
    let req = s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    let resp = common::kernel(&req, "function-revision");
    let receipt = &resp["function_revision"];
    for name in ["add", "sub", "neg", "mul", "div"] {
        let family = receipt["families"]
            .as_array()
            .unwrap()
            .iter()
            .find(|f| f["id"]["name"] == name)
            .unwrap();
        assert_eq!(
            family["id"]["package"]["source"],
            "vastitas:compat:operators"
        );
        assert!(
            receipt["pure"]["operator_sites"]
                .as_array()
                .unwrap()
                .iter()
                .any(|s| s["id"] == family["id"])
        );
    }
}

#[test]
fn short_qualified_and_glyph_spelling_record_the_same_checked_site() {
    let p = Scratch::empty("arithmetic spelling revision");
    p.write_package(
        "app",
        "
fn main()->Int {
    let a=add(4,3); let b=std::operator::add(4,3); let c=4+3;
    let e=sub(4,3); let f=std::operator::sub(4,3); let g=4-3;
    let i=mul(4,3); let j=std::operator::mul(4,3); let k=4*3;
    let m=neg(3); let n=std::operator::neg(3); let o= -3;
    let q=div(4,3); let r=std::operator::div(4,3); let s=4/3; 42
}",
        "",
    );
    let req = p.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    let response = common::kernel(&req, "function-revision");
    let sites = response["function_revision"]["pure"]["operator_sites"]
        .as_array()
        .unwrap();
    assert_eq!(sites.len(), 15);
    for (triple, op) in sites
        .as_chunks::<3>()
        .0
        .iter()
        .zip(["add", "sub", "mul", "neg", "div"])
    {
        assert_eq!(triple[0]["id"]["name"], op);
        assert_eq!(
            triple[0]["id"]["package"]["source"],
            "vastitas:compat:operators"
        );
        assert_eq!(triple[0], triple[1]);
        assert_eq!(triple[1], triple[2]);
    }
}

#[test]
fn a_short_name_cannot_select_a_conflicting_function_import_or_local_value() {
    let p = Scratch::empty("conflicting operator names");
    p.write_package("lib", "pub fn sum(x:Int,y:Int)->Int {90}", "");
    for src in [
        "fn add(x:Int,y:Int)->Int {90} fn main()->Int { let f = add; f(1,2) }",
        "use lib::sum as mul; fn main()->Int { mul(1,2) }",
        "use lib::sum as div; fn main()->Int { let f = div; f(1,2) }",
        "use std::operator::add as sub; fn main()->Int { sub(4,3) }",
        "use std::operator::add as sub; fn main()->Int { let f = sub; f(4,3) }",
        "fn main()->Int { let neg = fn(x:Int)->Int { 99 }; let f = neg; f(1) }",
        "fn f(mul:Fn<(Int,Int),Int>)->Int { mul(1,2) } fn main()->Int { 0 }",
    ] {
        p.write_package("app", src, "lib={path='../lib'}");
        let req = p.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
        for mode in ["check", "emit"] {
            common::assert_wire_rejected(&common::kernel(&req, mode), "E_NAME");
        }
    }
    native(
        "fn mul(a:Int,b:Int)->Int { 42 } fn main()->Int { let f = self::mul; if f(1,2) == self::mul(1,2) { 42 } else { 0 } }",
        &[],
        exits(42),
        "flat-local-operator.vast",
    );
}
