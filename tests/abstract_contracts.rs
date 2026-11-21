//! Bodyless contracts extend callable domains, without entering dispatch selection.
mod common;
use common::{Scratch, check, cli, exits, flat_module, kernel, native, ran, request, success};
use serde_json::json;
use std::process::Command;

const TYPES: &str = "abstract type Numeric; subtype Nat <: Numeric; subtype Int <: Numeric;";
const METHODS: &str = "fn widen(x: Nat) -> Int { int(x) } fn widen(x: Int) -> Int { x }";
const CONTRACT: &str = "fn widen(x: Numeric) -> Int domain((Numeric));";
fn reject(source: &str, code: &str) {
    common::reject(source, code, "contracts.vast");
    let raw = request(source, "contracts.vast");
    common::assert_rejected(raw, code);
}

#[test]
fn abstract_domains_extend_empty_generic_domains_with_and_without_functions() {
    for higher_order in [false, true] {
        let main = if higher_order {
            "fn main() -> Int { let f = fn(x: Int) -> Int { widen(x) }; let n: Nat = 20; widen(n) + f(22) }"
        } else {
            "fn main() -> Int { let n: Nat = 20; widen(n) + widen(22) }"
        };
        native(
            &format!("{TYPES} fn widen(x) domain(); {CONTRACT} {METHODS} {main}"),
            &[],
            exits(42),
            "contracts.vast",
        );
    }
    let s = Scratch::empty("contract library");
    let library = s.write(
        "library.vast",
        &format!("{TYPES} fn widen(x) domain(); {CONTRACT} {METHODS}"),
    );
    native(
        "fn main() -> Int { widen(42) }",
        &[library],
        exits(42),
        "contracts.vast",
    );
}

#[test]
fn callable_union_and_overlapping_contracts_are_order_independent() {
    let declarations = [
        TYPES,
        "fn widen(x) domain((Bool));",
        CONTRACT,
        "fn widen(x: Any) -> Int domain((Nat), (Bool), (Nat));",
        "fn widen(x: Int) -> Int domain((Int));",
        "fn widen(x: Bool) -> Int { if x { 2 } else { 0 } }",
        METHODS,
    ];
    for reversed in [false, true] {
        let mut parts = declarations.to_vec();
        if reversed {
            parts.reverse();
        }
        native(
            &(parts.join("\n")
                + "fn main() -> Int { let n: Nat = 20; widen(n) + widen(20) + widen(true) }"),
            &[],
            exits(42),
            "contracts.vast",
        );
    }
}

#[test]
fn empty_domains_are_explicit_and_nullary_contracts_are_callable() {
    success(&check(
        "abstract type Empty; fn f(x) domain(); fn f(x: Empty) -> Int domain();",
        "contracts.vast",
    ));
    reject(
        "abstract type Empty; fn f(x) domain(); fn f(x: Empty) -> Int domain((Empty));",
        "E_CONTRACT_EMPTY",
    );
    reject(
        "abstract type Empty; fn f(x) domain(); fn f(x: Any) -> Int domain((Int), (Empty)); fn f(x: Int) -> Int { x }",
        "E_CONTRACT_EMPTY",
    );
    native(
        "fn f() domain(); fn f() -> Int domain(()); fn f() -> Int { 42 } fn main() -> Int { f() }",
        &[],
        exits(42),
        "contracts.vast",
    );
    reject(
        "fn f() domain(); fn f() requires (HasEq) -> Int domain(()); fn f() -> Int { 42 }",
        "E_CONTRACT_DOMAIN",
    );
}

#[test]
fn each_contract_domain_must_satisfy_its_selectors_and_capabilities() {
    for (contract, code) in [
        ("fn f(x: Int) -> Int domain((Number));", "E_CONTRACT_DOMAIN"),
        (
            "fn f(x: Any) requires (HasOrder) -> Int domain((Any));",
            "E_CONTRACT_DOMAIN",
        ),
        (
            "fn f(x: Any) requires (Unknown) -> Int domain();",
            "E_CAPABILITY",
        ),
        ("fn f(x: Any) -> Int domain((Int, Int));", "E_ARITY"),
        ("fn f() -> Int domain();", "E_ARITY"),
        ("fn f(x: Any) -> Int domain((Missing));", "E_NAME"),
    ] {
        reject(
            &format!("fn f(x) domain(); {contract} fn f(x: Any) -> Int {{ 0 }}"),
            code,
        );
    }
    native(
        "abstract type A; abstract type B; subtype Int <: A; subtype Int <: B; fn f(x) domain(); fn f(x: A) requires (HasOrder) -> Int domain((B)); fn f(x: Int) -> Int { x } fn main() -> Int { f(42) }",
        &[],
        exits(42),
        "contracts.vast",
    );
}

#[test]
fn contracts_never_supply_candidates_or_select_by_result_type() {
    reject(
        &format!("{TYPES} fn widen(x) domain(); {CONTRACT}"),
        "E_DISPATCH_COVERAGE",
    );
    reject(
        &format!(
            "{TYPES} fn widen(x) domain(); {CONTRACT} fn widen(x: Any) requires (HasOrder) -> Int {{ 0 }} fn widen(x: Numeric) -> Int {{ 0 }}"
        ),
        "E_DISPATCH_AMBIGUOUS",
    );
    reject(
        "fn f(x) domain(); fn f(x: Number) -> Int domain((Nat)); fn f(x: Number) -> Int { 0 } fn f(x: Nat) -> Nat { x }",
        "E_CONTRACT_RESULT",
    );
    reject(
        &format!(
            "{TYPES} fn widen(x) domain(); {CONTRACT} {METHODS} fn widen(x: Nat) -> Nat domain((Nat));"
        ),
        "E_CONTRACT_RESULT",
    );
    // Even nonwinning and domain-external concrete bodies are independently checked.
    reject(
        "fn f(x) domain(); fn f(x: Int) -> Int domain((Int)); fn f(x: Any) -> Int { x } fn f(x: Int) -> Int { x }",
        "E_TYPE",
    );
    reject(
        "fn f(x) domain(); fn f(x: Int) -> Int domain((Int)); fn f(x: Int) -> Int { x } fn f(x: Bool) -> Int { x }",
        "E_TYPE",
    );
}

#[test]
fn pair_contract_results_are_exact_and_do_not_admit_numeric_coercions() {
    native(
        "fn f(x) domain(); fn f(x: Int) -> Pair<Int> domain((Int)); fn f(x: Int) -> Pair<Int> { pair(x, x) } fn main() -> Int { pair_first(f(21)) + pair_second(f(21)) }",
        &[],
        exits(42),
        "contracts.vast",
    );
    reject(
        "fn f(x) domain(); fn f(x: Int) -> Pair<Nat> domain((Int)); fn f(x: Int) -> Pair<Int> { pair(x, x) }",
        "E_CONTRACT_RESULT",
    );
    reject(
        "fn f(x) domain(); fn f(x: Nat) -> Int domain((Nat)); fn f(x: Nat) -> Int { int(x) } fn main() -> Int { f(1) }",
        "E_DISPATCH_DOMAIN",
    );
}

#[test]
fn raw_contract_ir_cannot_bypass_result_domain_or_protocol_checks() {
    let raw = request(
        &format!("{TYPES} fn widen(x) domain(); {CONTRACT} {METHODS}"),
        "contracts.vast",
    );
    assert_eq!(raw["version"], common::CURRENT_PROTOCOL);
    let mut module = raw["packages"][0]["modules"][0].clone();
    assert!(module["abstract_methods"][0].get("body").is_none());
    assert_eq!(kernel(&raw, "check")["ok"], true);
    for (mutation, code) in [
        ("result", "E_CONTRACT_RESULT"),
        ("body", "E_PROTOCOL"),
        ("winner", "E_PROTOCOL"),
        ("domain", "E_CONTRACT_DOMAIN"),
        ("span", "E_PROTOCOL"),
        // An extra parameter changes the contract's arity, which the kernel
        // compares with its generic's first.
        ("extra parameter", "E_ARITY"),
        ("function", "E_PROTOCOL"),
    ] {
        let mut bad = raw.clone();
        let contract = &mut flat_module(&mut bad)["abstract_methods"][0];
        match mutation {
            "result" => contract["return_type"]["name"] = json!("Nat"),
            "body" => contract["body"] = module["methods"][0]["body"].take(),
            "winner" => contract["selected"] = json!(0),
            "domain" => contract["domain"][0][0]["path"] = json!(["Bool"]),
            "span" => contract["domain"][0][0]["span"]["line"] = json!(0),
            "extra parameter" => {
                let param = contract["params"][0].clone();
                contract["params"].as_array_mut().unwrap().push(param);
            }
            _ => {
                contract["return_type"] = json!({"kind":"function","params":[],"return_type":{"kind":"named","name":"Int"}})
            }
        }
        common::assert_rejected(bad, code);
    }
}

/// A forged 2-ary contract that repeats a parameter name, with the arity of
/// its generic, reaches the kernel's duplicate-parameter check in `check` and
/// in `emit`.
#[test]
fn raw_contract_ir_cannot_repeat_a_parameter_name() {
    let raw = request(
        &format!(
            "{TYPES} fn join(x, y) domain(); fn join(x: Numeric, y: Numeric) -> Int domain((Numeric, Numeric)); fn join(x: Numeric, y: Numeric) -> Int {{ 1 }}"
        ),
        "contracts.vast",
    );
    assert_eq!(kernel(&raw, "check")["ok"], true);
    let mut bad = raw.clone();
    let params = &mut flat_module(&mut bad)["abstract_methods"][0]["params"];
    assert_eq!(params.as_array().map(Vec::len), Some(2), "{params}");
    params[1]["name"] = params[0]["name"].clone();
    for mode in ["check", "emit"] {
        let response = kernel(&bad, mode);
        common::assert_wire_rejected(&response, "E_DUPLICATE");
        assert_eq!(
            response["diagnostics"][0]["message"], "duplicate abstract method parameter",
            "{response}"
        );
    }
}

#[test]
fn package_contracts_resolve_aliases_but_keep_exact_generic_owner_authority() {
    let s = Scratch::empty("contract packages");
    s.write_package("lib",
        "pub mod types { pub abstract type Numeric; subtype Int <: Numeric; } pub use types::Numeric as N; pub fn f(x) domain(); fn f(x: N) -> Int domain((N)); fn f(x: Int) -> Int { x }",
        "",
    );
    s.write_package(
        "app",
        "use dep::f as call; fn main() -> Int { call(42) }",
        "dep={path='../lib'}",
    );
    success(
        &cli()
            .current_dir(&s.0)
            .args(["check", "--manifest-path", "app/Vastitas.toml"])
            .output()
            .unwrap(),
    );
    success(
        &cli()
            .current_dir(&s.0)
            .args([
                "build",
                "--manifest-path",
                "app/Vastitas.toml",
                "-o",
                "program",
            ])
            .output()
            .unwrap(),
    );
    let output = Command::new(s.0.join("program")).output().unwrap();
    assert_eq!(ran(&output), exits(42));
    for (source, code) in [
        ("fn dep::f(x: Int) -> Int domain((Int));", "E_OWNER"),
        (
            "use dep::f as imported; fn imported(x: Int) -> Int domain();",
            "E_OWNER",
        ),
        (
            "pub fn f(x) domain(); mod child { fn super::f(x: Int) -> Int domain(); }",
            "E_OWNER",
        ),
    ] {
        s.write("app/main.vast", source);
        let output = cli()
            .current_dir(&s.0)
            .args(["check", "--manifest-path", "app/Vastitas.toml"])
            .output()
            .unwrap();
        assert!(!output.status.success());
        common::expect_code(&output, code);
    }
}

#[test]
fn raw_package_contracts_cannot_forge_edit_rights_or_erase_contracts() {
    let s = Scratch::empty("contract authority");
    s.write_package(
        "lib",
        "pub fn f(x) domain(); fn f(x: Int) -> Int domain((Int)); fn f(x: Int) -> Int { x }",
        "",
    );
    s.write_package(
        "app",
        "fn main() -> Int { dep::f(42) }",
        "dep={path='../lib'}",
    );
    let raw = s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
    assert_eq!(kernel(&raw, "check")["ok"], true);
    let packages = raw["packages"].as_array().unwrap();
    let lib = packages.iter().position(|p| p["name"] == "lib").unwrap();
    let app = packages.iter().position(|p| p["name"] == "app").unwrap();
    let mut bad = raw.clone();
    let mut contract = bad["packages"][lib]["modules"][0]["abstract_methods"][0].clone();
    contract["name"] = json!("dep::f");
    bad["packages"][app]["modules"][0]["abstract_methods"] = json!([contract]);
    common::assert_rejected(bad, "E_OWNER");
    let mut bad = raw;
    bad["packages"][lib]["modules"][0]["abstract_methods"][0]["domain"][0][0]["path"] =
        json!(["Nat"]);
    common::assert_rejected(bad, "E_CONTRACT_DOMAIN");
}

#[test]
fn tuple_domains_expand_products_and_preserve_the_key_space_limit() {
    native(
        &format!(
            "{TYPES} fn f(x, y) domain(); fn f(x: Numeric, y: Bool) requires (HasEq) -> Int domain((Numeric, Bool)); fn f(x: Nat, y: Bool) -> Int {{ if y {{ int(x) }} else {{ 0 }} }} fn f(x: Int, y: Bool) -> Int {{ if y {{ x }} else {{ 0 }} }} fn main() -> Int {{ let n: Nat = 20; f(n, true) + f(22, true) }}"
        ),
        &[],
        exits(42),
        "contracts.vast",
    );
    reject(
        "fn f(a,b,c,d,e,farg,g) domain(); fn f(a: Any,b: Any,c: Any,d: Any,e: Any,farg: Any,g: Any) -> Int domain();",
        "E_LIMIT",
    );
    // A malformed base domain is not silently discarded by canonical union.
    reject(
        "fn f(x) domain((Int, Int)); fn f(x: Int) -> Int domain();",
        "E_DISPATCH_DOMAIN",
    );
}
