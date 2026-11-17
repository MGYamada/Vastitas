//! Bodyless contracts extend callable domains, without entering dispatch selection.
mod common;
use common::{Scratch, check, cli, exits, flat_module, kernel, native, ran, request, success};
use serde_json::{Value, json};
use std::process::Command;

const TYPES: &str = "abstract type Numeric; subtype Nat <: Numeric; subtype Int <: Numeric;";
const METHODS: &str = "method widen(x: Nat) -> Int { int(x) } method widen(x: Int) -> Int { x }";
const CONTRACT: &str = "abstract method widen(x: Numeric) -> Int { domain (Numeric); }";
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
            &format!("{TYPES} generic widen(x) {{ domain; }} {CONTRACT} {METHODS} {main}"),
            &[],
            exits(42),
            "contracts.vast",
        );
    }
    let s = Scratch::empty("contract library");
    let library = s.write(
        "library.vast",
        &format!("{TYPES} generic widen(x) {{ domain; }} {CONTRACT} {METHODS}"),
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
        "generic widen(x) { domain (Bool); }",
        CONTRACT,
        "abstract method widen(x: Any) -> Int { domain (Nat), (Bool), (Nat); }",
        "abstract method widen(x: Int) -> Int { domain (Int); }",
        "method widen(x: Bool) -> Int { if x { 2 } else { 0 } }",
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
        "abstract type Empty; generic f(x) { domain; } abstract method f(x: Empty) -> Int { domain; }",
        "contracts.vast",
    ));
    reject(
        "abstract type Empty; generic f(x) { domain; } abstract method f(x: Empty) -> Int { domain (Empty); }",
        "E_CONTRACT_EMPTY",
    );
    reject(
        "abstract type Empty; generic f(x) { domain; } abstract method f(x: Any) -> Int { domain (Int), (Empty); } method f(x: Int) -> Int { x }",
        "E_CONTRACT_EMPTY",
    );
    native(
        "generic f() { domain; } abstract method f() -> Int { domain (); } method f() -> Int { 42 } fn main() -> Int { f() }",
        &[],
        exits(42),
        "contracts.vast",
    );
    reject(
        "generic f() { domain; } abstract method f() requires (HasEq) -> Int { domain (); } method f() -> Int { 42 }",
        "E_CONTRACT_DOMAIN",
    );
}

#[test]
fn each_contract_domain_must_satisfy_its_selectors_and_capabilities() {
    for (contract, code) in [
        (
            "abstract method f(x: Int) -> Int { domain (Number); }",
            "E_CONTRACT_DOMAIN",
        ),
        (
            "abstract method f(x: Any) requires (HasOrder) -> Int { domain (Any); }",
            "E_CONTRACT_DOMAIN",
        ),
        (
            "abstract method f(x: Any) requires (Unknown) -> Int { domain; }",
            "E_CAPABILITY",
        ),
        (
            "abstract method f(x: Any) -> Int { domain (Int, Int); }",
            "E_ARITY",
        ),
        ("abstract method f() -> Int { domain; }", "E_ARITY"),
        (
            "abstract method f(x: Any) -> Int { domain (Missing); }",
            "E_NAME",
        ),
    ] {
        reject(
            &format!("generic f(x) {{ domain; }} {contract} method f(x: Any) -> Int {{ 0 }}"),
            code,
        );
    }
    native(
        "abstract type A; abstract type B; subtype Int <: A; subtype Int <: B; generic f(x) { domain; } abstract method f(x: A) requires (HasOrder) -> Int { domain (B); } method f(x: Int) -> Int { x } fn main() -> Int { f(42) }",
        &[],
        exits(42),
        "contracts.vast",
    );
}

#[test]
fn contracts_never_supply_candidates_or_select_by_result_type() {
    reject(
        &format!("{TYPES} generic widen(x) {{ domain; }} {CONTRACT}"),
        "E_DISPATCH_COVERAGE",
    );
    reject(
        &format!(
            "{TYPES} generic widen(x) {{ domain; }} {CONTRACT} method widen(x: Any) requires (HasOrder) -> Int {{ 0 }} method widen(x: Numeric) -> Int {{ 0 }}"
        ),
        "E_DISPATCH_AMBIGUOUS",
    );
    reject(
        "generic f(x) { domain; } abstract method f(x: Number) -> Int { domain (Nat); } method f(x: Number) -> Int { 0 } method f(x: Nat) -> Nat { x }",
        "E_CONTRACT_RESULT",
    );
    reject(
        &format!(
            "{TYPES} generic widen(x) {{ domain; }} {CONTRACT} {METHODS} abstract method widen(x: Nat) -> Nat {{ domain (Nat); }}"
        ),
        "E_CONTRACT_RESULT",
    );
    // Even nonwinning and domain-external concrete bodies are independently checked.
    reject(
        "generic f(x) { domain; } abstract method f(x: Int) -> Int { domain (Int); } method f(x: Any) -> Int { x } method f(x: Int) -> Int { x }",
        "E_TYPE",
    );
    reject(
        "generic f(x) { domain; } abstract method f(x: Int) -> Int { domain (Int); } method f(x: Int) -> Int { x } method f(x: Bool) -> Int { x }",
        "E_TYPE",
    );
}

#[test]
fn pair_contract_results_are_exact_and_do_not_admit_numeric_coercions() {
    native(
        "generic f(x) { domain; } abstract method f(x: Int) -> Pair<Int> { domain (Int); } method f(x: Int) -> Pair<Int> { pair(x, x) } fn main() -> Int { pair_first(f(21)) + pair_second(f(21)) }",
        &[],
        exits(42),
        "contracts.vast",
    );
    reject(
        "generic f(x) { domain; } abstract method f(x: Int) -> Pair<Nat> { domain (Int); } method f(x: Int) -> Pair<Int> { pair(x, x) }",
        "E_CONTRACT_RESULT",
    );
    reject(
        "generic f(x) { domain; } abstract method f(x: Nat) -> Int { domain (Nat); } method f(x: Nat) -> Int { int(x) } fn main() -> Int { f(1) }",
        "E_DISPATCH_DOMAIN",
    );
}

#[test]
fn raw_contract_ir_cannot_bypass_result_domain_or_protocol_checks() {
    let raw = request(
        &format!("{TYPES} generic widen(x) {{ domain; }} {CONTRACT} {METHODS}"),
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
            "{TYPES} generic join(x, y) {{ domain; }} abstract method join(x: Numeric, y: Numeric) -> Int {{ domain (Numeric, Numeric); }} method join(x: Numeric, y: Numeric) -> Int {{ 1 }}"
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
        "pub mod types { pub abstract type Numeric; subtype Int <: Numeric; } pub use types::Numeric as N; pub generic f(x) { domain; } abstract method f(x: N) -> Int { domain (N); } method f(x: Int) -> Int { x }",
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
    for source in [
        "abstract method dep::f(x: Int) -> Int { domain (Int); }",
        "use dep::f as imported; abstract method imported(x: Int) -> Int { domain; }",
        "pub generic f(x) { domain; } mod child { abstract method super::f(x: Int) -> Int { domain; } }",
    ] {
        s.write("app/main.vast", source);
        let output = cli()
            .current_dir(&s.0)
            .args(["check", "--manifest-path", "app/Vastitas.toml"])
            .output()
            .unwrap();
        assert!(!output.status.success());
        common::expect_code(&output, "E_OWNER");
    }
}

/// The root module of the request of the flat unit `source`, in which every
/// function, generic and abstract type is public.
fn raw_module(source: &str) -> Value {
    flat_module(&mut request(source, "contracts.vast")).take()
}
#[test]
fn raw_package_contracts_cannot_forge_edit_rights_or_erase_contracts() {
    let lib = raw_module(
        "generic f(x) { domain; } abstract method f(x: Int) -> Int { domain (Int); } method f(x: Int) -> Int { x }",
    );
    let mut app = raw_module("fn main() -> Int { 42 }");
    app["functions"][0]["body"]["result"] = json!({"kind":"call","callee":"dep::f","args":[{"kind":"integer","value":"42","span":{"start":0,"end":0,"line":1,"column":1}}],"span":{"start":0,"end":0,"line":1,"column":1}});
    let raw = json!({"version":common::CURRENT_PROTOCOL,"file":"contracts.vast","root":"/app","packages":[
        {"source":"/app","name":"app","version":"0.1.0","dependencies":[{"alias":"dep","target":"/lib"}],"modules":[app]},
        {"source":"/lib","name":"lib","version":"0.1.0","dependencies":[],"modules":[lib]}
    ]});
    assert_eq!(kernel(&raw, "check")["ok"], true);
    let mut bad = raw.clone();
    let mut contract = bad["packages"][1]["modules"][0]["abstract_methods"][0].clone();
    contract["name"] = json!("dep::f");
    bad["packages"][0]["modules"][0]["abstract_methods"] = json!([contract]);
    common::assert_rejected(bad, "E_OWNER");
    let mut bad = raw;
    bad["packages"][1]["modules"][0]["abstract_methods"][0]["domain"][0][0]["path"] =
        json!(["Nat"]);
    common::assert_rejected(bad, "E_CONTRACT_DOMAIN");
}

#[test]
fn tuple_domains_expand_products_and_preserve_the_key_space_limit() {
    native(
        &format!(
            "{TYPES} generic f(x, y) {{ domain; }} abstract method f(x: Numeric, y: Bool) requires (HasEq) -> Int {{ domain (Numeric, Bool); }} method f(x: Nat, y: Bool) -> Int {{ if y {{ int(x) }} else {{ 0 }} }} method f(x: Int, y: Bool) -> Int {{ if y {{ x }} else {{ 0 }} }} fn main() -> Int {{ let n: Nat = 20; f(n, true) + f(22, true) }}"
        ),
        &[],
        exits(42),
        "contracts.vast",
    );
    reject(
        "generic f(a,b,c,d,e,farg,g) { domain; } abstract method f(a: Any,b: Any,c: Any,d: Any,e: Any,farg: Any,g: Any) -> Int { domain; }",
        "E_LIMIT",
    );
    // A malformed base domain is not silently discarded by canonical union.
    reject(
        "generic f(x) { domain (Int, Int); } abstract method f(x: Int) -> Int { domain; }",
        "E_DISPATCH_DOMAIN",
    );
}
