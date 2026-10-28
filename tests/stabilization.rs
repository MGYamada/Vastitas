//! Regressions for the Stage 1 stabilization gate; acceptance and diagnostics
//! are tested at the actual CLI/wire boundary, including native branch results.
mod common;
use common::{Scratch, cli, kernel, native, reject, request};
use serde_json::json;

#[test]
fn closed_integer_expression_typing_is_symmetric_without_conversion_or_folding() {
    for extra in [
        "",
        "fn unused() -> Int { let g = fn(x: Int) -> Int { x }; g(0) }",
    ] {
        native(
            &format!(
                "fn left(n: Nat, c: Bool) -> Nat {{ let v = if c {{ 1 + 2 }} else {{ n }}; v }} fn right(n: Nat, c: Bool) -> Nat {{ let v = if c {{ n }} else {{ 1 + 2 }}; v }} fn main() -> Int {{ let n: Nat = 7; if (1 + 2) < n && n > (1 + 2) && (1 + 2) * n == n * (1 + 2) && left(n, true) == 3 && left(n, false) == n && right(n, true) == n && right(n, false) == 3 {{ 42 }} else {{ -1 }} }} {extra}"
            ),
            &[],
            "42",
            "constants.vast",
        );
    }
    reject(
        "fn f(n: Nat) -> Nat { (-1 + 2) * n }",
        "E_TYPE",
        "negative.vast",
    );
    reject(
        "fn f(n: Nat, i: Int) -> Nat { (i + 2) * n }",
        "E_TYPE",
        "variable.vast",
    );
    native(
        "fn main() -> Int { (1 - 2) * 3 }",
        &[],
        "-3",
        "default.vast",
    );
}

#[test]
fn else_if_limit_names_the_chain_and_accepts_the_documented_boundary() {
    let source = |count| {
        format!(
            "fn f(x: Int) -> Int {{ {} else {{ -1 }} }} fn main() -> Int {{ f(7) }}",
            (0..count)
                .map(|i| format!("if x == {i} {{ {i} }}"))
                .collect::<Vec<_>>()
                .join(" else ")
        )
    };
    native(&source(62), &[], "7", "chain.vast");
    let message = reject(&source(63), "E_LIMIT", "chain.vast");
    assert!(
        message.contains("`else if` chain") && message.contains("62"),
        "{message}"
    );
}

#[test]
fn reserved_control_names_and_missing_unpack_are_explained() {
    for word in ["while", "for", "loop", "mut"] {
        for source in [
            format!("fn {word}() -> Int {{ 0 }}"),
            format!("fn f({word}: Int) -> Int {{ 0 }}"),
            format!("fn f() -> Int {{ let {word} = 0; 0 }}"),
        ] {
            let error = vastitas::frontend::parse(&source, "names.vast")
                .unwrap_err()
                .remove(0);
            assert_eq!(error.code, "E_RESERVED");
            assert!(error.message.contains("reserved"));
            assert_eq!(&source[error.span.start..error.span.end], word);
        }
    }
    let message = reject(
        "fn f(p: Pointed<Scheme, QQ>) -> Int { p as { scheme: X, point: x }; 0 }",
        "E_PARSE",
        "unpack.vast",
    );
    assert!(message.contains("unpack value as"), "{message}");
}

#[test]
fn conversion_and_generative_identity_notes_are_specific() {
    for body in [
        "let n: Nat = 1; n + 2",
        "let n: Nat = 1; let i: Int = n; i",
        "let n: Nat = 1; twice(n)",
    ] {
        let message = reject(
            &format!("fn twice(x: Int) -> Int {{ x * 2 }} fn main() -> Int {{ {body} }}"),
            "E_TYPE",
            "conversion.vast",
        );
        assert!(message.contains("int(...)"), "{message}");
    }
    assert!(!reject("fn f(i: Int) -> Nat { i }", "E_TYPE", "conversion.vast").contains("int(...)"));
    for body in [
        "let p = apply(id(Affine(QQ, 2)), origin(Affine(QQ, 2))); 0",
        "let p = apply(id(space()), origin(space())); 0",
        "let p = pack { scheme: Affine(QQ, 2), point: origin(Affine(QQ, 2)) }; 0",
    ] {
        let message = reject(
            &format!("fn space() -> Scheme {{ Affine(QQ, 2) }} fn main() -> Int {{ {body} }}"),
            "E_ENDPOINT",
            "identity.vast",
        );
        assert!(message.contains("bind the object once"), "{message}");
    }
    let different = reject(
        "fn space() -> Scheme { Affine(QQ, 2) } fn main() -> Int { let p = apply(id(space()), origin(Affine(QQ, 2))); 0 }",
        "E_ENDPOINT",
        "identity.vast",
    );
    assert!(!different.contains("bind the object once"));
}

#[test]
fn coverage_notes_identify_candidates_capabilities_and_contract_sources() {
    for (source, reason) in [
        (
            "generic f(x) { domain (Bool); }\nmethod f(x: Number) -> Int { 0 }",
            "selector mismatch",
        ),
        (
            "generic f(x) { domain (Bool); }\nmethod f(x: Any) requires (HasOrder) -> Int { 0 }",
            "key lacks HasOrder",
        ),
        (
            "abstract type Logical; subtype Bool <: Logical;\ngeneric f(x) { domain (Int); }\nabstract method f(x: Logical) -> Int { domain (Logical); }\nmethod f(x: Number) -> Int { 0 }",
            "because of this abstract method contract",
        ),
    ] {
        let message = reject(source, "E_DISPATCH_COVERAGE", "coverage.vast");
        assert!(
            message.contains(reason) && message.contains("help: declare a method"),
            "{message}"
        );
        if reason.contains("contract") {
            assert!(message.contains("coverage.vast:3:1: note:"), "{message}");
        }
    }
}

#[test]
fn recursion_names_are_quoted_after_package_resolution_and_specialization() {
    let s = Scratch::empty("cycle");
    s.write(
        "Vastitas.toml",
        "[package]\nname='rec'\nversion='0.1.0'\nroot='main.vast'\n",
    );
    s.write("main.vast", "fn a() -> Int { b() } fn b() -> Int { a() }");
    let output = cli()
        .args(["check", "--manifest-path"])
        .arg(s.0.join("Vastitas.toml"))
        .output()
        .unwrap();
    assert!(!output.status.success());
    let message = String::from_utf8_lossy(&output.stderr);
    assert!(
        message.contains("`rec::a` → `rec::b` → `rec::a`"),
        "{message}"
    );
    let message = reject(
        "fn call(f: Fn<Int, Int>, x: Int) -> Int { f(x) } fn spin(x: Int) -> Int { call(spin, x) }",
        "E_RECURSION",
        "cycle.vast",
    );
    assert!(message.contains("`spin` → `call` → `spin`"), "{message}");
}

#[test]
fn unknown_wire_version_is_echoed_with_the_complete_supported_set() {
    let response = kernel(json!({"version": 999, "file": "unknown"}), "check");
    assert_eq!(response["version"], 999);
    assert_eq!(response["diagnostics"][0]["code"], "E_PROTOCOL");
    assert_eq!(
        response["diagnostics"][0]["message"],
        "unsupported IR protocol version 999; expected 2, 3, 4, 5"
    );
    let raw = request("fn main() -> Int { 42 }", "normal.vast");
    assert_eq!(kernel(&raw, "check")["version"], 2);

    use std::io::Write;
    use std::process::{Command, Stdio};
    let mut child = Command::new(common::kernel_path())
        .arg("check")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(b"{\"version\":5,")
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(!output.status.success());
    let response: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(response["version"], 2);
    assert_eq!(response["diagnostics"][0]["code"], "E_PROTOCOL");
}
