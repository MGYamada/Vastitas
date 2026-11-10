mod common;

use common::{Scratch, cli, kernel, success};
use serde_json::{Value, json};
use std::process::Command;

const PROFILES: &str = include_str!("../examples/packages/numerical/src/profiles/mod.vast");

fn bits(value: f64) -> u64 {
    value.to_bits()
}

fn source(complex: bool, m: u64, k: u64, n: u64, pad: u64) -> String {
    let profile = if complex {
        "ComplexSmooth"
    } else {
        "RealSmooth"
    };
    let scalar = if complex { "Complex<F64>" } else { "F64" };
    let literal = |real: f64, imaginary: f64| {
        if complex {
            format!("complex_bits({}, {})", bits(real), bits(imaginary))
        } else {
            format!("f64_bits({})", bits(real))
        }
    };
    let expected = if complex {
        literal(3.0 * k as f64, k as f64)
    } else {
        literal(2.0 * k as f64, 0.0)
    };
    let checked = if m > 0 && n > 0 {
        format!("runtime_expect(checked, {}, {}, {expected});", m - 1, n - 1)
    } else {
        String::new()
    };
    let header = format!(
        "m: Nat, k: Nat, n: Nat, \
         u: RuntimeSpace<profiles::{profile}, m>, \
         v: RuntimeSpace<profiles::{profile}, k>, \
         w: RuntimeSpace<profiles::{profile}, n>, \
         bu: RuntimeBasis<u>, bv: RuntimeBasis<v>, bw: RuntimeBasis<w>, \
         left: RuntimeMap<bv, bu, read>, right: RuntimeMap<bw, bv, read>, \
         output: RuntimeMap<bw, bu, write> initializes"
    );
    format!(
        r#"mod profiles;
resource fn multiply({header}) -> Unit {{
    runtime_gemm(left, right, output, overwrite, NativeFast);
    value {{ () }}
}}
resource fn forward({header}) -> Unit {{
    call multiply(m, k, n, u, v, w, bu, bv, bw, left, right, output) -> ();
    value {{ () }}
}}
resource fn main() -> Int {{
    let m: Nat = value {{ {m} }};
    let k: Nat = value {{ {k} }};
    let n: Nat = value {{ {n} }};
    let lda: Nat = value {{ m + {pad} }};
    let ldb: Nat = value {{ k + {pad} }};
    let ldc: Nat = value {{ m + {pad} }};
    let cap_a: Nat = value {{ lda * k }};
    let cap_b: Nat = value {{ ldb * n }};
    let cap_c: Nat = value {{ ldc * n }};
    runtime_space u = linear(profiles::{profile}, m);
    runtime_space v = linear(profiles::{profile}, k);
    runtime_space w = linear(profiles::{profile}, n);
    runtime_basis bu = basis(u);
    runtime_basis bv = basis(v);
    runtime_basis bw = basis(w);
    runtime_allocate data_a: {scalar}[cap_a] runtime_layout(m, k, lda, false);
    runtime_allocate data_b: {scalar}[cap_b] runtime_layout(k, n, ldb, false);
    runtime_allocate data_c: {scalar}[cap_c] runtime_layout(m, n, ldc, false);
    runtime_borrow init_a = write(data_a);
    runtime_fill(init_a, {left});
    runtime_release(init_a);
    runtime_borrow init_b = write(data_b);
    runtime_fill(init_b, {right});
    runtime_release(init_b);
    runtime_borrow a = read(data_a);
    runtime_borrow b = read(data_b);
    runtime_borrow c = write(data_c);
    runtime_map left = view(a, bv, bu);
    runtime_map right = view(b, bw, bv);
    runtime_map output = view(c, bw, bu);
    call forward(m, k, n, u, v, w, bu, bv, bw, left, right, output) -> ();
    runtime_release(c);
    runtime_borrow checked = read(data_c);
    {checked}
    runtime_release(checked);
    runtime_release(b);
    runtime_release(a);
    runtime_move data_a -> moved_a;
    runtime_drop(moved_a);
    runtime_drop(data_b);
    runtime_drop(data_c);
    value {{ 42 }}
}}
"#,
        left = literal(1.0, 1.0),
        right = literal(2.0, -1.0),
    )
}

fn fixture(source: &str) -> Scratch {
    let scratch = Scratch::empty("runtime shapes");
    scratch.write(
        "Vastitas.toml",
        "[package]\nname = \"runtime_shapes\"\nversion = \"0.1.0\"\nroot = \"src/main.vast\"\n",
    );
    scratch.write("src/main.vast", source);
    scratch.write("src/profiles/mod.vast", PROFILES);
    scratch
}

fn repeated_runtime_extents(complex: bool) -> String {
    let mut source = source(complex, 2, 3, 2, 1)
        .replace(
            "resource fn main() -> Int",
            "resource fn run(m: Nat, k: Nat, n: Nat, pad: Nat) -> Unit",
        )
        .replace("    let m: Nat = value { 2 };\n", "")
        .replace("    let k: Nat = value { 3 };\n", "")
        .replace("    let n: Nat = value { 2 };\n", "")
        .replace("value { m + 1 }", "value { m + pad }")
        .replace("value { k + 1 }", "value { k + pad }")
        .replace("value { 42 }", "value { () }");
    let call = "call forward(m, k, n, u, v, w, bu, bv, bw, left, right, output) -> ();";
    source = source.replace(call, &format!("{call}\n    {call}"));
    source.push_str(
        r#"
resource fn main() -> Int {
    let m1: Nat = value { 2 };
    let m2: Nat = value { m1 + 1 };
    let k: Nat = value { 3 };
    let n1: Nat = value { 2 };
    let n2: Nat = value { n1 + 2 };
    let p1: Nat = value { 1 };
    let p2: Nat = value { p1 + 1 };
    call run(m1, k, n1, p1) -> ();
    call run(m2, k, n2, p2) -> ();
    value { 42 }
}
"#,
    );
    source
}

fn transposed_accumulate(complex: bool) -> String {
    let literal = |real: f64, imaginary: f64| {
        if complex {
            format!("complex_bits({}, {})", bits(real), bits(imaginary))
        } else {
            format!("f64_bits({})", bits(real))
        }
    };
    let expected = if complex {
        literal(21.0, 6.0)
    } else {
        literal(15.0, 0.0)
    };
    let original = if complex {
        literal(9.0, 3.0)
    } else {
        literal(6.0, 0.0)
    };
    source(complex, 2, 3, 2, 1)
        .replace("let lda: Nat = value { m + 1 };", "let lda: Nat = value { k + 1 };")
        .replace("let cap_a: Nat = value { lda * k };", "let cap_a: Nat = value { lda * m };")
        .replace("runtime_layout(m, k, lda, false)", "runtime_layout(k, m, lda, true)")
        .replace("RuntimeMap<bw, bu, write> initializes", "RuntimeMap<bw, bu, read_write>")
        .replace(
            "runtime_borrow c = write(data_c);",
            &format!(
                "runtime_borrow init_c = write(data_c);\nruntime_fill(init_c, {});\nruntime_release(init_c);\nruntime_borrow c = read_write(data_c);",
                literal(1.0, 0.0),
            ),
        )
        .replace("overwrite, NativeFast)", &format!("accumulate, NativeFast, alpha={}, beta={})", literal(2.0, 0.0), literal(3.0, 0.0)))
        .replace(&original, &expected)
}

fn command(scratch: &Scratch, mode: &str) -> Command {
    let mut command = cli();
    command
        .args([mode, "--manifest-path"])
        .arg(scratch.0.join("Vastitas.toml"));
    command
}

fn request(scratch: &Scratch) -> Value {
    common::captured_wire(command(scratch, "check"), 8)
}

fn functions(raw: &Value) -> &Value {
    &raw["packages"][0]["modules"][0]["resource_functions"]
}

fn functions_mut(raw: &mut Value) -> &mut Value {
    &mut raw["packages"][0]["modules"][0]["resource_functions"]
}

#[track_caller]
fn rejected(source: &str, code: &str) -> String {
    let result = command(&fixture(source), "check").output().unwrap();
    assert!(
        !result.status.success(),
        "accepted invalid source: {source}"
    );
    common::expect_code(&result, code)
}

const LITERAL_SHAPES: &str = "mod profiles;
resource fn main() -> Int {
    runtime_space u = linear(profiles::RealSmooth, 2);
    runtime_basis bu = basis(u);
    runtime_allocate data: F64[4] runtime_layout(2, 2, 2, false);
    runtime_borrow w = write(data);
    runtime_map m = view(w, bu, bu);
    runtime_fill(w, f64_bits(4607182418800017408));
    runtime_release(w);
    runtime_borrow r = read(data);
    runtime_expect(r, 1, 1, f64_bits(4607182418800017408));
    runtime_release(r);
    runtime_drop(data);
    value { 0 }
}";

#[test]
fn literal_runtime_guards_reject_contradictions_and_erase_true_checks() {
    let s = fixture(LITERAL_SHAPES);
    success(&command(&s, "check").output().unwrap());
    let raw = request(&s);
    let response = kernel(&raw, "emit");
    assert_eq!(response["ok"], true, "{response}");
    let emitted = response["lean_source"].as_str().unwrap();
    assert!(!emitted.contains("runtimeLayoutValid"), "{emitted}");
    assert!(!emitted.contains("E_RUNTIME_GUARD:"), "{emitted}");
    let output = s.0.join("literal-shapes");
    success(
        &command(&s, "build")
            .arg("-o")
            .arg(&output)
            .output()
            .unwrap(),
    );
    let result = Command::new(output).output().unwrap();
    success(&result);
    assert_eq!(result.stdout, b"0\n");

    for invalid in [
        LITERAL_SHAPES.replace("RealSmooth, 2)", "RealSmooth, 3)"),
        LITERAL_SHAPES.replace("RealSmooth, 2)", "RealSmooth, 2147483648)"),
        LITERAL_SHAPES.replace("F64[4]", "F64[3]"),
        LITERAL_SHAPES.replace("runtime_layout(2, 2, 2", "runtime_layout(2, 2, 1"),
        LITERAL_SHAPES.replace("runtime_expect(r, 1, 1", "runtime_expect(r, 2, 1"),
        format!(
            "{}\nfn main() -> Int {{ 0 }}",
            LITERAL_SHAPES
                .replace("resource fn main", "resource fn unused")
                .replace("RealSmooth, 2)", "RealSmooth, 3)")
        ),
        "mod profiles;
         resource fn consume(u: RuntimeSpace<profiles::RealSmooth, 3>) -> Unit { value { () } }
         resource fn main() -> Int {
             runtime_space u = linear(profiles::RealSmooth, 2);
             call consume(u) -> ();
             value { 0 }
         }"
        .to_string(),
    ] {
        let result = command(&fixture(&invalid), "check").output().unwrap();
        assert!(!result.status.success(), "{invalid}");
        let error = String::from_utf8_lossy(&result.stderr);
        common::assert_first_code(&error, "E_RUNTIME_GUARD");
        assert!(error.contains("main.vast:"), "{error}");
    }
    // The kernel independently rechecks literal map dimensions in raw wire IR.
    let mut changed = raw;
    let space = &mut functions_mut(&mut changed)[0]["body"][0]["operation"];
    assert_eq!(space["op"], "space");
    space["dimension"] = json!({"kind":"literal","value":3});
    let response = kernel(changed, "emit");
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(response["diagnostics"][0]["code"], "E_RUNTIME_GUARD");
    assert!(response.get("lean_source").is_none());
}

/// A condition in which every extent is a literal is decided when the program
/// is checked, and one that fails is reported at its statement (#704): the
/// statement that allocates, reads a cell, declares a space, presents a map or
/// calls. The enclosing function is named in a note only.
#[test]
fn a_false_literal_guard_is_reported_at_its_statement() {
    const PHYSICAL: &str = "E_RUNTIME_GUARD: literal runtime extent, layout or cell guard is false";
    const NOMINAL: &str =
        "E_RUNTIME_GUARD: literal runtime space, map or call dimension guard is false";
    let issue = "resource fn main() -> Int {
    let k: Int = value { 1 };
    runtime_allocate d: F64[2] runtime_layout(2, 2, 2, false);
    runtime_drop(d);
    value { 42 }
}";
    let unused = format!(
        "{}\nfn main() -> Int {{ 0 }}",
        LITERAL_SHAPES
            .replace("resource fn main", "resource fn unused")
            .replace("F64[4]", "F64[3]")
    );
    let call = "mod profiles;
resource fn consume(u: RuntimeSpace<profiles::RealSmooth, 3>) -> Unit { value { () } }
resource fn main() -> Int {
    runtime_space u = linear(profiles::RealSmooth, 2);
    call consume(u) -> ();
    value { 0 }
}";
    for (source, place, message) in [
        (issue.to_string(), "3:5", PHYSICAL),
        (LITERAL_SHAPES.replace("F64[4]", "F64[3]"), "5:5", PHYSICAL),
        (
            LITERAL_SHAPES.replace("runtime_layout(2, 2, 2", "runtime_layout(2, 2, 1"),
            "5:5",
            PHYSICAL,
        ),
        (
            LITERAL_SHAPES.replace("runtime_expect(r, 1, 1", "runtime_expect(r, 2, 1"),
            "11:5",
            PHYSICAL,
        ),
        (unused, "5:5", PHYSICAL),
        (
            LITERAL_SHAPES.replace("RealSmooth, 2)", "RealSmooth, 2147483648)"),
            "3:5",
            NOMINAL,
        ),
        (
            LITERAL_SHAPES.replace("RealSmooth, 2)", "RealSmooth, 3)"),
            "7:5",
            NOMINAL,
        ),
        (call.to_string(), "5:5", NOMINAL),
    ] {
        let error = rejected(&source, "E_RUNTIME_GUARD");
        let first = error.lines().next().unwrap();
        assert!(
            first.ends_with(&format!("src/main.vast:{place}: {message}")),
            "{source}\n{error}"
        );
        // The old place, the `resource` keyword of the function, holds no
        // diagnostic. A note may still name the function there.
        assert_eq!(common::diagnostic_codes(&error).len(), 1, "{error}");
        for line in error.lines().skip(1) {
            assert!(line.contains(": note: "), "{error}");
        }
    }
}

#[test]
fn parser_preserves_runtime_slots_whole_layouts_access_and_both_arms() {
    let source = source(false, 2, 3, 2, 1).replace(
        "value { 42 }",
        "let flag: Bool = value { true };\nif flag { runtime_space branch_a = linear(profiles::RealSmooth, m); } else { runtime_space branch_b = linear(profiles::RealSmooth, 7); }\nvalue { 42 }",
    );
    let raw = request(&fixture(&source));
    let parsed = functions(&raw);
    assert_eq!(raw["version"], 8);
    assert_eq!(parsed[0]["parameters"][3]["kind"], "runtime_space");
    assert_eq!(
        parsed[0]["parameters"][3]["dimension"],
        json!({"kind":"slot","name":"m"})
    );
    assert_eq!(parsed[0]["parameters"][6]["kind"], "runtime_basis");
    assert_eq!(parsed[0]["parameters"][9]["kind"], "runtime_map");
    assert_eq!(parsed[0]["parameters"][11]["access"], "write");
    assert_eq!(parsed[0]["parameters"][11]["initializes"], true);
    let body = parsed[2]["body"].as_array().unwrap();
    let allocation = body
        .iter()
        .find(|s| s["action"]["op"] == "allocate")
        .unwrap();
    assert_eq!(allocation["kind"], "runtime");
    assert_eq!(
        allocation["action"]["elements"],
        json!({"kind":"slot","name":"cap_a"})
    );
    assert_eq!(allocation["action"]["layout"].as_object().unwrap().len(), 4);
    assert_eq!(
        allocation["action"]["layout"]["leading"],
        json!({"kind":"slot","name":"lda"})
    );
    let branch = body.iter().find(|s| s["kind"] == "branch_value").unwrap();
    assert_eq!(
        branch["yes"][0]["operation"]["dimension"],
        json!({"kind":"slot","name":"m"})
    );
    assert_eq!(
        branch["no"][0]["operation"]["dimension"],
        json!({"kind":"literal","value":7})
    );
    let extended = source
        .replace(
            "output: RuntimeMap<bw, bu, write> initializes",
            "output: RuntimeMap<bw, bu, read_write>",
        )
        .replace(
            "overwrite, NativeFast)",
            "accumulate, NativeFast, alpha=f64_bits(4607182418800017408), beta=coefficient(other))",
        );
    let extended = request(&fixture(&extended));
    assert_eq!(
        functions(&extended)[0]["parameters"][11]["access"],
        "read_write"
    );
    assert_eq!(
        functions(&extended)[0]["body"][0]["operation"]["beta"],
        json!({"kind":"loan","loan":"other"})
    );
}

#[test]
fn source_rejects_implicit_layouts_inline_extent_arithmetic_and_duplicate_coefficients() {
    let good = source(false, 2, 3, 2, 1);
    // Each case names its exact code and diagnostic, so an unrelated parse
    // error from a drifted replacement cannot satisfy it.
    for (from, to, code, message) in [
        (
            "runtime_layout(m, k, lda, false)",
            "runtime_layout(0, m, k, lda, false)",
            "E_RESOURCE_TYPE",
            "requires a literal condition",
        ),
        (
            "runtime_borrow a = read(data_a)",
            "runtime_borrow a = read(data_a, runtime_layout(m, k, lda, false))",
            "E_PARSE",
            "expected `)`, found `,`",
        ),
        (
            "F64[cap_a]",
            "F64[lda * k]",
            "E_PARSE",
            "expected `]`, found `*`",
        ),
        (
            "runtime_layout(m, k, lda, false)",
            "runtime_layout(m, k, lda, flag)",
            "E_RESOURCE_TYPE",
            "requires a literal condition",
        ),
        (
            "overwrite, NativeFast)",
            "overwrite, NativeFast, alpha=f64_bits(0), alpha=f64_bits(0))",
            "E_DUPLICATE",
            "",
        ),
        (
            "RealSmooth, m>",
            "RealSmooth, 18446744073709551616>",
            "E_RESOURCE_LIMIT",
            "exceeds 64 bits",
        ),
    ] {
        let error = rejected(&common::checked_replace(&good, from, to), code);
        assert!(error.contains(message), "{error}");
    }
}

#[test]
fn checker_preserves_runtime_call_identity_permissions_and_static_separation() {
    let good = source(false, 2, 3, 2, 1);
    success(&command(&fixture(&good), "check").output().unwrap());
    for (bad, code) in [
        (good.replace("view(b, bw, bv)", "view(b, bu, bv)"), "E_RUNTIME_CALL"),
        (good.replace("runtime_release(c);", "runtime_release(c);\ncall forward(m, k, n, u, v, w, bu, bv, bw, left, right, output) -> ();"), "E_RUNTIME_CALL"),
        (good.replace("runtime_fill(init_a, f64_bits(4607182418800017408));", ""), "E_RUNTIME_SHAPE"),
        (good.replace("runtime_borrow a = read(data_a)", "borrow a = read(data_a)"), "E_RUNTIME_TYPE"),
        (good.replace("runtime_drop(moved_a)", "runtime_drop(data_a)"), "E_RUNTIME_SHAPE"),
        (good.replace("let m: Nat = value { 2 };", "let m: Bool = value { true };"), "E_RUNTIME_EXTENT"),
        (good.replace("call forward(m, k, n, u, v, w, bu, bv, bw, left, right, output) -> ();", "if true { call forward(m, k, n, u, v, w, bu, bv, bw, left, right, output) -> (); } else {}"), "E_RUNTIME_BRANCH"),
    ] {
        assert_ne!(bad, good, "ineffective mutation for {code}");
        rejected(&bad, code);
    }
    let hidden = r#"
resource fn leaf(n: Nat) -> Unit {
    runtime_allocate data: F64[n] runtime_layout(n, 1, n, false);
    runtime_drop(data);
    value { () }
}

resource fn middle(n: Nat) -> Unit { call leaf(n) -> (); value { () } }
resource fn main() -> Int {
    let n: Nat = value { 2 };
    if true { call middle(n) -> (); } else {}
    value { 42 }
}
"#;
    let output = command(&fixture(hidden), "check").output().unwrap();
    assert!(!output.status.success());
    common::expect_code(&output, "E_RUNTIME_BRANCH");
}

#[test]
fn emitted_calls_use_runtime_extents_and_reuse_each_callers_destination() {
    for complex in [false, true] {
        let scratch = fixture(&repeated_runtime_extents(complex));
        success(&command(&scratch, "check").output().unwrap());
        let raw = request(&scratch);
        let response = kernel(&raw, "emit");
        assert_eq!(response["ok"], true, "{response}");
        let emitted = response["lean_source"].as_str().unwrap();
        let products: Vec<_> = emitted
            .lines()
            .filter(|line| line.trim_start().starts_with("VastitasGemmNative.gemm "))
            .collect();
        // Resource calls still expand at their static call sites. Every product
        // uses the same generic runtime ABI with scalar-slot extents.
        assert_eq!(products.len(), 4);
        assert!(products.iter().all(|line| line.contains("runtimeExtent_")));
        assert_eq!(products[0], products[1]);
        assert_eq!(products[2], products[3]);
        assert_eq!(emitted.matches("allocate shapeArena ").count(), 6);
    }
}

#[test]
fn kernel_rejects_forged_runtime_metadata_and_old_protocol_envelopes() {
    let raw = request(&fixture(&source(false, 2, 3, 2, 1)));
    assert_eq!(kernel(&raw, "check")["ok"], true);
    let mut forged = raw.clone();
    let body = functions_mut(&mut forged)[2]["body"]
        .as_array_mut()
        .unwrap();
    let allocation = body
        .iter_mut()
        .find(|s| s["action"]["op"] == "allocate")
        .unwrap();
    allocation["action"]["layout"]["offset"] = json!(8);
    common::assert_wire_rejected(&kernel(&forged, "check"), "E_PROTOCOL");
    let mut forged = raw.clone();
    functions_mut(&mut forged)[0]["parameters"][3]["dimension"] =
        json!({"kind":"slot","name":"missing"});
    common::assert_wire_rejected(&kernel(&forged, "check"), "E_RESOURCE_NAME");
    let mut forged = raw.clone();
    functions_mut(&mut forged)[0]["body"][0]["operation"]["alpha"] =
        json!({"kind":"loan","loan":"left"});
    common::assert_wire_rejected(&kernel(&forged, "check"), "E_RUNTIME_COEFFICIENT");
    for version in 2..8 {
        let mut legacy = raw.clone();
        legacy["version"] = json!(version);
        common::assert_wire_rejected(&kernel(&legacy, "check"), "E_PROTOCOL");
    }
}

#[test]
#[ignore = "requires pinned sequential LP64 OpenBLAS"]
fn runtime_native_executes_caller_shapes_padding_empty_axes_and_preflight_failure() {
    let prefix = std::env::var("VASTITAS_TEST_OPENBLAS_PREFIX").expect("OpenBLAS prefix");
    let cc = std::env::var("VASTITAS_TEST_NATIVE_CC").unwrap_or_else(|_| "cc".into());
    let mut positive = Vec::new();
    for complex in [false, true] {
        for (m, k, n, pad) in [
            (2, 3, 2, 0),
            (2, 3, 2, 2),
            (0, 3, 2, 1),
            (2, 0, 2, 1),
            (2, 3, 0, 1),
        ] {
            positive.push(source(complex, m, k, n, pad));
        }
    }
    positive.push(source(false, 2, 3, 2, 1).replace(": Nat", ": Int"));
    positive.push(repeated_runtime_extents(false));
    positive.push(repeated_runtime_extents(true));
    positive.push(transposed_accumulate(false));
    positive.push(transposed_accumulate(true));
    for (flag, m) in [(true, 2), (false, 3)] {
        positive.push(format!(
            "resource fn choose_extent(flag: Bool) -> Nat {{ value {{ if flag {{ 2 }} else {{ 3 }} }} }}\n{}",
            source(false, m, 3, 2, 1).replace(
                &format!("let m: Nat = value {{ {m} }};"),
                &format!("let flag: Bool = value {{ {flag} }};\nlet m: Nat = call choose_extent(flag) -> ();"),
            )
        ));
    }
    for source in positive {
        let scratch = fixture(&source);
        success(&command(&scratch, "check").output().unwrap());
        let program = scratch.0.join("program");
        success(
            &command(&scratch, "build")
                .args(["--openblas-prefix", &prefix, "--native-cc", &cc, "-o"])
                .arg(&program)
                .output()
                .unwrap(),
        );
        let output = Command::new(&program).output().unwrap();
        success(&output);
        assert_eq!(String::from_utf8(output.stdout).unwrap().trim(), "42");
    }
    // Each invalid caller shape must stop in physical preflight, before any
    // write. A missing preflight would let GEMM write with the wrong shape and
    // fail later in runtime_expect with E_NATIVE_EXPECT, so that code is refused.
    let valid = source(false, 2, 3, 2, 0);
    let padded = source(false, 2, 3, 2, 1);
    for (source, code) in [
        (
            common::checked_replace(&valid, "value { m + 0 }", "value { 1 }"),
            "E_RUNTIME_GUARD",
        ),
        (
            common::checked_replace(&valid, "value { lda * k }", "value { 0 }"),
            "E_RUNTIME_GUARD",
        ),
        (
            common::checked_replace(&valid, "value { 2 };", "value { 18446744073709551616 };"),
            "E_RUNTIME_EXTENT",
        ),
        (
            common::checked_replace(
                &padded.replace(": Nat", ": Int"),
                "let m: Int = value { 2 };",
                "let m: Int = value { -1 };",
            ),
            "E_RUNTIME_EXTENT",
        ),
        (
            common::checked_replace(
                &padded,
                "call forward(m, k, n, u, v, w, bu, bv, bw, left, right, output) -> ();",
                "let wrong_m: Nat = value { m + 1 };\ncall forward(wrong_m, k, n, u, v, w, bu, bv, bw, left, right, output) -> ();",
            ),
            "E_RUNTIME_GUARD",
        ),
    ] {
        let scratch = fixture(&source);
        let program = scratch.0.join("invalid-runtime");
        success(
            &command(&scratch, "build")
                .args(["--openblas-prefix", &prefix, "--native-cc", &cc, "-o"])
                .arg(&program)
                .output()
                .unwrap(),
        );
        let output = Command::new(program).output().unwrap();
        assert!(output.stdout.is_empty(), "{output:?}");
        let error = common::expect_code(&output, code);
        assert!(
            !common::diagnostic_codes(&error).contains(&"E_NATIVE_EXPECT".to_string()),
            "a write happened before the shape failure: {error}"
        );
    }
}

#[test]
fn runtime_storage_keeps_the_normal_build_free_of_blas() {
    let scratch = fixture(
        r#"
resource fn allocate_and_read(n: Nat) -> Unit {
    runtime_allocate data: F64[n] runtime_layout(n, 1, n, false);
    runtime_borrow output = write(data);
    runtime_fill(output, f64_bits(4607182418800017408));
    runtime_release(output);
    runtime_borrow input = read(data);
    runtime_expect(input, 0, 0, f64_bits(4607182418800017408));
    runtime_release(input);
    runtime_drop(data);
    value { () }
}
resource fn main() -> Int {
    let n: Nat = value { 2 + 1 };
    call allocate_and_read(n) -> ();
    value { 42 }
}
"#,
    );
    let response = kernel(request(&scratch), "emit");
    assert_eq!(response["ok"], true, "{response}");
    assert_eq!(response["numerical_runtime"], false);
    let source = response["lean_source"].as_str().unwrap();
    assert!(!source.contains("VastitasGemmNative"));
    let program = scratch.0.join("storage-only");
    success(
        &command(&scratch, "build")
            .arg("-o")
            .arg(&program)
            .output()
            .unwrap(),
    );
    let output = Command::new(program).output().unwrap();
    success(&output);
    assert_eq!(String::from_utf8(output.stdout).unwrap().trim(), "42");
}
