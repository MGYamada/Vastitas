//! Source → diagnostic-code and forged-wire regressions for the v0.1.0-alpha
//! kernel review (#534, #535, #553, #562, #563). Every case runs the actual
//! frontend and kernel; captured requests are mutated only to forge inputs that
//! the frontend never emits.
mod common;
use common::{Scratch, cli, kernel, kernel_path, root, success};
use serde_json::{Value, json};
use std::io::Write;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

fn package(source: &str) -> Scratch {
    let scratch = Scratch::empty("kernel review");
    scratch.write(
        "Vastitas.toml",
        "[package]\nname = \"review\"\nversion = \"0.1.0\"\nroot = \"src/main.vast\"\n",
    );
    scratch.write("src/main.vast", source);
    scratch
}

fn manifest(scratch: &Scratch) -> PathBuf {
    scratch.0.join("Vastitas.toml")
}

fn check(scratch: &Scratch) -> Output {
    cli()
        .args(["check", "--manifest-path"])
        .arg(manifest(scratch))
        .output()
        .unwrap()
}

fn rejection(scratch: &Scratch, code: &str) -> String {
    let output = check(scratch);
    let message = String::from_utf8(output.stderr).unwrap();
    assert!(!output.status.success(), "unexpected acceptance");
    assert!(message.contains(&format!(": {code}: ")), "{message}");
    message
}

fn location(source: &str, marker: &str) -> String {
    let before = &source[..source.find(marker).unwrap()];
    let line = before.bytes().filter(|&byte| byte == b'\n').count() + 1;
    let column = before.rsplit('\n').next().unwrap().chars().count() + 1;
    format!("main.vast:{line}:{column}")
}

fn assert_primary(message: &str, source: &str, marker: &str, code: &str) {
    let expected = format!("{}: {code}: ", location(source, marker));
    assert!(
        message.lines().next().unwrap().contains(&expected),
        "missing {expected}\n{message}"
    );
}

fn assert_note(message: &str, source: &str, marker: &str, note: &str) {
    let expected = format!("{}: note: {note}", location(source, marker));
    assert!(message.contains(&expected), "missing {expected}\n{message}");
}

/// Capture the frontend's actual request for a manifest without running the
/// kernel; the stub has no acceptance authority.
fn captured(manifest: &std::path::Path) -> Value {
    let scratch = Scratch::empty("kernel review capture");
    let wire = scratch.0.join("wire.json");
    let backend = scratch.write(
        "capture",
        &format!(
            "#!/bin/sh\ncat > '{}'\nprintf '%s\\n' '{{\"version\":9,\"ok\":false,\"diagnostics\":[{{\"code\":\"E_CAPTURED\",\"message\":\"captured\"}}]}}'\nexit 1\n",
            wire.display()
        ),
    );
    std::fs::set_permissions(&backend, std::fs::Permissions::from_mode(0o755)).unwrap();
    let output = cli()
        .env("VASTITAS_KERNEL", &backend)
        .args(["check", "--manifest-path"])
        .arg(manifest)
        .output()
        .unwrap();
    assert!(String::from_utf8_lossy(&output.stderr).contains("E_CAPTURED"));
    serde_json::from_slice(&std::fs::read(wire).unwrap()).unwrap()
}

/// Send raw bytes, as a tampered or truncated request would arrive.
fn raw_kernel(input: Vec<u8>) -> Value {
    let mut child = Command::new(kernel_path())
        .arg("check")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let writer = std::thread::spawn(move || stdin.write_all(&input));
    let output = child.wait_with_output().unwrap();
    writer.join().unwrap().unwrap();
    // Exit status 1 with a JSON answer, never an abort or signal.
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    serde_json::from_slice(&output.stdout).unwrap()
}

fn assert_protocol(response: &Value, fragment: &str) {
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(
        response["diagnostics"][0]["code"], "E_PROTOCOL",
        "{response}"
    );
    let message = response["diagnostics"][0]["message"].as_str().unwrap();
    assert!(message.contains(fragment), "{response}");
}

#[test]
fn function_exit_escape_names_each_leaked_owner_and_loan() {
    // #534: the primary span stays at the value block; notes name the owners.
    let one = "resource fn main() -> Int {\n    allocate data: F64[1];\n    value { 0 }\n}";
    let message = rejection(&package(one), "E_RESOURCE_ESCAPE");
    assert_primary(&message, one, "{ 0 }", "E_RESOURCE_ESCAPE");
    assert_note(
        &message,
        one,
        "allocate data",
        "leaked owner is `data`, introduced here",
    );

    let two = "resource fn main() -> Int {\n    allocate data: F64[1];\n    allocate other: F64[2];\n    allocate kept: F64[1];\n    drop(kept);\n    value { 0 }\n}";
    let message = rejection(&package(two), "E_RESOURCE_ESCAPE");
    for name in ["data", "other"] {
        assert_note(
            &message,
            two,
            &format!("allocate {name}"),
            &format!("leaked owner is `{name}`, introduced here"),
        );
    }
    assert!(!message.contains("`kept`"), "{message}");

    let loan = "resource fn main() -> Int {\n    allocate data: F64[4];\n    borrow w = write(data, layout(0, 2, 2, 2, false));\n    value { 0 }\n}";
    let message = rejection(&package(loan), "E_RESOURCE_ESCAPE");
    assert_note(
        &message,
        loan,
        "borrow w",
        "escaping loan is `w`, introduced here",
    );

    // A leaked callee owner is named in the callee.
    let nested = "resource fn helper() -> Unit {\n    allocate hidden: F64[1];\n    value { () }\n}\nresource fn main() -> Int {\n    call helper() -> ();\n    value { 0 }\n}";
    let message = rejection(&package(nested), "E_RESOURCE_ESCAPE");
    assert_note(
        &message,
        nested,
        "allocate hidden",
        "leaked owner is `hidden`, introduced here",
    );
}

#[test]
fn layout_rejection_names_the_failing_condition() {
    // #535: one case per condition reachable from source.
    for (layout, reason) in [
        (
            "8, 2, 2, 2, false",
            "view ends at byte 40, but the allocation has 32 bytes (4 elements of 8 bytes)",
        ),
        (
            "40, 0, 0, 1, false",
            "view offset 40 is beyond the allocation's 32 bytes",
        ),
        (
            "4, 1, 1, 1, false",
            "view offset 4 is not aligned to 8-byte elements",
        ),
        (
            "0, 2, 2, 1, false",
            "leading 1 is smaller than max(1, rows 2)",
        ),
        (
            "0, 2147483648, 0, 2147483648, false",
            "rows 2147483648 exceed the native limit 2^31 - 1",
        ),
        (
            "0, 1, 2147483648, 1, false",
            "columns 2147483648 exceed the native limit 2^31 - 1",
        ),
        (
            "0, 1, 1, 2147483648, false",
            "leading 2147483648 exceeds the native limit 2^31 - 1",
        ),
    ] {
        let source = format!(
            "resource fn main() -> Int {{\n    allocate data: F64[4];\n    borrow w = write(data, layout({layout}));\n    release(w);\n    drop(data);\n    value {{ 0 }}\n}}"
        );
        let message = rejection(&package(&source), "E_RESOURCE_LAYOUT");
        assert_primary(&message, &source, "borrow w", "E_RESOURCE_LAYOUT");
        assert!(
            message.contains(&format!("invalid layout: {reason}")),
            "{layout}: {message}"
        );
        assert_note(
            &message,
            &source,
            "allocate data",
            "borrowed allocation is `data`, introduced here",
        );
    }
}

#[test]
fn wire_numbers_duplicate_keys_nesting_and_encoding_fail_closed() {
    // #562.1/2: answered with E_PROTOCOL JSON before `Json.parse`.
    for input in [r#"{"version":1e1000000000}"#, r#"{"version":1e400}"#] {
        assert_protocol(&raw_kernel(input.into()), "exponent exceeds 2 digits");
    }
    assert_protocol(
        &raw_kernel(format!("{{\"version\":{}}}", "9".repeat(65)).into()),
        "significant digits",
    );
    for input in [
        r#"{"version":2,"version":9}"#,
        r#"{"version":9,"version":2}"#,
        r#"{"version":9,"version":2}"#,
    ] {
        assert_protocol(
            &raw_kernel(input.into()),
            "duplicate JSON object key 'version'",
        );
    }
    let deep = format!("{}{}", "[".repeat(20000), "]".repeat(20000));
    assert_protocol(
        &raw_kernel(deep.into()),
        "JSON nesting exceeds 16384 levels",
    );
    assert_protocol(&raw_kernel(vec![0xff, 0xfe]), "invalid UTF-8");

    // A nested duplicate inside an otherwise accepted actual request.
    let source = "fn main() -> Int { 1 }";
    let request = common::request(source, "duplicate.vast");
    assert_eq!(kernel(&request, "check")["ok"], true);
    let text = serde_json::to_string(&request).unwrap();
    let forged = text.replacen(
        "\"name\":\"main\"",
        "\"name\":\"main\",\"name\":\"other\"",
        1,
    );
    assert_ne!(forged, text);
    assert_protocol(
        &raw_kernel(forged.into()),
        "duplicate JSON object key 'name'",
    );
}

#[test]
fn gram_entries_and_literals_require_plain_decimal_digits() {
    // #562.3: `_` separators are rejected; the unmodified request is accepted.
    let manifest = root().join("examples/packages/diagonal-metrics/Vastitas.toml");
    let raw = captured(&manifest);
    assert_eq!(kernel(&raw, "check")["ok"], true);
    for entry in ["2_0", "-4_0", "+2", "", "-"] {
        let mut forged = raw.clone();
        let mut changed = false;
        for module in forged["packages"][0]["modules"].as_array_mut().unwrap() {
            for function in module["resource_functions"]
                .as_array_mut()
                .into_iter()
                .flatten()
            {
                for statement in function["body"].as_array_mut().unwrap() {
                    if statement["operation"]["gram"]["kind"] == "diagonal" && !changed {
                        statement["operation"]["gram"]["entries"][0] = json!(entry);
                        changed = true;
                    }
                }
            }
        }
        assert!(changed);
        let response = kernel(&forged, "check");
        assert_eq!(
            response["diagnostics"][0]["code"], "E_PROTOCOL",
            "{entry}: {response}"
        );
    }
    let mut literal = common::request("fn main() -> Int { 1000 }", "literal.vast");
    literal["functions"][0]["body"]["result"]["value"] = json!("1_000");
    assert_eq!(
        kernel(&literal, "check")["diagnostics"][0]["code"],
        "E_LITERAL"
    );
}

const BASE: &str = r#"
pub generic choose(x, y) { domain (Int, Int), (Bool, Bool); }
method choose(x: Any, y: Any) -> Int { 0 }
pub fn helper(x: Int) -> Int { x }
pub grant outer : choose to addon delegable { domain (Int, Int); }
pub transfer handoff : choose to addon;
"#;
const ADDON: &str = r#"
pub delegation inner : base::choose to addon::ops { domain (Int, Int); }
pub contribution fresh : base::choose { method base::choose(x: Bool, y: Bool) -> Int { 2 } }
pub mod ops {
  pub contribution sum : base::choose { method base::choose(x: Int, y: Int) -> Int { x + y } }
}
"#;
const EVENTS: &str = "borrow base::outer as parent; reborrow parent via addon::inner as child; apply addon::ops::sum using child; return child; return parent; transfer base::handoff; apply addon::fresh; seal base::choose;";

fn authority(base: &str, addon: &str, events: &str) -> Scratch {
    let s = Scratch::empty("kernel review authority");
    for (name, source, dependencies) in [
        ("base", base.to_owned(), ""),
        ("addon", addon.to_owned(), "base={path='../base'}"),
        (
            "app",
            format!(
                "assembly {{ {events} }} fn main() -> Int {{ base::choose(40, 2) + base::choose(true, true) }}"
            ),
            "base={path='../base'}\naddon={path='../addon'}",
        ),
    ] {
        s.write(
            &format!("{name}/Vastitas.toml"),
            &format!(
                "[package]\nname='{name}'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\n{dependencies}\n"
            ),
        );
        s.write(&format!("{name}/main.vast"), &source);
    }
    s
}

/// Every string list under a declaration path field, by JSON pointer.
fn path_lists(value: &Value, pointer: String, out: &mut Vec<String>) {
    match value {
        Value::Object(fields) => {
            for (key, child) in fields {
                let next = format!("{pointer}/{key}");
                if ["target", "grant", "contribution", "path", "grantee_path"]
                    .contains(&key.as_str())
                    && child.as_array().is_some_and(|items| {
                        !items.is_empty() && items.iter().all(Value::is_string)
                    })
                {
                    out.push(next.clone());
                }
                path_lists(child, next, out);
            }
        }
        Value::Array(items) => {
            for (index, child) in items.iter().enumerate() {
                path_lists(child, format!("{pointer}/{index}"), out);
            }
        }
        _ => {}
    }
}

#[test]
fn edit_paths_resolve_component_wise() {
    // #562.4: a component containing `:` is never re-split into a path.
    let s = authority(BASE, ADDON, EVENTS);
    let raw = captured(&s.0.join("app/Vastitas.toml"));
    assert_eq!(kernel(&raw, "check")["ok"], true);
    let mut pointers = Vec::new();
    path_lists(&raw, String::new(), &mut pointers);
    let declarations = pointers
        .iter()
        .filter(|pointer| !pointer.contains("/indexed_declarations/"))
        .count();
    assert!(declarations >= 8, "{pointers:?}");
    for pointer in pointers {
        let mut forged = raw.clone();
        let list = forged.pointer_mut(&pointer).unwrap();
        let parts: Vec<String> = list
            .as_array()
            .unwrap()
            .iter()
            .map(|part| part.as_str().unwrap().to_owned())
            .collect();
        let joined = if parts.len() > 1 {
            parts.join("::")
        } else {
            format!("self::{}", parts[0])
        };
        *list = json!([joined]);
        let response = kernel(&forged, "check");
        assert_eq!(
            response["diagnostics"][0]["code"], "E_PROTOCOL",
            "{pointer}: {response}"
        );
        let mut split = raw.clone();
        *split.pointer_mut(&pointer).unwrap() = json!(["a:", ":b"]);
        assert_eq!(
            kernel(&split, "check")["diagnostics"][0]["code"],
            "E_PROTOCOL",
            "{pointer}"
        );
    }
}

#[test]
fn grants_and_delegations_require_a_generic_target() {
    // #563.1: an explicit kind check, not a failed generic lookup.
    let base = BASE.replace(
        "pub grant outer : choose to addon",
        "pub grant stray : helper to addon delegable { domain (Int, Int); }\npub grant outer : choose to addon",
    );
    let output = cli()
        .args(["check", "--manifest-path"])
        .arg(authority(&base, ADDON, EVENTS).0.join("app/Vastitas.toml"))
        .output()
        .unwrap();
    let message = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success());
    assert!(
        message.contains("E_TYPE: unexpected declaration kind in edit assembly"),
        "{message}"
    );
}

/// The largest let chain inside the deepest accepted nesting, as source.
fn nested_chain(depth: usize, lets: usize) -> String {
    let mut inner = String::from("let v0 = 1;\n");
    for index in 1..lets {
        inner.push_str(&format!("let v{index} = v{} + 1;\n", index - 1));
    }
    inner.push_str(&format!("v{}\n", lets - 1));
    for _ in 0..depth {
        inner = format!("if true {{\n{inner}}} else {{ 0 }}\n");
    }
    format!("fn main() -> Int {{\n{inner}}}\n")
}

#[test]
fn generated_code_at_the_source_check_bounds_builds() {
    // #563.3: 62 nested branches (the parser bound) and the longest chain that
    // still fits the 4096-unit body budget; one more let is rejected.
    let scratch = Scratch::empty("kernel review bounds");
    let accepted = scratch.write("bound.vast", &nested_chain(62, 3907));
    let over = scratch.write("over.vast", &nested_chain(62, 3908));
    let output = cli().arg("check").arg(&over).output().unwrap();
    assert!(String::from_utf8_lossy(&output.stderr).contains("E_LIMIT"));
    let program = scratch.0.join("bound program");
    success(
        &cli()
            .arg("build")
            .arg(&accepted)
            .arg("-o")
            .arg(&program)
            .output()
            .unwrap(),
    );
    let output = Command::new(&program).output().unwrap();
    success(&output);
    assert_eq!(output.stdout, b"3907\n");
}

/// Protocol-2 IR beyond the frontend's parser nesting: `depth` nested
/// branches around a chain of `lets` dependent lets.
fn nested_ir(depth: usize, lets: usize) -> Value {
    let span = json!({"start": 0, "end": 1, "line": 1, "column": 1});
    let integer =
        |value: usize| json!({"kind": "integer", "value": value.to_string(), "span": span});
    let variable = |name: String| json!({"kind": "variable", "name": name, "span": span});
    let mut statements = vec![
        json!({"kind": "let", "name": "v0", "annotation": null, "value": integer(1), "span": span}),
    ];
    for index in 1..lets {
        statements.push(
            json!({"kind": "let", "name": format!("v{index}"), "annotation": null,
            "value": {"kind": "binary", "op": "+", "left": variable(format!("v{}", index - 1)),
                "right": integer(1), "span": span}, "span": span}),
        );
    }
    let mut result = variable(format!("v{}", lets - 1));
    let mut inner = Some(statements);
    for _ in 0..depth {
        let then =
            json!({"statements": inner.take().unwrap_or_default(), "result": result, "span": span});
        result = json!({"kind": "if", "condition": {"kind": "boolean", "value": true, "span": span},
            "then_branch": then, "else_branch": {"statements": [], "result": integer(1), "span": span},
            "span": span});
    }
    json!({"version": 2, "file": "bounds.vast", "generics": [], "methods": [],
        "functions": [{"name": "main", "params": [], "return_type": {"kind": "named", "name": "Int"},
            "body": {"statements": inner.unwrap_or_default(), "result": result, "span": span},
            "span": span}]})
}

#[test]
fn generated_code_at_the_kernel_check_bounds_elaborates() {
    // #563.3: deeper nesting than the parser admits still elaborates with the
    // generated recursion and heartbeat options.
    assert_eq!(
        kernel(nested_ir(128, 3710), "check")["diagnostics"][0]["code"],
        "E_LIMIT"
    );
    let response = kernel(nested_ir(128, 3709), "emit");
    assert_eq!(response["ok"], true, "{response}");
    let scratch = Scratch::empty("kernel review elaboration");
    scratch.write("Bound.lean", response["lean_source"].as_str().unwrap());
    scratch.write(
        "lean-toolchain",
        &std::fs::read_to_string(root().join("lean-kernel/lean-toolchain")).unwrap(),
    );
    let output = Command::new("lean")
        .current_dir(&scratch.0)
        .env("LEAN_PATH", root().join("lean-kernel/.lake/build/lib/lean"))
        .arg("Bound.lean")
        .output()
        .unwrap();
    success(&output);
}

fn reborrow_chain(depth: usize) -> Scratch {
    let mut a = String::new();
    let mut b = String::new();
    for index in 1..=depth {
        let (module, to) = if index % 2 == 1 {
            (&mut a, "b")
        } else {
            (&mut b, "a")
        };
        module.push_str(&format!(
            "  pub delegation d{index} : super::choose to review::{to} delegable {{ domain (Int); }}\n"
        ));
    }
    let mut events = String::from("  borrow g0 as l0;\n");
    for index in 1..=depth {
        let module = if index % 2 == 1 { "a" } else { "b" };
        events.push_str(&format!(
            "  reborrow l{} via {module}::d{index} as l{index};\n",
            index - 1
        ));
    }
    for index in (0..=depth).rev() {
        events.push_str(&format!("  return l{index};\n"));
    }
    package(&format!(
        "pub generic choose(x) {{ domain (Int); }}\nmethod choose(x: Any) -> Int {{ 0 }}\npub grant g0 : choose to review::a delegable {{ domain (Int); }}\npub mod a {{\n{a}}}\npub mod b {{\n{b}}}\nassembly {{\n{events}  seal choose;\n}}\nfn main() -> Int {{ choose(1) }}\n"
    ))
}

#[test]
fn authority_trace_audit_is_budgeted() {
    // #553: measured positive (64 nested reborrows, about 0.4 s) and a
    // rejection that previously grew as depth^4 (256 took 74 s).
    success(&check(&reborrow_chain(64)));
    for depth in [96, 1000] {
        let started = Instant::now();
        let message = rejection(&reborrow_chain(depth), "E_LIMIT");
        assert!(
            message.contains("authority trace audit exceeds the 200000000-unit work budget"),
            "{message}"
        );
        assert!(started.elapsed() < Duration::from_secs(30), "{depth}");
    }
}

#[test]
fn dispatch_table_construction_is_budgeted() {
    // #553: 7776 distinct arity-6 methods; previously O(keys × methods²)
    // before any other budget applied.
    let choices = ["Nat", "Int", "Bool", "Unit", "Number", "Any"];
    let mut source =
        String::from("generic g(a, b, c, d, e, f) { domain (Int, Int, Int, Int, Int, Int); }\n");
    for index in 0..7776usize {
        let mut rest = index;
        let mut params = Vec::new();
        for name in ["a", "b", "c", "d", "e"] {
            params.push(format!("{name}: {}", choices[rest % 6]));
            rest /= 6;
        }
        params.push("f: Any".into());
        source.push_str(&format!("method g({}) -> Int {{ 0 }}\n", params.join(", ")));
    }
    source.push_str("fn main() -> Int { g(1, 2, 3, 4, 5, 6) }\n");
    let scratch = Scratch::empty("kernel review dispatch");
    let started = Instant::now();
    let output = cli()
        .arg("check")
        .arg(scratch.write("family.vast", &source))
        .output()
        .unwrap();
    let message = String::from_utf8_lossy(&output.stderr);
    assert!(
        message.contains(
            "E_LIMIT: generic 'g': dispatch family exceeds the 16000000-unit table budget"
        ),
        "{message}"
    );
    assert!(started.elapsed() < Duration::from_secs(60));
}
