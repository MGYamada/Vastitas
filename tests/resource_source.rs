mod common;
use common::{Scratch, cli, kernel, success};
use serde_json::{Value, json};
use std::os::unix::fs::PermissionsExt;
use std::process::Command;

const MAIN: &str = include_str!("../examples/packages/storage/app/src/main.vast");
const OPERATIONS: &str =
    include_str!("../examples/packages/storage/buffers/src/operations/mod.vast");

fn fixture(main: &str, operations: &str) -> Scratch {
    let s = Scratch::empty("resource source");
    s.write(
        "app/Vastitas.toml",
        include_str!("../examples/packages/storage/app/Vastitas.toml"),
    );
    s.write("app/src/main.vast", main);
    s.write(
        "buffers/Vastitas.toml",
        include_str!("../examples/packages/storage/buffers/Vastitas.toml"),
    );
    s.write(
        "buffers/src/lib.vast",
        include_str!("../examples/packages/storage/buffers/src/lib.vast"),
    );
    s.write("buffers/src/operations/mod.vast", operations);
    s
}
fn check(s: &Scratch) -> std::process::Output {
    cli()
        .args(["check", "--manifest-path"])
        .arg(s.0.join("app/Vastitas.toml"))
        .output()
        .unwrap()
}
fn request(s: &Scratch) -> Value {
    let stub = s.write("capture", "#!/bin/sh\ncat > \"$(dirname \"$0\")/wire.json\"\nprintf '%s\\n' '{\"version\":8,\"ok\":false,\"diagnostics\":[{\"code\":\"E_CAPTURED\",\"message\":\"captured\"}]}'\nexit 1\n");
    std::fs::set_permissions(&stub, std::fs::Permissions::from_mode(0o755)).unwrap();
    let result = cli()
        .env("VASTITAS_KERNEL", stub)
        .args(["check", "--manifest-path"])
        .arg(s.0.join("app/Vastitas.toml"))
        .output()
        .unwrap();
    assert!(
        String::from_utf8_lossy(&result.stderr).contains("E_CAPTURED"),
        "{result:?}"
    );
    serde_json::from_slice(&std::fs::read(s.0.join("wire.json")).unwrap()).unwrap()
}
fn module(raw: &Value, name: &str, path: Value) -> String {
    let package = raw["packages"]
        .as_array()
        .unwrap()
        .iter()
        .position(|p| p["name"] == name)
        .unwrap();
    let index = raw["packages"][package]["modules"]
        .as_array()
        .unwrap()
        .iter()
        .position(|m| m["path"] == path)
        .unwrap();
    format!("/packages/{package}/modules/{index}")
}
fn rejected(main: &str, operations: &str, code: &str) {
    let output = check(&fixture(main, operations));
    assert!(!output.status.success(), "accepted {main}\n{operations}");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(code),
        "expected {code}: {output:?}"
    );
}

const SELF_COPY: &str = "resource fn main() -> Int {
    allocate data: F64[12];
    borrow w = write(data, layout(8, 2, 3, 4, false));
    fill(w, f64_bits(4607182418800017408));
    release(w);
    borrow l = read_write(data, layout(8, 2, 3, 4, true));
    copy(l, l);
    expect(l, 2, 1, f64_bits(4607182418800017408));
    release(l);
    drop(data);
    value { 0 }
}";

const COMPLEX_BOUNDARIES: &str = "resource fn main() -> Int {
    allocate data: Complex<F64>[8];
    borrow init = write(data, layout(0, 8, 1, 8, false));
    fill(init, complex_bits(4607182418800017408, 4611686018427387904));
    store(init, 1, 0, complex_bits(4613937818241073152, 4616189618054758400));
    release(init);
    borrow parent = read_write(data, layout(0, 8, 1, 8, false));
    borrow first = read(parent, layout(0, 1, 1, 1, false));
    expect(first, 0, 0, complex_bits(4607182418800017408, 4611686018427387904));
    release(first);
    borrow padded = read(parent, layout(16, 1, 2, 3, true));
    expect(padded, 0, 0, complex_bits(4613937818241073152, 4616189618054758400));
    expect(padded, 1, 0, complex_bits(4607182418800017408, 4611686018427387904));
    release(padded);
    borrow empty = read(parent, layout(8, 0, 1, 1, false));
    release(empty);
    release(parent);
    drop(data);
    allocate real: F64[2];
    borrow real_write = write(real, layout(8, 1, 1, 1, false));
    fill(real_write, f64_bits(4607182418800017408));
    release(real_write);
    borrow real_read = read(real, layout(8, 1, 1, 1, false));
    expect(real_read, 0, 0, f64_bits(4607182418800017408));
    release(real_read);
    drop(real);
    value { 42 }
}";

#[test]
fn complex_views_preserve_elements_through_source_wire_and_native_execution() {
    let s = fixture(COMPLEX_BOUNDARIES, OPERATIONS);
    success(&check(&s));
    let raw = request(&s);
    assert_eq!(kernel(&raw, "emit")["ok"], true);
    success(
        &cli()
            .args(["build", "--manifest-path"])
            .arg(s.0.join("app/Vastitas.toml"))
            .arg("-o")
            .arg(s.0.join("program"))
            .output()
            .unwrap(),
    );
    let result = Command::new(s.0.join("program")).output().unwrap();
    success(&result);
    assert_eq!(result.stdout, b"42\n");
    for layout in ["layout(0, 1, 1, 1, false)", "layout(16, 1, 2, 3, true)"] {
        let invalid = COMPLEX_BOUNDARIES.replace(
            layout,
            &layout.replacen(
                if layout.starts_with("layout(16,") {
                    "16"
                } else {
                    "0"
                },
                "8",
                1,
            ),
        );
        rejected(&invalid, OPERATIONS, "E_RESOURCE_REGION");
    }
    rejected(
        &COMPLEX_BOUNDARIES.replace(
            "read(parent, layout(0, 1, 1, 1, false))",
            "read(data, layout(8, 1, 1, 1, false))",
        ),
        OPERATIONS,
        "E_RESOURCE_LAYOUT",
    );
    // The original allocation is already fully initialized. Neither source nor
    // forged wire input may reinterpret an imaginary component as a new real one.
    let root = module(&raw, "storage_example", json!([]));
    let mut changed = raw.clone();
    let body = changed
        .pointer_mut(&format!("{root}/resource_functions/0/body"))
        .unwrap()
        .as_array_mut()
        .unwrap();
    let padded = body
        .iter_mut()
        .find(|statement| statement["action"]["layout"]["offset"] == 16)
        .unwrap();
    padded["action"]["layout"]["offset"] = json!(8);
    for operation in ["check", "emit"] {
        let rejected = kernel(&changed, operation);
        assert_eq!(rejected["ok"], false, "{rejected}");
        assert_eq!(rejected["diagnostics"][0]["code"], "E_RESOURCE_REGION");
        assert!(rejected.get("lean_source").is_none());
    }
}

#[test]
fn initialized_self_copy_is_checked_and_erased_before_native_generation() {
    let s = fixture(SELF_COPY, OPERATIONS);
    success(&check(&s));
    let raw = request(&s);
    let accepted = kernel(&raw, "emit");
    assert_eq!(accepted["ok"], true, "{accepted}");
    let source = accepted["lean_source"].as_str().unwrap();
    assert!(!source.contains("copy arena"), "{source}");
    let output = s.0.join("self-copy");
    success(
        &cli()
            .args(["build", "--manifest-path"])
            .arg(s.0.join("app/Vastitas.toml"))
            .arg("-o")
            .arg(&output)
            .output()
            .unwrap(),
    );
    let result = Command::new(output).output().unwrap();
    success(&result);
    assert_eq!(result.stdout, b"0\n");

    // The kernel must reject a forged returned source even though a self-copy
    // would disappear from native instructions after successful checking.
    let mut changed = raw;
    let root = module(&changed, "storage_example", json!([]));
    let action = changed
        .pointer_mut(&format!("{root}/resource_functions/0/body/5/action"))
        .unwrap();
    assert_eq!(action["op"], "copy");
    action["source"] = json!("w");
    action["target"] = json!("w");
    let response = kernel(changed, "emit");
    assert_eq!(response["ok"], false, "{response}");
    assert!(response.get("lean_source").is_none());
}

#[test]
fn self_copy_does_not_bypass_access_initialization_or_suspension() {
    for mode in ["read", "write"] {
        rejected(
            &SELF_COPY.replace("read_write(data", &format!("{mode}(data")),
            OPERATIONS,
            "E_RESOURCE_ACCESS",
        );
    }
    rejected(
        &SELF_COPY.replace("fill(w, f64_bits(4607182418800017408));", ""),
        OPERATIONS,
        "E_RESOURCE_INIT",
    );
    rejected(
        &SELF_COPY.replace(
            "copy(l, l);",
            "borrow child = read(l, layout(8, 1, 1, 1, false)); copy(l, l); release(child);",
        ),
        OPERATIONS,
        "E_RESOURCE_LOAN",
    );
    rejected(
        &SELF_COPY.replace("copy(l, l);", "copy(w, w);"),
        OPERATIONS,
        "E_RESOURCE_LOAN",
    );
}

#[test]
fn sequential_branch_writes_preserve_only_common_initialization() {
    let branches = (0..64)
        .map(|i| {
            format!(
                "if flag {{ store(output, 0, {}, f64_bits(0)); }} \
                 else {{ store(output, 0, {}, f64_bits(0)); }}",
                2 * i,
                2 * i + 1
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let main = format!(
        "resource fn main() -> Int {{
            let flag: Bool = value {{ true }};
            allocate data: F64[129];
            borrow output = write(data, layout(0, 1, 129, 1, false));
            store(output, 0, 128, f64_bits(0));
            {branches}
            release(output);
            borrow shared = read(data, layout(1024, 1, 1, 1, false));
            expect(shared, 0, 0, f64_bits(0));
            release(shared);
            drop(data);
            value {{ 42 }}
        }}"
    );
    for source in [
        main.clone(),
        main.replace("value { true }", "value { false }"),
    ] {
        let s = fixture(&source, OPERATIONS);
        success(&check(&s));
        success(
            &cli()
                .args(["build", "--manifest-path"])
                .arg(s.0.join("app/Vastitas.toml"))
                .arg("-o")
                .arg(s.0.join("program"))
                .output()
                .unwrap(),
        );
        let output = Command::new(s.0.join("program")).output().unwrap();
        success(&output);
        assert_eq!(output.stdout, b"42\n");
    }
    for offset in [0, 8] {
        rejected(
            &main.replace("layout(1024,", &format!("layout({offset},")),
            OPERATIONS,
            "E_RESOURCE_INIT",
        );
    }
    rejected(
        &main.replace("store(output, 0, 127,", "store(output, 0, 129,"),
        OPERATIONS,
        "E_RESOURCE_BOUNDS",
    );
    let mut raw = request(&fixture(&main, OPERATIONS));
    let root = module(&raw, "storage_example", json!([]));
    let body = raw
        .pointer_mut(&format!("{root}/resource_functions/0/body"))
        .unwrap()
        .as_array_mut()
        .unwrap();
    // The common store is required by the independently checked raw program.
    body.remove(3);
    let response = kernel(raw, "emit");
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(response["diagnostics"][0]["code"], "E_RESOURCE_INIT");
    assert!(response.get("lean_source").is_none());
}

#[test]
fn cell_writes_initialize_padded_call_outputs_without_prefill() {
    let stores: Vec<_> = (0..2)
        .flat_map(|row| {
            (0..3).map(move |column| {
                format!(
                    "store(output, {row}, {column}, f64_bits({}));",
                    ((row * 3 + column + 1) as f64).to_bits()
                )
            })
        })
        .collect();
    let expected = (0..2)
        .flat_map(|row| {
            (0..3).map(move |column| {
                format!(
                    "expect(input, {column}, {row}, f64_bits({}));",
                    ((row * 3 + column + 1) as f64).to_bits()
                )
            })
        })
        .collect::<Vec<_>>()
        .join("\n");
    let main = format!(
        "resource fn initialize(output: Write<F64, 2, 3> initializes) -> Unit {{
            if false {{ {} }} else {{ {} }}
            value {{ () }}
        }}
        resource fn main() -> Int {{
            allocate data: F64[12];
            borrow output = write(data, layout(8, 2, 3, 4, false));
            call initialize(output) -> ();
            release(output);
            borrow input = read(data, layout(8, 2, 3, 4, true));
            {expected}
            release(input);
            drop(data);
            value {{ 42 }}
        }}",
        stores.join("\n"),
        stores.iter().rev().cloned().collect::<Vec<_>>().join("\n")
    );
    let s = fixture(&main, OPERATIONS);
    success(&check(&s));
    let raw = request(&s);
    let response = kernel(&raw, "emit");
    assert_eq!(response["ok"], true, "{response}");
    assert!(
        !response["lean_source"]
            .as_str()
            .unwrap()
            .contains("fill arena")
    );
    success(
        &cli()
            .args(["build", "--manifest-path"])
            .arg(s.0.join("app/Vastitas.toml"))
            .arg("-o")
            .arg(s.0.join("program"))
            .output()
            .unwrap(),
    );
    let result = Command::new(s.0.join("program")).output().unwrap();
    success(&result);
    assert_eq!(result.stdout, b"42\n");
    rejected(&main.replace(&stores[5], ""), OPERATIONS, "E_RESOURCE_INIT");
    // The untaken arm also needs a complete initialization guarantee. Tampered
    // raw IR cannot reuse acceptance of the valid original source.
    let root = module(&raw, "storage_example", json!([]));
    let mut changed = raw;
    changed
        .pointer_mut(&format!("{root}/resource_functions/0/body/0/yes"))
        .unwrap()
        .as_array_mut()
        .unwrap()
        .pop();
    let response = kernel(changed, "emit");
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(response["diagnostics"][0]["code"], "E_RESOURCE_INIT");
    assert!(response.get("lean_source").is_none());
}

#[test]
fn internal_gemm_cannot_supply_public_mathematical_authority() {
    let raw = request(&fixture(MAIN, OPERATIONS));
    let root = module(&raw, "storage_example", json!([]));
    let mut changed = raw;
    let span = changed
        .pointer(&format!("{root}/resource_functions/0/body/0/span"))
        .unwrap()
        .clone();
    *changed
        .pointer_mut(&format!("{root}/resource_functions/0/body/0"))
        .unwrap() = json!({
        "span": span,
        "kind": "action", "action": {"op": "gemm", "left": "a", "right": "b", "output": "c",
            "conjugate_left": false, "conjugate_right": false, "mode": "overwrite", "policy": "native_fast"}
    });
    let response = kernel(changed, "emit");
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(
        response["diagnostics"][0]["code"], "E_PROTOCOL",
        "{response}"
    );
    // A missing span used to fail before the action decoder was reached,
    // leaving the resource-only GEMM bypass untested.
    assert!(
        response["diagnostics"][0]["message"]
            .as_str()
            .unwrap()
            .contains("unknown resource source operation"),
        "{response}"
    );
    assert!(response.get("lean_source").is_none());
}

#[test]
fn package_resource_entry_builds_owned_returns_and_pure_fn_dispatch_together() {
    let s = fixture(MAIN, OPERATIONS);
    success(&check(&s));
    let output = s.0.join("program");
    success(
        &cli()
            .args(["build", "--manifest-path"])
            .arg(s.0.join("app/Vastitas.toml"))
            .arg("-o")
            .arg(&output)
            .output()
            .unwrap(),
    );
    let result = Command::new(output).output().unwrap();
    success(&result);
    assert_eq!(result.stdout, b"42\n");
    // Runtime failure occurs before the pure return expression publishes 42.
    s.write(
        "buffers/src/operations/mod.vast",
        &OPERATIONS.replace(
            "expect(input, 0, 0, f64_bits(4613937818241073152))",
            "expect(input, 0, 0, f64_bits(0))",
        ),
    );
    let failed = s.0.join("fails");
    success(
        &cli()
            .args(["build", "--manifest-path"])
            .arg(s.0.join("app/Vastitas.toml"))
            .arg("-o")
            .arg(&failed)
            .output()
            .unwrap(),
    );
    let result = Command::new(failed).output().unwrap();
    assert!(!result.status.success());
    assert!(
        String::from_utf8_lossy(&result.stderr).contains("E_NATIVE_EXPECT"),
        "{result:?}"
    );
    assert!(result.stdout.is_empty());
}

#[test]
fn resource_wire_preserves_unresolved_names_and_rejects_older_versions() {
    let raw = request(&fixture(MAIN, OPERATIONS));
    assert_eq!(raw["version"], 8);
    let root = module(&raw, "storage_example", json!([]));
    assert_eq!(
        raw.pointer(&format!("{root}/resource_functions/0/body/0/callee"))
            .unwrap(),
        "make"
    );
    let accepted = kernel(&raw, "emit");
    assert_eq!(accepted["ok"], true, "{accepted}");
    assert_eq!(accepted["storage_runtime"], true);
    for version in 2..8 {
        let mut old = raw.clone();
        old["version"] = json!(version);
        let response = kernel(old, "check");
        assert_eq!(response["ok"], false, "{version}: {response}");
        assert_eq!(response["version"], version);
    }
    let mut flat = common::request("fn main() -> Int { 42 }", "legacy.vast");
    flat["resource_functions"] = json!([]);
    assert_eq!(kernel(flat, "check")["ok"], false);
}

#[test]
fn raw_resource_wire_cannot_supply_checked_owners_targets_or_alias_evidence() {
    let raw = request(&fixture(MAIN, OPERATIONS));
    let root = module(&raw, "storage_example", json!([]));
    let operations = module(&raw, "storage_buffers", json!(["operations"]));
    for (pointer, key, value) in [
        ("".to_string(), "checked", json!(true)),
        (root.clone(), "resource_headers", json!([])),
        (
            format!("{root}/resource_functions/0"),
            "owner",
            json!("trusted"),
        ),
        (
            format!("{root}/resource_functions/0/body/0"),
            "callee",
            json!(0),
        ),
        (
            format!("{root}/resource_functions/0/body/1/action"),
            "disjoint",
            json!(true),
        ),
        (
            format!("{operations}/resource_functions/0/body/0/action"),
            "initialized",
            json!(true),
        ),
        (
            format!("{operations}/resource_functions/0/body/0/action"),
            "allocation",
            json!(1),
        ),
        (
            format!("{root}/resource_functions/0/value_body/result"),
            "checked",
            json!(true),
        ),
    ] {
        let mut changed = raw.clone();
        changed.pointer_mut(&pointer).unwrap()[key] = value;
        let response = kernel(changed, "emit");
        assert_eq!(response["ok"], false, "{pointer}/{key}: {response}");
        assert_eq!(
            response["diagnostics"][0]["code"], "E_PROTOCOL",
            "{response}"
        );
        assert!(response.get("lean_source").is_none());
    }
    for field in ["arguments", "results"] {
        let mut changed = raw.clone();
        changed
            .pointer_mut(&format!("{root}/resource_functions/0/body/0"))
            .unwrap()[field] = json!(vec!["name"; 65]);
        let response = kernel(changed, "emit");
        assert_eq!(response["ok"], false, "{response}");
        assert_eq!(
            response["diagnostics"][0]["code"], "E_RESOURCE_LIMIT",
            "{response}"
        );
    }
    let mut changed = raw.clone();
    let first = changed
        .pointer(&format!("{root}/resource_functions/0/body/0"))
        .unwrap()
        .clone();
    changed
        .pointer_mut(&format!("{root}/resource_functions/0"))
        .unwrap()["body"] = json!(vec![first.clone(); 4097]);
    // A single oversized body is rejected by the wire decoder first.
    let response = kernel(&changed, "check");
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(
        response["diagnostics"][0]["code"], "E_PROTOCOL",
        "{response}"
    );
    // Individually decodable bodies must still share one global source budget.
    changed
        .pointer_mut(&format!("{root}/resource_functions/0"))
        .unwrap()["body"] = json!(vec![first; 4096]);
    let response = kernel(changed, "check");
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(
        response["diagnostics"][0]["code"], "E_RESOURCE_LIMIT",
        "{response}"
    );
}

#[test]
fn resource_source_enforces_move_borrow_initialization_and_name_scopes() {
    rejected(
        &MAIN.replace("drop(returned);", "drop(data); drop(returned);"),
        OPERATIONS,
        "E_RESOURCE_MOVE",
    );
    rejected(
        MAIN,
        &OPERATIONS.replace("fill(output, f64_bits(4613937818241073152));", ""),
        "E_RESOURCE_TYPE",
    );
    rejected(
        MAIN,
        &OPERATIONS.replace("pub resource fn inspect", "resource fn inspect"),
        "E_VISIBILITY",
    );
    rejected(
        MAIN,
        &format!("{OPERATIONS}\nresource fn invalid() -> Unit {{ drop(missing); value {{ () }} }}"),
        "E_RESOURCE_NAME",
    );
    rejected(
        MAIN,
        &OPERATIONS.replace(
            "expect(input, 0, 0, f64_bits(4613937818241073152));",
            "fill(input, f64_bits(0));",
        ),
        "E_RESOURCE_ACCESS",
    );
    rejected(
        &MAIN.replace("increment(answer(40))", "let data: Int = 1; data"),
        OPERATIONS,
        "E_SHADOW",
    );
    rejected(
        &MAIN.replace(
            "fn(x: Int) -> Int { x + 1 }",
            "fn(data: Int) -> Int { data + 1 }",
        ),
        OPERATIONS,
        "E_CAPTURE",
    );
    rejected(
        &MAIN.replace("increment(answer(40))", "make()"),
        OPERATIONS,
        "E_TYPE",
    );
    rejected(
        &MAIN.replace("call make() -> (data);", "call answer() -> (data);"),
        OPERATIONS,
        "E_TYPE",
    );
    rejected(
        MAIN,
        &OPERATIONS.replace("F64[8]", "F64[18446744073709551616]"),
        "E_RESOURCE_LIMIT",
    );
    rejected(
        MAIN,
        &OPERATIONS.replace("value { () }", "value { true }"),
        "E_TYPE",
    );
}

#[test]
fn resource_source_keeps_nonwinning_pure_bodies_and_library_entry_rules() {
    rejected(
        &MAIN.replace(
            "method answer(x: Number) -> Int { 0 }",
            "method answer(x: Number) -> Int { true }",
        ),
        OPERATIONS,
        "E_TYPE",
    );
    let s = fixture("use buffers::make; fn main() -> Int { 42 }", OPERATIONS);
    success(&check(&s));
    let raw = request(&s);
    let response = kernel(raw, "emit");
    assert_eq!(response["ok"], true, "{response}");
    assert_eq!(response["storage_runtime"], false);
    assert!(
        !response["lean_source"]
            .as_str()
            .unwrap()
            .contains("VastitasStorageNative")
    );
    // Only the checked pure runtime is present in this isolated build root.
    // The protocol-8 request still contains all unused resource definitions.
    let runtime = s.0.join("pure-kernel");
    s.write(
        "pure-kernel/lean-toolchain",
        include_str!("../lean-kernel/lean-toolchain"),
    );
    s.write(
        "pure-kernel/lakefile.toml",
        "name = \"vastitas_kernel\"\n[[lean_lib]]\nname = \"VastitasKernel\"\n",
    );
    s.write(
        "pure-kernel/VastitasKernel/IndexedRuntime.lean",
        include_str!("../lean-kernel/VastitasKernel/IndexedRuntime.lean"),
    );
    let executable = s.0.join("pure-program");
    success(
        &cli()
            .env("VASTITAS_KERNEL", common::kernel_path())
            .env("VASTITAS_KERNEL_ROOT", &runtime)
            .args(["build", "--manifest-path"])
            .arg(s.0.join("app/Vastitas.toml"))
            .arg("-o")
            .arg(&executable)
            .output()
            .unwrap(),
    );
    let result = Command::new(executable).output().unwrap();
    success(&result);
    assert_eq!(result.stdout, b"42\n");
    s.write("app/src/main.vast", "use buffers::make;");
    success(&check(&s));
    let response = kernel(request(&s), "emit");
    assert_eq!(response["ok"], false);
    assert_eq!(response["diagnostics"][0]["code"], "E_MAIN");
}
