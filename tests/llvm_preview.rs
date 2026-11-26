//! Complete qualification modules through the ordinary source driver.
mod common;
use common::{Scratch, expect_code, success};
use std::process::Output;

const TARGET: [&str; 5] = [
    "--llvm-preview",
    "--target-triple",
    "aarch64-apple-darwin",
    "--data-layout",
    "e-m:o-i64:64-n32:64-S128",
];
const TABLE: &str = "pub indexed finite A { x; y; }
indexed table swap(A) -> A { (y) => x; (x) => y; }
pub fn pick(a: A<>) -> A<> { finite::lookup::<swap>(a) }";
const ASSEMBLED: &str = "fn keep(x: Bool) -> Bool { false }
contribution prefer : keep {
    fn keep(x: Bool) requires (HasEq) -> Bool { x }
}
assemble keep { apply prefer; }
fn main() -> Int { if keep(false) { 314 } else { 9 } }";

const ORDERED_CALLS: &str = include_str!("../llvm/fixtures/OrderedCalls.vast");

fn preview(s: &Scratch, source: &str) -> Output {
    s.write_package("app", source, "");
    s.command("check", "app/Vastitas.toml")
        .args(TARGET)
        .output()
        .unwrap()
}

#[test]
fn proof_input_pairs_the_complete_revision_with_the_same_llvm_publication() {
    let s = Scratch::empty("LLVM proof input");
    let source = include_str!("../llvm/fixtures/ComparisonMethod.vast");
    for body in [source.to_owned(), source.replace("apply ordered;", "")] {
        let assembly = preview(&s, &body);
        success(&assembly);
        let check = || s.command("check", "app/Vastitas.toml");
        let receipt = check().arg("--print-function-revision").output().unwrap();
        success(&receipt);
        let capture = check()
            .arg("--llvm-proof-input")
            .args(&TARGET[1..])
            .output()
            .unwrap();
        success(&capture);
        let bundle: serde_json::Value = serde_json::from_slice(&capture.stdout).unwrap();
        let revision: serde_json::Value = serde_json::from_slice(&receipt.stdout).unwrap();
        assert_eq!(bundle["revision"], revision);
        assert_eq!(
            bundle["llvm"]["ir"].as_str().unwrap().as_bytes(),
            assembly.stdout
        );
        assert_eq!(bundle["llvm"]["kind"], "boxed-control-flow");
        assert_eq!(bundle["llvm"]["official_kernel_checked"], false);
    }
    for conflicting in [
        vec!["--llvm-preview"],
        vec!["--expect-function-revision", "missing.json"],
        vec!["--print-function-revision"],
        vec!["--llvm-proof-input"],
    ] {
        let rejected = s
            .command("check", "app/Vastitas.toml")
            .arg("--llvm-proof-input")
            .args(&TARGET[1..])
            .args(conflicting)
            .output()
            .unwrap();
        expect_code(&rejected, "E_USAGE");
        assert!(rejected.stdout.is_empty());
    }
}

const LITERAL_COMPARISON: &str = include_str!("../llvm/fixtures/LiteralComparison.vast");
const BOXED_PAIRS: &str = include_str!("../llvm/fixtures/BoxedPairs.vast");

fn assembled_selectors(parent: &str, child: &str) -> String {
    format!(
        "abstract type {parent};
abstract type {child} <: {parent};
subtype Bool <: {child};
fn pick(x) domain((Bool));
contribution methods : pick {{
    fn pick(x: Cold) -> Bool {{ false }}
    fn pick(x: Warm) -> Bool {{ true }}
}}
assemble pick {{ apply methods; }}
fn main() -> Int {{ if pick(false) {{ 42 }} else {{ 7 }} }}"
    )
}

#[test]
fn assembled_selector_hierarchy_binds_the_winner_on_every_kernel_route() {
    let s = Scratch::empty("physical selector revision");
    let compile = |parent, child| {
        let output = preview(&s, &assembled_selectors(parent, child));
        success(&output);
        let raw = s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
        let revision = common::kernel(&raw, "function-revision");
        let text = String::from_utf8(output.stdout).unwrap();
        (raw, revision["function_revision"].clone(), text)
    };
    let (warm, revision, warm_ir) = compile("Cold", "Warm");
    let (mut cold, other, cold_ir) = compile("Warm", "Cold");
    let call = "/pure/dispatch_calls/0";
    let a = revision.pointer(call).unwrap();
    let b = other.pointer(call).unwrap();
    assert_eq!(a["id"], b["id"]);
    assert_eq!(a["key"], b["key"]);
    assert_ne!(a["method"], b["method"]);
    for (ir, value) in [(&warm_ir, 1), (&cold_ir, 0)] {
        assert!(ir.contains(&format!(
            "define internal i1 @vq_selected(i1 %arg) {{\nentry:\n  ret i1 {value}\n}}"
        )));
    }
    cold["expected_function_revision"] = revision;
    common::assert_wire_rejected(&common::kernel(&cold, "check"), "E_FUNCTION_REVISION");
    cold.as_object_mut()
        .unwrap()
        .remove("expected_function_revision");
    // Both decoded hierarchies are lawful. Only the original .vast bytes
    // determine which of the two contributed definitions is more specific.
    cold["root_source"] = warm["root_source"].clone();
    for args in [
        &["check"][..],
        &["emit"],
        &["function-revision"],
        &["llvm-check", TARGET[2], TARGET[4]],
        &["llvm-build", TARGET[2], TARGET[4]],
    ] {
        let response = common::kernel_with_args(&cold, args);
        common::assert_wire_rejected(&response, "E_HIERARCHY_SOURCE");
        assert!(response.get("llvm").is_none());
    }
}

#[cfg(feature = "llvm-native")]
#[test]
fn assembled_selector_order_drives_both_native_exit_edges() {
    let s = Scratch::empty("native selector order");
    for (parent, child, status) in [("Cold", "Warm", 42), ("Warm", "Cold", 7)] {
        s.write_package("app", &assembled_selectors(parent, child), "");
        for (name, flags) in [("lean", &[][..]), ("llvm", &["--llvm-preview"][..])] {
            let build = s
                .command("build", "app/Vastitas.toml")
                .args(flags)
                .args(["-o", name])
                .output()
                .unwrap();
            success(&build);
            assert_eq!(
                std::process::Command::new(s.0.join(name))
                    .status()
                    .unwrap()
                    .code(),
                Some(status)
            );
        }
    }
}

#[test]
fn boolean_comparison_replays_the_selected_truth_table_and_checks_the_other_method() {
    let s = Scratch::empty("boxed Boolean comparison");
    let source = include_str!("../llvm/fixtures/BoolComparison.vast");
    let selected = preview(&s, source);
    success(&selected);
    let text = std::str::from_utf8(&selected.stdout).unwrap();
    for predicate in ["eq", "ne"] {
        let operation = format!(
            "%cmp0_2 = icmp {predicate} i32 %b0v0, %b0v1\n  %b0v2 = zext i1 %cmp0_2 to i32"
        );
        assert_eq!(text.matches(&operation).count(), 1);
    }
    let revision = s
        .command("check", "app/Vastitas.toml")
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&revision);
    s.write(
        "selected.json",
        std::str::from_utf8(&revision.stdout).unwrap(),
    );

    let fallback = preview(&s, &source.replace("apply equality;", ""));
    success(&fallback);
    assert_ne!(selected.stdout, fallback.stdout);
    let stale = s
        .command("check", "app/Vastitas.toml")
        .args(TARGET)
        .args(["--expect-function-revision", "selected.json"])
        .output()
        .unwrap();
    expect_code(&stale, "E_FUNCTION_REVISION");
    assert!(stale.stdout.is_empty());

    for invalid in [
        source.replace("left != right", "left < right"),
        source.replace("left == right", "left >= right"),
    ] {
        let rejected = preview(&s, &invalid);
        expect_code(&rejected, "E_OPERATOR");
        assert!(rejected.stdout.is_empty());
    }
}

#[test]
fn repeated_assembled_calls_retain_both_occurrences_in_the_revision_and_llvm() {
    let s = Scratch::empty("repeated assembled comparison");
    let original = include_str!("../llvm/fixtures/ComparisonMethod.vast");
    let repeated = original.replace("{ 42 }", "{ if before(right, left) { 9 } else { 42 } }");
    let result = preview(&s, &repeated);
    success(&result);
    let text = String::from_utf8(result.stdout).unwrap();
    let bodies: Vec<_> = text
        .split("define internal ")
        .filter_map(|section| section.split_once("\n}").map(|(body, _)| body))
        .filter(|body| body.contains("call i32 @vq_f"))
        .collect();
    assert_eq!(bodies.len(), 1);
    let calls: Vec<_> = bodies[0]
        .lines()
        .filter_map(|line| line.split_once("call i32 @vq_f"))
        .map(|(dst, call)| (dst.trim(), call.split_once('(').unwrap().0))
        .collect();
    assert_eq!(calls.len(), 2);
    assert_eq!(calls[0].1, calls[1].1);
    assert_ne!(calls[0].0, calls[1].0);

    let receipt = s
        .command("check", "app/Vastitas.toml")
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&receipt);
    let revision: serde_json::Value = serde_json::from_slice(&receipt.stdout).unwrap();
    let records = revision["pure"]["dispatch_calls"].as_array().unwrap();
    assert_eq!(records.len(), 2);
    let family = revision["families"]
        .as_array()
        .unwrap()
        .iter()
        .find(|family| family["id"]["name"] == "before")
        .unwrap();
    let selected = &family["dispatch"][0]["selected"];
    assert_eq!(selected["origin"]["contribution"]["name"], "ordered");
    for record in records {
        assert_eq!(record["method"], selected["ordinal"]);
        assert_eq!(record["id"], records[0]["id"]);
    }
    s.write("twice.json", std::str::from_utf8(&receipt.stdout).unwrap());
    s.write_package("app", original, "");
    let once = s
        .command("check", "app/Vastitas.toml")
        .args(TARGET)
        .args(["--expect-function-revision", "twice.json"])
        .output()
        .unwrap();
    expect_code(&once, "E_FUNCTION_REVISION");
    assert!(once.stdout.is_empty());
}

#[test]
fn literal_comparisons_bind_both_assembled_bodies_to_the_revision() {
    let s = Scratch::empty("exact literal comparison");
    let original = preview(&s, LITERAL_COMPARISON);
    success(&original);
    let receipt = s
        .command("check", "app/Vastitas.toml")
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&receipt);
    std::fs::write(s.0.join("receipt.json"), receipt.stdout).unwrap();
    let replay = || {
        s.command("check", "app/Vastitas.toml")
            .args(TARGET)
            .args(["--expect-function-revision", "receipt.json"])
            .output()
            .unwrap()
    };
    let matched = replay();
    success(&matched);
    assert_eq!(matched.stdout, original.stdout);

    // Editing either method preserves its Boolean answer and all LLVM bytes.
    // Each original integer is still part of the checked program's revision.
    for (old, new) in [("0 == 256", "0 == 512"), ("!= -1", "!= -257")] {
        let edited = preview(&s, &LITERAL_COMPARISON.replace(old, new));
        success(&edited);
        assert_eq!(edited.stdout, original.stdout);
        let stale = replay();
        expect_code(&stale, "E_FUNCTION_REVISION");
        assert!(stale.stdout.is_empty());
    }
}

#[cfg(feature = "llvm-native")]
#[test]
fn literal_comparisons_use_full_integers_in_the_native_selected_method() {
    for (op, status) in [("!=", 42), ("==", 7)] {
        check_native_status(&LITERAL_COMPARISON.replace("!=", op), status);
    }
}

#[cfg(feature = "llvm-native")]
fn check_native_status(source: &str, status: i32) {
    let s = Scratch::empty("assembled native comparison");
    s.write_package("app", source, "");
    for (name, flags) in [("lean", &[][..]), ("llvm", &["--llvm-preview"][..])] {
        let build = s
            .command("build", "app/Vastitas.toml")
            .args(flags)
            .args(["-o", name])
            .output()
            .unwrap();
        success(&build);
        assert_eq!(
            std::process::Command::new(s.0.join(name))
                .status()
                .unwrap()
                .code(),
            Some(status)
        );
    }
}

#[test]
fn executable_actions_return_one_artifact_for_the_same_wire_and_target() {
    let project = Scratch::empty("shared executable artifact");
    for (source, kind) in [
        (
            include_str!("../llvm/fixtures/ExitStatus.vast"),
            "entry-status",
        ),
        (ASSEMBLED, "assembled-bool"),
        (
            "resource fn main() -> Int { value { -1 } }",
            "storage-program",
        ),
    ] {
        project.write_package("app", source, "");
        let wire = project.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
        for (triple, layout) in [
            (TARGET[2], TARGET[4]),
            ("x86_64-unknown-linux-gnu", "e-m:e-i64:64-n8:16:32:64-S128"),
        ] {
            let checked = common::kernel_with_args(&wire, &["llvm-check", triple, layout]);
            let built = common::kernel_with_args(&wire, &["llvm-build", triple, layout]);
            assert_eq!(checked["ok"], true, "{checked}");
            assert_eq!(checked["llvm"]["kind"], kind);
            assert_eq!(checked["llvm"]["triple"], triple);
            assert_eq!(checked["llvm"]["layout"], layout);
            assert_eq!(checked, built);
            let proof = common::kernel_with_args(&wire, &["llvm-proof-input", triple, layout]);
            assert_eq!(proof["ok"], true, "{proof}");
            assert_eq!(proof["llvm"], checked["llvm"]);
            let fields = proof["function_revision"].as_object().unwrap();
            assert!(fields.contains_key("schema") && !fields.contains_key("input"));
        }
        let mut stale = wire;
        stale["expected_function_revision"] = serde_json::json!({});
        let check = common::kernel_with_args(&stale, &["llvm-check", TARGET[2], TARGET[4]]);
        let build = common::kernel_with_args(&stale, &["llvm-build", TARGET[2], TARGET[4]]);
        common::assert_wire_rejected(&check, "E_FUNCTION_REVISION");
        assert!(check.get("llvm").is_none());
        assert_eq!(check, build);
        let proof = common::kernel_with_args(&stale, &["llvm-proof-input", TARGET[2], TARGET[4]]);
        common::assert_wire_rejected(&proof, "E_ARGUMENT");
        assert!(proof.get("llvm").is_none() && proof.get("function_revision").is_none());
    }
}

#[test]
fn only_a_root_main_selects_the_executable_checker() {
    let project = Scratch::empty("library entry scope");
    project.write_package("lib", "pub fn main() -> Int { 19 }", "");
    for (source, dependencies) in [
        (TABLE.to_string(), ""),
        (
            format!("{TABLE}\nmod inner {{ pub fn main() -> Int {{ 7 }} }}"),
            "",
        ),
        (TABLE.to_string(), "lib={path='../lib'}"),
    ] {
        project.write_package("app", &source, dependencies);
        let wire = project.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL);
        let check = common::kernel_with_args(&wire, &["llvm-check", TARGET[2], TARGET[4]]);
        if source == TABLE && dependencies.is_empty() {
            assert_eq!(check["llvm"]["kind"], "unary-lookup", "{check}");
        } else {
            // The finite lookup library profile accounts for every definition.
            common::assert_wire_rejected(&check, "E_UNSUPPORTED");
        }
        let build = common::kernel_with_args(&wire, &["llvm-build", TARGET[2], TARGET[4]]);
        common::assert_wire_rejected(&build, "E_MAIN");
        assert!(build.get("llvm").is_none());
    }
}

#[test]
fn exact_exit_status_and_library_bytes_come_from_checked_public_core() {
    let s = Scratch::empty("LLVM check");
    for (literal, status) in [
        ("0", "00"),
        ("42", "2A"),
        ("256", "00"),
        ("-257", "FF"),
        ("340282366920938463463374607431768211498", "2A"),
    ] {
        let out = preview(&s, &format!("fn main() -> Int {{ {literal} }}"));
        success(&out);
        let text = String::from_utf8(out.stdout).unwrap();
        assert!(text.starts_with("target triple = "), "{text}");
        assert!(
            text.ends_with(&format!(
                "define i32 @main() {{\nentry:\n  ret i32 u0x{status}\n}}\n"
            )),
            "{text}"
        );
        assert_eq!(text.matches("define ").count(), 1);
    }
    let a = preview(&s, TABLE);
    success(&a);
    let leaf = String::from_utf8(a.stdout).unwrap();
    assert!(leaf.contains("k0000:\n  ret i32 u0x0001\nk0001:\n  ret i32 u0x0000\n"));
    let b = preview(
        &s,
        &format!("{TABLE}\npub fn forward(a: A<>) -> A<> {{ pick(a) }}"),
    );
    success(&b);
    let linked = String::from_utf8(b.stdout).unwrap();
    assert!(linked.starts_with(&leaf));
    assert!(linked.ends_with("  %result = call i32 @vq_lookup(i32 %tag)\n  ret i32 %result\n}\n"));
}

#[test]
fn binary_lookup_preserves_nominal_axes_and_composition_order() {
    let s = Scratch::empty("binary LLVM lookup");
    let group = include_str!("../llvm/fixtures/S3Composition.vast");
    let output = preview(&s, group);
    success(&output);
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("define i32 @vq_lookup2(i32 %row, i32 %col)"));
    // (1,2) and (2,1) have different products in S3.
    assert!(text.contains("k0008:\n  ret i32 u0x0004\n"));
    assert!(text.contains("k000D:\n  ret i32 u0x0003\n"));
    let swapped = group.replace(">(g, f)", ">(f, g)");
    let reversed = preview(&s, &swapped);
    success(&reversed);
    assert!(
        String::from_utf8(reversed.stdout)
            .unwrap()
            .contains("define i32 @vq_lookup2(i32 %col, i32 %row)")
    );
    let rectangular = "indexed finite A { a; b; }
indexed finite B { x; y; z; }
indexed table t(A,B) -> A {
    (a,x) => b; (b,x) => a; (a,y) => a; (b,y) => b; (a,z) => a; (b,z) => a;
}
pub fn pick(i: A<>, j: B<>) -> A<> { finite::lookup::<t>(i,j) }";
    let output = preview(&s, rectangular);
    success(&output);
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("icmp ult i32 %row, u0x0002"));
    assert!(text.contains("icmp ult i32 %col, u0x0003"));
    assert!(text.contains("mul i32 %row, u0x0003"));
    let empty = "indexed finite A {} indexed finite B { x; }
indexed table t(B,A) -> B {} pub fn pick(i: B<>, j: A<>) -> B<> { finite::lookup::<t>(i,j) }";
    let output = preview(&s, empty);
    success(&output);
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains("icmp ult i32 %col, u0x0000"));
    assert!(text.ends_with("switch i32 %index, label %miss [\n  ]\nmiss:\n  ret i32 -1\n}\n"));
}

#[test]
fn closed_exact_operators_retain_method_keys_and_unbounded_values() {
    let s = Scratch::empty("LLVM canonical arithmetic");
    let big = "340282366920938463463374607431768211457";
    for (expression, expected) in [
        ("int(2 - 9)", "00"),
        ("int(4 * 70)", "18"),
        ("let n: Nat = 7; let d: Nat = 2; int(n / d)", "03"),
        ("let n: Nat = 7; let d: Int = -3; n / d", "FE"),
        ("let n: Nat = 3; -7 / n", "FD"),
        ("let n: Nat = 0; -7 / n", "00"),
        ("-7 / 0", "00"),
        ("std::operator::neg(-17)", "11"),
        (&format!("({big} * {big}) - ({big} + 1)"), "FF"),
    ] {
        let output = preview(&s, &format!("fn main() -> Int {{ {expression} }}"));
        success(&output);
        assert!(
            String::from_utf8(output.stdout)
                .unwrap()
                .ends_with(&format!("  ret i32 u0x{expected}\n}}\n")),
            "{expression}"
        );
    }

    let mut results = Vec::new();
    for expression in [
        "n / d + 12",
        "std::operator::add(std::operator::div(n, d), 12)",
    ] {
        let output = preview(
            &s,
            &format!("fn main() -> Int {{ let n: Nat = 7; let d = -3; {expression} }}"),
        );
        success(&output);
        let receipt = s
            .command("check", "app/Vastitas.toml")
            .arg("--print-function-revision")
            .output()
            .unwrap();
        success(&receipt);
        let mut revision: serde_json::Value = serde_json::from_slice(&receipt.stdout).unwrap();
        let sites = revision["pure"]["operator_sites"].as_array().unwrap();
        let divide = sites.iter().find(|s| s["id"]["name"] == "div").unwrap();
        assert_eq!(
            divide["id"]["package"]["source"],
            "vastitas:compat:operators"
        );
        assert_eq!(divide["key"], serde_json::json!(["Nat", "Int"]));
        results.push((output.stdout, sites.clone()));
        revision["pure"]["operator_sites"][0]["key"] = serde_json::json!(["Bool"]);
        std::fs::write(
            s.0.join("forged.json"),
            serde_json::to_vec(&revision).unwrap(),
        )
        .unwrap();
        let forged = s
            .command("check", "app/Vastitas.toml")
            .args(TARGET)
            .args(["--expect-function-revision", "forged.json"])
            .output()
            .unwrap();
        expect_code(&forged, "E_FUNCTION_REVISION");
        assert!(forged.stdout.is_empty());
    }
    assert_eq!(results[0], results[1]);
}

#[test]
fn boxed_integer_exports_bind_their_argument_order_and_full_revision() {
    let s = Scratch::empty("boxed integer ABI");
    let source = include_str!("../llvm/fixtures/BoxedArithmetic.vast");
    let out = preview(&s, source);
    success(&out);
    let text = String::from_utf8(out.stdout).unwrap();
    assert!(text.contains("; boxed (Nat, Int) -> Int"));
    assert!(text.contains("call ptr @vastitas_nat_int_div_v1(ptr %v3, ptr %v1)"));
    assert!(text.contains("call ptr @vastitas_int_add_v1(ptr %v4, ptr %v4)"));
    let revision = s
        .command("check", "app/Vastitas.toml")
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&revision);
    std::fs::write(s.0.join("revision.json"), revision.stdout).unwrap();

    let changed = source.replace("div(remainder, divisor)", "div(divisor, remainder)");
    let other = preview(&s, &changed);
    success(&other);
    assert!(
        String::from_utf8(other.stdout)
            .unwrap()
            .contains("call ptr @vastitas_int_nat_div_v1(ptr %v1, ptr %v3)")
    );
    let stale = s
        .command("check", "app/Vastitas.toml")
        .args(TARGET)
        .arg("--expect-function-revision")
        .arg(s.0.join("revision.json"))
        .output()
        .unwrap();
    expect_code(&stale, "E_FUNCTION_REVISION");
    assert!(stale.stdout.is_empty());
    for hidden in [
        source.replace("pub fn", "fn"),
        format!("{source} fn sibling(x: Int) -> Int {{ x }}"),
    ] {
        let result = preview(&s, &hidden);
        expect_code(&result, "E_UNSUPPORTED");
        assert!(result.stdout.is_empty());
    }
}

#[test]
fn integer_predicate_binds_operand_order_and_scalar_result_to_its_revision() {
    let s = Scratch::empty("integer predicate revision");
    let source = include_str!("../llvm/fixtures/IntegerPredicate.vast");
    let original = preview(&s, source);
    success(&original);
    let text = String::from_utf8(original.stdout).unwrap();
    assert!(text.contains("define i32 @vq_exact(ptr %v0, ptr %v1)"));
    assert!(text.contains("call i32 @vastitas_int_le_v1(ptr %v3, ptr %v1)"));
    assert!(text.contains("ret i32 %v4"));

    let revision = s
        .command("check", "app/Vastitas.toml")
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&revision);
    let saved = s.0.join("revision.json");
    std::fs::write(&saved, revision.stdout).unwrap();

    let changed = preview(&s, &source.replace("offset <= b", "b <= offset"));
    success(&changed);
    assert!(
        String::from_utf8(changed.stdout)
            .unwrap()
            .contains("call i32 @vastitas_int_le_v1(ptr %v1, ptr %v3)")
    );
    let stale = s
        .command("check", "app/Vastitas.toml")
        .args(TARGET)
        .arg("--expect-function-revision")
        .arg(saved)
        .output()
        .unwrap();
    expect_code(&stale, "E_FUNCTION_REVISION");
    assert!(stale.stdout.is_empty());
}

#[test]
fn boxed_program_preserves_call_targets_and_borrowed_returns() {
    let s = Scratch::empty("boxed integer module");
    let source = include_str!("../llvm/fixtures/BoxedProgram.vast");
    let out = preview(&s, source);
    success(&out);
    let text = String::from_utf8(out.stdout).unwrap();
    assert_eq!(text.matches("define internal ptr ").count(), 4);
    assert!(text.contains("call void @vastitas_retain_v1(ptr %v0)\n  ret ptr %v0"));
    assert!(text.contains("%v3 = call ptr @vq_f2(ptr %v1, ptr %v2)"));
    assert!(text.contains("call i32 @vastitas_exit_status_v1(ptr %result)"));
    let revision = s
        .command("check", "app/Vastitas.toml")
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&revision);
    s.write("saved.json", std::str::from_utf8(&revision.stdout).unwrap());
    let changed = preview(&s, &source.replace("keep(x) + x", "keep(x) - x"));
    success(&changed);
    assert_ne!(text.as_bytes(), changed.stdout);
    let stale = s
        .command("check", "app/Vastitas.toml")
        .args(TARGET)
        .args(["--expect-function-revision", "saved.json"])
        .output()
        .unwrap();
    expect_code(&stale, "E_FUNCTION_REVISION");
    assert!(stale.stdout.is_empty());
    let excessive = "fn sq(x: Int) -> Int { x * x } fn main() -> Int { let x = sq(256);";
    let mut source = excessive.to_string();
    for i in 1..=12 {
        let prev = if i == 1 {
            "x".into()
        } else {
            format!("x{}", i - 1)
        };
        source.push_str(&format!("let x{i} = sq({prev});"));
    }
    source.push_str("x12 }");
    expect_code(&preview(&s, &source), "E_UNSUPPORTED");
}

#[test]
fn assembled_calls_keep_the_selected_target_and_ordered_nested_arguments() {
    let s = Scratch::empty("assembled nested calls");
    let original = preview(&s, ORDERED_CALLS);
    success(&original);
    let llvm = std::str::from_utf8(&original.stdout).unwrap();
    let mut calls = llvm.lines().filter(|line| line.contains("call ptr @vq_f"));
    assert_eq!(
        calls.next().unwrap().trim(),
        "%v2 = call ptr @vq_f0(ptr %v0, ptr %v1)"
    );
    assert_eq!(
        calls.next().unwrap().trim(),
        "%v5 = call ptr @vq_f0(ptr %v3, ptr %v4)"
    );
    assert_eq!(
        calls.next().unwrap().trim(),
        "%v6 = call ptr @vq_f1(ptr %v2, ptr %v5)"
    );
    let revision = s
        .command("check", "app/Vastitas.toml")
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&revision);
    s.write(
        "original.json",
        std::str::from_utf8(&revision.stdout).unwrap(),
    );

    for changed in [
        ORDERED_CALLS.replace(
            "pick(delta(9, 4), delta(3, 1))",
            "let a = delta(9, 4); let b = delta(3, 1); pick(b, a)",
        ),
        ORDERED_CALLS.replace("apply forward;", ""),
    ] {
        let other = preview(&s, &changed);
        success(&other);
        assert_ne!(other.stdout, original.stdout);
        let stale = s
            .command("check", "app/Vastitas.toml")
            .args(TARGET)
            .args(["--expect-function-revision", "original.json"])
            .output()
            .unwrap();
        expect_code(&stale, "E_FUNCTION_REVISION");
        assert!(stale.stdout.is_empty());
    }
}

#[cfg(feature = "llvm-native")]
#[test]
fn native_assembled_nested_calls_observe_argument_and_method_changes() {
    check_native_status(ORDERED_CALLS, 23);
    check_native_status(
        &ORDERED_CALLS.replace("delta(9, 4), delta(3, 1)", "delta(3, 1), delta(9, 4)"),
        17,
    );
    check_native_status(&ORDERED_CALLS.replace("apply forward;", ""), 17);
}

#[test]
fn typed_forwarding_preserves_the_llvm_module_for_singleton_and_assembled_methods() {
    let project = Scratch::empty("typed forwarding in a sealed family");
    let direct = "fn relay(x: Int) -> Int { x }
fn keep(x: Int) -> Int { x }
contribution prefer : keep { fn keep(x: Int) requires (HasEq) -> Int { x } }
assemble keep { apply prefer; }
fn main() -> Int { relay(keep(42)) }";
    let original = preview(&project, direct);
    success(&original);
    let revision = project
        .command("check", "app/Vastitas.toml")
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&revision);
    project.write(
        "direct.json",
        std::str::from_utf8(&revision.stdout).unwrap(),
    );

    let bound = direct.replace("{ x }", "{ let y: Int = x; y }");
    let forwarded = preview(&project, &bound);
    success(&forwarded);
    assert_eq!(forwarded.stdout, original.stdout);
    let text = std::str::from_utf8(&forwarded.stdout).unwrap();
    assert_eq!(text.matches("; boxed (Int) -> Int").count(), 3);
    assert_eq!(text.matches("ret ptr %v0").count(), 3);
    let stale = project
        .command("check", "app/Vastitas.toml")
        .args(TARGET)
        .args(["--expect-function-revision", "direct.json"])
        .output()
        .unwrap();
    expect_code(&stale, "E_FUNCTION_REVISION");
    assert!(stale.stdout.is_empty());
}

#[test]
fn boxed_pair_results_bind_both_methods_to_the_revision() {
    let s = Scratch::empty("pair-valued method revision");
    let original = preview(&s, BOXED_PAIRS);
    success(&original);
    let text = std::str::from_utf8(&original.stdout).unwrap();
    assert_eq!(text.matches("define internal ptr ").count(), 5);
    for signature in [
        "(Nat) -> Pair<Nat>",
        "(Int) -> Pair<Int>",
        "(Pair<Int>) -> Pair<Int>",
    ] {
        assert!(text.contains(&format!("; boxed {signature}")));
    }
    let receipt = s
        .command("check", "app/Vastitas.toml")
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&receipt);
    s.write(
        "revision.json",
        std::str::from_utf8(&receipt.stdout).unwrap(),
    );
    let replay = || {
        s.command("check", "app/Vastitas.toml")
            .args(TARGET)
            .args(["--expect-function-revision", "revision.json"])
            .output()
            .unwrap()
    };
    let matched = replay();
    success(&matched);
    assert_eq!(matched.stdout, original.stdout);

    for edited in [
        BOXED_PAIRS.replace("apply prioritized;", ""),
        BOXED_PAIRS.replace("pair(0, x)", "pair(1, x)"),
    ] {
        let other = preview(&s, &edited);
        success(&other);
        assert_ne!(other.stdout, original.stdout);
        let stale = replay();
        expect_code(&stale, "E_FUNCTION_REVISION");
        assert!(stale.stdout.is_empty());
    }
    let invalid = preview(&s, "pub fn bad(p: Pair<Int>) -> Pair<Nat> { p }");
    expect_code(&invalid, "E_TYPE");
    assert!(invalid.stdout.is_empty());
}

#[cfg(feature = "llvm-native")]
#[test]
fn boxed_pair_results_select_both_native_methods() {
    check_native_status(BOXED_PAIRS, 42);
    check_native_status(&BOXED_PAIRS.replace("apply prioritized;", ""), 43);
}

#[cfg(feature = "llvm-native")]
#[test]
fn boxed_program_links_the_integer_runtime_and_returns_the_checked_status() {
    let s = Scratch::empty("boxed integer executable");
    let source = include_str!("../llvm/fixtures/BoxedProgram.vast");
    for (divisor, status) in [(3, 84), (0, 0), (1, 254)] {
        s.write_package("app", &source.replace(", 3)", &format!(", {divisor})")), "");
        let build = || {
            let mut command = s.command("build", "app/Vastitas.toml");
            command.args(["--llvm-preview", "-o", "program"]);
            command
        };
        success(&build().output().unwrap());
        let path = s.0.join("program");
        assert_eq!(
            std::process::Command::new(&path).status().unwrap().code(),
            Some(status)
        );
        let saved = std::fs::read(&path).unwrap();
        let failed = build().args(["--native-cc", "false"]).output().unwrap();
        expect_code(&failed, "E_BUILD");
        assert_eq!(std::fs::read(path).unwrap(), saved);
    }
}

#[test]
fn singleton_uses_boxed_runtime_when_a_closed_fold_exceeds_its_budget() {
    let s = Scratch::empty("singleton exact runtime");
    let source = include_str!("../llvm/fixtures/SingletonPower.vast");
    let original = preview(&s, source);
    success(&original);
    let receipt = s
        .command("check", "app/Vastitas.toml")
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&receipt);
    let revision: serde_json::Value = serde_json::from_slice(&receipt.stdout).unwrap();
    let sites = revision["pure"]["operator_sites"].as_array().unwrap();
    assert_eq!(sites.len(), 9);
    for (i, site) in sites.iter().enumerate() {
        assert_eq!(site["core"], 0);
        assert_eq!(site["id"]["name"], if i < 8 { "mul" } else { "div" });
        assert_eq!(site["key"], serde_json::json!(["Int", "Int"]));
    }
    std::fs::write(s.0.join("revision.json"), receipt.stdout).unwrap();
    let named = source.replace("x0 * x0", "std::operator::mul(x0, x0)");
    let changed = preview(&s, &named);
    success(&changed);
    assert_eq!(changed.stdout, original.stdout);
    let stale = s
        .command("check", "app/Vastitas.toml")
        .args(TARGET)
        .args(["--expect-function-revision", "revision.json"])
        .output()
        .unwrap();
    expect_code(&stale, "E_FUNCTION_REVISION");
    assert!(stale.stdout.is_empty());
}

#[test]
fn closed_constant_folding_limits_expansion_through_bindings() {
    let s = Scratch::empty("LLVM fold budget");
    let mut source = String::from("fn main() -> Int { let x0 = 256;");
    for i in 1..=12 {
        source.push_str(&format!("let x{i} = x{} * x{};", i - 1, i - 1));
    }
    source.push_str("x12 }");
    let rejected = preview(&s, &source);
    success(&s.command("check", "app/Vastitas.toml").output().unwrap());
    expect_code(&rejected, "E_UNSUPPORTED");
    assert!(rejected.stdout.is_empty());
}

#[test]
fn repeated_direct_calls_pay_for_each_finite_table_lookup() {
    let s = Scratch::empty("finite LLVM table budget");
    let tags: Vec<_> = (0..128).map(|i| format!("a{i}")).collect();
    let rows: Vec<_> = tags
        .iter()
        .map(|tag| format!("({tag}) => {tag};"))
        .collect();
    let mut definitions = format!(
        "indexed finite A {{ {}; }} indexed table tableA(A) -> A {{ {} }}
         fn f0(x: A<>) -> A<> {{ finite::lookup::<tableA>(x) }}",
        tags.join("; "),
        rows.join(" "),
    );
    for depth in 1..=12 {
        let prev = depth - 1;
        definitions.push_str(&format!(
            "\nfn f{depth}(x: A<>) -> A<> {{ f{prev}(f{prev}(x)) }}"
        ));
    }
    for depth in [3, 12] {
        let program = format!(
            "{definitions}\nfn main() -> Int {{ if f{depth}(A::a0) == A::a0 {{ 0 }} else {{ 1 }} }}"
        );
        let llvm = preview(&s, &program);
        success(&s.check_manifest("app/Vastitas.toml"));
        if depth == 3 {
            success(&llvm);
        } else {
            expect_code(&llvm, "E_UNSUPPORTED");
            assert!(llvm.stdout.is_empty());
        }
    }
}

#[test]
fn llvm_preview_rejects_unsupported_bodies_and_stale_revisions_before_printing() {
    let s = Scratch::empty("LLVM preview rejected");
    for source in [
        "fn choose(n: Int) -> Int { if n == 0 { 1 } else { n } } fn main() -> Int { choose(4) }",
        "fn f(n: Int) -> Int { if n == 0 { 1 } else { n } } fn main() -> Int { 7 }",
    ] {
        let result = preview(&s, source);
        success(&result);
        let llvm = String::from_utf8(result.stdout).unwrap();
        assert!(llvm.contains("call i32 @vastitas_int_eq_v1"));
        assert!(llvm.contains(" = phi ptr "));
    }
    for source in [
        "fn main() -> Int { let x = show!(-1); x }",
        "resource fn main() -> Int { value { if true { 3 } else { 4 } } }",
        "pub fn pick(a: Bool) -> Bool { !a }",
    ] {
        let o = preview(&s, source);
        success(&s.command("check", "app/Vastitas.toml").output().unwrap());
        expect_code(&o, "E_UNSUPPORTED");
        assert!(o.stdout.is_empty(), "partial bytes for {source}");
    }
    let identity = preview(&s, "pub fn pick(a: Bool) -> Bool { a }");
    success(&identity);
    let text = String::from_utf8(identity.stdout).unwrap();
    assert!(text.contains("define i32 @vq_exact(i32 %v0)"));
    assert!(text.contains("ret i32 %v0"));
    assert!(!text.contains("vastitas_retain") && !text.contains("vastitas_release"));

    let original = "fn main() -> Int { 7 }";
    s.write_package("app", original, "");
    let rev = s
        .command("check", "app/Vastitas.toml")
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&rev);
    std::fs::write(s.0.join("revision.json"), rev.stdout).unwrap();
    let with_revision = || {
        s.command("check", "app/Vastitas.toml")
            .args(TARGET)
            .args(["--expect-function-revision", "revision.json"])
            .output()
            .unwrap()
    };
    success(&with_revision());
    s.write("app/main.vast", "fn main() -> Int { 263 }"); // same exit byte
    let stale = with_revision();
    expect_code(&stale, "E_FUNCTION_REVISION");
    assert!(stale.stdout.is_empty());
}

#[test]
fn linked_closure_program_preserves_kleisli_calls_and_both_exit_edges() {
    let source = include_str!("../examples/packages/finite-kleisli/src/main.vast");
    let p = Scratch::empty("LLVM closure package");
    p.copy_stdlib(&common::STDLIB_PACKAGES, &[]);
    p.copy_sources(&common::root().join("monad"), "monad", &[]);
    let manifest = "app/Vastitas.toml";
    for (comparison, status) in [("==", 0), ("!=", 1)] {
        p.write_package(
            "app",
            &source.replace(
                "lifted == C::rightId",
                &format!("lifted {comparison} C::rightId"),
            ),
            "std={path='../stdlib'}\nmonad={path='../monad'}",
        );
        let rev = p
            .command("check", manifest)
            .arg("--print-function-revision")
            .output()
            .unwrap();
        success(&rev);
        let revision: serde_json::Value = serde_json::from_slice(&rev.stdout).unwrap();
        let file = p.0.join("closure.json");
        std::fs::write(&file, rev.stdout).unwrap();
        let check = || {
            p.command("check", manifest)
                .args(TARGET)
                .args(["--expect-function-revision", "closure.json"])
                .output()
                .unwrap()
        };
        let result = check();
        success(&result);
        let text = std::str::from_utf8(&result.stdout).unwrap();
        assert_eq!(text.matches("define internal i32 @f").count(), 6);
        assert!(text.contains("phi i32 ["));
        assert!(text.contains("switch i32"));
        assert!(text.contains("and i1"));
        let mut forged = revision.clone();
        let symbols = forged["pure"]["symbols"].as_array_mut().unwrap();
        let mut operations = Vec::new();
        for symbol in symbols {
            if symbol["id"]["package"]["name"] == "vastitas_monad" {
                assert_eq!(symbol["id"]["module"], serde_json::json!(["kleisli"]));
                operations.push(symbol["id"]["name"].as_str().unwrap().to_owned());
                let monad = &mut symbol["specialization"]["finite_indices"][0]["monad"]["name"];
                assert_eq!(monad, "M");
                *monad = "Other".into();
            }
        }
        operations.sort();
        assert_eq!(operations, ["bind", "compose", "lift", "unit"]);
        std::fs::write(file, serde_json::to_vec(&forged).unwrap()).unwrap();
        let rejected = check();
        expect_code(&rejected, "E_FUNCTION_REVISION");
        assert!(rejected.stdout.is_empty());

        #[cfg(feature = "llvm-native")]
        {
            let out = p
                .command("build", manifest)
                .args(["--llvm-preview", "-o", "closure"])
                .output()
                .unwrap();
            success(&out);
            let run = std::process::Command::new(p.0.join("closure"))
                .output()
                .unwrap();
            assert_eq!(run.status.code(), Some(status));
            assert!(run.stdout.is_empty() && run.stderr.is_empty());
        }
        #[cfg(not(feature = "llvm-native"))]
        assert!(text.contains(if status == 0 { "icmp eq" } else { "icmp ne" }));
    }
}

#[test]
fn every_declared_function_must_belong_to_the_preview_module() {
    let s = Scratch::empty("LLVM source exports");
    let caller = "pub fn forward(a: A<>) -> A<> { pick(a) }";
    let extra = "pub fn extra(f: Fn<Int, Int>) -> Int { f(1) }";
    for module in [
        TABLE.into(),
        format!("{TABLE}\n{caller}"),
        "fn main() -> Int { 0 }".into(),
        "resource fn main() -> Int { value { 0 } }".into(),
    ] {
        let result = preview(&s, &format!("{module}\n{extra}"));
        success(&s.command("check", "app/Vastitas.toml").output().unwrap());
        expect_code(&result, "E_UNSUPPORTED");
        assert!(result.stdout.is_empty());
    }
}

#[test]
fn sealed_library_revision_is_checked_on_the_complete_module() {
    let s = Scratch::empty("LLVM assembly revision");
    let source = format!(
        "{TABLE}\nuse self::pick as selected; assemble selected {{}}\n\
         pub fn forward(a: A<>) -> A<> {{ selected(a) }}"
    );
    let original = preview(&s, &source);
    success(&original);
    let receipt = s
        .command("check", "app/Vastitas.toml")
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&receipt);
    let mut revision: serde_json::Value = serde_json::from_slice(&receipt.stdout).unwrap();
    let file = s.0.join("revision.json");
    std::fs::write(&file, &receipt.stdout).unwrap();
    let replay = || {
        s.command("check", "app/Vastitas.toml")
            .args(TARGET)
            .args(["--expect-function-revision", "revision.json"])
            .output()
            .unwrap()
    };
    let matched = replay();
    success(&matched);
    assert_eq!(matched.stdout, original.stdout);

    // The alias and the defining name seal the same function and produce the
    // same LLVM bytes. Only the revision of this particular assembly is valid.
    let changed = preview(&s, &source.replace("assemble selected", "assemble pick"));
    success(&changed);
    assert_eq!(changed.stdout, original.stdout);
    let stale = replay();
    expect_code(&stale, "E_FUNCTION_REVISION");
    assert!(stale.stdout.is_empty());

    s.write("app/main.vast", &source);
    assert_eq!(revision["pure"]["calls"][0]["core"], 0);
    revision["pure"]["calls"][0]["core"] = 1.into();
    std::fs::write(file, serde_json::to_vec(&revision).unwrap()).unwrap();
    let forged = replay();
    expect_code(&forged, "E_FUNCTION_REVISION");
    assert!(forged.stdout.is_empty());
}

#[test]
fn assembled_bool_uses_the_checked_contribution_and_keeps_the_other_body() {
    let s = Scratch::empty("LLVM assembled Bool");
    let original = preview(&s, ASSEMBLED);
    success(&original);
    let text = std::str::from_utf8(&original.stdout).unwrap();
    assert_eq!(text.matches("define ").count(), 3);
    assert!(text.contains("call i1 @vq_selected(i1 0)"));
    assert!(text.contains("phi i32 [ u0x3A, %yes ], [ u0x09, %no ]"));
    assert!(text.contains("define internal i1 @vq_selected(i1 %arg) {\nentry:\n  ret i1 %arg"));
    assert!(text.contains("define internal i1 @vq_method0000(i1 %arg) {\nentry:\n  ret i1 0"));

    let receipt = s
        .command("check", "app/Vastitas.toml")
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&receipt);
    let file = s.write(
        "revision.json",
        std::str::from_utf8(&receipt.stdout).unwrap(),
    );
    let replay = || {
        s.command("check", "app/Vastitas.toml")
            .args(TARGET)
            .args(["--expect-function-revision", "revision.json"])
            .output()
            .unwrap()
    };
    let matched = replay();
    success(&matched);
    assert_eq!(matched.stdout, original.stdout);
    let revision: serde_json::Value = serde_json::from_slice(&receipt.stdout).unwrap();
    let (selected, definition, symbol) = (
        &revision["pure"]["dispatch_calls"][0],
        &revision["families"]
            .as_array()
            .unwrap()
            .iter()
            .find(|f| f["id"]["name"] == "keep")
            .unwrap()["dispatch"][0]["selected"],
        &revision["pure"]["symbols"][0],
    );
    assert_eq!(selected["id"], symbol["id"]);
    assert_eq!(selected["method"], definition["ordinal"]);
    assert_eq!(definition["origin"]["contribution"]["name"], "prefer");
    assert_eq!(
        symbol["specialization"]["definition"],
        definition["definition"]
    );
    for pointer in ["/pure/dispatch_calls/0/method", "/pure/calls/0/core"] {
        let mut forged = revision.clone();
        let value = forged.pointer_mut(pointer).unwrap();
        *value = (value.as_u64().unwrap() + 1).into();
        std::fs::write(&file, serde_json::to_vec(&forged).unwrap()).unwrap();
        let rejected = replay();
        expect_code(&rejected, "E_FUNCTION_REVISION");
        assert!(rejected.stdout.is_empty());
    }
    std::fs::write(file, receipt.stdout).unwrap();
    let renamed = preview(&s, &ASSEMBLED.replace("prefer", "alternate"));
    success(&renamed);
    assert_eq!(renamed.stdout, original.stdout);
    expect_code(&replay(), "E_FUNCTION_REVISION");

    let changed = preview(&s, &ASSEMBLED.replace("Bool { false }", "Bool { true }"));
    success(&changed);
    assert!(
        std::str::from_utf8(&changed.stdout)
            .unwrap()
            .contains("define internal i1 @vq_method0000(i1 %arg) {\nentry:\n  ret i1 1")
    );
}

#[test]
fn target_choice_and_output_form_are_explicit() {
    let s = Scratch::empty("LLVM options");
    s.write_package("app", "fn main() -> Int { 1 }", "");
    for options in [
        vec!["--llvm-preview"],
        vec!["--target-triple", "test"],
        vec!["--llvm-preview", "--data-layout", "e"],
        vec!["--llvm-proof-input", "--target-triple", "test"],
        [TARGET.as_slice(), &["--print-function-revision"]].concat(),
    ] {
        let o = s
            .command("check", "app/Vastitas.toml")
            .args(options)
            .output()
            .unwrap();
        expect_code(&o, "E_USAGE");
    }
    let build = s
        .command("build", "app/Vastitas.toml")
        .args(["--llvm-proof-input", "-o", "program"])
        .output()
        .unwrap();
    expect_code(&build, "E_USAGE");
    assert!(build.stdout.is_empty());
    for (triple, layout) in [("bad\"triple", "e"), ("arm64", "e\n;injected")] {
        let o = s
            .command("check", "app/Vastitas.toml")
            .args([
                "--llvm-preview",
                "--target-triple",
                triple,
                "--data-layout",
                layout,
            ])
            .output()
            .unwrap();
        expect_code(&o, "E_ARGUMENT");
        assert!(o.stdout.is_empty());
    }
}

#[cfg(not(feature = "llvm-native"))]
#[test]
fn check_only_driver_preserves_old_output_on_llvm_build() {
    let s = Scratch::empty("LLVM check-only build");
    s.write_package("app", "fn main() -> Int { 42 }", "");
    s.write("program", "old");
    let out = s
        .command("build", "app/Vastitas.toml")
        .args(["--llvm-preview", "-o", "program"])
        .output()
        .unwrap();
    expect_code(&out, "E_BUILD");
    assert_eq!(std::fs::read(s.0.join("program")).unwrap(), b"old");
}

#[cfg(feature = "llvm-native")]
#[test]
fn checked_llvm_executable_installs_atomically_and_rejects_unsupported_replacements() {
    use std::{fs, process::Command};
    let s = Scratch::empty("LLVM native");
    s.write_package(
        "app",
        "fn main() -> Int { -340282366920938463463374607431768211457 }",
        "",
    );
    let output = s.write("program", "old");
    let build = || {
        let mut cmd = s.command("build", "app/Vastitas.toml");
        cmd.args(["--llvm-preview", "-o", "program"]);
        cmd
    };
    success(&build().output().unwrap());
    assert_eq!(Command::new(&output).status().unwrap().code(), Some(255));
    let saved = fs::read(&output).unwrap();
    let fail_link = build().args(["--native-cc", "false"]).output().unwrap();
    expect_code(&fail_link, "E_BUILD");
    assert_eq!(fs::read(&output).unwrap(), saved);
    let overwrite_source = s
        .command("build", "app/Vastitas.toml")
        .args(["--llvm-preview", "-o", "app/main.vast"])
        .output()
        .unwrap();
    expect_code(&overwrite_source, "E_OUTPUT");
    s.write("app/main.vast", "fn main() -> Int { let x = show!(-1); x }");
    let unsupported = build().output().unwrap();
    expect_code(&unsupported, "E_UNSUPPORTED");
    assert_eq!(fs::read(&output).unwrap(), saved);
}

#[cfg(feature = "llvm-native")]
#[test]
fn imported_callees_execute_only_with_their_current_source_revision() {
    let s = Scratch::empty("LLVM imported function");
    let manifest = "app/Vastitas.toml";
    let build = || {
        s.command("build", manifest)
            .args([
                "--llvm-preview",
                "--expect-function-revision",
                "revision.json",
                "-o",
                "llvm-program",
            ])
            .output()
            .unwrap()
    };
    s.write(
        "app/defs.vast",
        "pub fn left() -> Int { 42 } pub fn next() -> Int { 7 }",
    );
    let installed = s.0.join("llvm-program");
    for (name, status) in [("left", 42), ("next", 7)] {
        let source =
            format!("mod defs; use defs::{name} as picked; fn main() -> Int {{ picked() }}");
        s.write_package("app", &source, "");
        if name == "next" {
            let previous = std::fs::read(&installed).unwrap();
            expect_code(&build(), "E_FUNCTION_REVISION");
            assert_eq!(std::fs::read(&installed).unwrap(), previous);
        }
        let revision = s
            .command("check", manifest)
            .arg("--print-function-revision")
            .output()
            .unwrap();
        success(&revision);
        std::fs::write(s.0.join("revision.json"), revision.stdout).unwrap();
        success(&build());
        assert_eq!(
            std::process::Command::new(&installed)
                .status()
                .unwrap()
                .code(),
            Some(status)
        );
        assert_eq!(s.build_and_run(manifest), common::exits(status));
    }
}

#[cfg(feature = "llvm-native")]
#[test]
fn assembled_method_result_selects_the_native_exit_edge() {
    let s = Scratch::empty("LLVM assembled executable");
    for (argument, status) in [("false", 9), ("true", 58)] {
        s.write_package(
            "app",
            &ASSEMBLED.replace("keep(false)", &format!("keep({argument})")),
            "",
        );
        let out = s
            .command("build", "app/Vastitas.toml")
            .args(["--llvm-preview", "-o", "assembled"])
            .output()
            .unwrap();
        success(&out);
        assert_eq!(
            std::process::Command::new(s.0.join("assembled"))
                .status()
                .unwrap()
                .code(),
            Some(status)
        );
    }
}

#[cfg(feature = "llvm-native")]
#[test]
fn canonical_arithmetic_build_uses_the_same_checked_exit_as_the_reference() {
    let s = Scratch::empty("LLVM folded executable");
    let source = "fn main() -> Int {
        let n: Nat = 7; let d = -3;
        std::operator::add(std::operator::div(n, d), int(5 - 8)) + 12
    }";
    s.write_package("app", source, "");
    for (output, options) in [("reference", &[][..]), ("llvm", &["--llvm-preview"][..])] {
        let built = s
            .command("build", "app/Vastitas.toml")
            .args(options)
            .args(["-o", output])
            .output()
            .unwrap();
        success(&built);
        let run = std::process::Command::new(s.0.join(output))
            .output()
            .unwrap();
        assert_eq!(run.status.code(), Some(10));
        assert!(run.stdout.is_empty());
        assert!(run.stderr.is_empty());
    }
}

#[cfg(feature = "llvm-native")]
#[test]
fn building_an_llvm_program_installs_it_without_running_it() {
    use std::{fs, os::unix::fs::PermissionsExt, process::Command};
    let s = Scratch::empty("LLVM build without execution");
    s.write_package("app", "fn main() -> Int { 0 }", "");
    let marker = s.0.join("executed");
    let stub = s.write(
        "linked-program",
        "#!/bin/sh\nprintf ran >> \"$VASTITAS_TEST_EXEC_MARKER\"\n",
    );
    let linker = s.write(
        "linker",
        concat!(
            "#!/bin/sh\nset -eu\n",
            "while [ \"$1\" != -o ]; do shift; done\n",
            "cp \"$VASTITAS_TEST_LINKED_PROGRAM\" \"$2\"\nchmod +x \"$2\"\n",
        ),
    );
    fs::set_permissions(&linker, fs::Permissions::from_mode(0o700)).unwrap();
    success(
        &s.command("build", "app/Vastitas.toml")
            .args(["--llvm-preview", "--native-cc", "./linker", "-o", "program"])
            .env("VASTITAS_TEST_LINKED_PROGRAM", &stub)
            .env("VASTITAS_TEST_EXEC_MARKER", &marker)
            .output()
            .unwrap(),
    );
    assert!(!marker.exists(), "build ran the linked program");
    success(
        &Command::new(s.0.join("program"))
            .env("VASTITAS_TEST_EXEC_MARKER", &marker)
            .output()
            .unwrap(),
    );
    assert_eq!(fs::read(marker).unwrap(), b"ran");
}

#[test]
fn storage_entry_returns_the_checked_literal_after_its_effects() {
    let s = Scratch::empty("LLVM storage status");
    let empty = preview(&s, "resource fn main() -> Int { value { -1 } }");
    success(&empty);
    let text = std::str::from_utf8(&empty.stdout).unwrap();
    assert!(text.ends_with("  ret i32 255\n}\n"));
    assert!(!text.contains("storage_new"));
    let source = "resource fn main() -> Int { allocate a: F32<RR>[1]; borrow w = write(a, layout(0,1,1,1,false)); fill(w, f32_bits(17)); release(w); borrow r = read(a, layout(0,1,1,1,false)); expect(r,0,0,f32_bits(18)); release(r); drop(a); value { 42 } }";
    let output = preview(&s, source);
    success(&output);
    let text = std::str::from_utf8(&output.stdout).unwrap();
    assert!(text.contains("call i32 @vq_storage_fill("));
    assert!(text.contains("  ret i32 42"));
    #[cfg(feature = "llvm-native")]
    {
        let host = s
            .command("build", "app/Vastitas.toml")
            .args(["--llvm-preview", "-o", "llvm-program"])
            .output()
            .unwrap();
        success(&host);
        let llvm = std::process::Command::new(s.0.join("llvm-program"))
            .output()
            .unwrap();
        let control = s.build_and_run("app/Vastitas.toml");
        assert_eq!(common::ran(&llvm), control);
        assert_eq!(String::from_utf8_lossy(&llvm.stderr), control.stderr);
        assert_eq!(llvm.status.code(), Some(1));
        common::expect_code(&llvm, "E_NATIVE_EXPECT");
    }
}

#[test]
fn inlined_resource_calls_only_erase_reached_literal_unit_returns() {
    let s = Scratch::empty("LLVM resource unit returns");
    let source = "resource fn touch() -> Unit { value { () } }
resource fn main() -> Int { call touch() -> (); value { 42 } }";
    let output = preview(&s, source);
    success(&output);
    assert!(
        std::str::from_utf8(&output.stdout)
            .unwrap()
            .ends_with("  ret i32 42\n}\n")
    );
    for unsupported in [
        source.replace("call touch() -> ();", ""),
        source.replace("value { () }", "value { if true { () } else { () } }"),
        format!("fn spare() -> Unit {{ () }}\n{source}"),
    ] {
        let rejected = preview(&s, &unsupported);
        common::expect_code(&rejected, "E_UNSUPPORTED");
        assert!(rejected.stdout.is_empty());
    }
}

#[test]
fn storage_branch_preserves_both_arms_and_executes_the_selected_path() {
    let source = include_str!("../llvm/fixtures/StorageBranch.vast");
    let scratch = Scratch::empty("LLVM nested storage branch");
    for (outer, inner, expected, status) in [
        (true, false, 42, 42),
        (true, true, 17, 42),
        (false, true, 7, 42),
        (false, false, 42, 1),
    ] {
        let program = source
            .replace("if true {", &format!("if {outer} {{"))
            .replace("if false { fill", &format!("if {inner} {{ fill"))
            .replace(
                "expect(r,0,0,f32_bits(42))",
                &format!("expect(r,0,0,f32_bits({expected}))"),
            );
        let output = preview(&scratch, &program);
        success(&output);
        let ir = std::str::from_utf8(&output.stdout).unwrap();
        assert!(ir.contains(&format!("br i1 {outer}, label %next2, label %next9")));
        assert!(ir.contains(&format!("br i1 {inner}, label %next5, label %next7")));
        assert_eq!(ir.matches("call i32 @vq_storage_fill(").count(), 3);
        assert_eq!(ir.matches("call i32 @vq_storage_allocate(").count(), 3);
        assert_eq!(ir.matches("call void @vstorage_delete(").count(), 2);
        let control = scratch.build_and_run("app/Vastitas.toml");
        assert_eq!(control.status, status);
        if status == 1 {
            assert!(
                control.stderr.contains("E_NATIVE_EXPECT"),
                "{}",
                control.stderr
            );
        }
        #[cfg(feature = "llvm-native")]
        {
            let binary = scratch.0.join("llvm-branch");
            success(
                &scratch
                    .command("build", "app/Vastitas.toml")
                    .args(["--llvm-preview", "-o"])
                    .arg(&binary)
                    .output()
                    .unwrap(),
            );
            let actual = std::process::Command::new(binary).output().unwrap();
            assert_eq!(common::ran(&actual), control);
            assert_eq!(String::from_utf8_lossy(&actual.stderr), control.stderr);
        }
    }
}

#[test]
fn storage_branch_checks_the_cold_arm_and_never_uses_a_slot_projection_as_a_decision() {
    let source = include_str!("../llvm/fixtures/StorageBranch.vast");
    let scratch = Scratch::empty("LLVM checked branch revision");
    success(&preview(&scratch, source));
    let revision = scratch
        .command("check", "app/Vastitas.toml")
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&revision);
    let saved = scratch.0.join("branch.json");
    std::fs::write(&saved, &revision.stdout).unwrap();
    success(&preview(
        &scratch,
        &source.replace("f32_bits(17)", "f32_bits(18)"),
    ));
    let stale = scratch
        .command("check", "app/Vastitas.toml")
        .args(TARGET)
        .arg("--expect-function-revision")
        .arg(&saved)
        .output()
        .unwrap();
    expect_code(&stale, "E_FUNCTION_REVISION");
    assert!(stale.stdout.is_empty());

    let malformed = preview(&scratch, &source.replace("drop(second);", ""));
    expect_code(&malformed, "E_RESOURCE_JOIN");
    assert!(malformed.stdout.is_empty());
    let dynamic = source.replace("if true {", "let flag: Bool = value { true }; if flag {");
    let rejected = preview(&scratch, &dynamic);
    expect_code(&rejected, "E_UNSUPPORTED");
    assert!(rejected.stdout.is_empty());
    success(
        &scratch
            .command("check", "app/Vastitas.toml")
            .output()
            .unwrap(),
    );
}
