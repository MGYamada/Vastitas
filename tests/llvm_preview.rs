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

fn preview(s: &Scratch, source: &str) -> Output {
    s.write_package("app", source, "");
    s.command("check", "app/Vastitas.toml")
        .args(TARGET)
        .output()
        .unwrap()
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
        "fn main() -> Int { let x = show!(-1); x }",
        "resource fn main() -> Int { value { 3 } }",
        "pub fn pick(a: Bool) -> Bool { a }",
    ] {
        let o = preview(&s, source);
        success(&s.command("check", "app/Vastitas.toml").output().unwrap());
        expect_code(&o, "E_UNSUPPORTED");
        assert!(o.stdout.is_empty(), "partial bytes for {source}");
    }
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
        [TARGET.as_slice(), &["--print-function-revision"]].concat(),
    ] {
        let o = s
            .command("check", "app/Vastitas.toml")
            .args(options)
            .output()
            .unwrap();
        expect_code(&o, "E_USAGE");
    }
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
    s.write(
        "app/main.vast",
        "fn choose(n: Int) -> Int { if n == 0 { 1 } else { n } } fn main() -> Int { choose(4) }",
    );
    let unsupported = build().output().unwrap();
    expect_code(&unsupported, "E_UNSUPPORTED");
    assert_eq!(fs::read(&output).unwrap(), saved);
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
