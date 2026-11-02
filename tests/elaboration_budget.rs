//! Aggregate work is rejected by the common kernel before expensive body copies.
mod common;
use common::{Scratch, cli, kernel, request, success};
use std::fmt::Write;
use std::fs;

fn body(lets: usize) -> String {
    let mut source = String::new();
    for i in 0..lets {
        writeln!(source, "let value{i}: Int = 0 + 1;").unwrap();
    }
    source.push('0');
    source
}

fn method(name: &str, lets: usize) -> String {
    format!(
        "method {name}(a: Any, b: Any, c: Any, d: Any, e: Any, f: Any) -> Int {{ {} }}",
        body(lets)
    )
}

fn family(name: &str, lets: usize) -> String {
    format!(
        "generic {name}(a, b, c, d, e, f) {{ domain (Int, Int, Int, Int, Int, Int); }}\n{}\n",
        method(name, lets)
    )
}

fn assert_budget(response: &serde_json::Value) {
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(response["diagnostics"][0]["code"], "E_LIMIT", "{response}");
    assert!(
        response["diagnostics"][0]["message"]
            .as_str()
            .unwrap()
            .contains("program-wide elaboration"),
        "{response}"
    );
    assert!(response.get("lean_source").is_none(), "{response}");
}

#[test]
fn expanded_body_work_is_bounded_for_check_emit_and_native_build() {
    let source = family("wide", 300) + "fn main() -> Int { 0 }";
    let raw = request(&source, "large-dispatch.vast");
    for mode in ["check", "emit"] {
        assert_budget(&kernel(&raw, mode));
    }
    let scratch = Scratch::empty("elaboration budget");
    let input = scratch.write("large.vast", &source);
    let output = scratch.write("program", "previous artifact");
    for mode in ["check", "build"] {
        let mut command = cli();
        command.arg(mode).arg(&input);
        if mode == "build" {
            command.arg("-o").arg(&output);
        }
        let result = command.output().unwrap();
        assert!(!result.status.success());
        let message = String::from_utf8_lossy(&result.stderr);
        assert!(message.contains("E_LIMIT"), "{message}");
        assert!(message.contains("program-wide elaboration"), "{message}");
    }
    assert_eq!(fs::read_to_string(output).unwrap(), "previous artifact");
}

#[test]
fn separate_families_cannot_reset_the_aggregate_budget() {
    // Each family is below the limit; all three together exceed it. The unused
    // broad method still covers every key, not just the single declared domain.
    let source = (0..3)
        .map(|i| family(&format!("wide{i}"), 25))
        .collect::<String>()
        + "fn main() -> Int { 0 }";
    assert_budget(&kernel(request(&source, "many-families.vast"), "check"));
    let small = family("wide", 3) + "fn main() -> Int { wide(1, 2, 3, 4, 5, 6) }";
    success(&common::check(&small, "small-dispatch.vast"));
}

#[test]
fn unapplied_and_applied_bodies_share_the_preparation_budget() {
    for (ordinary_lets, unused_lets) in [(0, 300), (25, 50)] {
        let scratch = Scratch::empty("unapplied work");
        let manifest = scratch.write(
            "Vastitas.toml",
            "[package]\nname='budget'\nversion='0.1.0'\nroot='main.vast'\n",
        );
        scratch.write(
            "main.vast",
            &(family("wide", ordinary_lets)
                + &format!(
                    "pub contribution unused : wide {{ {} }}\nfn main() -> Int {{ 0 }}",
                    method("wide", unused_lets)
                )),
        );
        let result = cli()
            .args(["check", "--manifest-path"])
            .arg(manifest)
            .output()
            .unwrap();
        let message = String::from_utf8_lossy(&result.stderr);
        assert!(
            !result.status.success(),
            "accepted {ordinary_lets}/{unused_lets}"
        );
        assert!(message.contains("E_LIMIT"), "{message}");
        assert!(message.contains("program-wide elaboration"), "{message}");
    }
}

#[test]
fn concrete_fn_specializations_charge_actual_body_work() {
    // Source preflight is small and the instance count is below 4096. Distinct
    // callbacks require enough copies of the same body to exhaust actual work.
    let mut source = String::new();
    for i in 0..1100 {
        writeln!(source, "fn callback{i}(x: Int) -> Int {{ x }}").unwrap();
    }
    writeln!(
        source,
        "fn heavy(callback: Fn<Int, Int>) -> Int {{ {} }}",
        body(256)
    )
    .unwrap();
    source.push_str("fn main() -> Int {\n");
    for i in 0..1100 {
        writeln!(source, "let result{i} = heavy(callback{i});").unwrap();
    }
    source.push_str("0 }");
    assert_budget(&kernel(request(&source, "specialized-work.vast"), "check"));
}
