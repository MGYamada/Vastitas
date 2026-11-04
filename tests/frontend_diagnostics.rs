//! Replay source → frontend diagnostic cases from
//! `fixtures/frontend-diagnostics.json` through the CLI. The backend is absent,
//! so each expectation concerns the frontend alone. The cases are plain data
//! that a Lean-native frontend (#152) can replay unchanged.
mod common;
use common::{Scratch, cli, root};
use serde_json::Value;

fn check(input: &str, source: &str) -> String {
    let s = Scratch::empty("frontend diagnostics");
    let mut command = cli();
    command
        .arg("check")
        .env("VASTITAS_KERNEL", s.0.join("absent backend"));
    match input {
        "flat" => {
            command.arg(s.write("case.vast", source));
        }
        "package" => {
            s.write(
                "Vastitas.toml",
                "[package]\nname = 'case'\nversion = '0.1.0'\nroot = 'case.vast'\n",
            );
            s.write("case.vast", source);
            command
                .arg("--manifest-path")
                .arg(s.0.join("Vastitas.toml"));
        }
        _ => panic!("unknown input kind {input}"),
    }
    let output = command.output().unwrap();
    assert!(
        !output.status.success(),
        "the absent backend was not reported"
    );
    String::from_utf8(output.stderr).unwrap()
}

// Diagnostics must not carry terminal controls, bidirectional controls or other
// invisible format characters from the source.
fn printable(diagnostics: &str) -> bool {
    diagnostics.chars().all(|ch| {
        let format = matches!(
            ch as u32,
            0x00AD
                | 0x061C
                | 0x200B..=0x200F
                | 0x202A..=0x202E
                | 0x2060..=0x206F
                | 0xFE00..=0xFE0F
                | 0xFEFF
                | 0xE0000..=0xE0FFF
        );
        ch == '\n' || !(ch.is_control() || format)
    })
}

#[test]
fn source_cases_produce_the_recorded_frontend_diagnostics() {
    let text =
        std::fs::read_to_string(root().join("tests/fixtures/frontend-diagnostics.json")).unwrap();
    let fixture: Value = serde_json::from_str(&text).unwrap();
    let cases = fixture["cases"].as_array().unwrap();
    assert!(!cases.is_empty());
    let mut failures = Vec::new();
    for (index, case) in cases.iter().enumerate() {
        let source = case["source"].as_str().unwrap();
        let diagnostics = check(case["input"].as_str().unwrap(), source);
        let first = diagnostics.lines().next().unwrap_or_default();
        let expected = match case["code"].as_str() {
            None => first
                .contains("E_BACKEND")
                .then_some(())
                .ok_or("frontend rejected it"),
            Some(code) => {
                let location = format!("case.vast:{}:{}: {code}: ", case["line"], case["column"]);
                let message = case["message"].as_str().unwrap();
                (first.contains(&location) && first.contains(message))
                    .then_some(())
                    .ok_or("unexpected first diagnostic")
            }
        };
        if let Err(reason) = expected.and_then(|()| {
            printable(&diagnostics)
                .then_some(())
                .ok_or("diagnostics contain control or format characters")
        }) {
            failures.push(format!(
                "case {index} (#{}): {reason}\nsource: {source:?}\nexpected: {} {}:{} {}\nactual: {diagnostics:?}",
                case["issue"], case["code"], case["line"], case["column"], case["message"]
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
