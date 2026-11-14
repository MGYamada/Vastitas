//! Rendered diagnostics: their codes, their messages and the assertions on them.
use std::process::Output;

/// The diagnostic codes in rendered compiler or executable output, in order.
/// A diagnostic line is `<path>:<line>:<column>: CODE: message`, `CODE: message`
/// or `<prefix>: CODE: message` (for example Lean's `uncaught exception:`).
/// Each line contributes at most its first code; notes (which may quote other
/// codes), usage text and message continuations contribute none.
pub fn diagnostic_codes(stderr: &str) -> Vec<String> {
    stderr
        .lines()
        .filter(|line| !line.starts_with("note: ") && !line.contains(": note: "))
        .filter_map(|line| {
            let starts = std::iter::once(0).chain(line.match_indices(": ").map(|(at, _)| at + 2));
            starts
                .filter_map(|start| {
                    let rest = &line[start..];
                    let end = rest
                        .find(|c: char| !(c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_'))
                        .unwrap_or(rest.len());
                    let code = &rest[..end];
                    (code.len() > 2 && code.starts_with("E_") && rest[end..].starts_with(": "))
                        .then(|| code.to_string())
                })
                .next()
        })
        .collect()
}
/// Asserts that `output` failed and that its first diagnostic code is exactly
/// `code`. A substring match would let `E_TYPE` accept `E_RESOURCE_TYPE` and an
/// unrelated parse error accept any expected rejection. Returns stderr.
#[track_caller]
pub fn expect_code(output: &Output, code: &str) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        !output.status.success(),
        "expected {code}, but the command succeeded\nstdout:\n{}\nstderr:\n{stderr}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_first_code(&stderr, code);
    stderr
}
/// Asserts that the first diagnostic code in rendered output is exactly `code`.
#[track_caller]
pub fn assert_first_code(stderr: &str, code: &str) {
    let codes = diagnostic_codes(stderr);
    assert_eq!(
        codes.first().map(String::as_str),
        Some(code),
        "expected first diagnostic {code}; found {codes:?}\nstderr:\n{stderr}"
    );
    assert_source_names(&message_text(stderr));
}
/// The rendered diagnostics without the `<path>:<line>:<column>: ` location of
/// each line, so that a test can speak about the messages alone.
pub fn message_text(rendered: &str) -> String {
    let digits = |text: &str| text.bytes().take_while(u8::is_ascii_digit).count();
    let message = |line: &str| -> String {
        for (at, _) in line.match_indices(':') {
            let rest = &line[at + 1..];
            let row = digits(rest);
            if row == 0 || !rest[row..].starts_with(':') {
                continue;
            }
            let rest = &rest[row + 1..];
            let column = digits(rest);
            if column > 0 && rest[column..].starts_with(": ") {
                return rest[column + 2..].to_string();
            }
        }
        line.to_string()
    };
    rendered.lines().map(message).collect::<Vec<_>>().join("\n")
}
/// The decimal character codes of `text` joined by `_`: how an internal
/// declaration symbol of the kernel encodes a package location.
pub fn symbol_encoding(text: &str) -> String {
    let codes: Vec<String> = text.chars().map(|c| (c as u32).to_string()).collect();
    codes.join("_")
}
/// Asserts that diagnostics name declarations as the source does: `text` holds
/// no internal declaration symbol of the kernel (`ns_f_` and a length) and no
/// run of eight or more decimal numbers joined by `_`, which is how such a
/// symbol encodes the canonical location of a package. Every rejection that a
/// test checks through this harness passes here.
#[track_caller]
pub fn assert_source_names(text: &str) {
    let symbol = text
        .match_indices("ns_f_")
        .any(|(at, prefix)| text[at + prefix.len()..].starts_with(|c: char| c.is_ascii_digit()));
    let encoded = text
        .split(|c: char| !(c.is_ascii_digit() || c == '_'))
        .any(|run| run.split('_').filter(|number| !number.is_empty()).count() >= 8);
    assert!(
        !symbol && !encoded,
        "a diagnostic names a declaration by an internal symbol or an encoded path:\n{text}"
    );
}
/// Like [`expect_code`], for `expected` written as `CODE` or `CODE: message
/// prefix`: the code must match exactly and the whole text must appear.
#[track_caller]
pub fn expect_diagnostic(output: &Output, expected: &str) -> String {
    let code = expected.split(':').next().unwrap();
    let stderr = expect_code(output, code);
    assert!(stderr.contains(expected), "expected {expected:?}: {stderr}");
    stderr
}
