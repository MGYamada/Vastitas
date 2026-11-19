//! Edition syntax and the native comparison corpus share the public compiler path.
mod common;
use common::{check, exits, native, reject};

#[test]
fn implicit_overloads_select_static_targets_in_both_branches() {
    let source = include_str!("fixtures/FamilyComparison.vast");
    native(source, &[], exits(0), "FamilyComparison.vast");
}

#[test]
fn static_family_values_are_selected_by_argument_key() {
    let declarations = "fn step(x: Nat) -> Nat { x - 1 } fn step(x: Int) -> Int { x + 1 }";
    native(
        &format!(
            "{declarations} fn call(f: Fn<(Int), Int>) -> Int {{ f(40) }} fn main() -> Int {{ let n: Nat = 2; let go = step; int(go(n)) + call(step) }}"
        ),
        &[],
        exits(42),
        "static.vast",
    );
    let bad = format!(
        "{declarations} fn call(f: Fn<(Int), Bool>) -> Bool {{ f(0) }} fn main() -> Int {{ if call(step) {{ 1 }} else {{ 0 }} }}"
    );
    assert!(!check(&bad, "result.vast").status.success());
}

#[test]
fn retired_spellings_do_not_silently_register_a_family() {
    for old in [
        "generic step(x) { domain (Int); }",
        "method step(x: Int) -> Int { x }",
        "abstract method step(x: Int) -> Int { domain (Int); }",
    ] {
        reject(old, "E_PARSE", "legacy.vast");
    }
}
