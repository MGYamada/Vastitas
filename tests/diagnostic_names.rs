//! A diagnostic names a declaration as the source does: by its path
//! `package::module::name`, and a binder by its spelling. The kernel checks the
//! headers of a package program under internal symbols that encode the canonical
//! location of each package; no message may print one. Each test pins the
//! complete message text of one rejection, without its `path:line:column:`
//! locations. The last test pins the locations as well: a note about a method
//! must point at that method (#727).
//!
//! A program with a grant uses the latest wire protocol. A package program
//! without edit declarations uses an earlier one, whose rejections also pass
//! through `LegacySource.describeDiagnostic`. The tests say where they use the
//! earlier protocol.
mod common;
use common::{Scratch, checked_replace, expect_code, message_text, symbol_encoding};

const BASE: &str = "pub generic choose(x, y) { domain (Int, Int); }
method choose(x: Number, y: Number) -> Int { 0 }
pub grant integers : choose to addon { domain (Int, Int); }
";
const ADDON: &str =
    "pub contribution sum : base::choose { method base::choose(x: Int, y: Int) -> Int { x + y } }";
const EVENTS: &str =
    "borrow base::integers as edit; apply addon::sum using edit; return edit; seal base::choose;";
const CALL: &str = "fn main() -> Int { base::choose(40, 2) }";

/// The packages `base`, `addon` (which depends on `base`) and the root `app`
/// (which depends on both). `events` is the body of the assembly of `app`; an
/// empty one declares no assembly.
fn packages(base: &str, addon: &str, events: &str, main: &str) -> Scratch {
    let s = Scratch::empty("diagnostic names");
    s.write_package("base", base, "");
    s.write_package("addon", addon, "base={path='../base'}");
    let assembly = if events.is_empty() {
        String::new()
    } else {
        format!("assembly {{ {events} }} ")
    };
    s.write_package(
        "app",
        &format!("{assembly}{main}"),
        "base={path='../base'}\naddon={path='../addon'}",
    );
    s
}

/// Checks `app`, which must be rejected with `code` first, and returns the
/// rendered diagnostics.
#[track_caller]
fn rendered(s: &Scratch, code: &str) -> String {
    expect_code(&s.check_manifest("app/Vastitas.toml"), code)
}

/// Checks `app`, which must be rejected with `code` first, and returns the
/// lines of the message text. No line may hold an internal symbol, the scratch
/// directory or the encoding of that directory in an internal symbol.
#[track_caller]
fn rejected(s: &Scratch, code: &str) -> Vec<String> {
    let text = message_text(&rendered(s, code));
    assert!(
        !text.contains("ns_f_") && !text.contains("ns_b_"),
        "an internal symbol names a declaration or a binder:\n{text}"
    );
    for directory in [s.0.clone(), s.0.canonicalize().unwrap()] {
        let directory = directory.to_str().unwrap();
        assert!(
            !text.contains(directory) && !text.contains(&symbol_encoding(directory)),
            "a message holds the location of the scratch directory:\n{text}"
        );
    }
    text.lines().map(str::to_owned).collect()
}

const DUPLICATE: [&str; 3] = [
    "E_DUPLICATE: generic 'base::choose': duplicate normalized method signature",
    "note: candidate method for generic 'base::choose' declared here",
    "note: candidate method for generic 'base::choose' declared here",
];

#[test]
fn equal_methods_of_two_contributions_name_the_generic_by_its_path() {
    let addon = format!(
        "{ADDON} pub contribution other : base::choose {{ method base::choose(a: Int, b: Int) -> Int {{ a * b }} }}"
    );
    let events = "borrow base::integers as a; apply addon::sum using a; apply addon::other using a; return a; seal base::choose;";
    assert_eq!(
        rejected(&packages(BASE, &addon, events, CALL), "E_DUPLICATE"),
        DUPLICATE
    );
}

#[test]
fn equal_methods_inside_one_contribution_name_the_generic_by_its_path() {
    let addon = checked_replace(
        ADDON,
        "{ x + y } }",
        "{ x + y } method base::choose(a: Int, b: Int) -> Int { a * b } }",
    );
    assert_eq!(
        rejected(&packages(BASE, &addon, EVENTS, CALL), "E_DUPLICATE"),
        DUPLICATE
    );
}

#[test]
fn equal_methods_of_a_contribution_and_the_defining_module_name_the_generic_by_its_path() {
    let base = checked_replace(BASE, "x: Number, y: Number", "x: Int, y: Int");
    assert_eq!(
        rejected(&packages(&base, ADDON, EVENTS, CALL), "E_DUPLICATE"),
        DUPLICATE
    );
}

#[test]
fn a_repeated_generic_parameter_is_named_as_it_is_written() {
    let repeated = "generic g(x, x) { domain (Int, Int); } method g(a: Int, b: Int) -> Int { a }";
    let expected = ["E_DUPLICATE: duplicate generic parameter 'x'"];
    assert_eq!(
        rejected(
            &packages(&format!("{BASE}{repeated}"), ADDON, EVENTS, CALL),
            "E_DUPLICATE"
        ),
        expected
    );
    // A package program without edit declarations uses an earlier protocol.
    let plain = packages(
        &format!("pub fn one() -> Int {{ 1 }} {repeated}"),
        "pub fn two() -> Int { 2 }",
        "",
        "fn main() -> Int { base::one() }",
    );
    assert_eq!(rejected(&plain, "E_DUPLICATE"), expected);
}

#[test]
fn a_call_outside_the_domain_of_a_dependency_generic_names_it_by_its_path() {
    let expected =
        ["E_DISPATCH_DOMAIN: generic 'base::choose' does not admit call key (Bool, Int)"];
    let call = "fn main() -> Int { base::choose(true, 2) }";
    // The assembly of `app` edits the generic.
    assert_eq!(
        rejected(&packages(BASE, ADDON, EVENTS, call), "E_DISPATCH_DOMAIN"),
        expected
    );
    // No assembly edits it.
    assert_eq!(
        rejected(&packages(BASE, ADDON, "", call), "E_DISPATCH_DOMAIN"),
        expected
    );
    // The path starts with the name of the package in its manifest, even when
    // the source reaches the package through another dependency alias.
    let s = packages(BASE, ADDON, "", call);
    s.write_package(
        "app",
        "fn main() -> Int { lib::choose(true, 2) }",
        "lib={path='../base'}\naddon={path='../addon'}",
    );
    assert_eq!(rejected(&s, "E_DISPATCH_DOMAIN"), expected);
    // No package declares a grant or a contribution: an earlier protocol.
    let base = BASE.lines().take(2).collect::<Vec<_>>().join("\n");
    assert_eq!(
        rejected(
            &packages(&base, "pub fn two() -> Int { 2 }", "", call),
            "E_DISPATCH_DOMAIN"
        ),
        expected
    );
    // A generic in a module of the dependency is named with that module.
    let nested =
        "pub mod inner { pub generic pick(x) { domain (Int); } method pick(x: Int) -> Int { x } }";
    assert_eq!(
        rejected(
            &packages(
                &format!("{BASE}{nested}"),
                ADDON,
                EVENTS,
                "fn main() -> Int { base::inner::pick(true) }"
            ),
            "E_DISPATCH_DOMAIN"
        ),
        ["E_DISPATCH_DOMAIN: generic 'base::inner::pick' does not admit call key (Bool)"]
    );
}

#[test]
fn an_ambiguity_left_at_the_seal_names_the_generic_and_its_candidates_by_path() {
    let base = checked_replace(
        BASE,
        "pub grant",
        "method choose(x: Int, y: Number) -> Int { 1 }\npub grant",
    );
    let addon = checked_replace(ADDON, "x: Int, y: Int", "x: Number, y: Int");
    assert_eq!(
        rejected(
            &packages(&base, &addon, EVENTS, CALL),
            "E_DISPATCH_AMBIGUOUS"
        ),
        [
            "E_DISPATCH_AMBIGUOUS: generic 'base::choose': multiple incomparable optimal methods at key (Int, Int)",
            "note: candidate method `base::choose(Int, Number)` declared here; selectors are not narrower in every argument",
            "note: candidate method `base::choose(Number, Int)` declared here; selectors are not narrower in every argument",
            "note: help: declare `base::choose(Int, Int)` to resolve this key; recheck the entire family after editing",
        ]
    );
}

#[test]
fn an_uncovered_key_names_the_generic_and_its_candidates_by_path() {
    // A generic that the assembly edits.
    let base = checked_replace(
        BASE,
        "domain (Int, Int); }\nmethod",
        "domain (Int, Int), (Bool, Bool); }\nmethod",
    );
    assert_eq!(
        rejected(&packages(&base, ADDON, EVENTS, CALL), "E_DISPATCH_COVERAGE"),
        [
            "E_DISPATCH_COVERAGE: generic 'base::choose': declared domain key has no applicable method at key (Bool, Bool)",
            "note: candidate method `base::choose(Number, Number)` declared here; selector mismatch",
            "note: candidate method `base::choose(Int, Int)` declared here; selector mismatch",
            "note: key (Bool, Bool) comes from this generic's domain",
            "note: help: declare a method for `base::choose` applicable at (Bool, Bool); recheck every promised domain",
        ]
    );
    // A generic of the dependency that no assembly edits.
    let base = format!(
        "{BASE}pub generic other(x) {{ domain (Bool); }} method other(x: Number) -> Int {{ 0 }}"
    );
    assert_eq!(
        rejected(&packages(&base, ADDON, EVENTS, CALL), "E_DISPATCH_COVERAGE"),
        [
            "E_DISPATCH_COVERAGE: generic 'base::other': declared domain key has no applicable method at key (Bool)",
            "note: candidate method `base::other(Number)` declared here; selector mismatch",
            "note: key (Bool) comes from this generic's domain",
            "note: help: declare a method for `base::other` applicable at (Bool); recheck every promised domain",
        ]
    );
}

#[test]
fn abstract_types_are_named_by_path_in_hierarchy_notes_and_candidate_signatures() {
    let cycle = format!("{BASE}abstract type A <: B; abstract type B <: A;");
    assert_eq!(
        rejected(&packages(&cycle, ADDON, EVENTS, CALL), "E_HIERARCHY"),
        [
            "E_HIERARCHY: abstract hierarchy contains a cycle or invalid nominal relation",
            "note: 'base::A' participates in this inheritance cycle",
            "note: 'base::B' participates in this inheritance cycle",
        ]
    );
    let builtin = format!("{BASE}abstract type Wide <: Number; subtype Bool <: Wide;");
    assert_eq!(
        rejected(&packages(&builtin, ADDON, EVENTS, CALL), "E_HIERARCHY"),
        [
            "E_HIERARCHY: abstract declarations change a builtin subtype relation",
            "note: membership propagates through 'base::Wide'",
        ]
    );
    let base = format!(
        "pub abstract type Small <: Number; subtype Int <: Small;\n{}",
        checked_replace(
            BASE,
            "pub grant",
            "method choose(x: Small, y: Number) -> Int { 1 }\npub grant"
        )
    );
    let addon = checked_replace(ADDON, "x: Int, y: Int", "x: Number, y: base::Small");
    assert_eq!(
        rejected(
            &packages(&base, &addon, EVENTS, CALL),
            "E_DISPATCH_AMBIGUOUS"
        ),
        [
            "E_DISPATCH_AMBIGUOUS: generic 'base::choose': multiple incomparable optimal methods at key (Int, Int)",
            "note: candidate method `base::choose(base::Small, Number)` declared here; selectors are not narrower in every argument",
            "note: candidate method `base::choose(Number, base::Small)` declared here; selectors are not narrower in every argument",
            "note: help: declare `base::choose(base::Small, base::Small)` to resolve this key; recheck the entire family after editing",
        ]
    );
}

#[test]
fn the_audit_of_an_unapplied_contribution_names_the_generic_by_its_path() {
    let addon = format!(
        "{ADDON} pub contribution spare : base::choose {{ method base::choose(x: Int) -> Int {{ x }} }}"
    );
    assert_eq!(
        rejected(&packages(BASE, &addon, EVENTS, CALL), "E_ARITY"),
        [
            "E_ARITY: generic 'base::choose': method selector arity differs from its generic",
            "note: candidate method for generic 'base::choose' declared here",
        ]
    );
}

/// Checks `app`, which must be rejected with `code` first, and returns each
/// rendered line with its location relative to the scratch directory:
/// `package/main.vast:line:column: text`.
#[track_caller]
fn located(s: &Scratch, code: &str) -> Vec<String> {
    let directory = format!("{}/", s.0.canonicalize().unwrap().display());
    rendered(s, code)
        .lines()
        .map(|line| {
            line.strip_prefix(&directory)
                .unwrap_or_else(|| panic!("no location in the scratch directory: {line}"))
                .to_owned()
        })
        .collect()
}

// #727: the audit numbers a method by its place in its contribution. The final
// surface holds no method of an unapplied contribution, and the same number
// names another method there: first the method of `base`, then the method of
// the applied `sum`. Every note must point at the method of `spare` that the
// audit rejects; the diagnostic itself stays at the generic.
#[test]
fn the_audit_of_an_unapplied_contribution_points_at_the_method_it_rejects() {
    const ARITY: &str = "base/main.vast:1:5: E_ARITY: generic 'base::choose': method selector arity differs from its generic";
    const ACCEPTED: &str = "    method base::choose(a: Number, b: Int) -> Int { 0 }";
    const UNARY: &str = "    method base::choose(c: Int) -> Int { c }";
    // `sum` and its method are on line 1 of `addon`, the methods of `spare`
    // on line 3 and after.
    let spare = |methods: &[&str]| {
        format!(
            "{ADDON}\npub contribution spare : base::choose {{\n{}\n}}",
            methods.join("\n")
        )
    };
    let note = |line: usize| {
        format!(
            "addon/main.vast:{line}:5: note: candidate method for generic 'base::choose' declared here"
        )
    };
    // Its first method: that number names the method of `base`.
    assert_eq!(
        located(&packages(BASE, &spare(&[UNARY]), EVENTS, CALL), "E_ARITY"),
        [ARITY.to_string(), note(3)]
    );
    // Its second method: that number names the method of the applied `sum`.
    assert_eq!(
        located(
            &packages(BASE, &spare(&[ACCEPTED, UNARY]), EVENTS, CALL),
            "E_ARITY"
        ),
        [ARITY.to_string(), note(4)]
    );
    // Another code of the audit with a candidate note.
    let unsupported = "    method base::choose(c: Int, d: Int) -> Int requires (Foo) { c }";
    assert_eq!(
        located(
            &packages(BASE, &spare(&[unsupported]), EVENTS, CALL),
            "E_CAPABILITY"
        ),
        [
            "base/main.vast:1:5: E_CAPABILITY: generic 'base::choose': unsupported static capability 'Foo'"
                .to_string(),
            note(3)
        ]
    );
    // No assembly applies a contribution: the final surface holds one method,
    // and the number of the second method of `spare` names none.
    assert_eq!(
        located(
            &packages(BASE, &spare(&[ACCEPTED, UNARY]), "", CALL),
            "E_ARITY"
        ),
        [ARITY.to_string(), note(4)]
    );
}
