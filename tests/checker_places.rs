//! Diagnostics of the checker about a construct of a source file have the
//! place of that construct (#735). They used to have the place `FILE:1:1` of
//! the first input: the root manifest in manifest mode, the entry file in
//! flat mode.
mod common;
use common::Scratch;

/// The first diagnostic line of checking `source` as the root module of a
/// package, from the name of the file on.
#[track_caller]
fn package_diagnostic(source: &str) -> String {
    let s = Scratch::empty("checker places");
    s.write(
        "Vastitas.toml",
        "[package]\nname = \"places\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n",
    );
    s.write("main.vast", source);
    let output = s.check_manifest("Vastitas.toml");
    first_line(&output, "main.vast:")
}

#[track_caller]
fn first_line(output: &std::process::Output, file: &str) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(!output.status.success(), "accepted:\n{stderr}");
    common::assert_source_names(&stderr);
    let first = stderr.lines().next().unwrap();
    let at = first
        .find(file)
        .unwrap_or_else(|| panic!("no place in {file}: {stderr}"));
    first[at..].to_string()
}

#[test]
fn an_entry_point_with_another_signature_is_reported_at_main() {
    let source = "fn helper() -> Int { 1 }\n\nfn main(n: Int) -> Int { n }\n";
    assert_eq!(
        package_diagnostic(source),
        "main.vast:3:1: E_MAIN: entry point must have signature fn main() -> Int"
    );
    // Flat mode, with a comment on line 1.
    let output = common::check(&format!("// comment\n{source}"), "flat.vast");
    assert_eq!(
        first_line(&output, "flat.vast:"),
        "flat.vast:4:1: E_MAIN: entry point must have signature fn main() -> Int"
    );
}

#[test]
fn a_repeated_name_is_reported_at_the_second_declaration_with_the_name() {
    for (source, expected) in [
        (
            "indexed marker Kind;\nfn Kind() -> Int { 1 }\nfn main() -> Int { 0 }\n",
            "main.vast:2:1: E_DUPLICATE: `Kind` is declared more than once in this module",
        ),
        (
            "fn Kind() -> Int { 1 }\nindexed marker Kind;\nfn main() -> Int { 0 }\n",
            "main.vast:2:1: E_DUPLICATE: `Kind` is declared more than once in this module",
        ),
        (
            "indexed marker Kind;\nindexed marker Kind;\nfn main() -> Int { 0 }\n",
            "main.vast:2:1: E_DUPLICATE: `Kind` is declared more than once in this module",
        ),
        (
            "fn f() -> Int { 1 }\nfn f() -> Int { 2 }\nfn main() -> Int { 0 }\n",
            "main.vast:2:1: E_DUPLICATE: `f` is declared more than once in this module",
        ),
    ] {
        assert_eq!(package_diagnostic(source), expected, "{source}");
    }
}

#[test]
fn errors_of_a_type_in_a_signature_are_reported_at_the_signature() {
    let natural = "indexed marker QQ;
indexed implementation Grid(QQ, affine_descriptor) capabilities();
indexed global Base(Grid);
indexed family Point(object(Grid), object(Grid)) = point constraints(same_base(0, 1));
fn f(p: self::Point<3, Base>) -> Int { 0 }
fn main() -> Int { 0 }
";
    assert_eq!(
        package_diagnostic(natural),
        "main.vast:5:9: E_TYPE: natural literal used at a non-natural index"
    );
    let legacy = "indexed marker K;\nfn f(X: Scheme) -> Int { 0 }\nfn main() -> Int { 0 }\n";
    assert_eq!(
        package_diagnostic(legacy),
        "main.vast:2:6: E_TYPE: legacy geometry syntax requires exactly one explicit library compatibility export"
    );
    let result = "indexed marker K;\nfn f() -> Scheme { 0 }\nfn main() -> Int { 0 }\n";
    assert_eq!(
        package_diagnostic(result),
        "main.vast:2:1: E_TYPE: legacy geometry syntax requires exactly one explicit library compatibility export"
    );
}

/// An indexed type `F<…>` that its rules do not admit has the place of the
/// path of its family, in a parameter and in a result type; an argument that
/// is a name has its own place. `Object<D, K>` has no place of its own, so it
/// has the place of its parameter.
#[test]
fn an_invalid_indexed_type_in_a_signature_is_reported_at_its_family() {
    let prelude = "indexed marker QQ;
indexed implementation Grid(QQ, affine_descriptor) capabilities();
indexed global Base(Grid);
indexed family Same(object(Grid), object(Grid)) = token constraints(same_object(0, 1));
";
    for (signature, expected) in [
        (
            "fn f(X: Object<Grid, QQ>, p:   self::Same<X, Base>) -> Int { 0 }",
            "main.vast:5:32: E_TYPE: invalid indexed annotation Same<X, Base>",
        ),
        (
            "fn f(X: Object<Grid, QQ>) ->   self::Same<X, Base> { 0 }",
            "main.vast:5:32: E_TYPE: invalid indexed annotation Same<X, Base>",
        ),
        (
            "fn f(n: Int, p: self::Same<n, Base>) -> Int { 0 }",
            "main.vast:5:28: E_TYPE: an object index requires an object value",
        ),
        (
            "fn f(X:   Object<Base, QQ>) -> Int { 0 }",
            "main.vast:5:6: E_TYPE: invalid indexed annotation Base<QQ>",
        ),
    ] {
        assert_eq!(
            package_diagnostic(&format!("{prelude}{signature}\nfn main() -> Int {{ 0 }}\n")),
            expected,
            "{signature}"
        );
    }
}

/// More than 4096 indexed declarations are reported at the 4097th, whose
/// place is its keyword `indexed`.
#[test]
fn the_declaration_beyond_the_limit_on_indexed_declarations_has_the_place() {
    let markers = |count: usize| -> String {
        (0..count)
            .map(|i| format!("pub indexed marker M{i};\n"))
            .collect::<String>()
            + "fn main() -> Int { 0 }\n"
    };
    assert_eq!(
        package_diagnostic(&markers(4097)),
        "main.vast:4097:5: E_LIMIT: more than 4096 indexed declarations"
    );
}
