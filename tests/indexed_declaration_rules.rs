//! Each rule of classifications, global objects, families, package
//! declarations and primitives has a message of its own, which states the
//! broken rule and names the declarations (#736). The four size limits of one
//! indexed declaration are `E_LIMIT`. Before, every such declaration gave
//! `E_TYPE: invalid indexed declaration, package, or primitive contract`.
mod common;
use common::{Scratch, cli, success};

fn check(source: &str) -> std::process::Output {
    let s = Scratch::empty("indexed declaration rules");
    s.write(
        "Vastitas.toml",
        "[package]\nname = \"rules\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n",
    );
    s.write("main.vast", source);
    cli()
        .current_dir(&s.0)
        .args(["check", "--manifest-path", "Vastitas.toml"])
        .output()
        .unwrap()
}

/// The first diagnostic of a rejected program, from the file name on.
#[track_caller]
fn first_diagnostic(source: &str) -> String {
    let output = check(source);
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(!output.status.success(), "accepted {source}");
    common::assert_source_names(&stderr);
    let first = stderr.lines().next().unwrap();
    first[first.find("main.vast:").expect(&stderr)..].to_string()
}

const DESCRIPTORS: &str = "indexed marker QQ;
indexed implementation Grid(QQ, affine_descriptor) capabilities(origin, dimension);
indexed implementation Plain(QQ, affine_descriptor) capabilities();
indexed global Base(Grid);
";

const PRESENTED: &str = "indexed marker QQ;
indexed implementation AffineQQ(QQ, presented_affine(rational)) capabilities();
indexed classification AffineScheme { parents(); domain(AffineQQ); };
indexed family Over(object(AffineScheme), object(AffineScheme), object(AffineScheme)) = relative constraints(structural(0, 2), structural(1, 2));
indexed affine SpecQQ(AffineQQ) = spec[];
indexed affine Line(AffineQQ) = spec[t] over SpecQQ;
";

const SMOOTH: &str = "indexed marker CInfReal;
indexed implementation SmoothR(CInfReal, smooth_affine) capabilities();
indexed classification CInfAffine { parents(); domain(SmoothR); };
indexed family Smooth(object(CInfAffine), object(CInfAffine)) = smooth constraints(canonical(0), canonical(1));
indexed family Tangent(object(CInfAffine)) = tangent constraints(canonical(0));
";

/// `prelude`, then `declarations` from line 1 + the lines of `prelude`, then `main`.
fn program(prelude: &str, declarations: &str) -> String {
    format!("{prelude}{declarations}\nfn main() -> Int {{ 0 }}\n")
}

#[track_caller]
fn assert_rule(prelude: &str, declarations: &str, expected: &str) {
    let line = prelude.lines().count() + declarations.lines().count();
    assert_eq!(
        first_diagnostic(&program(prelude, declarations)),
        format!("main.vast:{line}:1: {expected}"),
        "{declarations}"
    );
}

#[test]
fn classifications_name_the_broken_rule() {
    for (declarations, expected) in [
        (
            "indexed classification C { parents(); domain(Grid, Grid); };",
            "E_TYPE: the domain of the classification `rules::C` names `rules::Grid` twice",
        ),
        (
            "indexed classification P { parents(); domain(Grid); };\nindexed classification C { parents(P, P); domain(Grid); };",
            "E_TYPE: the parents of the classification `rules::C` name `rules::P` twice",
        ),
        (
            "indexed classification C { parents(); domain(); };",
            "E_TYPE: the domain of the classification `rules::C` must not be empty",
        ),
        (
            "indexed classification C { parents(); domain(Base); };",
            "E_TYPE: each path of the domain of the classification `rules::C` must name an implementation, but `rules::Base` is not one",
        ),
        (
            "indexed classification C { parents(Grid); domain(Grid); };",
            "E_TYPE: each parent of the classification `rules::C` must be a classification, but `rules::Grid` is not one",
        ),
        (
            "indexed classification P { parents(); domain(Grid); };\nindexed classification C { parents(P); domain(Grid, Plain); };",
            "E_TYPE: the domain of the parent `rules::P` of the classification `rules::C` must contain every implementation of the domain of `rules::C`, but it does not contain `rules::Plain`",
        ),
    ] {
        assert_rule(DESCRIPTORS, declarations, expected);
    }
    // The first classification of the cycle is reported.
    assert_eq!(
        first_diagnostic(&program(
            DESCRIPTORS,
            "indexed classification B { parents(C); domain(Grid); };\nindexed classification C { parents(B); domain(Grid); };"
        )),
        "main.vast:5:1: E_TYPE: the parents of the classification `rules::B` must not form a cycle, but they reach one through `rules::C`"
    );
}

#[test]
fn global_objects_name_the_broken_rule() {
    assert_rule(
        DESCRIPTORS,
        "indexed global G(QQ);",
        "E_TYPE: the global object `rules::G` must name an implementation, but `rules::QQ` is not one",
    );
    assert_rule(
        PRESENTED,
        "indexed global G(AffineQQ);",
        "E_TYPE: the global object `rules::G` must not name the `presented_affine` implementation `rules::AffineQQ`: an `indexed affine` declaration declares the objects of that implementation",
    );
}

#[test]
fn families_name_the_broken_rule() {
    for (prelude, declarations, expected) in [
        (
            DESCRIPTORS,
            "indexed family F(object(QQ)) = token constraints();",
            "E_TYPE: the parameter `object(rules::QQ)` at position 0 of the family `rules::F` must name a classification or an implementation",
        ),
        (
            DESCRIPTORS,
            "indexed family F(object(Grid), marker) = token constraints(same_base(0, 1));",
            "E_TYPE: the constraint `same_base(0, 1)` of the family `rules::F` must name two positions of `object(…)` parameters",
        ),
        (
            DESCRIPTORS,
            "indexed family F(object(Grid), object(Grid)) = token constraints(over(0, 1));",
            "E_TYPE: the constraint `over(0, 1)` of the family `rules::F` must name the position of an `object(…)` parameter and then the position of a `marker` parameter",
        ),
        (
            DESCRIPTORS,
            "indexed family Point(object(Grid), object(Grid)) = point constraints();",
            "E_TYPE: the `point` family `rules::Point` must have the constraint `same_base(0, 1)`",
        ),
        (
            DESCRIPTORS,
            "indexed family Mor(object(Grid)) = morphism constraints();",
            "E_TYPE: the `morphism` family `rules::Mor` must have exactly two parameters, both `object(…)`",
        ),
        (
            PRESENTED,
            "indexed family Point(object(AffineScheme), object(AffineScheme)) = point constraints(same_base(0, 1));",
            "E_TYPE: every implementation in the domains of the parameters of the `point` family `rules::Point` must have the representation `affine_descriptor`, but `rules::AffineQQ` does not",
        ),
        (
            PRESENTED,
            "indexed family R(object(AffineScheme), object(AffineScheme), object(AffineScheme)) = relative constraints(structural(0, 2));",
            "E_TYPE: the `relative` family `rules::R` must have exactly the constraints `structural(0, 2), structural(1, 2)`",
        ),
        (
            DESCRIPTORS,
            "indexed family R(object(Grid), object(Grid), object(Grid)) = relative constraints(structural(0, 2), structural(1, 2));",
            "E_TYPE: every implementation in the domains of the parameters of the `relative` family `rules::R` must have the representation `presented_affine`, but `rules::Grid` does not",
        ),
        (
            SMOOTH,
            "indexed family S(object(CInfAffine)) = smooth constraints(canonical(0));",
            "E_TYPE: the `smooth` family `rules::S` must have exactly two parameters, both `object(…)`",
        ),
        (
            SMOOTH,
            "indexed family T(object(CInfAffine)) = cotangent constraints();",
            "E_TYPE: the `cotangent` family `rules::T` must have exactly the constraint `canonical(0)`",
        ),
    ] {
        assert_rule(prelude, declarations, expected);
    }
}

#[test]
fn package_declarations_name_the_broken_rule() {
    const POINT: &str =
        "indexed family Point(object(Grid), object(Grid)) = point constraints(same_base(0, 1));\n";
    for (declarations, expected) in [
        (
            "indexed package P { };",
            "E_TYPE: the package declaration `rules::P` must have at least one case",
        ),
        (
            "indexed package P { case(Grid, QQ) { } case(Grid, QQ) { } };",
            "E_TYPE: two cases of the package declaration `rules::P` have the witness type `rules::Grid<rules::QQ>`",
        ),
        (
            "indexed package P { case(Base, QQ) { } };",
            "E_TYPE: the witness type of the case `rules::Base<rules::QQ>` of the package declaration `rules::P` must be an object type, but `rules::Base` is neither a classification nor an implementation",
        ),
        (
            "indexed package P { case(Plain, QQ) { Point(witness, global(Base)); } };",
            "E_TYPE: the field `rules::Point(witness, global(Base))` of the case `rules::Plain<rules::QQ>` of the package declaration `rules::P` must be a valid type for every witness, but the bound index `witness` at position 0 does not fit the parameter `object(rules::Grid)` of `rules::Point`",
        ),
    ] {
        assert_rule(&format!("{DESCRIPTORS}{POINT}"), declarations, expected);
    }
}

#[test]
fn primitives_name_the_broken_rule() {
    const FAMILIES: &str = "indexed classification Shape { parents(); domain(Grid, Plain); };
indexed family Point(object(Shape), object(Shape)) = point constraints(same_base(0, 1));
indexed family Mor(object(Shape), object(Shape)) = morphism constraints(same_base(0, 1));
";
    let descriptors = format!("{DESCRIPTORS}{FAMILIES}");
    for (declarations, expected) in [
        (
            "indexed primitive o = origin((Shape, QQ), Point, Base);",
            "E_TYPE: every implementation of `rules::Shape<rules::QQ>` must have the capability `origin` for the `origin` primitive `rules::o`, but `rules::Plain` lacks it",
        ),
        (
            "indexed primitive size = dimension((Shape, QQ));",
            "E_TYPE: every implementation of `rules::Shape<rules::QQ>` must have the capability `dimension` for the `dimension` primitive `rules::size`, but `rules::Plain` lacks it",
        ),
        (
            "indexed primitive o = origin((Grid, QQ), Mor, Base);",
            "E_TYPE: the family `rules::Mor` of the `origin` primitive `rules::o` must have the representation `point`",
        ),
        (
            "indexed primitive i = identity((Grid, QQ), Point);",
            "E_TYPE: the family `rules::Point` of the `identity` primitive `rules::i` must have the representation `morphism`",
        ),
        (
            "indexed primitive c = compose(Point);",
            "E_TYPE: the family `rules::Point` of the `compose` primitive `rules::c` must have the representation `morphism`",
        ),
        (
            "indexed primitive a = apply(Point, Mor);",
            "E_TYPE: the family `rules::Point` of the `apply` primitive `rules::a` must have the representation `morphism`",
        ),
        (
            "indexed primitive g = global(Grid);",
            "E_TYPE: the path of the `global` primitive `rules::g` must name a global object of an `affine_descriptor` implementation, but `rules::Grid` is not one",
        ),
    ] {
        assert_rule(&descriptors, declarations, expected);
    }
    for (declarations, expected) in [
        (
            "indexed affine S(AffineQQ) = spec[];\nindexed primitive v = relative_view(Over, SpecQQ, S);",
            "E_TYPE: `rules::S` must lie on the base chain of `rules::SpecQQ` in the `relative_view` primitive `rules::v`",
        ),
        (
            "indexed affine Origin(AffineQQ) = spec[] over Line by(t -> 0);\nindexed affine Curve(AffineQQ) = spec[t, x] relations(x^2 - t) over Line by(t -> t);\nindexed affine F(AffineQQ) = fiber(Curve, Origin) via(t -> t) inverse(t -> t);\nindexed primitive lift = relative_pair(Over, F);",
            "E_TYPE: the fiber product `rules::F` of the `relative_pair` primitive `rules::lift` must be declared without `via`",
        ),
        (
            "indexed primitive lift = relative_pair(Over, Line);",
            "E_TYPE: `rules::Line` of the `relative_pair` primitive `rules::lift` must be a fiber product declared without `via`",
        ),
        (
            "indexed family Plain(object(AffineScheme)) = token constraints();\nindexed primitive c = relative_compose(Plain);",
            "E_TYPE: the family `rules::Plain` of the `relative_compose` primitive `rules::c` must be a relative family",
        ),
        (
            "indexed primitive d = descriptor(AffineQQ);",
            "E_TYPE: the implementation `rules::AffineQQ` of the `descriptor` primitive `rules::d` must have the representation `affine_descriptor`",
        ),
    ] {
        assert_rule(PRESENTED, declarations, expected);
    }
    for (declarations, expected) in [
        (
            "indexed primitive c = smooth_compose(Tangent);",
            "E_TYPE: the family `rules::Tangent` of the `smooth_compose` primitive `rules::c` must have the representation `smooth`",
        ),
        (
            "indexed primitive e = fiber_equal(Smooth);",
            "E_TYPE: the family `rules::Smooth` of the `fiber_equal` primitive `rules::e` must have the representation `tangent` or `cotangent`",
        ),
        (
            "indexed primitive l = linearize(Smooth, Smooth);",
            "E_TYPE: the family `rules::Smooth` of the `linearize` primitive `rules::l` must have the representation `tape`",
        ),
    ] {
        assert_rule(SMOOTH, declarations, expected);
    }
}

/// The name of a marker, a global object or a primitive used as a value says
/// what the name is. It used to say that generic families are not Fn values.
#[test]
fn an_indexed_declaration_used_as_a_value_says_what_it_names() {
    for (value, expected) in [
        ("QQ", "`QQ` names a marker, which is not a value"),
        ("Base", "`Base` names a global object, which is not a value"),
        (
            "size",
            "`size` names a primitive, which is not a value; call it with its operands",
        ),
        (
            "Grid",
            "`Grid` names an implementation, which is not a value",
        ),
    ] {
        let source = format!(
            "{DESCRIPTORS}indexed primitive size = dimension((Grid, QQ));\nfn main() -> Int {{ let x = {value}; 0 }}\n"
        );
        assert_eq!(
            first_diagnostic(&source),
            format!("main.vast:6:28: E_TYPE: {expected}")
        );
    }
}

/// A reserved name of an `indexed` declaration is reported at the name, not
/// at the start of the module.
#[test]
fn a_reserved_name_of_an_indexed_declaration_is_reported_at_the_name() {
    assert_eq!(
        first_diagnostic(
            "fn helper() -> Int { 1 }\n\n   indexed marker Nat;\nfn main() -> Int { 0 }\n"
        ),
        "main.vast:3:19: E_RESERVED: `Nat` is reserved and cannot be used as a declaration or binding name"
    );
    // The spellings of the geometric core may name indexed declarations.
    success(&check("indexed marker QQ;\nfn main() -> Int { 0 }\n"));
}

/// `count` implementations `I0`, `I1`, … over `QQ`, one per line.
fn implementations(count: usize) -> String {
    (0..count)
        .map(|i| format!("indexed implementation I{i}(QQ, affine_descriptor) capabilities();\n"))
        .collect()
}

fn names(prefix: &str, count: usize) -> String {
    (0..count)
        .map(|i| format!("{prefix}{i}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Each limit admits its value and rejects the next count with `E_LIMIT`.
#[test]
fn the_size_limits_of_one_declaration_are_e_limit() {
    let marker = "indexed marker QQ;\n";
    let classification = |count| {
        program(
            &format!("{marker}{}", implementations(65)),
            &format!(
                "indexed classification C {{ parents(); domain({}); }};",
                names("I", count)
            ),
        )
    };
    success(&check(&classification(64)));
    assert_eq!(
        first_diagnostic(&classification(65)),
        "main.vast:67:1: E_LIMIT: the domain of the classification `rules::C` has 65 implementations, more than the limit of 64"
    );

    let family = |count| {
        program(
            marker,
            &format!(
                "indexed family F({}) = token constraints();",
                vec!["domain"; count].join(", ")
            ),
        )
    };
    success(&check(&family(16)));
    assert_eq!(
        first_diagnostic(&family(17)),
        "main.vast:2:1: E_LIMIT: the family `rules::F` has 17 parameters, more than the limit of 16"
    );

    let cases = |count| {
        let cases: String = (0..count)
            .map(|i| format!("case(I{i}, QQ) {{ }} "))
            .collect();
        program(
            &format!("{marker}{}", implementations(65)),
            &format!("indexed package P {{ {cases}}};"),
        )
    };
    success(&check(&cases(64)));
    assert_eq!(
        first_diagnostic(&cases(65)),
        "main.vast:67:1: E_LIMIT: the package declaration `rules::P` has 65 cases, more than the limit of 64"
    );

    let fields = |count| {
        program(
            &format!(
                "{marker}indexed implementation Grid(QQ, affine_descriptor) capabilities();\nindexed family F() = token constraints();\n"
            ),
            &format!(
                "indexed package P {{ case(Grid, QQ) {{ {}}} }};",
                "F(); ".repeat(count)
            ),
        )
    };
    success(&check(&fields(64)));
    assert_eq!(
        first_diagnostic(&fields(65)),
        "main.vast:4:1: E_LIMIT: the case `rules::Grid<rules::QQ>` of the package declaration `rules::P` has 65 fields, more than the limit of 64"
    );
}
