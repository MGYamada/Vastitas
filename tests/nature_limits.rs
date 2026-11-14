//! Limits and messages of `nature::dimension` physical metrics (Stage 4,
//! #759, review findings S4-01, S4-13, S4-14, S4-15 and S4-23). An
//! application that depends on copies of the stdlib and of the `nature`
//! package declares physical interpretations whose entries or values are at
//! the published bounds and just beyond them. The tests check what the kernel
//! accepts, the code of each rejection and the text of its message.
mod common;
use common::{Scratch, expect_code, success};
use std::path::Path;

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap()
}

/// Copies every `.vast` and `.toml` file under `from` to `to` in `s`.
fn copy_tree(s: &Scratch, from: &Path, to: &str) {
    let mut stack = vec![from.to_path_buf()];
    while let Some(directory) = stack.pop() {
        for entry in std::fs::read_dir(&directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                stack.push(path);
            } else if matches!(
                path.extension().and_then(|e| e.to_str()),
                Some("vast" | "toml")
            ) {
                let relative = path.strip_prefix(from).unwrap().to_str().unwrap();
                s.write(&format!("{to}/{relative}"), &read(&path));
            }
        }
    }
}

const APP_MANIFEST: &str = "[package]\nname = \"limits_demo\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n\n[dependencies]\nstd = { path = \"../stdlib\" }\nnature = { path = \"../nature\" }\n";

/// The imports of every application, and the dimensionless quantity `Ratio`.
const HEADER: &str = "use std::geometry::smooth::affine::SmoothR;
use std::geometry::metric::MetricForm;
use nature::dimension::Reading;
use nature::dimension::PhysicalMetric;
use nature::dimension::L;
use nature::dimension::Length;
use nature::dimension::Time;

indexed quantity Ratio = 1;
";

const MAIN: &str = "\nfn main() -> Int { 42 }\n";

/// The application `HEADER`, `declarations` and `MAIN` in `app/` with copies
/// of the stdlib in `stdlib/` and of the nature package in `nature/`, as in
/// the repository.
fn fixture(declarations: &str) -> Scratch {
    common::prepare_stdlib_package();
    let s = Scratch::empty("nature limits");
    let stdlib = common::root().join("stdlib");
    s.write("stdlib/Vastitas.toml", &read(&stdlib.join("Vastitas.toml")));
    for directory in ["target/package", "src/geometry", "src/differential"] {
        copy_tree(&s, &stdlib.join(directory), &format!("stdlib/{directory}"));
    }
    copy_tree(&s, &common::root().join("nature"), "nature");
    s.write("app/Vastitas.toml", APP_MANIFEST);
    s.write("app/main.vast", &format!("{HEADER}{declarations}{MAIN}"));
    s
}

fn check(declarations: &str) -> std::process::Output {
    fixture(declarations).check_manifest("app/Vastitas.toml")
}

#[track_caller]
fn accepts(declarations: &str) {
    success(&check(declarations));
}

/// Rejects `declarations` with `code` and returns the message text.
#[track_caller]
fn rejects(declarations: &str, code: &str) -> String {
    common::message_text(&expect_code(&check(declarations), code))
}

/// The chart `C = Affine(2)[x, t]` read as two ratios, with its Euclidean
/// metric `E`.
const RATIO_CHART: &str = "indexed affine C(SmoothR) = Affine(2)[x, t];
indexed reading r: Reading<C> = (x: Ratio, t: Ratio);
indexed metric E: MetricForm<C> = euclidean;
";

/// `2^100 + 1` as a literal: 101 bits.
const A101: &str = "1267650600228229401496703205377";

/// The scales `a` and `b` of `Ratio`, both `2^100 + 1`, and the physical
/// interpretation of `E` whose x·x entry is `entry`.
fn cancelling(entry: &str) -> String {
    format!(
        "{RATIO_CHART}indexed scale a = {A101} of Ratio;
indexed scale b = {A101} of Ratio;
indexed physical P: PhysicalMetric<C> = interpret(E, reading = r, gram(({entry}, 0), (0, 1)));
"
    )
}

/// Before it computes a power, the kernel bounds the size of an entry
/// multiplied out: the bits of the coefficient and of each magnitude, once per
/// unit of its exponent, are at most `metricEntryBits` (512) in the numerator
/// and in the denominator. `a^5 * b^-5` has 505 bits in each and evaluates to
/// 1; `a^6 * b^-6` has 606 and is `E_LIMIT`, although its factors cancel
/// (S4-01).
#[test]
fn an_entry_is_bounded_before_its_powers_are_computed() {
    accepts(&cancelling("a^5 * b^-5"));
    let message = rejects(&cancelling("a^6 * b^-6"), "E_LIMIT");
    assert!(
        message.contains(
            "the entry in row 1, column 1 of the physical metric `limits_demo::P`, multiplied out, \
             has up to 606 bits in its numerator and 606 in its denominator, beyond the limit of \
             512 bits of a Gram entry"
        ),
        "{message}"
    );
    // The coefficient counts too: 7 bits and 505 are 512.
    accepts(&format!(
        "{RATIO_CHART}indexed scale a = {A101} of Ratio;
indexed scale b = {A101} of Ratio;
indexed metric G: MetricForm<C> = gram((100, 0), (0, 1));
indexed physical P: PhysicalMetric<C> = interpret(G, reading = r, gram((100 * a^5 * b^-5, 0), (0, 1)));
"
    ));
    let message = rejects(&cancelling("200 * a^5 * b^-5"), "E_LIMIT");
    assert!(
        message.contains("has up to 513 bits in its numerator and 505 in its denominator"),
        "{message}"
    );
}

/// The physical metric of the review's probe: on a 16-dimensional object,
/// every entry is `a0^64 * … * a7^64 * b0^∓64 * … * b7^∓64` of scales with
/// about 500-bit magnitudes, each within its own limit. Before the bound, the
/// kernel spent about 20 s on it and printed a 300 KB number when it was
/// rejected. Now each form is `E_LIMIT` at its first entry, with a short
/// message (S4-01, S4-13).
#[test]
fn the_review_probe_is_rejected_at_its_first_entry() {
    let n = 16;
    let coordinates: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
    let mut declarations = format!(
        "indexed affine C(SmoothR) = Affine({n})[{}];\nindexed reading r: Reading<C> = ({});\n",
        coordinates.join(", "),
        coordinates
            .iter()
            .map(|c| format!("{c}: Ratio"))
            .collect::<Vec<_>>()
            .join(", ")
    );
    // Three 51-digit fractions: a magnitude of about 500 bits.
    let literal = |k: usize, j: usize| format!("{}{:02}{:02}", "7".repeat(47), k, j);
    for k in 0..8 {
        let magnitude = (0..3)
            .map(|j| format!("frac({}, {})", literal(k, j), literal(k, j + 3)))
            .collect::<Vec<_>>()
            .join(" * ");
        declarations += &format!("indexed scale a{k} = {magnitude} of Ratio;\n");
        declarations += &format!("indexed scale b{k} = {magnitude} of Ratio;\n");
    }
    let row = format!("({})", vec!["1"; n].join(", "));
    declarations += &format!(
        "indexed metric G: MetricForm<C> = gram({});\n",
        vec![row; n].join(", ")
    );
    for sign in ["-", ""] {
        let monomial = (0..8)
            .map(|k| format!("a{k}^64"))
            .chain((0..8).map(|k| format!("b{k}^{sign}64")))
            .collect::<Vec<_>>()
            .join(" * ");
        let row = format!("({})", vec![monomial; n].join(", "));
        let source = format!(
            "{declarations}indexed physical P: PhysicalMetric<C> = interpret(G, reading = r, gram({}));\n",
            vec![row; n].join(", ")
        );
        let output = check(&source);
        let stderr = expect_code(&output, "E_LIMIT");
        assert!(stderr.len() < 2000, "{} bytes:\n{stderr}", stderr.len());
        assert!(
            stderr.contains("the entry in row 1, column 1 of the physical metric `limits_demo::P`"),
            "{stderr}"
        );
    }
}

/// A rejected entry writes its magnitude only within 512 bits:
/// `normalized(x: wide, t: t0)` with `wide = 2^300` gives the x·x entry
/// `1/2^600`, which the message names by its size (S4-13).
#[test]
fn a_message_writes_no_magnitude_beyond_the_entry_bound() {
    let message = rejects(
        "indexed affine C(SmoothR) = Affine(2)[x, t];
indexed reading phys: Reading<C> = (x: Length, t: Time);
indexed metric G: MetricForm<C> = gram((frac(1, 9), 0), (0, frac(1, 4)));
indexed scale wide = 1073741824^10 of Length;
indexed scale t0 = 2 of Time;
indexed physical P: PhysicalMetric<C> = interpret(G, reading = phys, normalized(x: wide, t: t0));
",
        "E_DIMENSION",
    );
    assert!(
        message.contains(
            "gives the x·x entry, in row 1, column 1, a magnitude with more than 512 bits in its \
             numerator or denominator, but the metric `limits_demo::G` has 1/9 there"
        ),
        "{message}"
    );
    assert!(message.len() < 400, "{message}");
}

/// The chart read as two lengths, two scales of `Length` with magnitude 1,
/// and the interpretation of its Euclidean metric with `entry` on the
/// diagonal: its terms have the dimension of `entry` times L².
fn lengths(entry: &str, value: &str) -> String {
    format!(
        "indexed affine C(SmoothR) = Affine(2)[x, t];
indexed reading lens: Reading<C> = (x: Length, t: Length);
indexed scale one = 1 of Length;
indexed scale two = 1 of Length;
indexed metric E: MetricForm<C> = euclidean;
indexed physical P: PhysicalMetric<C> = interpret(E, reading = lens, gram(({entry}, 0), (0, {entry})){value});
"
    )
}

/// The value of an accepted physical metric is within `dimensionExponent`
/// (64), so a declaration can write it: L^64 is accepted with and without
/// `value = L^64`, and L^65 and L^130, the review's case, are `E_LIMIT`
/// (S4-14).
#[test]
fn the_value_of_a_physical_metric_is_within_the_exponent_bound() {
    accepts(&lengths("one^62", ""));
    accepts(&lengths("one^62", ", value = L^64"));
    let message = rejects(&lengths("one^63", ""), "E_LIMIT");
    assert!(
        message.contains(
            "the nonzero terms of the physical metric `limits_demo::P` have dimension L^65, which \
             raises `vastitas_nature::dimension::L` to the power 65, beyond the limit of 64 in \
             absolute value"
        ),
        "{message}"
    );
    let message = rejects(&lengths("one^64 * two^64", ""), "E_LIMIT");
    assert!(message.contains("dimension L^130"), "{message}");
    let message = rejects(&lengths("one^64 * two^64", ", value = L^130"), "E_LIMIT");
    assert!(message.contains("to the power 130"), "{message}");
}

/// The module `mine` declares a second base dimension `L` and its quantity.
const MINE: &str = "mod mine { pub indexed base_dimension L; pub indexed quantity Len = L; }
indexed affine C(SmoothR) = Affine(2)[x, t];
indexed metric E: MetricForm<C> = euclidean;
";

/// When two base dimensions of a program share a short name, messages write
/// each by its full path, so they do not contradict themselves (S4-15).
#[test]
fn messages_qualify_base_dimensions_that_share_a_name() {
    let message = rejects(
        &format!(
            "{MINE}indexed reading r: Reading<C> = (x: Length, t: Length);
indexed physical P: PhysicalMetric<C> = interpret(E, reading = r, euclidean, value = mine::L^2);
"
        ),
        "E_DIMENSION",
    );
    assert!(
        message.contains(
            "the physical metric `limits_demo::P` declares the value limits_demo::mine::L^2, but \
             its nonzero terms have dimension vastitas_nature::dimension::L^2"
        ),
        "{message}"
    );
    let message = rejects(
        &format!(
            "{MINE}indexed reading r: Reading<C> = (x: Length, t: mine::Len);
indexed physical P: PhysicalMetric<C> = interpret(E, reading = r, euclidean);
"
        ),
        "E_DIMENSION",
    );
    assert!(
        message.contains(
            "the term x·x has dimension vastitas_nature::dimension::L^2 and the term t·t has \
             dimension limits_demo::mine::L^2"
        ),
        "{message}"
    );
    // Without a second `L`, the short names stay.
    let message = rejects(
        "indexed affine C(SmoothR) = Affine(2)[x, t];
indexed metric E: MetricForm<C> = euclidean;
indexed reading r: Reading<C> = (x: Length, t: Time);
indexed physical P: PhysicalMetric<C> = interpret(E, reading = r, euclidean);
",
        "E_DIMENSION",
    );
    assert!(
        message.contains("the term x·x has dimension L^2 and the term t·t has dimension T^2"),
        "{message}"
    );
}

/// A count of one is singular: a physical metric on a line needs "1 row of 1
/// entry", and a chart's metric with one row "has 1 row" (S4-23).
#[test]
fn shape_messages_count_one_row_in_the_singular() {
    let message = rejects(
        "indexed affine S(SmoothR) = Affine(1)[s];
indexed reading r: Reading<S> = (s: Ratio);
indexed metric E: MetricForm<S> = euclidean;
indexed physical P: PhysicalMetric<S> = interpret(E, reading = r, gram());
",
        "E_DIMENSION",
    );
    assert!(
        message.contains(
            "on the 1-dimensional object `limits_demo::S` needs 1 row of 1 entry, but it has 0 rows"
        ),
        "{message}"
    );
    let message = rejects(
        &format!(
            "{RATIO_CHART}indexed physical P: PhysicalMetric<C> = interpret(E, reading = r, gram((1, 0)));\n"
        ),
        "E_DIMENSION",
    );
    assert!(
        message.contains("needs 2 rows of 2 entries, but it has 1 row")
            && !message.contains("1 rows"),
        "{message}"
    );
}
