//! The limits of the spectral profile (Stage 5, #806; C16). A free module has
//! rank at most `spectralRank` = 4; a trace power and a branch exponent are at
//! most `spectralPower` = 8; every polynomial that the kernel reads or computes
//! stays within the term limit `algebraTerms`, and the computation of a
//! spectral pair, a trace power and a witness check within the work budget
//! `algebraWork`. Each limit is the kernel's `E_LIMIT` with its exact message,
//! reported instead of the error of the comparison that it guards (no
//! `E_SPECTRAL` identity or symmetry message appears), and within a time bound
//! far below that of a check. The declarations at the limits are accepted.
mod common;
use common::{Scratch, expect_code, root, success};
use std::process::Output;
use std::time::{Duration, Instant};

/// The time that one check may take. On a developer machine each check below
/// takes less than a second.
const BOUND: Duration = Duration::from_secs(30);

/// The time within which a limit is reported. A limit stops the check before
/// the products and comparisons that it guards; on a developer machine each
/// limit below is reported within half a second.
const LIMIT_BOUND: Duration = Duration::from_secs(10);

/// Parts of the messages of the comparisons that the limits guard: the
/// identities of a certificate, the gap certificate and `symmetric`.
const COMPARISONS: &[&str] = &[
    "E_SPECTRAL",
    "failed its check",
    "failed Jacobi's formula",
    "does not certify the gap",
    "differs from its entry",
];

/// The output of a check and the time that it took.
struct Checked {
    output: Output,
    elapsed: Duration,
}

impl std::ops::Deref for Checked {
    type Target = Output;

    fn deref(&self) -> &Output {
        &self.output
    }
}

/// `(1 + x0 + … + x{k-1})^power`.
fn sum(k: usize, power: usize) -> String {
    let terms: Vec<String> = (0..k).map(|i| format!("x{i}")).collect();
    format!("(1 + {})^{power}", terms.join(" + "))
}

/// `basis(e1, …, en)`.
fn basis(n: usize) -> String {
    let vectors: Vec<String> = (1..=n).map(|i| format!("e{i}")).collect();
    format!("basis({})", vectors.join(", "))
}

/// `rows(…)` of the `n × n` matrix with `entry(i, j)` in row `i` and column `j`.
fn rows(n: usize, entry: impl Fn(usize, usize) -> String) -> String {
    let rows: Vec<String> = (0..n)
        .map(|i| {
            let row: Vec<String> = (0..n).map(|j| entry(i, j)).collect();
            format!("({})", row.join(", "))
        })
        .collect();
    format!("rows({})", rows.join(", "))
}

/// Checks a package with the object `C = Affine(dimension)[x0, …]` and the
/// spectral declarations `declarations`, and returns the output and the time.
/// The check must end within `BOUND`.
fn check(dimension: usize, declarations: &str) -> Checked {
    common::prepare_stdlib_package();
    let s = Scratch::empty("spectral limits");
    s.write(
        "Vastitas.toml",
        &format!(
            "[package]\nedition = \"2026\"\nname = \"spectral_limits\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n\n[dependencies]\nstd = {{ path = {:?} }}\n",
            root().join("stdlib")
        ),
    );
    let coordinates: Vec<String> = (0..dimension).map(|i| format!("x{i}")).collect();
    s.write(
        "main.vast",
        &format!(
            "use std::geometry::smooth::affine::SmoothR;\n\
             use std::geometry::smooth::affine::Smooth;\n\
             use std::geometry::smooth::affine::Line;\n\
             use std::linalg::spectral::FreeModule;\n\
             use std::linalg::spectral::Endomorphism;\n\
             use std::linalg::spectral::Spectrum;\n\
             use std::linalg::spectral::Branch;\n\
             indexed affine C(SmoothR) = Affine({dimension})[{}];\n\
             {declarations}\n\
             fn main() -> Int {{ 42 }}\n",
            coordinates.join(", ")
        ),
    );
    let started = Instant::now();
    let output = s.check_manifest("Vastitas.toml");
    let elapsed = started.elapsed();
    assert!(elapsed < BOUND, "the check took {elapsed:?}");
    Checked { output, elapsed }
}

/// The check fails within `LIMIT_BOUND` with `E_LIMIT` at `main.vast`, whose
/// first diagnostic says exactly `message`, and no message of a comparison
/// appears.
#[track_caller]
fn limited(checked: &Checked, message: &str) {
    let error = expect_code(checked, "E_LIMIT");
    let first = error.lines().next().unwrap_or_default();
    let (location, reported) = first
        .split_once(": E_LIMIT: ")
        .unwrap_or_else(|| panic!("no E_LIMIT diagnostic first: {error}"));
    assert!(location.contains("main.vast:"), "{error}");
    assert_eq!(reported, message, "{error}");
    for comparison in COMPARISONS {
        assert!(!error.contains(comparison), "{comparison}: {error}");
    }
    assert!(
        checked.elapsed < LIMIT_BOUND,
        "the limit took {:?}",
        checked.elapsed
    );
}

/// The rotation field of the plane with its spectrum.
const ROTATION: &str = "indexed free_module V: FreeModule<C> = basis(e1, e2);
indexed endomorphism H: Endomorphism<C> = rows((x0, x1), (x1, -x0)) of V symmetric;
indexed spectrum S: Spectrum<C> = eigen(H, t);";

/// A free module of rank 4 is at the limit, with a field, its spectrum and its
/// eighth trace power. A fifth basis vector is `E_LIMIT` at the free module:
/// the field on it is declared `symmetric` and is not, and the limit is
/// reported instead of that comparison's `E_SPECTRAL` (C1, C12).
#[test]
fn the_rank_is_bounded_at_the_free_module() {
    let field = |n: usize| {
        format!(
            "indexed free_module V: FreeModule<C> = {};\n\
             indexed endomorphism H: Endomorphism<C> = {} of V symmetric;\n\
             indexed spectrum S: Spectrum<C> = eigen(H, t);\n\
             indexed morphism tr8: Smooth<C, Line> = trace_power(H, 8);",
            basis(n),
            rows(n, |i, j| {
                if i <= j {
                    format!("x{}", (i + j) % 2)
                } else {
                    "0".into()
                }
            })
        )
    };
    let symmetric = format!(
        "indexed free_module V: FreeModule<C> = {};\n\
         indexed endomorphism H: Endomorphism<C> = {} of V symmetric;\n\
         indexed spectrum S: Spectrum<C> = eigen(H, t);\n\
         indexed morphism tr8: Smooth<C, Line> = trace_power(H, 8);",
        basis(4),
        rows(4, |i, j| format!("x{}", (i + j) % 2))
    );
    success(&check(2, &symmetric));
    limited(
        &check(2, &field(5)),
        "the free module `spectral_limits::V` has rank 5, beyond the limit of 4 (`spectralRank`)",
    );
}

/// The eighth trace power and the exponent 8, with the witness
/// `(x0^2 + x1^2)^7 · t/2`, are at the limit; the ninth power and the
/// exponent 9 are `E_LIMIT`.
#[test]
fn powers_and_exponents_are_bounded() {
    success(&check(
        2,
        &format!(
            "{ROTATION}\nindexed morphism tr8: Smooth<C, Line> = trace_power(H, 8);\n\
             indexed branch B: Branch<C> = simple(S, localize = x0^2 + x1^2, \
             witness = frac(1, 2) * (x0^2 + x1^2)^7 * t, exponent = 8);"
        ),
    ));
    limited(
        &check(
            2,
            &format!("{ROTATION}\nindexed morphism tr9: Smooth<C, Line> = trace_power(H, 9);"),
        ),
        "the `trace_power` declaration `spectral_limits::tr9` takes the power 9, beyond the limit of 8 (`spectralPower`)",
    );
    limited(
        &check(
            2,
            &format!(
                "{ROTATION}\nindexed branch B: Branch<C> = simple(S, localize = x0^2 + x1^2, \
                 witness = frac(1, 2) * t, exponent = 9);"
            ),
        ),
        "the branch `spectral_limits::B` has the exponent 9, beyond the limit of 8 (`spectralPower`)",
    );
}

/// An entry of 969 terms, a characteristic polynomial, a trace power and a
/// power of the localization beyond the term limit are each `E_LIMIT`. The
/// entry is out of place in a field declared `symmetric`, and the limit comes
/// before that comparison. The image of a trace power is bounded too: the
/// diagonal entries `(1 + x{4i} + … + x{4i+3})^8` of 495 terms each are within
/// the limit, and so is every entry of `H¹`, but their sum `tr(H)` has 1977
/// terms.
#[test]
fn terms_are_bounded_before_any_comparison() {
    let block = |i: usize| {
        let terms: Vec<String> = (4 * i..4 * i + 4).map(|k| format!("x{k}")).collect();
        format!("(1 + {})^8", terms.join(" + "))
    };
    limited(
        &check(
            16,
            &format!(
                "indexed free_module V: FreeModule<C> = {};\n\
                 indexed endomorphism H: Endomorphism<C> = {} of V symmetric;\n\
                 indexed morphism tr: Smooth<C, Line> = trace_power(H, 1);",
                basis(4),
                rows(4, |i, j| if i == j { block(i) } else { "0".into() })
            ),
        ),
        "the `trace_power` declaration `spectral_limits::tr`: algebraic term limit exceeded",
    );
    limited(
        &check(
            16,
            &format!(
                "indexed free_module V: FreeModule<C> = basis(e1, e2);\n\
                 indexed endomorphism H: Endomorphism<C> = rows((x0, {}), (x1, 0)) of V symmetric;",
                sum(16, 3)
            ),
        ),
        "the endomorphism `spectral_limits::H` on `spectral_limits::C`: algebraic term limit exceeded",
    );
    limited(
        &check(
            8,
            &format!(
                "indexed free_module V: FreeModule<C> = {};\n\
                 indexed endomorphism H: Endomorphism<C> = {} of V symmetric;\n\
                 indexed spectrum S: Spectrum<C> = eigen(H, t);",
                basis(4),
                rows(4, |i, j| if i == j { sum(8, 2) } else { "0".into() })
            ),
        ),
        "computing the spectral pair of the spectrum `spectral_limits::S`: algebraic term limit exceeded",
    );
    limited(
        &check(
            12,
            &format!(
                "indexed free_module V: FreeModule<C> = {};\n\
                 indexed endomorphism H: Endomorphism<C> = {} of V;\n\
                 indexed morphism tr8: Smooth<C, Line> = trace_power(H, 8);",
                basis(4),
                rows(4, |i, j| format!(
                    "x{} + x{}",
                    (i + j) % 12,
                    (4 * i + j) % 12
                ))
            ),
        ),
        "the `trace_power` declaration `spectral_limits::tr8`: algebraic term limit exceeded",
    );
    limited(
        &check(
            8,
            &format!(
                "indexed free_module V: FreeModule<C> = basis(e1, e2);\n\
                 indexed endomorphism H: Endomorphism<C> = rows((x0, x1), (x1, -x0)) of V symmetric;\n\
                 indexed spectrum S: Spectrum<C> = eigen(H, t);\n\
                 indexed branch B: Branch<C> = simple(S, localize = {}, witness = frac(1, 2) * t, exponent = 8);",
                sum(8, 2)
            ),
        ),
        "checking the witness of the branch `spectral_limits::B`: algebraic term limit exceeded",
    );
}

/// A symmetric 4 × 4 field whose entries are the 455-term polynomial
/// `(1 + x0 + … + x11)^3` stops on the work budget while its spectral pair is
/// computed, before the kernel compares the characteristic polynomial with
/// the cofactor determinant; with linear entries the pair is computed and
/// checked.
#[test]
fn the_spectral_pair_is_bounded_by_the_work_budget() {
    let field = |entry: String| {
        format!(
            "indexed free_module V: FreeModule<C> = {};\n\
             indexed endomorphism H: Endomorphism<C> = {} of V symmetric;\n\
             indexed spectrum S: Spectrum<C> = eigen(H, t);",
            basis(4),
            rows(4, |_, _| entry.clone())
        )
    };
    success(&check(12, &field(sum(12, 1))));
    limited(
        &check(12, &field(sum(12, 3))),
        "computing the spectral pair of the spectrum `spectral_limits::S`: algebraic work limit exceeded",
    );
}

/// The contract of a trace power computes its image tr(Hᵏ). It does not depend
/// on the call, so the kernel decides it once for each binding in each pass and
/// reuses the verdict at the calls and at their Core nodes (#812). A rank-4
/// field on the line with dense entries of degree 8 and its eighth trace power,
/// called from 64 functions, checks within a few times the time of one call;
/// when each call and each Core node computed the image again, each call added
/// more than half a second, and the 64 calls exceeded `BOUND`.
#[test]
fn many_calls_of_a_trace_power_reuse_its_checked_image() {
    let entry = |i: usize, j: usize| {
        let terms: Vec<String> = (0..=8)
            .map(|d| {
                let c = (i + j + d) % 3 + 1;
                match d {
                    0 => format!("{c}"),
                    1 => format!("{c} * x0"),
                    _ => format!("{c} * x0^{d}"),
                }
            })
            .collect();
        terms.join(" + ")
    };
    let program = |calls: usize| {
        let uses: String = (0..calls)
            .map(|k| format!("fn use{k}() -> Smooth<C, Line> {{ tr8() }}\n"))
            .collect();
        format!(
            "indexed free_module V: FreeModule<C> = {};\n\
             indexed endomorphism H: Endomorphism<C> = {} of V;\n\
             indexed morphism tr8: Smooth<C, Line> = trace_power(H, 8);\n\
             {uses}",
            basis(4),
            rows(4, entry)
        )
    };
    let one = check(1, &program(1));
    success(&one);
    let many = check(1, &program(64));
    success(&many);
    assert!(
        many.elapsed < one.elapsed * 3 + Duration::from_secs(5),
        "64 calls took {:?}, one call {:?}",
        many.elapsed,
        one.elapsed
    );
}
