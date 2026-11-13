//! The work budget of the identities of a polynomial frame (Stage 4, #759; a
//! finding of the Stage 4 review). The kernel charges each product of two
//! entries of `P·Q` and `Q·P` for the steps of the product before it computes
//! it (`FrameDeclarations.productWork`), so the budget `algebraWork` bounds the
//! time of the products. The frames here are on `Affine(16)` and within every
//! other limit; their entries are the 455-term polynomial
//! `(1 + x0 + … + x11)^3`. When a product of a 455-term polynomial and a
//! constant was charged 456 units, the first frame was accepted after 14
//! seconds, and the two frames of
//! `the_products_of_a_dense_polynomial_frame_end_on_work` took 26 and 74
//! seconds, on a developer machine.
mod common;
use common::{Scratch, cli, expect_code, root, success};
use std::process::Output;
use std::time::{Duration, Instant};

/// The dimension of the object of the frames.
const N: usize = 16;

/// The time that one check may take. With the old charge the checks took 14
/// to 74 seconds on a developer machine, with this one at most 3.
const BOUND: Duration = Duration::from_secs(30);

/// `(1 + x0 + … + x11)^3`.
fn cube() -> String {
    let sum: Vec<String> = (0..12).map(|i| format!("x{i}")).collect();
    format!("(1 + {})^3", sum.join(" + "))
}

/// `columns(…)` of the `N × N` matrix with `entry(i, j)` in row `i` and
/// column `j`.
fn columns(entry: impl Fn(usize, usize) -> String) -> String {
    let columns: Vec<String> = (0..N)
        .map(|j| {
            let column: Vec<String> = (0..N).map(|i| entry(i, j)).collect();
            format!("({})", column.join(", "))
        })
        .collect();
    format!("columns({})", columns.join(", "))
}

/// The unipotent frame `P = I + Σ A·E_ij` with its inverse `Q = I − Σ A·E_ij`,
/// for `(i, j)` in `places`, all in the upper right block, so that `A` meets
/// `A` in no product.
fn unipotent(places: &[(usize, usize)]) -> (String, String) {
    assert!(places.iter().all(|&(i, j)| i < N / 2 && j >= N / 2));
    let a = cube();
    let entry = |sign: &str, i: usize, j: usize| {
        if i == j {
            "1".to_string()
        } else if places.contains(&(i, j)) {
            format!("{sign}{a}")
        } else {
            "0".to_string()
        }
    };
    (
        columns(|i, j| entry("", i, j)),
        columns(|i, j| entry("-1 * ", i, j)),
    )
}

/// The first `count` places of the upper right block, row by row.
fn block(count: usize) -> Vec<(usize, usize)> {
    (0..N / 2)
        .flat_map(|i| (N / 2..N).map(move |j| (i, j)))
        .take(count)
        .collect()
}

/// Checks the package with the frame `b: Frame<C> = P inverse = Q` and returns
/// the output. The check must end within `BOUND`.
fn check((matrix, inverse): (String, String)) -> Output {
    common::prepare_stdlib_package();
    let s = Scratch::empty("frame limits");
    s.write(
        "Vastitas.toml",
        &format!(
            "[package]\nname = \"frame_limits\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n\n[dependencies]\nstd = {{ path = {:?} }}\n",
            root().join("stdlib")
        ),
    );
    let coordinates: Vec<String> = (0..N).map(|i| format!("x{i}")).collect();
    s.write(
        "main.vast",
        &format!(
            "use std::geometry::smooth::affine::SmoothR;\nuse std::geometry::frame::Frame;\n\
             indexed affine C(SmoothR) = Affine({N})[{}];\n\
             indexed frame b: Frame<C> = {matrix} inverse = {inverse};\n\
             fn main() -> Int {{ 42 }}\n",
            coordinates.join(", ")
        ),
    );
    let started = Instant::now();
    let output = cli()
        .current_dir(&s.0)
        .args(["check", "--manifest-path", "Vastitas.toml"])
        .output()
        .unwrap();
    assert!(
        started.elapsed() < BOUND,
        "the check took {:?}",
        started.elapsed()
    );
    output
}

/// The message of a frame beyond the work budget.
const WORK: &str = "E_LIMIT: checking the declared inverse of the frame `frame_limits::b` on `frame_limits::C`: algebraic work limit exceeded";

/// A unipotent frame with a few large entries is within the budget. With all
/// 64 entries of its upper right block, each of its 128 products of `A` and
/// the constant 1 is charged 207,936 units, and the frame is beyond the
/// budget of 8,000,000 units, before the kernel computes most of them. The
/// old charge accepted it after 14 seconds.
#[test]
fn a_unipotent_frame_is_charged_for_the_products_of_its_large_entries() {
    success(&check(unipotent(&block(8))));
    let error = expect_code(&check(unipotent(&block(64))), "E_LIMIT");
    assert!(error.contains(WORK), "{error}");
    assert_eq!(error.lines().count(), 1, "{error}");
}

/// Every entry of `P` is `A` and every entry of `Q` is 1, so `P·Q` has 4096
/// products of `A` and 1. The old charge let `(1 + x0 + … + x9)^3` reach the
/// comparison (`E_FRAME` after 26 seconds) and stopped the frame of `A` on
/// work after 74 seconds. The products are now charged beyond the budget
/// after a few dozen of them.
#[test]
fn the_products_of_a_dense_polynomial_frame_end_on_work() {
    for variables in [10, 12] {
        let sum: Vec<String> = (0..variables).map(|i| format!("x{i}")).collect();
        let a = format!("(1 + {})^3", sum.join(" + "));
        let error = expect_code(
            &check((columns(|_, _| a.clone()), columns(|_, _| "1".into()))),
            "E_LIMIT",
        );
        assert!(error.contains(WORK), "{variables}: {error}");
    }
}
