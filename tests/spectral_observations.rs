//! The Stage 5 acceptance program, `examples/packages/geometry/spectral-observations`
//! (#806; the native evidence of C3 to C5, C9 to C11, C14 and C18). The
//! program depends on std and on `nature`, declares its free modules,
//! endomorphism fields, spectra, branch, invariants and dimensionless chart in
//! `src/profile.vast`, and observes them in `src/main.vast`, where observation
//! `k` adds `2^(k - 1)` when it fails. These tests run it in place and
//! mutated, submit forged and tampered wire to the kernel, and run the
//! rejected packages of Stage 5 under `examples/reject/packages/`.
mod common;
use common::{Run, Scratch, assert_wire_rejected, cli, expect_code, kernel, root, success};
use serde_json::{Value, json};
use std::collections::BTreeSet;

const EXAMPLE: &str = "examples/packages/geometry/spectral-observations";
const MANIFEST: &str =
    include_str!("../examples/packages/geometry/spectral-observations/Vastitas.toml");
const PROFILE: &str =
    include_str!("../examples/packages/geometry/spectral-observations/src/profile.vast");
const MAIN: &str =
    include_str!("../examples/packages/geometry/spectral-observations/src/main.vast");
/// The program has the observations `1..=CODES`.
const CODES: u32 = 32;
/// The name of the program's package.
const PACKAGE: &str = "spectral_observations";

/// The rejected packages of Stage 5, by directory. Each must be rejected,
/// print nothing on standard output and print exactly the lines of
/// `<directory>.stderr`, with the repository root removed.
const REJECTED_PACKAGES: [&str; 6] = [
    "examples/reject/packages/spectral-gap-at-origin",
    "examples/reject/packages/spectral-jordan-branch",
    "examples/reject/packages/spectral-not-symmetric",
    "examples/reject/packages/spectral-other-object",
    "examples/reject/packages/spectral-wrong-witness",
    "examples/reject/packages/spectral-rank-limit",
];

/// The program with `profile` and `main` as its two modules, in a scratch
/// directory. It depends on the repository's std and nature packages by
/// absolute path, so that both reach one std package.
fn fixture(profile: &str, main: &str) -> Scratch {
    common::prepare_stdlib_package();
    let s = Scratch::empty("spectral observations");
    let manifest = common::checked_replace(
        &common::checked_replace(
            MANIFEST,
            "\"../../../stdlib\"",
            &format!("{:?}", root().join("stdlib")),
        ),
        "\"../../../nature\"",
        &format!("{:?}", root().join("nature")),
    );
    s.write("app/Vastitas.toml", &manifest);
    s.write("app/src/profile.vast", profile);
    s.write("app/src/main.vast", main);
    s
}

fn check(s: &Scratch) -> std::process::Output {
    s.check_manifest("app/Vastitas.toml")
}

fn run(s: &Scratch) -> Run {
    s.check_build_and_run("app/Vastitas.toml")
}

/// What the program does when the bits of its failed observations add up to
/// `failures`: it shows the sum, and returns 0 only when it is 0.
fn failed(failures: u64) -> Run {
    Run {
        status: i32::from(failures != 0),
        stdout: String::new(),
        stderr: format!("failures = {failures}\n"),
    }
}

/// `MAIN` with extra items inserted before its helpers.
fn with(extra: &str) -> String {
    common::checked_replace(MAIN, "fn verdict(", &format!("{extra}\nfn verdict("))
}

#[track_caller]
fn rejects(main: &str, code: &str) -> String {
    expect_code(&check(&fixture(PROFILE, main)), code)
}

fn request(s: &Scratch) -> Value {
    s.captured("app/Vastitas.toml", common::CURRENT_PROTOCOL)
}

/// The bits that the `verdict` calls of `main` add on failure, in source
/// order. Each is the last argument of its call.
fn bits(main: &str) -> Vec<u64> {
    let mut found = Vec::new();
    let mut rest = main;
    while let Some(at) = rest.find("verdict(") {
        let open = at + "verdict".len();
        if rest[..at].ends_with("fn ") {
            // The helper's definition, not a call.
            rest = &rest[open..];
            continue;
        }
        let (mut depth, mut comma, mut close) = (0, None, None);
        for (i, c) in rest[open..].char_indices() {
            match c {
                '(' => depth += 1,
                ')' if depth == 1 => {
                    close = Some(open + i);
                    break;
                }
                ')' => depth -= 1,
                ',' if depth == 1 => comma = Some(open + i),
                _ => {}
            }
        }
        let (comma, close) = (comma.unwrap(), close.unwrap());
        found.push(rest[comma + 1..close].trim().parse().unwrap());
        rest = &rest[close..];
    }
    found
}

/// The bit of observation `code`.
fn bit(code: u32) -> u64 {
    1 << (code - 1)
}

/// JSON pointer to the module `path` of the program's package.
fn module_pointer(raw: &Value, path: &[&str]) -> String {
    let packages = raw["packages"].as_array().unwrap();
    let p = packages
        .iter()
        .position(|p| p["name"] == PACKAGE)
        .expect("the program's package");
    let m = packages[p]["modules"]
        .as_array()
        .unwrap()
        .iter()
        .position(|m| m["path"] == json!(path))
        .unwrap_or_else(|| panic!("no module {path:?}"));
    format!("/packages/{p}/modules/{m}")
}

/// JSON pointer to a named declaration of the program, in either module.
fn declaration_pointer(raw: &Value, name: &str) -> String {
    for path in [&[][..], &["profile"][..]] {
        let module = module_pointer(raw, path);
        if let Some(d) = raw
            .pointer(&format!("{module}/indexed_declarations"))
            .unwrap()
            .as_array()
            .unwrap()
            .iter()
            .position(|d| d["name"] == name)
        {
            return format!("{module}/indexed_declarations/{d}");
        }
    }
    panic!("no declaration {name}")
}

/// JSON pointer to the body of a named function of `main.vast`.
fn body_pointer(raw: &Value, name: &str) -> String {
    let module = module_pointer(raw, &[]);
    let f = raw
        .pointer(&format!("{module}/functions"))
        .unwrap()
        .as_array()
        .unwrap()
        .iter()
        .position(|f| f["name"] == name)
        .unwrap_or_else(|| panic!("no function {name}"));
    format!("{module}/functions/{f}/body")
}

/// JSON pointer to the first call of `callee`, in source order, below `at`.
fn call_pointer(raw: &Value, at: &str, callee: &str) -> String {
    fn find(value: &Value, at: String, callee: &str) -> Option<String> {
        match value {
            Value::Object(fields) => {
                if fields.get("kind") == Some(&json!("call")) && fields["callee"] == callee {
                    return Some(at);
                }
                fields
                    .iter()
                    .filter(|(key, _)| *key != "span")
                    .find_map(|(key, child)| find(child, format!("{at}/{key}"), callee))
            }
            Value::Array(items) => items
                .iter()
                .enumerate()
                .find_map(|(index, child)| find(child, format!("{at}/{index}"), callee)),
            _ => None,
        }
    }
    find(raw.pointer(at).unwrap(), at.to_owned(), callee)
        .unwrap_or_else(|| panic!("no call of {callee} below {at}"))
}

/// `raw` with the value at `path` replaced.
fn forged(raw: &Value, path: &str, value: Value) -> Value {
    let mut changed = raw.clone();
    *changed
        .pointer_mut(path)
        .unwrap_or_else(|| panic!("no {path}")) = value;
    changed
}

/// The kernel's response rejects the wire with `code`, and its first
/// diagnostic says `message`.
#[track_caller]
fn rejected_with(response: &Value, code: &str, message: &str) {
    assert_wire_rejected(response, code);
    let said = response["diagnostics"][0]["message"].as_str().unwrap();
    assert!(said.contains(message), "{said}");
}

/// The program's two modules.
#[derive(Clone)]
struct Program {
    profile: String,
    main: String,
}

impl Program {
    fn shipped() -> Self {
        Self {
            profile: PROFILE.to_owned(),
            main: MAIN.to_owned(),
        }
    }

    /// The program with the only occurrence of `from`, in either module,
    /// replaced by `to`.
    #[track_caller]
    fn mutate(&mut self, from: &str, to: &str) {
        let count = self.profile.matches(from).count() + self.main.matches(from).count();
        assert_eq!(count, 1, "{from:?} must occur once");
        for module in [&mut self.profile, &mut self.main] {
            *module = module.replacen(from, to, 1);
        }
    }

    fn fixture(&self) -> Scratch {
        fixture(&self.profile, &self.main)
    }
}

/// Observation `k` adds `2^(k - 1)`: the bits of `main` are exactly those of
/// `1..=CODES`, each once, so the failures `m` that the program shows name
/// the failed observations.
#[test]
fn each_observation_adds_its_own_bit() {
    let found = bits(MAIN);
    assert_eq!(
        found,
        (1..=CODES).map(bit).collect::<Vec<_>>(),
        "the bits of main, in source order"
    );
}

/// The program checks, builds and shows no failures in place, with the paths
/// of its manifest (C18).
#[test]
fn the_example_checks_builds_and_shows_no_failures_in_place() {
    common::prepare_stdlib_package();
    let manifest = format!("{EXAMPLE}/Vastitas.toml");
    success(
        &cli()
            .current_dir(root())
            .args(["check", "--manifest-path", &manifest])
            .output()
            .unwrap(),
    );
    let scratch = Scratch::empty("spectral observations in place");
    let program = scratch.0.join("program");
    success(
        &cli()
            .current_dir(root())
            .args(["build", "--manifest-path", &manifest, "-o"])
            .arg(&program)
            .output()
            .unwrap(),
    );
    let output = std::process::Command::new(&program).output().unwrap();
    assert_eq!(common::ran(&output), failed(0));
    // The copy that the other tests mutate is the same program.
    assert_eq!(run(&Program::shipped().fixture()), failed(0));
}

/// A source mutation and the observations it falsifies.
type Mutation = (&'static str, &'static str, &'static [u32]);

/// Each observation can fail. Within a group, the mutations falsify disjoint
/// observations, the program shows exactly the sum of their bits, and every
/// observation is falsified by some group.
#[test]
fn mutated_observations_change_the_native_result() {
    let groups: [&[Mutation]; 3] = [
        &[
            // C4: another reference, another tr(H), another coefficient.
            (
                "pullback(t -> 2*x^2 + 2*y^2)",
                "pullback(t -> 2*x^2 + 3*y^2)",
                &[1],
            ),
            (
                "tr1: Smooth<Plane, Line> = trace_power(H, 1)",
                "tr1: Smooth<Plane, Line> = trace_power(H, 2)",
                &[2],
            ),
            // The coefficient of t^1 is 0, whose gradient is not -1/2 of (4x, 4y).
            (
                "c0: Smooth<Plane, Line> = char_coefficient(S, 0)",
                "c0: Smooth<Plane, Line> = char_coefficient(S, 1)",
                &[3],
            ),
            // C5: the gradient at (2, 1) is (8, 4).
            (
                "a: Smooth<Pt, Plane> = plane_at(1, 2)",
                "a: Smooth<Pt, Plane> = plane_at(2, 1)",
                &[4],
            ),
            // C9: 6 and 2 are no eigenvalues; -5 is one.
            ("on(p, line_at(5)), 64)", "on(p, line_at(6)), 64)", &[7]),
            ("on(q, line_at(1)), 256)", "on(q, line_at(2)), 256)", &[9]),
            (
                "!on(p, line_at(4)), 1024)",
                "!on(p, line_at(-5)), 1024)",
                &[11],
            ),
            // C10: d lambda at ((1, 0), 1) is (1, 0), still a unit covector,
            // and it lies over (1, 0), not over p.
            (
                "d_plus: Cotangent<Plane> = dlambda(p, line_at(5))",
                "d_plus: Cotangent<Plane> = dlambda(q, line_at(1))",
                &[13, 32],
            ),
            // C11: the entry (e1, e2) read at (e2, e2), in both projectors.
            (
                "p12 = branch_projector(Smooth, Line, branch = B, e1, e2)",
                "p12 = branch_projector(Smooth, Line, branch = B, e2, e2)",
                &[16, 17],
            ),
            // C3: t does not annihilate H(1, 0); another polynomial is not chi.
            (
                "verdict(ann_h(z), 131072)",
                "verdict(ann_h(q), 131072)",
                &[18],
            ),
            (
                "element = t^2 - x^2 - y^2)",
                "element = t^2 - x^2 + y^2)",
                &[20],
            ),
            // [[2, 1], [1, 2]] in place of 2I: t - 2 does not annihilate it,
            // its entry (f1, f2) is 1, and its invariants are not those of J.
            (
                "TwoI: Endomorphism<Pt> = rows((2, 0), (0, 2)) of W symmetric",
                "TwoI: Endomorphism<Pt> = rows((2, 1), (1, 2)) of W symmetric",
                &[21, 23, 25],
            ),
            // 0 in place of N: t annihilates it and its entry (f1, f2) is 0.
            (
                "N: Endomorphism<Pt> = rows((0, 1), (0, 0)) of W;",
                "N: Endomorphism<Pt> = rows((0, 0), (0, 0)) of W;",
                &[27, 29],
            ),
        ],
        &[
            // C5: the gradients at (3, 4) and at the origin.
            ("vplane(p, 12, 16)", "vplane(p, 16, 12)", &[5]),
            ("vplane(z, 0, 0)", "vplane(a, 0, 0)", &[6]),
            // C9: -5 is no eigenvalue at (1, 0), nor -1 at the origin, which
            // is off the chart; (1, 0) with -1 is a branch point.
            ("on(p, line_at(-5)), 128)", "on(q, line_at(-5)), 128)", &[8]),
            (
                "on(q, line_at(-1)), 512)",
                "on(z, line_at(-1)), 512)",
                &[10],
            ),
            (
                "!on(z, line_at(0)), 2048)",
                "!on(q, line_at(-1)), 2048)",
                &[12],
            ),
            // C10: d lambda at 5 in place of -5.
            (
                "d_minus: Cotangent<Plane> = dlambda(p, line_at(-5))",
                "d_minus: Cotangent<Plane> = dlambda(p, line_at(5))",
                &[14],
            ),
            // C3: 0 annihilates every H(p).
            (
                "ann_h = annihilates(Smooth, spectrum = S, element = t);",
                "ann_h = annihilates(Smooth, spectrum = S, element = 0 * t);",
                &[19],
            ),
            // (t - 2)^2 annihilates J (Cayley-Hamilton), (t - 3)^2 does not.
            (
                "ann_j2 = annihilates(Smooth, spectrum = SJ, element = (t - 2)^2)",
                "ann_j2 = annihilates(Smooth, spectrum = SJ, element = (t - 3)^2)",
                &[31],
            ),
            (
                "ann_j = annihilates(Smooth, spectrum = SJ, element = t - 2)",
                "ann_j = annihilates(Smooth, spectrum = SJ, element = (t - 2)^2)",
                &[22],
            ),
            // [[2, 2], [0, 2]] in place of J: its entry (f1, f2) of J - 2I is 2,
            // and its invariants are still those of 2I.
            (
                "J: Endomorphism<Pt> = rows((2, 1), (0, 2)) of W;",
                "J: Endomorphism<Pt> = rows((2, 2), (0, 2)) of W;",
                &[24],
            ),
            // diag(0, 1) in place of 0: t does not annihilate it, and its
            // invariants are not those of N.
            (
                "Zero: Endomorphism<Pt> = rows((0, 0), (0, 0)) of W symmetric",
                "Zero: Endomorphism<Pt> = rows((0, 0), (0, 1)) of W symmetric",
                &[26, 30],
            ),
            // The entry (f1, f1) of diag(0, 1) - I is -1.
            (
                "act_zero = action_entry(Smooth, spectrum = SZero, element = t, f1, f2)",
                "act_zero = action_entry(Smooth, spectrum = SZero, element = t - 1, f1, f1)",
                &[28],
            ),
        ],
        &[
            // C10: d lambda at 5 against the sharp of d lambda at -5 is -1.
            (
                "reads(pairing(d_plus, sharp_euclid(d_plus)), 1, 1)",
                "reads(pairing(d_plus, sharp_euclid(d_minus)), 1, 1)",
                &[15],
            ),
            // d lambda at -5 lies over p, not over (1, 0).
            (
                "lies_over(d_minus, p), 2147483648)",
                "lies_over(d_minus, q), 2147483648)",
                &[32],
            ),
            // C11: the entry (e2, e2) at 5 is 1/5.
            (
                "reads(p22(p, line_at(-5)), 4, 5)",
                "reads(p22(p, line_at(5)), 4, 5)",
                &[17],
            ),
            // The other contrasts of the point, one at a time.
            (
                "ann_two = annihilates(Smooth, spectrum = STwoI, element = t - 2)",
                "ann_two = annihilates(Smooth, spectrum = STwoI, element = t - 3)",
                &[21],
            ),
            (
                "act_two = action_entry(Smooth, spectrum = STwoI, element = t - 2, f1, f2)",
                "act_two = action_entry(Smooth, spectrum = STwoI, element = t - 1, f1, f1)",
                &[23],
            ),
            (
                "ann_zero = annihilates(Smooth, spectrum = SZero, element = t)",
                "ann_zero = annihilates(Smooth, spectrum = SZero, element = t - 1)",
                &[26],
            ),
            (
                "ann_n = annihilates(Smooth, spectrum = SN, element = t);",
                "ann_n = annihilates(Smooth, spectrum = SN, element = t^2);",
                &[27],
            ),
            (
                "act_n = action_entry(Smooth, spectrum = SN, element = t, f1, f2)",
                "act_n = action_entry(Smooth, spectrum = SN, element = t, f2, f1)",
                &[29],
            ),
            // [[2, 1], [0, 3]] in place of J has other invariants, and
            // (t - 2)^2 does not annihilate it.
            (
                "J: Endomorphism<Pt> = rows((2, 1), (0, 2)) of W;",
                "J: Endomorphism<Pt> = rows((2, 1), (0, 3)) of W;",
                &[25, 31],
            ),
        ],
    ];
    let mut shown = BTreeSet::new();
    for (index, mutations) in groups.iter().enumerate() {
        let mut program = Program::shipped();
        let mut flipped = BTreeSet::new();
        for (from, to, codes) in *mutations {
            program.mutate(from, to);
            for code in *codes {
                assert!(flipped.insert(*code), "group {index} repeats code {code}");
            }
        }
        let expected = flipped.iter().map(|code| bit(*code)).sum::<u64>();
        assert_eq!(
            run(&program.fixture()),
            failed(expected),
            "group {index}: {flipped:?}"
        );
        shown.extend(flipped);
    }
    assert_eq!(shown, (1..=CODES).collect());
}

/// The frontend's request for the program is of the current protocol, and the
/// kernel emits it (C14).
#[test]
fn the_example_emits_from_the_frontend_request() {
    let raw = request(&Program::shipped().fixture());
    assert_eq!(raw["version"], common::CURRENT_PROTOCOL);
    let accepted = kernel(&raw, "emit");
    assert_eq!(accepted["ok"], true, "{accepted}");
}

/// No spectral record carries a characteristic polynomial, an adjugate, a
/// quotient, a map or an embedded field: each is an unknown field of the
/// kernel's decoder, which computes them all (C2, C14).
#[test]
fn raw_wire_rejects_spectral_certificates_and_forged_maps() {
    let raw = request(&Program::shipped().fixture());
    let h = declaration_pointer(&raw, "H");
    let s = declaration_pointer(&raw, "S");
    let b = declaration_pointer(&raw, "B");
    let tr2 = declaration_pointer(&raw, "tr2");
    let c0 = declaration_pointer(&raw, "c0");
    let ann = declaration_pointer(&raw, "ann_j");
    let dlambda = declaration_pointer(&raw, "dlambda");
    let p12 = declaration_pointer(&raw, "p12");
    assert_eq!(raw.pointer(&s).unwrap()["kind"], "spectrum");
    assert_eq!(raw.pointer(&b).unwrap()["kind"], "branch");
    assert_eq!(
        raw.pointer(&tr2).unwrap()["definition"]["kind"],
        "trace_power"
    );
    assert_eq!(
        raw.pointer(&p12).unwrap()["binding"]["op"],
        "branch_projector"
    );
    let polynomial = json!([{ "op": "natural", "value": "1" }]);
    for (pointer, field) in [
        (h.clone(), "characteristic"),
        (s.clone(), "characteristic"),
        (s.clone(), "adjugate"),
        (s.clone(), "quotient"),
        (s.clone(), "certificate"),
        (b.clone(), "quotient"),
        (b.clone(), "certificate"),
        (format!("{tr2}/definition"), "map"),
        (format!("{tr2}/definition"), "image"),
        (format!("{c0}/definition"), "characteristic"),
        (format!("{ann}/binding"), "rows"),
        (format!("{ann}/binding"), "characteristic"),
        (format!("{dlambda}/binding"), "witness"),
        (format!("{dlambda}/binding"), "quotient"),
        (format!("{p12}/binding"), "adjugate"),
    ] {
        let mut extra = raw.clone();
        extra.pointer_mut(&pointer).unwrap()[field] = polynomial.clone();
        rejected_with(
            &kernel(extra, "emit"),
            "E_PROTOCOL",
            &format!("unknown protocol field '{field}'"),
        );
    }
}

/// The kernel checks every declaration that the wire carries: a field that is
/// not symmetric, a chart without a gap, a perturbed witness, a localization
/// with the fiber coordinate, a spectrum or a branch that names a declaration
/// of another object, and an invariant of a field of another object are each
/// `E_SPECTRAL`, and a power beyond the limit is `E_LIMIT` (C1, C8, C14).
#[test]
fn tampered_spectral_declarations_are_rejected_by_the_kernel() {
    let raw = request(&Program::shipped().fixture());
    let h = declaration_pointer(&raw, "H");
    let s = declaration_pointer(&raw, "S");
    let b = declaration_pointer(&raw, "B");
    let tr2 = declaration_pointer(&raw, "tr2");
    let n = |value: &str| json!({ "op": "natural", "value": value });
    let coordinate = |name: &str| json!({ "op": "coordinate", "name": name });
    let gap =
        "does not certify the gap: W·χ′ − g^e is not a multiple of the characteristic polynomial χ";
    for (path, value, code, message) in [
        // The entry (e2, e1) of H is -y, its entry (e1, e2) y.
        (
            format!("{h}/rows/1/0"),
            json!({ "op": "neg", "operand": coordinate("y") }),
            "E_SPECTRAL",
            "is declared `symmetric`, but its entry (e1, e2) differs from its entry (e2, e1)",
        ),
        // g = 1: the eigenvalues meet at the origin.
        (format!("{b}/localize"), n("1"), "E_SPECTRAL", gap),
        // W = (1/2 + 10^-20) t.
        (
            format!("{b}/witness/factors/0"),
            json!({ "op": "fraction", "numerator": "50000000000000000001",
                    "denominator": "100000000000000000000" }),
            "E_SPECTRAL",
            gap,
        ),
        (
            format!("{b}/localize"),
            coordinate("t"),
            "E_SPECTRAL",
            "contains the fiber coordinate `t`",
        ),
        (
            format!("{b}/localize"),
            n("0"),
            "E_SPECTRAL",
            "is zero; a branch localizes at a nonzero `localize`",
        ),
        // W = t^2 / 2 is not reduced.
        (
            format!("{b}/witness/factors/1"),
            json!({ "op": "pow", "base": coordinate("t"), "exponent": "2" }),
            "E_SPECTRAL",
            "has degree 2 in the fiber coordinate `t`; a witness is reduced, of degree below the rank 2",
        ),
        // A spectrum on the plane of the field J on the point.
        (
            format!("{s}/endomorphism/path"),
            json!(["J"]),
            "E_SPECTRAL",
            "its endomorphism `spectral_observations::profile::J` is on `vastitas_geometry::smooth::affine::Pt`",
        ),
        // A branch on the plane of the spectrum of J.
        (
            format!("{b}/spectrum/path"),
            json!(["SJ"]),
            "E_SPECTRAL",
            "a branch and its spectrum have one object",
        ),
        // tr(J^2) as a map on the plane.
        (
            format!("{tr2}/definition/endomorphism/path"),
            json!(["J"]),
            "E_SPECTRAL",
            "is a smooth map on `spectral_observations::profile::Plane`, but its endomorphism",
        ),
        (
            format!("{s}/fiber"),
            json!("x"),
            "E_SPECTRAL",
            "the fiber coordinate `x`",
        ),
        (
            format!("{tr2}/definition/power"),
            json!("9"),
            "E_LIMIT",
            "takes the power 9, beyond the limit of 8 (`spectralPower`)",
        ),
    ] {
        rejected_with(&kernel(forged(&raw, &path, value), "emit"), code, message);
    }
}

/// The bindings and bodies are checked as the frontend sends them: an
/// observation that names the spectrum of another object than its point, or a
/// function body whose call reaches a primitive of another object, fails its
/// call (`E_ENDPOINT`), and a binding that names a spectrum where its branch
/// must be fails the declaration (`E_SPECTRAL`) (C14). The kernel regression
/// `SpectralRegression.lean` tampers with the embedded data of checked Core,
/// which the wire cannot carry.
#[test]
fn tampered_spectral_bindings_and_bodies_are_rejected_by_the_kernel() {
    let raw = request(&Program::shipped().fixture());
    let main = body_pointer(&raw, "main");
    let gradient = body_pointer(&raw, "gradient");
    let ann_two = declaration_pointer(&raw, "ann_two");
    let on = declaration_pointer(&raw, "on");
    for (path, value, code, message) in [
        // ann_two observes the spectrum of H on the plane, at the point o.
        (
            format!("{ann_two}/binding/spectrum/path"),
            json!(["S"]),
            "E_ENDPOINT",
            "ann_two requires a point with target Plane (the spectrum's object), but the supplied point has target Pt",
        ),
        // The point o reaches an observation of the plane.
        (
            format!("{}/callee", call_pointer(&raw, &main, "ann_two")),
            json!("ann_h"),
            "E_ENDPOINT",
            "ann_h requires a point with target Plane (the spectrum's object), but the supplied point has target Pt",
        ),
        // A spectrum where the branch must be.
        (
            format!("{on}/binding/branch/path"),
            json!(["S"]),
            "E_SPECTRAL",
            "is not a branch declaration",
        ),
        // The gradient of a map on the plane with the eigenvalue's
        // differential, whose operands are a point and an eigenvalue: the map
        // Plane -> Line is no point of the plane.
        (
            format!("{}/callee", call_pointer(&raw, &gradient, "differential")),
            json!("dlambda"),
            "E_ENDPOINT",
            "dlambda requires a point with target Plane (the branch's object), but the supplied point has target Line",
        ),
    ] {
        rejected_with(&kernel(forged(&raw, &path, value), "emit"), code, message);
    }
}

/// Objects, spectra and lines are static: an observation of the point at a
/// point of the plane, a branch observation at the point, and an eigenvalue
/// that is not on the line are each rejected before code generation (C1).
#[test]
fn spectral_mismatches_are_rejected_statically() {
    for (body, message) in [
        (
            "fn bad() -> Bool { ann_two(plane_at(1, 2)) }",
            "ann_two requires a point with target Pt (the spectrum's object), but the supplied point has target Plane",
        ),
        (
            "fn bad() -> Bool { on(pt_at(), line_at(5)) }",
            "on requires a point with target Plane (the branch's object), but the supplied point has target Pt",
        ),
        (
            "fn bad() -> Pair<Int> { p11(plane_at(3, 4), plane_at(5, 0)) }",
            "p11 requires a value with target Line (the primitive's declared line), but the supplied value has target Plane",
        ),
    ] {
        let stderr = rejects(&with(body), "E_ENDPOINT");
        assert!(stderr.contains(message), "{body}: {stderr}");
    }
}

/// The rejected packages of Stage 5 print their recorded diagnostics: the
/// gap at the origin and the Jordan block (C8), a field that is not
/// symmetric and a field of another object (C1), a perturbed witness (C8)
/// and a rank beyond the limit (C1, C16).
#[test]
fn rejected_stage5_packages_print_their_diagnostics() {
    common::prepare_stdlib_package();
    for directory in REJECTED_PACKAGES {
        let manifest = format!("{directory}/Vastitas.toml");
        let output = cli()
            .current_dir(root())
            .args(["check", "--manifest-path", &manifest])
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(1),
            "{directory} must be rejected"
        );
        assert!(output.stdout.is_empty(), "{directory}: no output on stdout");
        // The driver prints canonical paths, so remove both spellings of the
        // root: a checkout reached through a symbolic link differs.
        let mut stderr = String::from_utf8(output.stderr).unwrap();
        for prefix in [root().to_path_buf(), root().canonicalize().unwrap()] {
            stderr = stderr.replace(&format!("{}/", prefix.display()), "");
        }
        let expected = std::fs::read_to_string(root().join(format!("{directory}.stderr"))).unwrap();
        assert_eq!(stderr, expected, "{directory}");
        assert_eq!(expected.lines().count(), 1, "{directory}");
        common::assert_source_names(&expected);
    }
}
