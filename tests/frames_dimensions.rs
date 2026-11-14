//! The Stage 4 acceptance program, `examples/packages/frames-and-dimensions`
//! (#759; C22, and the native evidence of C1 to C19). The program depends on
//! std and on `nature`, declares its frames, maps, metrics and physical
//! reading in `src/profile.vast`, and observes them in `src/main.vast`, one
//! failure code per observation. These tests run it in place and mutated,
//! check the protocol it selects, submit forged and tampered wire to the
//! kernel, and run the rejected packages of Stage 4 under
//! `examples/reject/packages/`. The byte identity of C17 is tested in
//! `tests/nature_dimension.rs`.
mod common;
use common::{Scratch, assert_wire_rejected, cli, expect_code, kernel, root, success};
use serde_json::{Value, json};

const EXAMPLE: &str = "examples/packages/frames-and-dimensions";
const MANIFEST: &str = include_str!("../examples/packages/frames-and-dimensions/Vastitas.toml");
const PROFILE: &str = include_str!("../examples/packages/frames-and-dimensions/src/profile.vast");
const MAIN: &str = include_str!("../examples/packages/frames-and-dimensions/src/main.vast");
/// The program's failure codes are exactly `1..=CODES`.
const CODES: u32 = 36;
/// The name of the program's package.
const PACKAGE: &str = "frames_and_dimensions";

/// The rejected packages of Stage 4, by directory. Each must be rejected,
/// print nothing on standard output and print exactly the lines of
/// `<directory>.stderr`, with the repository root removed.
const REJECTED_PACKAGES: [&str; 6] = [
    "examples/reject/packages/frame-singular",
    "examples/reject/packages/frame-wrong-inverse",
    "examples/reject/packages/frame-other-frame",
    "examples/reject/packages/frame-other-object",
    "examples/reject/packages/dimension-dx2-dt2",
    "examples/reject/packages/dimension-wrong-kind",
];

/// The program with `profile` and `main` as its two modules, in a scratch
/// directory. It depends on the repository's std and nature packages by
/// absolute path, so that both reach one std package.
fn fixture(profile: &str, main: &str) -> Scratch {
    common::prepare_stdlib_package();
    let s = Scratch::empty("frames and dimensions");
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

fn run(s: &Scratch) -> Vec<u8> {
    s.check_build_and_run("app/Vastitas.toml")
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
    s.captured("app/Vastitas.toml", 9)
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

/// JSON pointer to the result expression of a named function of `main.vast`.
fn result_pointer(raw: &Value, name: &str) -> String {
    let module = module_pointer(raw, &[]);
    let f = raw
        .pointer(&format!("{module}/functions"))
        .unwrap()
        .as_array()
        .unwrap()
        .iter()
        .position(|f| f["name"] == name)
        .unwrap_or_else(|| panic!("no function {name}"));
    format!("{module}/functions/{f}/body/result")
}

/// `raw` with the value at `path` replaced.
fn forged(raw: &Value, path: &str, value: Value) -> Value {
    let mut changed = raw.clone();
    *changed
        .pointer_mut(path)
        .unwrap_or_else(|| panic!("no {path}")) = value;
    changed
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

/// The program with the failure code `k` of every `verdict` call replaced by
/// `2^(k - 1)`, as in `tests/smooth_differential.rs`. Its native result
/// `42 + m` then names exactly the failed observations, as the bits of `m`.
/// The codes must be exactly `1..=CODES`, each used once.
fn bitmask(main: &str) -> String {
    let mut masked = String::new();
    let mut codes = Vec::new();
    let mut rest = main;
    while let Some(at) = rest.find("verdict(") {
        let open = at + "verdict".len();
        masked.push_str(&rest[..open]);
        if rest[..at].ends_with("fn ") {
            // The helper's definition, not a call.
            rest = &rest[open..];
            continue;
        }
        // The code is the last argument, before the call's closing parenthesis.
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
        let code: u32 = rest[comma + 1..close].trim().parse().unwrap();
        codes.push(code);
        masked.push_str(&rest[open..=comma]);
        masked.push_str(&format!(" {}", 1u64 << (code - 1)));
        rest = &rest[close..];
    }
    masked.push_str(rest);
    codes.sort_unstable();
    assert_eq!(codes, (1..=CODES).collect::<Vec<_>>());
    masked
}

/// The program checks, builds and prints 42 in place, with the paths of its
/// manifest (C22).
#[test]
fn the_example_checks_builds_and_prints_42_in_place() {
    common::prepare_stdlib_package();
    let manifest = format!("{EXAMPLE}/Vastitas.toml");
    success(
        &cli()
            .current_dir(root())
            .args(["check", "--manifest-path", &manifest])
            .output()
            .unwrap(),
    );
    let scratch = Scratch::empty("frames and dimensions in place");
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
    success(&output);
    assert_eq!(output.stdout, b"42\n");
    // The copy that the other tests mutate is the same program.
    assert_eq!(run(&Program::shipped().fixture()), b"42\n");
}

/// A source mutation and the codes of the observations it falsifies.
type Mutation = (&'static str, &'static str, &'static [u32]);

/// Each observation can fail. Within a group, the mutations falsify disjoint
/// observations, and every code is falsified by some group.
#[test]
fn mutated_observations_change_the_native_result() {
    let groups: [(&[Mutation], u64); 4] = [
        (
            &[
                // C1: the array of v in b lies over p, not over q.
                ("over(w, p), 1)", "over(w, q), 1)", &[1]),
                // C4: v = (3, 2) decodes from its array, not (2, 1).
                (
                    "same_vector(dec_b(w), v)",
                    "same_vector(dec_b(w), vplane(p, 2, 1))",
                    &[4],
                ),
                // A seed at f(p) = (5, 2) is no failure.
                (
                    "dimage(image_at(5, 3), 1, 2)",
                    "dimage(image_at(5, 2), 1, 2)",
                    &[8],
                ),
                // C7: the entry (0, 0) of M_b2c2 is 2/3, not 4.
                (
                    "reads(entry_00(m), 4, 1)",
                    "reads(entry_00(m2), 4, 1)",
                    &[13],
                ),
                // The rank-one map in place of f.
                (
                    "then(m, move_b2b(p))), m2)",
                    "then(k, move_b2b(p))), m2)",
                    &[17],
                ),
                // C9: r at p reads -1, not -2.
                (
                    "reads(entry_01(move_xyr(q)), -2, 1)",
                    "reads(entry_01(move_xyr(p)), -2, 1)",
                    &[21],
                ),
                // C10: apply moves the array to f(p) = (5, 2).
                (
                    "!over(apply_map(m, w), image_at(2, 1))",
                    "!over(apply_map(m, w), image_at(5, 2))",
                    &[25],
                ),
                // C11: a map of rank two sends neither array to zero.
                (
                    "pullback(u -> x + y, v -> 2*x + 2*y)",
                    "pullback(u -> x + y, v -> 2*x + 3*y)",
                    &[29, 30],
                ),
                // C12: another metric has another Gram matrix in b, and
                // another inverse.
                ("gram((2, 1), (1, 1))", "gram((3, 1), (1, 1))", &[33, 35]),
            ],
            22_298_038_451,
        ),
        (
            &[
                // C2: the coordinate frame is not b.
                (
                    "reads(first(enc_xy(v)), 3, 1)",
                    "reads(first(enc_b(v)), 3, 1)",
                    &[2],
                ),
                (
                    "same_vector(dec_r(enc_r(v)), v)",
                    "same_vector(dec_r(enc_r(v)), vplane(p, 1, 1))",
                    &[5],
                ),
                // C5: changes of frame at p and at q do not compose.
                (
                    "then(move_b2b(p), move_bb2(p))",
                    "then(move_b2b(p), move_bb2(q))",
                    &[9],
                ),
                (
                    "reads(entry_00(m2), 2, 3)",
                    "reads(entry_00(m), 2, 3)",
                    &[14],
                ),
                // C7: coapply of another covector.
                (
                    "coapply_map(m, coenc_c(beta))), pullback(f(), p, beta)), 18)",
                    "coapply_map(m, coenc_c(dimage(fp, 2, 1)))), pullback(f(), p, beta)), 18)",
                    &[18],
                ),
                // C8 and C10: with g(u, v) = u + v, g(f(p)) = 7 and the
                // composite reads (5/2, 11/2).
                ("pullback(t -> u*v)", "pullback(t -> u + v)", &[20, 27]),
                // C9: the array lies over p.
                (
                    "over(enc_r(v), p) && !over(enc_r(v), q), 22)",
                    "over(enc_r(v), q) && !over(enc_r(v), q), 22)",
                    &[22],
                ),
                // C10: coapply moves the array back to p, not to q.
                (
                    "coover(coapply_map(m, coenc_c(beta)), p)",
                    "coover(coapply_map(m, coenc_c(beta)), q)",
                    &[26],
                ),
            ],
            103_424_316,
        ),
        (
            &[
                // C2: r at q gives v = (3, 2) the array (-1, 1).
                (
                    "reads(first(enc_r(v)), 1, 1)",
                    "reads(first(enc_r(vplane(q, 3, 2))), 1, 1)",
                    &[3],
                ),
                // C4: a covector decodes over its own point.
                (
                    "same_covector(codec_b(coenc_b(alpha)), alpha)",
                    "same_covector(codec_b(coenc_b(alpha)), dplane(q, 1, 3))",
                    &[6],
                ),
                (
                    "then(move_b2r(p), move_bb2(p))",
                    "then(move_b2r(q), move_bb2(q))",
                    &[10],
                ),
                // C6: alpha pairs with (2, 3) to 11.
                (
                    "pairing(alpha, v)",
                    "pairing(alpha, vplane(p, 2, 3))",
                    &[11],
                ),
                // C7: the Jacobian at q.
                (
                    "matrix_xyuv(f(), p)), 15)",
                    "matrix_xyuv(f(), q)), 15)",
                    &[15],
                ),
                ("coenc_c2(beta)", "coenc_c2(dimage(fp, 2, 1))", &[19]),
                // C9: the change of frame at p accepts the array over p.
                (
                    "first(apply_map(move_rb(q), enc_r(v)))",
                    "first(apply_map(move_rb(p), enc_r(v)))",
                    &[23],
                ),
                // C10: g at f(p) composes with f at p.
                (
                    "matrix_cl(g(), image_at(5, 3))",
                    "matrix_cl(g(), image_at(5, 2))",
                    &[28],
                ),
                // C11: the 0 x 2 matrix at q does not apply to an array over p.
                (
                    "matrix_bz(to_pt(), p), w)",
                    "matrix_bz(to_pt(), q), w)",
                    &[32],
                ),
                // C12: the first row of the Gram matrix in b2.
                (
                    "gram_b(apply_map(move_b2b(p), vec_b2(p, 0, 1)))",
                    "gram_b(apply_map(move_b2b(p), vec_b2(p, 1, 0)))",
                    &[34],
                ),
            ],
            10_876_110_414,
        ),
        (
            &[
                // C4: r at q gives alpha the array (1, 10).
                (
                    "reads(cosecond(coenc_r(alpha)), 8, 1)",
                    "reads(cosecond(coenc_r(dplane(q, 1, 3))), 8, 1)",
                    &[7],
                ),
                // C6: arrays over one point pair to 9.
                ("enc_b(vplane(q, 3, 2))", "enc_b(vplane(p, 3, 2))", &[12]),
                (
                    "matrix_xyuv(f(), p)), 16)",
                    "matrix_xyuv(flatten(), p)), 16)",
                    &[16],
                ),
                // C9: the change from the coordinate frame to r at p does not
                // compose with the matrix of the shear, whose target point is
                // shear(p) = (4, 1).
                ("move_xyr(compose_smooth(shear(), p))", "move_xyr(p)", &[24]),
                // C11: the point p as a map has its image at p, not at q.
                ("vec_b(p, 0, 0)", "vec_b(q, 0, 0)", &[31]),
                // C12: the second column of the inverse Gram matrix in b.
                ("covec_b(p, 1, 0)", "covec_b(p, 0, 1)", &[35]),
                // C18: the gradient of x + 2t is (9, 8).
                ("pullback(t -> x + t)", "pullback(t -> x + 2*t)", &[36]),
            ],
            52_621_772_906,
        ),
    ];
    let mut shown = std::collections::BTreeSet::new();
    for (index, (mutations, expected)) in groups.iter().enumerate() {
        let mut program = Program::shipped();
        let mut flipped = std::collections::BTreeSet::new();
        for (from, to, codes) in *mutations {
            program.mutate(from, to);
            for code in *codes {
                assert!(flipped.insert(*code), "group {index} repeats code {code}");
            }
        }
        let bits: u64 = flipped.iter().map(|code| 1u64 << (code - 1)).sum();
        assert_eq!(*expected, 42 + bits, "group {index}: {flipped:?}");
        let masked = Program {
            main: bitmask(&program.main),
            ..program.clone()
        };
        assert_eq!(
            String::from_utf8(run(&masked.fixture())).unwrap(),
            format!("{expected}\n"),
            "group {index}: {flipped:?}"
        );
        if index == 0 {
            // The shipped codes add up: 42 + 1 + 4 + 8 + 13 + 17 + 21 + 25 +
            // 29 + 30 + 33 + 35.
            assert_eq!(run(&program.fixture()), b"258\n");
        }
        shown.extend(flipped);
    }
    assert_eq!(shown, (1..=CODES).collect());
}

/// The program selects protocol 9; protocols 7 and 8 reject its envelope,
/// and so do the older protocols (C14).
#[test]
fn the_example_selects_protocol_nine_and_older_envelopes_reject_it() {
    let raw = request(&Program::shipped().fixture());
    assert_eq!(raw["version"], 9);
    let accepted = kernel(&raw, "emit");
    assert_eq!(accepted["ok"], true, "{accepted}");
    for version in [7, 8] {
        let mut changed = raw.clone();
        changed["version"] = json!(version);
        assert_wire_rejected(&kernel(changed, "emit"), "E_PROTOCOL");
    }
    for version in 2..7 {
        let mut changed = raw.clone();
        changed["version"] = json!(version);
        let rejected = kernel(changed, "emit");
        assert_eq!(rejected["ok"], false, "version {version}: {rejected}");
    }
}

/// The kernel's response rejects the wire with `code`, and its first
/// diagnostic says `message`.
#[track_caller]
fn rejected_with(response: &Value, code: &str, message: &str) {
    assert_wire_rejected(response, code);
    let said = response["diagnostics"][0]["message"].as_str().unwrap();
    assert!(said.contains(message), "{said}");
}

/// A constant frame has no inverse on the wire, a frame polynomial in the
/// point needs a true one, and no frame record or frame binding carries a
/// matrix: the kernel computes every certificate and every embedded frame
/// itself (C1, C2, C14).
#[test]
fn raw_wire_rejects_forged_frame_records() {
    let raw = request(&Program::shipped().fixture());
    let b = declaration_pointer(&raw, "b");
    let r = declaration_pointer(&raw, "r");
    let matrix = declaration_pointer(&raw, "matrix_bc");
    let transition = declaration_pointer(&raw, "move_bb2");
    let encode = declaration_pointer(&raw, "enc_b");
    assert_eq!(raw.pointer(&b).unwrap()["kind"], "frame");
    assert_eq!(raw.pointer(&b).unwrap()["inverse"], Value::Null);
    assert_eq!(raw.pointer(&r).unwrap()["inverse"]["kind"], "columns");
    assert_eq!(
        raw.pointer(&matrix).unwrap()["binding"]["op"],
        "frame_matrix"
    );
    assert_eq!(
        raw.pointer(&transition).unwrap()["binding"]["op"],
        "frame_transition"
    );
    let n = |value: &str| json!({ "op": "natural", "value": value });
    let half =
        |numerator: &str| json!({ "op": "fraction", "numerator": numerator, "denominator": "2" });
    for (path, value, message) in [
        // The exact inverse of b, declared for the constant frame: the
        // kernel computes it, so a declared one is rejected.
        (
            format!("{b}/inverse"),
            json!({ "kind": "columns", "columns": [[n("1"), n("0")], [half("-1"), half("1")]] }),
            "is constant, so the kernel computes its inverse",
        ),
        // r without its inverse.
        (
            format!("{r}/inverse"),
            Value::Null,
            "depends on the point, so it needs its inverse",
        ),
        // r with the inverse of b, columns((1, 0), (-1/2, 1/2)).
        (
            format!("{r}/inverse/columns/1/0"),
            half("-1"),
            "is not its inverse: P·Q ≠ I",
        ),
        // b with the columns (1, 0) and (2, 0).
        (
            format!("{b}/columns/columns/1"),
            json!([n("2"), n("0")]),
            "is singular",
        ),
    ] {
        rejected_with(
            &kernel(forged(&raw, &path, value), "emit"),
            "E_FRAME",
            message,
        );
    }
    // A matrix, an inverse or a transition on a frame declaration or binding
    // is an unknown field.
    let identity = json!([["1", "0"], ["0", "1"]]);
    for (pointer, field) in [
        (b.clone(), "matrix"),
        (b.clone(), "rows"),
        (format!("{matrix}/binding"), "matrix"),
        (format!("{matrix}/binding"), "inverse"),
        (format!("{matrix}/binding"), "entries"),
        (format!("{transition}/binding"), "transition"),
        (format!("{transition}/binding"), "matrix"),
        (format!("{encode}/binding"), "inverse"),
        (format!("{encode}/binding"), "variance"),
    ] {
        let mut extra = raw.clone();
        extra.pointer_mut(&pointer).unwrap()[field] = identity.clone();
        rejected_with(
            &kernel(extra, "emit"),
            "E_PROTOCOL",
            &format!("unknown protocol field '{field}'"),
        );
    }
}

/// A frame binding embeds the declaration of the frame it names, so a binding
/// that names another frame changes the type of its value, and a function
/// body that mixes frames fails its call (C3, C5, C14). The wire names
/// frames only; the kernel regression `FrameRegression.lean` tampers with the
/// embedded matrices of checked Core, which the wire cannot carry.
#[test]
fn tampered_frame_bindings_and_bodies_are_rejected_by_the_kernel() {
    let raw = request(&Program::shipped().fixture());
    let encode = declaration_pointer(&raw, "enc_b");
    let matrix = declaration_pointer(&raw, "matrix_bc");
    let transition = declaration_pointer(&raw, "move_bb2");
    let gram = result_pointer(&raw, "gram_b");
    assert_eq!(raw.pointer(&gram).unwrap()["callee"], "coenc_b");
    assert_eq!(
        raw.pointer(&format!("{gram}/args/0/args/0/callee"))
            .unwrap(),
        "dec_b"
    );
    for (path, value, code, message) in [
        // The encoding into b names b2.
        (
            format!("{encode}/binding/frame/path"),
            json!(["b2"]),
            "E_TYPE",
            "expected Coords<b>, found Coords<b2>",
        ),
        // The matrix of f names a source frame on the target of f.
        (
            format!("{matrix}/binding/source/path"),
            json!(["c"]),
            "E_ENDPOINT",
            "matrix_bc requires a map with source Image (the source frame's object), but the supplied map has source Plane",
        ),
        // A change of frame from b on Plane to c on Image.
        (
            format!("{transition}/binding/target/path"),
            json!(["c"]),
            "E_ENDPOINT",
            "the source frame `frames_and_dimensions::profile::b` is on `frames_and_dimensions::profile::Plane` \
             and the target frame `frames_and_dimensions::profile::c` is on `frames_and_dimensions::profile::Image`",
        ),
        // A name that is not a frame.
        (
            format!("{transition}/binding/target/path"),
            json!(["Plane"]),
            "E_FRAME",
            "`frames_and_dimensions::profile::Plane` is not a frame declaration",
        ),
        // The Gram row decodes an array in b with the frame b2.
        (
            format!("{gram}/args/0/args/0/callee"),
            json!("dec_b2"),
            "E_ENDPOINT",
            "dec_b2 requires an array with frame b2 (the primitive's frame), but the supplied array has frame b",
        ),
        // A covector decoding where the vector array of b is decoded.
        (
            format!("{gram}/args/0/args/0/callee"),
            json!("codec_b"),
            "E_ENDPOINT",
            "codec_b requires an array of family CoCoords, but the supplied array has family Coords",
        ),
    ] {
        rejected_with(&kernel(forged(&raw, &path, value), "emit"), code, message);
    }
}

/// Frames, objects and variance are static: arrays in b and in b2, a vector
/// of another object of the same dimension, a map from b applied to an array
/// in b2, a vector where an array is expected, and a vector array where a
/// covector array is expected are each rejected before code generation (C3).
#[test]
fn frame_mismatches_are_rejected_statically() {
    let stderr = rejects(
        &with("fn bad(v: Tangent<Plane>) -> Bool { same_coords(enc_b(v), enc_b2(v)) }"),
        "E_ENDPOINT",
    );
    assert!(
        stderr.contains("Coords<b>") && stderr.contains("Coords<b2>"),
        "{stderr}"
    );
    let stderr = rejects(
        &with(concat!(
            "indexed primitive vimage = fiber_vector(Tangent, Smooth, Image);\n",
            "fn bad(p: Smooth<Pt, Image>) -> Coords<b> { enc_b(vimage(p, 1, 2)) }",
        )),
        "E_ENDPOINT",
    );
    assert!(
        stderr.contains(
            "enc_b requires a vector with object Plane (the frame's object), but the supplied vector has object Image"
        ),
        "{stderr}"
    );
    let stderr = rejects(
        &with(
            "fn bad(w: Coords<b>) -> Coords<c> { apply_map(matrix_bc(f(), plane_at(1, 1)), apply_map(move_bb2(plane_at(1, 1)), w)) }",
        ),
        "E_ENDPOINT",
    );
    assert!(
        stderr.contains(
            "apply_map requires an array with frame b (the map's source frame), but the supplied array has frame b2"
        ),
        "{stderr}"
    );
    let stderr = rejects(
        &with("fn bad(v: Tangent<Plane>) -> Bool { same_coords(enc_b(v), v) }"),
        "E_ENDPOINT",
    );
    assert!(
        stderr.contains(
            "same_coords requires a second operand of family Coords, but the supplied second operand has family Tangent"
        ),
        "{stderr}"
    );
    let stderr = rejects(
        &with("fn bad(alpha: CoCoords<b>, w: Coords<b>) -> Pair<Int> { pair_arrays(w, alpha) }"),
        "E_ENDPOINT",
    );
    assert!(
        stderr.contains(
            "pair_arrays requires a covector array of family CoCoords, but the supplied covector array has family Coords"
        ),
        "{stderr}"
    );
}

/// The rejected packages of Stage 4 print their recorded diagnostics: a
/// singular frame and a wrong declared inverse (C1, C2), arrays of two frames
/// and a change of frame between two objects (C3, C5), the Euclidean metric
/// under a length and a time (C17) and a scale of another kind (C19).
#[test]
fn rejected_stage4_packages_print_their_diagnostics() {
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
        common::assert_source_names(&expected);
    }
}
