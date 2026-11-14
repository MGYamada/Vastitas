//! `std::geometry::frame` from a path package (Stage 4, #759; C3, C21). An
//! application that depends on a copy of the stdlib declares frames on its own
//! objects with the library's families, declares frame primitives that name
//! those frames, and observes their values natively. The tests also audit the
//! module's public names and its family contracts (ADR 0001 §11).
mod common;
use common::{Scratch, expect_code};
use serde_json::{Value, json};
use std::path::Path;

/// The plane with the constant frame b = columns((1, 0), (1, 2)), the frame
/// r = columns((1, 0), (x, 1)) polynomial in the point, with its declared
/// inverse, and the frame l = columns((2)) of the line. At p = (1, 2) the
/// array (1, 2) in r is the vector (3, 2), whose array in b is (2, 1), and
/// f(x, y) = x^2 + y has the differential (2, 1), whose array in b is (2, 4).
/// Each observation has its own failure code, so `main` prints 42 only when
/// all of them hold.
const MAIN: &str = r#"
use std::geometry::smooth::affine::SmoothR;
use std::geometry::smooth::affine::Smooth;
use std::geometry::smooth::affine::Tangent;
use std::geometry::smooth::affine::Cotangent;
use std::geometry::smooth::affine::Pt;
use std::geometry::smooth::affine::Line;
use std::geometry::smooth::affine::same_vector;
use std::geometry::smooth::affine::same_covector;
use std::geometry::frame::Frame;
use std::geometry::frame::Coords;
use std::geometry::frame::CoCoords;
use std::geometry::frame::FrameMap;
use std::differential::differential;

indexed affine Plane(SmoothR) = Affine(2)[x, y];
indexed frame b: Frame<Plane> = columns((1, 0), (1, 2));
indexed frame r: Frame<Plane> = columns((1, 0), (x, 1)) inverse = columns((1, 0), (-x, 1));
indexed frame l: Frame<Line> = columns((2));
indexed morphism f: Smooth<Plane, Line> = pullback(t -> x^2 + y);

indexed primitive plane_at = smooth_int_point(Smooth, Plane, Pt);
indexed primitive vplane = fiber_vector(Tangent, Smooth, Plane);
indexed primitive enc_b = frame_encode(Tangent, Coords, frame = b);
indexed primitive dec_b = frame_decode(Coords, Tangent, frame = b);
indexed primitive dec_r = frame_decode(Coords, Tangent, frame = r);
indexed primitive coenc_b = frame_encode(Cotangent, CoCoords, frame = b);
indexed primitive codec_b = frame_decode(CoCoords, Cotangent, frame = b);
indexed primitive vec_r = frame_vector(Coords, Smooth, frame = r);
indexed primitive matrix_bl = frame_matrix(Smooth, FrameMap, source = b, target = l);
indexed primitive matrix_rl = frame_matrix(Smooth, FrameMap, source = r, target = l);
indexed primitive move_rb = frame_transition(Smooth, FrameMap, source = r, target = b);
indexed primitive move_br = frame_transition(Smooth, FrameMap, source = b, target = r);
indexed primitive apply_map = frame_apply(FrameMap, Coords);
indexed primitive then = frame_compose(FrameMap);
indexed primitive pairing = frame_pairing(CoCoords, Coords);
indexed primitive first = frame_component(Coords, 0);
indexed primitive second = frame_component(Coords, 1);
indexed primitive entry_01 = frame_entry(FrameMap, 0, 1);
indexed primitive same_coords = frame_equal(Coords);
indexed primitive same_map = frame_equal(FrameMap);
indexed primitive over = frame_at(Coords, Smooth);

fn verdict(ok: Bool, code: Int) -> Int { if ok { 0 } else { code } }

// A component, entry or pairing reads n / d.
fn reads(value: Pair<Int>, n: Int, d: Int) -> Bool {
    pair_first(value) == n && pair_second(value) == d
}

fn main() -> Int {
    let p: Smooth<Pt, Plane> = plane_at(1, 2);
    let v: Tangent<Plane> = vplane(p, 3, 2);
    let w: Coords<b> = enc_b(v);
    let a: Coords<r> = vec_r(p, 1, 2);
    let dg: Cotangent<Plane> = differential(f(), p);
    let alpha: CoCoords<b> = coenc_b(dg);
    42 + verdict(reads(first(w), 2, 1) && reads(second(w), 1, 1) && over(w, p), 1)
       // Decoding after encoding, and encoding after decoding, are identities.
       + verdict(same_vector(dec_b(w), v) && same_coords(enc_b(dec_b(w)), w), 2)
       + verdict(same_covector(codec_b(alpha), dg), 3)
       // The array (1, 2) in r is v, and the transition from r to b takes it to w.
       + verdict(same_vector(dec_r(a), v) && same_coords(apply_map(move_rb(p), a), w), 4)
       // The transitions between r and b are inverse.
       + verdict(same_coords(apply_map(move_br(p), apply_map(move_rb(p), a)), a), 5)
       // dg(v) = 8 in the frame b.
       + verdict(reads(pairing(alpha, w), 8, 1), 6)
       // M_bl = (1, 2): one map array entry, and the change of frame from r.
       + verdict(reads(entry_01(matrix_bl(f(), p)), 2, 1), 7)
       + verdict(same_map(then(matrix_bl(f(), p), move_rb(p)), matrix_rl(f(), p)), 8)
}
"#;

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap()
}

/// The application `main` in `app/`, with a copy of the stdlib in `stdlib/`
/// as its `std` path dependency.
fn fixture(main: &str) -> Scratch {
    common::prepare_stdlib_package();
    let s = Scratch::empty("stdlib frames");
    let stdlib = common::root().join("stdlib");
    s.write("stdlib/Vastitas.toml", &read(&stdlib.join("Vastitas.toml")));
    let mut stack = ["target/package", "src/geometry", "src/differential"]
        .map(|d| stdlib.join(d))
        .to_vec();
    while let Some(directory) = stack.pop() {
        for entry in std::fs::read_dir(&directory).unwrap() {
            let path = entry.unwrap().path();
            let relative = path.strip_prefix(&stdlib).unwrap().to_str().unwrap();
            if path.is_dir() {
                stack.push(path.clone());
            } else if matches!(
                path.extension().and_then(|e| e.to_str()),
                Some("vast" | "toml")
            ) {
                s.write(&format!("stdlib/{relative}"), &read(&path));
            }
        }
    }
    s.write(
        "app/Vastitas.toml",
        "[package]\nname = \"stdlib_frames_demo\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n\n[dependencies]\nstd = { path = \"../stdlib\" }\n",
    );
    s.write("app/main.vast", main);
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
    expect_code(&check(&fixture(main)), code)
}

fn request(s: &Scratch) -> Value {
    s.captured("app/Vastitas.toml", 9)
}

/// The module of a package in the wire.
fn module<'a>(wire: &'a Value, package: &str, path: &[&str]) -> &'a Value {
    wire["packages"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["name"] == package)
        .unwrap_or_else(|| panic!("no package {package}"))["modules"]
        .as_array()
        .unwrap()
        .iter()
        .find(|m| m["path"] == json!(path))
        .unwrap_or_else(|| panic!("{package}: no module {path:?}"))
}

/// `value` without its source spans.
fn without_spans(value: &Value) -> Value {
    let mut value = value.clone();
    common::remove_spans(&mut value);
    value
}

#[test]
fn frames_from_the_library_check_build_and_run_from_a_path_package() {
    assert_eq!(run(&fixture(MAIN)), b"42\n");
}

/// Each observation can fail: a wrong component, a vector other than the
/// decoded one and an entry of another map array change the printed number
/// by their own codes, 1, 4 and 7.
#[test]
fn mutated_frame_observations_change_the_native_result() {
    let main = common::checked_replace(MAIN, "reads(first(w), 2, 1)", "reads(first(w), 3, 1)");
    let main = common::checked_replace(
        &main,
        "same_vector(dec_r(a), v)",
        "same_vector(dec_r(a), vplane(p, 1, 2))",
    );
    let main = common::checked_replace(
        &main,
        "reads(entry_01(matrix_bl(f(), p)), 2, 1)",
        "reads(entry_01(matrix_rl(f(), p)), 2, 1)",
    );
    // 42 + 1 + 4 + 7: the components of w are (2, 1); the array (1, 2) in r
    // is (3, 2), not (1, 2); M_rl = (1, 3/2).
    assert_eq!(run(&fixture(&main)), b"54\n");
}

/// The module exports exactly the four families, and nothing else (C21).
#[test]
fn frame_module_exports_exactly_its_four_families() {
    let wire = request(&fixture(MAIN));
    let frame = module(&wire, "vastitas_geometry", &["frame"]);
    let names: Vec<&str> = frame["indexed_declarations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|d| {
            assert_eq!(d["public"], true, "{d}");
            d["name"].as_str().unwrap()
        })
        .collect();
    assert_eq!(names, ["Frame", "Coords", "CoCoords", "FrameMap"]);
    for items in ["imports", "functions", "generics", "methods"] {
        assert_eq!(frame[items], json!([]), "{items}");
    }
    // The families and their contracts: a frame of a smooth affine object,
    // arrays of vectors and covectors in one frame, and maps between two.
    let declarations = without_spans(&frame["indexed_declarations"]);
    let frame_index = json!({ "kind": "frame", "family": { "path": ["Frame"] } });
    assert_eq!(
        declarations,
        json!([
            { "name": "Frame", "kind": "family", "public": true,
              "parameters": [{ "kind": "object",
                  "domain": { "path": ["super", "smooth", "affine", "CInfAffine"] } }],
              "constraints": [{ "kind": "canonical", "object": 0 }],
              "representation": "frame" },
            { "name": "Coords", "kind": "family", "public": true,
              "parameters": [frame_index], "constraints": [], "representation": "frame_vector" },
            { "name": "CoCoords", "kind": "family", "public": true,
              "parameters": [frame_index], "constraints": [], "representation": "frame_covector" },
            { "name": "FrameMap", "kind": "family", "public": true,
              "parameters": [frame_index, frame_index], "constraints": [],
              "representation": "frame_map" },
        ])
    );
    // The library declares no frame and no frame primitive: the application
    // declares them with their frames.
    for p in wire["packages"].as_array().unwrap() {
        if p["name"] == "stdlib_frames_demo" {
            continue;
        }
        for m in p["modules"].as_array().unwrap() {
            for d in m["indexed_declarations"].as_array().into_iter().flatten() {
                assert_ne!(d["kind"], "frame", "{d}");
                let op = d["binding"]["op"].as_str().unwrap_or("");
                assert!(!op.starts_with("frame_"), "{d}");
            }
        }
    }
    // No other name resolves in the module.
    for name in [
        "Basis",
        "Columns",
        "frame",
        "columns",
        "encode",
        "transition",
    ] {
        let stderr = rejects(
            &with(&format!("use std::geometry::frame::{name};")),
            "E_NAME",
        );
        assert!(
            stderr.contains(&format!("undefined name '{name}'")),
            "{stderr}"
        );
    }
}

/// A frame of an object outside `CInfAffine` is rejected (`E_FRAME`).
#[test]
fn a_frame_of_an_object_outside_cinf_affine_is_rejected() {
    let stderr = rejects(
        &with("indexed frame bad: Frame<std::geometry::smooth::BaseSmooth> = columns();"),
        "E_FRAME",
    );
    assert!(stderr.contains("BaseSmooth"), "{stderr}");
}

/// Arrays in two frames of one object are distinct types: comparing an array
/// in b with one in b2 is a static `E_ENDPOINT` that names both frames (C3).
#[test]
fn arrays_in_different_frames_of_one_object_are_rejected_statically() {
    let stderr = rejects(
        &with(concat!(
            "indexed frame b2: Frame<Plane> = columns((2, 0), (0, 1));\n",
            "indexed primitive enc_b2 = frame_encode(Tangent, Coords, frame = b2);\n",
            "fn bad(v: Tangent<Plane>) -> Bool { same_coords(enc_b(v), enc_b2(v)) }",
        )),
        "E_ENDPOINT",
    );
    assert!(
        stderr.contains("Coords<b>") && stderr.contains("Coords<b2>"),
        "{stderr}"
    );
}
