//! The frame primitives of Stage 4 (#759) through the public source path,
//! with the emit corpus program `tests/emit_corpus/frame-primitives`. The
//! frontend parses each form into the binding that the kernel decodes; these
//! tests capture the wire and submit it to the kernel, which checks the frame
//! bindings and runs the program.
mod common;
use common::{Scratch, assert_wire_rejected, cli, kernel, success};
use serde_json::{Value, json};

const MANIFEST: &str = include_str!("emit_corpus/frame-primitives/Vastitas.toml");
const MAIN: &str = include_str!("emit_corpus/frame-primitives/main.vast");

fn package() -> Scratch {
    let s = Scratch::empty("frame primitives");
    s.write("Vastitas.toml", MANIFEST);
    s.write("main.vast", MAIN);
    s
}

/// The wire that the frontend sends for the program.
fn request(s: &Scratch) -> Value {
    s.captured("Vastitas.toml", common::CURRENT_PROTOCOL)
}

/// JSON pointer to the binding of the named primitive declaration.
fn binding_pointer(raw: &Value, name: &str) -> String {
    let [module] = raw["packages"][0]["modules"].as_array().unwrap().as_slice() else {
        panic!("one module expected");
    };
    let index = module["indexed_declarations"]
        .as_array()
        .unwrap()
        .iter()
        .position(|d| d["name"] == name)
        .unwrap_or_else(|| panic!("no declaration {name}"));
    assert_eq!(
        module["indexed_declarations"][index]["kind"], "primitive",
        "{name}"
    );
    format!("/packages/0/modules/0/indexed_declarations/{index}/binding")
}

/// The program declares every frame primitive, and the kernel accepts it.
#[test]
fn frame_primitives_decode_and_the_kernel_accepts_them() {
    let raw = request(&package());
    let frame_ops: Vec<&str> = vastitas::indexed::primitive_families()
        .iter()
        .map(|family| family.op)
        .filter(|op| op.starts_with("frame_"))
        .collect();
    let declared: Vec<&str> = raw["packages"][0]["modules"][0]["indexed_declarations"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|d| d["kind"] == "primitive")
        .filter_map(|d| d["binding"]["op"].as_str())
        .collect();
    for op in &frame_ops {
        assert!(declared.contains(op), "the program declares no {op}");
    }
    let response = kernel(&raw, "check");
    assert_eq!(response["ok"], true, "{response}");
}

/// A natural field is an unsigned decimal string of at most 64 digits on the
/// wire, and every field of a frame binding is required: anything else is a
/// protocol error of the kernel's decoder, whatever the frontend would send.
#[test]
fn raw_wire_rejects_forged_frame_bindings() {
    let raw = request(&package());
    let first = binding_pointer(&raw, "first");
    let entry = binding_pointer(&raw, "entry_01");
    let encode = binding_pointer(&raw, "enc_b");
    let matrix = binding_pointer(&raw, "matrix_bl");
    assert_eq!(raw.pointer(&format!("{first}/index")).unwrap(), "0");
    assert_eq!(raw.pointer(&format!("{entry}/row")).unwrap(), "0");
    assert_eq!(raw.pointer(&format!("{entry}/column")).unwrap(), "1");
    let forged = |path: String, value: Value| {
        let mut changed = raw.clone();
        *changed.pointer_mut(&path).unwrap() = value;
        changed
    };
    for value in [
        json!(0),
        json!("-1"),
        json!("x"),
        json!("1.5"),
        json!(""),
        json!("9".repeat(65)),
        json!(null),
    ] {
        for path in [
            format!("{first}/index"),
            format!("{entry}/row"),
            format!("{entry}/column"),
        ] {
            assert_wire_rejected(&kernel(forged(path, value.clone()), "emit"), "E_PROTOCOL");
        }
    }
    for (binding, field) in [
        (&encode, "frame"),
        (&matrix, "source"),
        (&matrix, "target"),
        (&first, "index"),
        (&entry, "column"),
    ] {
        let mut missing = raw.clone();
        missing
            .pointer_mut(binding)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .remove(field)
            .unwrap_or_else(|| panic!("no field {field}"));
        assert_wire_rejected(&kernel(missing, "emit"), "E_PROTOCOL");
    }
}

/// Once the kernel checks the frame bindings, the program checks, builds and
/// exits with 42 (#836): each observation of `main` adds its own power of two.
/// The name is cited by docs/spec/std-geometry-frame.toml.
#[test]
fn frame_program_checks_builds_and_exits_with_42() {
    let s = package();
    success(
        &cli()
            .current_dir(&s.0)
            .args(["check", "--manifest-path", "Vastitas.toml"])
            .output()
            .unwrap(),
    );
    let output = s.0.join("program");
    success(
        &cli()
            .current_dir(&s.0)
            .args(["build", "--manifest-path", "Vastitas.toml", "-o"])
            .arg(&output)
            .output()
            .unwrap(),
    );
    let result = std::process::Command::new(output).output().unwrap();
    assert_eq!(common::ran(&result), common::exits(42));
}
