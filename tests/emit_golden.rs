//! The Lean source that the kernel emits for representative packages is
//! pinned byte for byte. A codegen change is intentional only when a fixture
//! is regenerated with `VASTITAS_UPDATE_EMIT_FIXTURES=1 cargo test --test
//! emit_golden` and its diff is reviewed. `scripts/capture_emit.py` does the
//! same for every example without storing the output in the repository.
mod common;
use common::{captured_wire, kernel, regenerate_fixture, root};
use serde_json::Value;
use std::collections::BTreeSet;
use std::fs;

/// One fixture per codegen profile: the Stage 1 example and the corpus copy
/// whose entry point also calls the global object and a composite (indexed,
/// indexed-calls), Stage 2 relative maps, coefficients, points, pairs,
/// isomorphisms and Cartesian squares (affine-geometry), `relative_view` (the
/// emit corpus), smooth maps and their equality (smooth-objects), fibers,
/// tapes and pullbacks (smooth-cotangent), metrics with `flat` and `sharp`
/// (smooth-metric), and the standard-library differential profile
/// (stdlib-differential). The generated backward functions of compiled
/// reverse Core (#623) are pinned for the Stage 3 acceptance program
/// (smooth-differential), for maps that a branch chooses (reverse-branch) and
/// for a tape bound by `let` or passed to a function (reverse-tape).
const CASES: &[(&str, &str, u64)] = &[
    ("indexed", "examples/packages/indexed/Vastitas.toml", 7),
    (
        "indexed-calls",
        "tests/emit_corpus/indexed-calls/Vastitas.toml",
        7,
    ),
    (
        "affine-geometry",
        "examples/packages/affine-geometry/Vastitas.toml",
        9,
    ),
    (
        "relative-view",
        "tests/emit_corpus/relative-view/Vastitas.toml",
        9,
    ),
    (
        "smooth-objects",
        "examples/packages/smooth-objects/Vastitas.toml",
        9,
    ),
    (
        "smooth-cotangent",
        "examples/packages/smooth-cotangent/Vastitas.toml",
        9,
    ),
    (
        "smooth-metric",
        "examples/packages/smooth-metric/Vastitas.toml",
        9,
    ),
    (
        "stdlib-differential",
        "examples/packages/stdlib-differential/Vastitas.toml",
        9,
    ),
    (
        "smooth-differential",
        "examples/packages/smooth-differential/Vastitas.toml",
        9,
    ),
    (
        "reverse-branch",
        "tests/emit_corpus/reverse-branch/Vastitas.toml",
        9,
    ),
    (
        "reverse-tape",
        "tests/emit_corpus/reverse-tape/Vastitas.toml",
        9,
    ),
    (
        "reverse-domain",
        "tests/emit_corpus/reverse-domain/Vastitas.toml",
        9,
    ),
];

/// The frame primitives of Stage 4 (#759) in one program: arrays of vectors
/// and covectors in a constant and a polynomial frame, the matrices of a
/// smooth map in two pairs of frames, a transition, contraction in frames and
/// the observations (frame-primitives). `frame_lean_matches_the_emit_fixtures`
/// checks them, apart from `CASES`.
const FRAME_CASES: &[(&str, &str, u64)] = &[(
    "frame-primitives",
    "tests/emit_corpus/frame-primitives/Vastitas.toml",
    9,
)];

/// Every wire operation of an indexed primitive declaration (docs/protocol.md)
/// with the text its lowering writes (`renderPrimitive` in
/// `lean-kernel/VastitasKernel/IndexedCodegen.lean`), or `None` for
/// `relative_view`, whose lowering is its operand. A global object is bound by
/// `let` in the corpus, which separates it from the base-object argument that
/// `origin` renders. The test checks that the list names each family of
/// `vastitas::indexed::primitive_families()` once. The kernel compiles every
/// reverse pass that it can read into Core (#623), so `cotangent_pullback`
/// and `differential` have a text of that Core: the Jacobian step along a
/// declared map, and the forward image at which a differential's unit
/// covector lies. Every compiled pass writes these texts, so
/// `tests/reverse_core.rs` checks the compiled Core of each operation.
/// `linearize` and `cotangent_backward` keep their own lowering where a
/// function receives the tape (reverse-tape).
const WIRE_OPERATIONS: &[(&str, Option<&str>)] = &[
    (
        "descriptor",
        Some("VastitasKernel.IndexedRuntime.descriptor "),
    ),
    (
        "global",
        Some(":= VastitasKernel.IndexedRuntime.baseObject;"),
    ),
    ("origin", Some("VastitasKernel.IndexedRuntime.origin ")),
    ("identity", Some("VastitasKernel.IndexedRuntime.identity ")),
    ("dimension", Some(").dimension")),
    ("compose", Some("VastitasKernel.IndexedRuntime.compose ")),
    ("apply", Some("VastitasKernel.IndexedRuntime.apply ")),
    (
        "relative_compose",
        Some("VastitasKernel.AlgebraRuntime.Map.compose "),
    ),
    ("relative_view", None),
    (
        "relative_equal",
        Some("VastitasKernel.AlgebraRuntime.Map.same "),
    ),
    (
        "relative_coefficient",
        Some("VastitasKernel.AlgebraRuntime.Map.coefficient "),
    ),
    (
        "relative_int_point",
        Some("VastitasKernel.AlgebraRuntime.Map.intPoint "),
    ),
    (
        "relative_pair",
        Some("VastitasKernel.AlgebraRuntime.Map.pair "),
    ),
    (
        "smooth_compose",
        Some("VastitasKernel.SmoothRuntime.Program.compose "),
    ),
    ("smooth_equal", Some("VastitasKernel.SmoothRuntime.same ")),
    (
        "smooth_composite",
        Some("VastitasKernel.SmoothRuntime.composite "),
    ),
    (
        "smooth_int_point",
        Some("VastitasKernel.SmoothRuntime.intPoint "),
    ),
    ("fiber_vector", Some("VastitasKernel.SmoothRuntime.vector ")),
    ("fiber_at", Some("VastitasKernel.SmoothRuntime.fiberAt ")),
    (
        "fiber_equal",
        Some("VastitasKernel.SmoothRuntime.fiberEqual "),
    ),
    (
        "fiber_component",
        Some("VastitasKernel.SmoothRuntime.component "),
    ),
    (
        "fiber_pairing",
        Some("VastitasKernel.SmoothRuntime.pairing "),
    ),
    (
        "cotangent_pullback",
        Some("VastitasKernel.SmoothRuntime.jacobianStep "),
    ),
    (
        "differential",
        Some("VastitasKernel.SmoothRuntime.applyPoint "),
    ),
    ("linearize", Some("VastitasKernel.SmoothRuntime.linearize ")),
    (
        "cotangent_backward",
        Some("VastitasKernel.SmoothRuntime.backward "),
    ),
    ("flat", Some("VastitasKernel.SmoothRuntime.flat ")),
    ("sharp", Some("VastitasKernel.SmoothRuntime.sharp ")),
    // Arrays in a frame are fibers of the smooth runtime, so the frame
    // profile reads them with its vector, component, pairing and point test,
    // and these witnesses are shared with the smooth ops: the bytes of
    // tests/fixtures/emit/frame-primitives.lean pin which op lowers them.
    // `frame_encode` and `frame_decode` are witnessed by their tangent
    // lowering, and `frame_equal` by the equality of frame matrices.
    (
        "frame_encode",
        Some("VastitasKernel.FrameRuntime.encodeTangent "),
    ),
    (
        "frame_decode",
        Some("VastitasKernel.FrameRuntime.decodeTangent "),
    ),
    ("frame_vector", Some("VastitasKernel.SmoothRuntime.vector ")),
    (
        "frame_matrix",
        Some("VastitasKernel.FrameRuntime.frameMatrix "),
    ),
    (
        "frame_transition",
        Some("VastitasKernel.FrameRuntime.transition "),
    ),
    ("frame_apply", Some("VastitasKernel.FrameRuntime.apply ")),
    (
        "frame_coapply",
        Some("VastitasKernel.FrameRuntime.coapply "),
    ),
    (
        "frame_compose",
        Some("VastitasKernel.FrameRuntime.compose "),
    ),
    (
        "frame_pairing",
        Some("VastitasKernel.SmoothRuntime.pairing "),
    ),
    (
        "frame_component",
        Some("VastitasKernel.SmoothRuntime.component "),
    ),
    ("frame_entry", Some("VastitasKernel.FrameRuntime.entry ")),
    (
        "frame_equal",
        Some("VastitasKernel.FrameRuntime.matrixEqual "),
    ),
    ("frame_at", Some("VastitasKernel.SmoothRuntime.fiberAt ")),
];

/// The `op` of every `primitive` declaration anywhere in a wire request.
fn primitive_operations(value: &Value, found: &mut BTreeSet<String>) {
    match value {
        Value::Object(fields) => {
            if fields.get("kind") == Some(&Value::String("primitive".into()))
                && let Some(op) = fields.get("binding").and_then(|b| b["op"].as_str())
            {
                found.insert(op.to_owned());
            }
            fields
                .values()
                .for_each(|child| primitive_operations(child, found));
        }
        Value::Array(items) => items
            .iter()
            .for_each(|child| primitive_operations(child, found)),
        _ => {}
    }
}

/// The first byte where two texts differ, with its position and a window of
/// each side, for a readable failure on the single-line function bodies.
fn first_difference(expected: &str, actual: &str) -> String {
    let (e, a) = (expected.as_bytes(), actual.as_bytes());
    let index = e
        .iter()
        .zip(a)
        .position(|(x, y)| x != y)
        .unwrap_or(e.len().min(a.len()));
    let line = e[..index].iter().filter(|&&byte| byte == b'\n').count() + 1;
    let column = index
        - e[..index]
            .iter()
            .rposition(|&byte| byte == b'\n')
            .map_or(0, |p| p + 1)
        + 1;
    let window = |bytes: &[u8]| {
        let start = index.saturating_sub(60);
        let end = (index + 60).min(bytes.len());
        String::from_utf8_lossy(&bytes[start..end]).into_owned()
    };
    format!(
        "byte {index} (line {line}, column {column}):\n  fixture: {:?}\n  actual:  {:?}",
        window(e),
        window(a)
    )
}

/// The wire request of a case, captured from `vastitas check`; it must use
/// protocol `version`.
fn request(manifest: &str, version: u64) -> Value {
    captured_wire(
        common::manifest_command("check", root().join(manifest)),
        version,
    )
}

/// Emits each case with the kernel and compares the generated Lean with its
/// fixture, which `VASTITAS_UPDATE_EMIT_FIXTURES=1` regenerates first. Adds
/// the primitive ops that the cases declare to `declared` and returns the
/// generated Lean of all cases.
fn emit_and_compare(cases: &[(&str, &str, u64)], declared: &mut BTreeSet<String>) -> String {
    let regenerate = regenerate_fixture("VASTITAS_UPDATE_EMIT_FIXTURES");
    let mut sources = String::new();
    let mut failures = Vec::new();
    for (name, manifest, version) in cases {
        let wire = request(manifest, *version);
        primitive_operations(&wire, declared);
        let response = kernel(&wire, "emit");
        assert_eq!(response["ok"], true, "{name}: {response}");
        let actual = response["lean_source"]
            .as_str()
            .unwrap_or_else(|| panic!("{name}: no lean_source in {response}"));
        sources.push_str(actual);
        let path = root().join(format!("tests/fixtures/emit/{name}.lean"));
        if regenerate {
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(&path, actual).unwrap();
        }
        let expected = fs::read_to_string(&path)
            .unwrap_or_else(|_| panic!("{name}: regenerate the emit fixtures as documented"));
        if actual != expected {
            failures.push(format!(
                "{name}: generated Lean differs from tests/fixtures/emit/{name}.lean at {}",
                first_difference(&expected, actual)
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    sources
}

/// For each op in `declared` except `relative_view`, the generated Lean
/// `sources` contains the op's lowering text (its witness). The lowering of
/// `relative_view` is its operand, so it has no witness: only the bytes of
/// tests/fixtures/emit/relative-view.lean pin it.
fn assert_witnessed(declared: &BTreeSet<String>, sources: &str) {
    for (op, witness) in WIRE_OPERATIONS {
        if let Some(witness) = witness
            && declared.contains(*op)
        {
            assert!(
                sources.contains(witness),
                "no emit fixture lowers {op}: {witness:?} is absent from the generated Lean"
            );
        }
    }
}

#[test]
fn generated_lean_matches_the_emit_fixtures() {
    common::prepare_stdlib_package();
    let mut declared = BTreeSet::new();
    let sources = emit_and_compare(CASES, &mut declared);
    // `WIRE_OPERATIONS` names each family of the generated table once, so a
    // family added to the table without an entry here fails this assertion,
    // and the declaration assertion below then requires a fixture for it.
    let mut listed: Vec<&str> = WIRE_OPERATIONS.iter().map(|(op, _)| *op).collect();
    let mut families: Vec<&str> = vastitas::indexed::primitive_families()
        .iter()
        .map(|family| family.op)
        .collect();
    listed.sort_unstable();
    families.sort_unstable();
    assert_eq!(
        listed, families,
        "WIRE_OPERATIONS must name each family of the primitive table once"
    );
    // The cases together declare every wire primitive, and each case lowers
    // its primitives from an entry point. The declarations are read from the
    // wire that the frontend sends, so the frame cases count here although
    // the frame test checks their generated Lean. Each op that `CASES`
    // declare has its witness in their generated Lean; the frame test checks
    // the witnesses of the ops that the frame cases declare.
    let mut all = declared.clone();
    for (_, manifest, version) in FRAME_CASES {
        primitive_operations(&request(manifest, *version), &mut all);
    }
    let expected: BTreeSet<String> = WIRE_OPERATIONS
        .iter()
        .map(|(op, _)| (*op).to_owned())
        .collect();
    assert_eq!(
        all, expected,
        "the emit fixtures must declare every wire operation"
    );
    assert_witnessed(&declared, &sources);
}

/// The generated Lean of the frame cases, and the witnesses of every op that
/// they declare. With `generated_lean_matches_the_emit_fixtures`, every wire
/// operation is lowered by some fixture.
#[test]
fn frame_lean_matches_the_emit_fixtures() {
    common::prepare_stdlib_package();
    let mut declared = BTreeSet::new();
    let sources = emit_and_compare(FRAME_CASES, &mut declared);
    let frame_ops: Vec<&str> = vastitas::indexed::primitive_families()
        .iter()
        .map(|family| family.op)
        .filter(|op| op.starts_with("frame_"))
        .collect();
    assert_eq!(frame_ops.len(), 13);
    for op in frame_ops {
        assert!(declared.contains(op), "no frame case declares {op}");
    }
    assert_witnessed(&declared, &sources);
}
