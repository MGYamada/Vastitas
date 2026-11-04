//! The Lean source that the kernel emits for representative packages is
//! pinned byte for byte. A codegen change is intentional only when a fixture
//! is regenerated with `VASTITAS_UPDATE_EMIT_FIXTURES=1 cargo test --test
//! emit_golden` and its diff is reviewed. `scripts/capture_emit.py` does the
//! same for every example without storing the output in the repository.
mod common;
use common::{captured_wire, cli, kernel, regenerate_fixture, root};
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
/// (stdlib-differential).
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
];

/// Every wire operation of an indexed primitive declaration (docs/protocol.md)
/// with the text its lowering writes (`renderPrimitive` in
/// `lean-kernel/VastitasKernel/IndexedCodegen.lean`), or `None` for
/// `relative_view`, whose lowering is its operand. A global object is bound by
/// `let` in the corpus, which separates it from the base-object argument that
/// `origin` renders.
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
        Some("VastitasKernel.SmoothRuntime.pullback "),
    ),
    (
        "differential",
        Some("VastitasKernel.SmoothRuntime.differential "),
    ),
    ("linearize", Some("VastitasKernel.SmoothRuntime.linearize ")),
    (
        "cotangent_backward",
        Some("VastitasKernel.SmoothRuntime.backward "),
    ),
    ("flat", Some("VastitasKernel.SmoothRuntime.flat ")),
    ("sharp", Some("VastitasKernel.SmoothRuntime.sharp ")),
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

#[test]
fn generated_lean_matches_the_emit_fixtures() {
    common::prepare_stdlib_package();
    let regenerate = regenerate_fixture("VASTITAS_UPDATE_EMIT_FIXTURES");
    let mut declared = BTreeSet::new();
    let mut sources = String::new();
    let mut failures = Vec::new();
    for (name, manifest, version) in CASES {
        let mut command = cli();
        command
            .args(["check", "--manifest-path"])
            .arg(root().join(manifest));
        let wire = captured_wire(command, *version);
        primitive_operations(&wire, &mut declared);
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
    // The fixtures together declare every wire primitive and lower each one
    // from an entry point, so a codegen change to any primitive shows up as a
    // fixture diff.
    let expected: BTreeSet<String> = WIRE_OPERATIONS
        .iter()
        .map(|(op, _)| (*op).to_owned())
        .collect();
    assert_eq!(
        declared, expected,
        "the emit fixtures must declare every wire operation"
    );
    for (op, witness) in WIRE_OPERATIONS {
        if let Some(witness) = witness {
            assert!(
                sources.contains(witness),
                "no emit fixture lowers {op}: {witness:?} is absent from the generated Lean"
            );
        }
    }
}
