//! Compiled reverse Core (#623). After acceptance, the kernel compiles every
//! reverse site — a pullback in either mode, a differential, or the reverse
//! pass of a tape that `linearize` builds — into Core: forward Core at the
//! site, and one generated backward function per site, placed first in the
//! module. A declared map is pulled back by its Jacobian table; a map value
//! whose structure the compilation does not open (a function parameter, a
//! composite, a branch) by the runtime reverse pass with saved forward values.
//! These tests pin that shape for the Stage 3 acceptance program, check that
//! the wire cannot name the compiler's declarations, and run the corpus
//! packages where a branch chooses the map and where a tape is bound by `let`
//! or passed to a function. `tests/emit_golden.rs` pins the same programs
//! byte for byte; `tests/smooth_differential.rs` runs the acceptance program
//! with its mutations.
mod common;
use common::{
    Scratch, assert_wire_rejected, captured_wire, checked_replace, cli,
    generated_reverse_functions, kernel, lean_definitions, lean_function_id, regenerate_fixture,
    root, success,
};
use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::path::Path;
use std::process::Command;

const ACCEPTANCE: &str = "examples/packages/smooth-differential/Vastitas.toml";
const BRANCH_MANIFEST: &str = include_str!("emit_corpus/reverse-branch/Vastitas.toml");
const BRANCH_MAIN: &str = include_str!("emit_corpus/reverse-branch/main.vast");
const TAPE_MANIFEST: &str = include_str!("emit_corpus/reverse-tape/Vastitas.toml");
const TAPE_MAIN: &str = include_str!("emit_corpus/reverse-tape/main.vast");
const DOMAIN_MANIFEST: &str = include_str!("emit_corpus/reverse-domain/Vastitas.toml");
const DOMAIN_MAIN: &str = include_str!("emit_corpus/reverse-domain/main.vast");

/// The names under which these programs call the reverse passes.
const REVERSE: &[&str] = &[
    "pullback",
    "pullback_recomputed",
    "differential",
    "backward",
];

/// The runtime reverse pass along a map value that the compilation does not open.
const REFERENCE: &str =
    "(VastitasKernel.SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.saved ";

/// The same at a recomputing site: an opaque step keeps the site's policy.
const RECOMPUTED_REFERENCE: &str =
    "(VastitasKernel.SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.recomputed ";

/// The wire request that `check` sends for a manifest.
fn wire(manifest: &Path) -> Value {
    let mut command = cli();
    command.args(["check", "--manifest-path"]).arg(manifest);
    captured_wire(command, 9)
}

/// The Lean source that the kernel emits for a wire request.
fn emitted(request: &Value) -> String {
    let response = kernel(request, "emit");
    assert_eq!(response["ok"], true, "{response}");
    response["lean_source"].as_str().unwrap().to_owned()
}

/// The functions of the root module, in wire order.
fn functions(request: &Value) -> &[Value] {
    request["packages"][0]["modules"][0]["functions"]
        .as_array()
        .unwrap()
}

/// The calls of any of `callees` in a wire value.
fn calls(value: &Value, callees: &[&str]) -> usize {
    match value {
        Value::Object(fields) => {
            let own = fields.get("kind") == Some(&json!("call"))
                && fields
                    .get("callee")
                    .and_then(Value::as_str)
                    .is_some_and(|callee| callees.contains(&callee));
            usize::from(own)
                + fields
                    .values()
                    .map(|child| calls(child, callees))
                    .sum::<usize>()
        }
        Value::Array(items) => items.iter().map(|child| calls(child, callees)).sum(),
        _ => 0,
    }
}

/// The calls of any of `callees` in the root module's functions.
fn function_calls(request: &Value, callees: &[&str]) -> usize {
    functions(request)
        .iter()
        .map(|function| calls(function, callees))
        .sum()
}

/// The reverse sites of the root module's functions.
fn sites(request: &Value) -> usize {
    function_calls(request, REVERSE)
}

/// The Lean definition of the source function `name`, which the kernel emits
/// as `f_<index>` for its position in the wire.
fn definition<'a>(source: &'a str, request: &Value, name: &str) -> &'a str {
    let index = functions(request)
        .iter()
        .position(|function| function["name"] == name)
        .unwrap();
    lean_definitions(source)
        .into_iter()
        .find(|(lean, _)| lean_function_id(lean) == Some(index))
        .unwrap_or_else(|| panic!("no definition of {name}:\n{source}"))
        .1
}

/// The Jacobian table of the step that starts `call`:
/// `(VastitasKernel.SmoothRuntime.jacobianStep <outputs> (<table>) …`.
fn jacobian_table(call: &str) -> &str {
    let rest = call
        .strip_prefix("(VastitasKernel.SmoothRuntime.jacobianStep ")
        .unwrap();
    let (outputs, table) = rest.split_once(' ').unwrap();
    assert!(
        !outputs.is_empty() && outputs.bytes().all(|byte| byte.is_ascii_digit()),
        "{call}"
    );
    assert!(table.starts_with('('), "{call}");
    let mut depth = 0;
    for (index, character) in table.char_indices() {
        match character {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return &table[..=index];
                }
            }
            _ => {}
        }
    }
    panic!("unbalanced Jacobian step: {call}")
}

fn package(manifest: &str, main: &str) -> Scratch {
    let s = Scratch::empty("reverse core");
    s.write("Vastitas.toml", manifest);
    s.write("main.vast", main);
    s
}

/// `check`, `build` and run a package; its standard output.
fn run(s: &Scratch) -> String {
    success(
        &cli()
            .current_dir(&s.0)
            .args(["check", "--manifest-path", "Vastitas.toml"])
            .output()
            .unwrap(),
    );
    let program = s.0.join("program");
    success(
        &cli()
            .current_dir(&s.0)
            .args(["build", "--manifest-path", "Vastitas.toml", "-o"])
            .arg(&program)
            .output()
            .unwrap(),
    );
    let output = Command::new(&program).output().unwrap();
    success(&output);
    String::from_utf8(output.stdout).unwrap()
}

#[test]
fn acceptance_sites_compile_to_generated_backward_functions() {
    let request = wire(&root().join(ACCEPTANCE));
    let source = emitted(&request);
    let count = functions(&request).len();
    // The 22 reverse calls of the acceptance program, and one generated
    // function for each, numbered after the source functions and placed first.
    let sites = sites(&request);
    assert_eq!(sites, 22);
    let generated = generated_reverse_functions(&source, count);
    let ids: Vec<usize> = generated
        .iter()
        .map(|(name, _)| lean_function_id(name).unwrap())
        .collect();
    assert_eq!(ids, (count..count + sites).collect::<Vec<_>>(), "{source}");
    // The function that holds a site calls its generated function once.
    for (name, _) in &generated {
        assert_eq!(
            source.matches(&format!("({name} ")).count(),
            1,
            "{name}\n{source}"
        );
    }
    let inside = |text: &str| -> usize {
        generated
            .iter()
            .map(|(_, body)| body.matches(text).count())
            .sum()
    };
    // Every Jacobian step lies in a generated function and carries its table
    // as a literal: rational polynomials, without a variable.
    let steps = source
        .matches("(VastitasKernel.SmoothRuntime.jacobianStep ")
        .count();
    assert!(steps > 0, "{source}");
    assert_eq!(
        inside("(VastitasKernel.SmoothRuntime.jacobianStep "),
        steps,
        "{source}"
    );
    for (at, _) in source.match_indices("(VastitasKernel.SmoothRuntime.jacobianStep ") {
        let table = jacobian_table(&source[at..]);
        assert!(
            table.ends_with(" : List (List VastitasKernel.AlgebraRuntime.Poly))"),
            "{table}"
        );
        assert!(!table.contains("v_"), "{table}");
    }
    // The only runtime reverse passes: the three gradient functions differentiate
    // their parameter h, and code 3 pulls back along composite(gAfterF). Each
    // is the whole body of its generated function, and the map it pulls back
    // along is the first argument of the call.
    assert_eq!(
        source.matches("SmoothRuntime.pullback ").count(),
        4,
        "{source}"
    );
    assert_eq!(inside(REFERENCE), 4, "{source}");
    let definitions = lean_definitions(&source);
    let mut callers = BTreeSet::new();
    for (name, body) in generated
        .iter()
        .filter(|(_, body)| body.contains(REFERENCE))
    {
        assert!(
            body.split_once(":=\n  ").unwrap().1.starts_with(REFERENCE),
            "{body}"
        );
        assert!(!body.contains("jacobianStep"), "{body}");
        let call = format!("({name} ");
        let (lean, text) = definitions
            .iter()
            .find(|(_, text)| text.contains(&call))
            .unwrap();
        let map = text[text.find(&call).unwrap() + call.len()..]
            .split(' ')
            .next()
            .unwrap();
        let caller = functions(&request)[lean_function_id(lean).unwrap()]["name"]
            .as_str()
            .unwrap();
        if caller == "main" {
            // The composite is bound before the site and passed as the map.
            assert!(
                text.contains(&format!(
                    "(let {map} := (VastitasKernel.SmoothRuntime.composite "
                )),
                "{text}"
            );
        } else {
            // The map is the gradient function's first parameter, h.
            assert!(
                text.starts_with(&format!(
                    "def {lean} ({map} : VastitasKernel.SmoothRuntime.Program) "
                )),
                "{text}"
            );
        }
        assert!(callers.insert(caller), "{caller}");
    }
    assert_eq!(
        callers,
        BTreeSet::from([
            "gradient_euclid",
            "gradient_lorentz",
            "gradient_skew",
            "main"
        ])
    );
    // The two recomputing passes (codes 12 and 25) evaluate the forward
    // images of their 2 and 3 steps in their generated function; the saved
    // ones receive the images from the caller.
    assert_eq!(
        generated
            .iter()
            .filter(|(_, body)| body.contains("SmoothRuntime.applyPoint "))
            .count(),
        function_calls(&request, &["pullback_recomputed"])
    );
    assert_eq!(inside("SmoothRuntime.applyPoint "), 5, "{source}");
    // Each differential (dg and the three gradients) passes the unit
    // covector at the image of its point, which the site evaluates, to its
    // generated function.
    let unit_seeds = source
        .match_indices("(VastitasKernel.SmoothRuntime.vector v_")
        .filter(|(at, _)| {
            let rest = &source[at + "(VastitasKernel.SmoothRuntime.vector ".len()..];
            let (point, rest) = rest.split_once(' ').unwrap();
            rest.starts_with("[(1 : Int)]); (f_")
                && source.contains(&format!(
                    "(let {point} := (VastitasKernel.SmoothRuntime.applyPoint "
                ))
        })
        .count();
    assert_eq!(unit_seeds, function_calls(&request, &["differential"]));
    assert_eq!(unit_seeds, 4);
    // No routine that the compiled Core replaces remains.
    for absent in [
        "SmoothRuntime.differential ",
        "SmoothRuntime.backward ",
        "SmoothRuntime.linearize ",
        "PullbackMode.recomputed",
    ] {
        assert!(!source.contains(absent), "{absent}\n{source}");
    }
}

#[test]
fn the_wire_cannot_name_the_compiled_declarations() {
    // After compilation, the first site (the inner pullback of `stepwise`,
    // along g) calls the declarations `__vastitas_rd0_0`, `__vastitas_rd0_1`
    // and its generated function, which the ledger names `__vastitas_rf0`.
    // The compilation runs after the check, so the wire can neither declare
    // nor call these names.
    let raw = wire(&root().join(ACCEPTANCE));
    let module = "/packages/0/modules/0";
    let declarations = raw
        .pointer(&format!("{module}/indexed_declarations"))
        .unwrap()
        .as_array()
        .unwrap();
    let declaration = |name: &str| declarations.iter().position(|d| d["name"] == name).unwrap();
    let function = |name: &str| {
        functions(&raw)
            .iter()
            .position(|f| f["name"] == name)
            .unwrap()
    };
    let renamed = |value: &Value, name: &str| {
        let mut value = value.clone();
        value["name"] = json!(name);
        value
    };
    let appended = |path: &str, value: Value| {
        let mut changed = raw.clone();
        changed
            .pointer_mut(path)
            .unwrap()
            .as_array_mut()
            .unwrap()
            .push(value);
        changed
    };
    let replaced = |path: &str, value: Value| {
        let mut changed = raw.clone();
        *changed.pointer_mut(path).unwrap() = value;
        changed
    };
    let stepwise = format!("{module}/functions/{}/body/result", function("stepwise"));
    assert_eq!(raw.pointer(&stepwise).unwrap()["callee"], "pullback");
    let verdict = format!("{module}/functions/{}", function("verdict"));
    let main = format!("{module}/functions/{}/body/result", function("main"));
    // `42 + verdict(…, 1) + … + verdict(…, 24)`: the last addition's right operand.
    assert_eq!(
        raw.pointer(&format!("{main}/right")).unwrap()["callee"],
        "verdict",
        "{}",
        raw.pointer(&main).unwrap()
    );
    let dline = &declarations[declaration("dline")];
    let sq = &declarations[declaration("sq")];
    let cases = [
        // A declaration, a morphism or a function under a compiler name.
        (
            appended(
                &format!("{module}/indexed_declarations"),
                renamed(dline, "__vastitas_rd0_0"),
            ),
            "E_RESERVED",
        ),
        (
            appended(
                &format!("{module}/indexed_declarations"),
                renamed(sq, "__vastitas_rd0_1"),
            ),
            "E_RESERVED",
        ),
        (
            appended(
                &format!("{module}/functions"),
                renamed(raw.pointer(&verdict).unwrap(), "__vastitas_rf0"),
            ),
            "E_RESERVED",
        ),
        // A call of a compiler name that nothing declares.
        (
            replaced(&format!("{stepwise}/callee"), json!("__vastitas_rd0_1")),
            "E_NAME",
        ),
        (
            replaced(&format!("{main}/right/callee"), json!("__vastitas_rf0")),
            "E_NAME",
        ),
        // The bindings of the compiled steps have no wire form.
        (
            replaced(
                &format!(
                    "{module}/indexed_declarations/{}/binding/op",
                    declaration("dline")
                ),
                json!("smooth_apply"),
            ),
            "E_PROTOCOL",
        ),
        (
            replaced(
                &format!(
                    "{module}/indexed_declarations/{}/binding/op",
                    declaration("dline")
                ),
                json!("cotangent_jacobian"),
            ),
            "E_PROTOCOL",
        ),
    ];
    for (request, code) in cases {
        assert_wire_rejected(&kernel(&request, "check"), code);
        assert_wire_rejected(&kernel(&request, "emit"), code);
    }
}

#[test]
fn a_branch_chooses_the_map_of_a_reverse_pass() {
    // Both branches are observed: g after f and h send 3 to 18 with
    // derivatives 12 and 6, and every observation has its own power of two.
    assert_eq!(run(&package(BRANCH_MANIFEST, BRANCH_MAIN)), "42\n");
    // h(t) = 5t + 3 has h(3) = 18 and derivative 5: the observations of the
    // else branch fail (2 + 8 + 32 + 128).
    let main = checked_replace(BRANCH_MAIN, "pullback(t -> 6*t)", "pullback(t -> 5*t + 3)");
    assert_eq!(run(&package(BRANCH_MANIFEST, &main)), "212\n");
    // g(x, y) = x + y + 6 has g(f(3)) = 18 and (g after f)'(3) = 7: the
    // observations of the then branch fail (1 + 4 + 16 + 64).
    let main = checked_replace(
        BRANCH_MAIN,
        "pullback(t -> x^2 + y)",
        "pullback(t -> x + y + 6)",
    );
    assert_eq!(run(&package(BRANCH_MANIFEST, &main)), "127\n");
    // Each of the four sites is compiled. The branch stays in the function
    // that holds the site and is one step, pulled back by the runtime reverse
    // pass in the site's policy; in `squared` the declared sq after it is a
    // Jacobian step.
    let request = wire(&root().join("tests/emit_corpus/reverse-branch/Vastitas.toml"));
    let source = emitted(&request);
    let generated = generated_reverse_functions(&source, functions(&request).len());
    assert_eq!(generated.len(), sites(&request), "{source}");
    assert_eq!(generated.len(), 4, "{source}");
    for (name, steps, reference) in [
        ("chosen", 0, REFERENCE),
        ("recomputed", 0, RECOMPUTED_REFERENCE),
        ("squared", 1, REFERENCE),
        ("slope", 0, REFERENCE),
    ] {
        let caller = definition(&source, &request, name);
        assert_eq!(caller.matches("(if ").count(), 1, "{name}: {caller}");
        let (generated, body) = generated
            .iter()
            .find(|(generated, _)| caller.contains(&format!("({generated} ")))
            .unwrap();
        assert_eq!(
            body.matches("SmoothRuntime.pullback ").count(),
            1,
            "{name} calls {generated}: {body}"
        );
        assert_eq!(
            body.matches(reference).count(),
            1,
            "{name} calls {generated}: {body}"
        );
        assert_eq!(
            body.matches("SmoothRuntime.jacobianStep ").count(),
            steps,
            "{name} calls {generated}: {body}"
        );
    }
    // The recomputing function reads no image of its one opaque step, so it
    // binds none: its body is the runtime reverse pass alone.
    let caller = definition(&source, &request, "recomputed");
    let (_, body) = generated
        .iter()
        .find(|(generated, _)| caller.contains(&format!("({generated} ")))
        .unwrap();
    assert!(
        body.split_once(":=\n  ")
            .unwrap()
            .1
            .starts_with(RECOMPUTED_REFERENCE),
        "{body}"
    );
    assert!(!source.contains("SmoothRuntime.differential "), "{source}");
}

#[test]
fn a_tape_bound_by_let_compiles_and_a_tape_passed_to_a_function_keeps_its_routine() {
    assert_eq!(run(&package(TAPE_MANIFEST, TAPE_MAIN)), "42\n");
    // g(x, y) = x + y + 6: (g after f)'(3) = 7. The compiled passes of the
    // let-bound tape and the pass in `through` both read the new map, so
    // codes 1, 2 and 8 fail, and the comparisons still hold.
    let main = checked_replace(
        TAPE_MAIN,
        "pullback(t -> x^2 + y)",
        "pullback(t -> x + y + 6)",
    );
    assert_eq!(run(&package(TAPE_MANIFEST, &main)), "53\n");
    // The four passes in `main` (three on the tape, one pullback) are
    // compiled; the tape's `let` stays, and `through` runs the Stage 3
    // routine on the tape it receives.
    let request = wire(&root().join("tests/emit_corpus/reverse-tape/Vastitas.toml"));
    let source = emitted(&request);
    let generated = generated_reverse_functions(&source, functions(&request).len());
    assert_eq!(sites(&request), 5);
    assert_eq!(generated.len(), 4, "{source}");
    let main = definition(&source, &request, "main");
    let through = definition(&source, &request, "through");
    for (name, _) in &generated {
        assert_eq!(main.matches(&format!("({name} ")).count(), 1, "{main}");
    }
    assert_eq!(source.matches("SmoothRuntime.linearize ").count(), 1);
    assert_eq!(
        main.matches("SmoothRuntime.linearize ").count(),
        1,
        "{main}"
    );
    assert_eq!(source.matches("SmoothRuntime.backward ").count(), 1);
    assert_eq!(
        through.matches("SmoothRuntime.backward ").count(),
        1,
        "{through}"
    );
    assert!(!source.contains("SmoothRuntime.pullback "), "{source}");
}

#[test]
fn a_reverse_pass_through_an_object_outside_the_cotangent_domain_keeps_the_runtime_pass() {
    // psi after phi passes through `Out`, which the cotangent family does not
    // cover; the two sites through it keep the runtime reverse pass, and the
    // site along `twice` is compiled.
    assert_eq!(run(&package(DOMAIN_MANIFEST, DOMAIN_MAIN)), "42\n");
    // phi(t) = t^3 makes psi after phi 3t^3, which is 24 at 2, so both
    // observations through `Out` fail (2 + 4).
    let main = checked_replace(DOMAIN_MAIN, "pullback(u -> t^2)", "pullback(u -> t^3)");
    assert_eq!(run(&package(DOMAIN_MANIFEST, &main)), "48\n");
    let request = wire(&root().join("tests/emit_corpus/reverse-domain/Vastitas.toml"));
    let source = emitted(&request);
    let generated = generated_reverse_functions(&source, functions(&request).len());
    assert_eq!(generated.len(), 1, "{source}");
    assert_eq!(
        source.matches("SmoothRuntime.jacobianStep ").count(),
        1,
        "{source}"
    );
    assert_eq!(source.matches(REFERENCE).count(), 1, "{source}");
    assert_eq!(
        source
            .matches("(VastitasKernel.SmoothRuntime.differential ")
            .count(),
        1,
        "{source}"
    );
}

/// The wire of the acceptance example, with the checkout root written as
/// `/vastitas`. `VastitasAlgebraTest.ReverseExampleRegression` runs it through
/// the protocol-9 checker and evaluates `main` before and after the compilation.
const EXAMPLE_WIRE: &str = "tests/fixtures/reverse-example.wire.json";

#[test]
fn the_acceptance_example_wire_fixture_is_current() {
    let request = wire(&root().join(ACCEPTANCE));
    let text = format!(
        "{}\n",
        serde_json::to_string_pretty(&request)
            .unwrap()
            .replace(root().to_str().unwrap(), "/vastitas")
    );
    let path = root().join(EXAMPLE_WIRE);
    if regenerate_fixture("VASTITAS_UPDATE_EMIT_FIXTURES") {
        std::fs::write(&path, &text).unwrap();
    }
    assert_eq!(
        std::fs::read_to_string(&path).unwrap(),
        text,
        "regenerate with VASTITAS_UPDATE_EMIT_FIXTURES=1 cargo test --test reverse_core"
    );
}
