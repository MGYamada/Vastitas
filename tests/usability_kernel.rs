use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use serde_json::{Value, json};

fn request(source: &str) -> Value {
    serde_json::to_value(vastitas::frontend::parse(source, "kernel-usability.vast").unwrap())
        .unwrap()
}

fn check(request: &Value) -> Value {
    let executable =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("lean-kernel/.lake/build/bin/vastitas-kernel");
    let mut child = Command::new(executable)
        .arg("check")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("build the Lean kernel before running integration tests");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(&serde_json::to_vec(request).unwrap())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    let response: Value = serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|error| panic!("invalid backend response: {error}; {:?}", output.stderr));
    assert_eq!(output.status.success(), response["ok"] == true);
    response
}

fn diagnostic(response: &Value, code: &str) -> Value {
    assert_eq!(response["ok"], false, "{response}");
    let diagnostics = response["diagnostics"].as_array().unwrap();
    assert_eq!(diagnostics.len(), 1, "{response}");
    let diagnostic = &diagnostics[0];
    assert_eq!(diagnostic["code"], code, "{response}");
    assert!(diagnostic["notes"].is_array(), "{response}");
    diagnostic.clone()
}

#[test]
fn forged_ir_cannot_bypass_the_natural_to_integer_contract() {
    let mut raw = request("fn convert(n: Nat) -> Int { 0 }");
    let span = raw["functions"][0]["body"]["result"]["span"].clone();
    raw["functions"][0]["body"]["result"] = json!({
        "kind": "call", "callee": "int", "span": span,
        "args": [{"kind": "variable", "name": "n", "span": span}],
    });
    assert_eq!(check(&raw)["ok"], true);

    raw["functions"][0]["params"][0]["ty"]["name"] = json!("Int");
    let d = diagnostic(&check(&raw), "E_TYPE");
    assert_eq!(d["message"], "expected Nat, found Int");
    assert_eq!(d["notes"], json!([]));

    raw["functions"][0]["body"]["result"]["args"] = json!([]);
    let d = diagnostic(&check(&raw), "E_ARITY");
    assert_eq!(d["message"], "int expects 1 argument, found 0");
    assert_eq!(d["span"], span);
}

#[test]
fn source_reserved_keywords_are_also_rejected_in_forged_ir() {
    for name in ["return", "while", "for", "loop", "mut", "int"] {
        let mut raw = request("fn harmless() -> Int { 0 }");
        raw["functions"][0]["name"] = json!(name);
        let d = diagnostic(&check(&raw), "E_NAME");
        assert!(d["message"].as_str().unwrap().contains("reserved"));
    }
}

#[test]
fn named_endpoint_notes_are_deduplicated_and_aliases_keep_identity() {
    let source = "fn main() -> Int {\n let X = Affine(QQ, 2);\n let Alias = X;\n let Y = Affine(QQ, 2);\n let p = apply(id(Alias), origin(Y));\n 0\n}";
    let d = diagnostic(&check(&request(source)), "E_ENDPOINT");
    let message = d["message"].as_str().unwrap();
    assert!(message.contains("Morphism<X, X>"), "{d}");
    assert!(message.contains("Point<Y, Base(QQ)>"), "{d}");
    assert!(!message.contains("Scheme#"), "{d}");
    let notes = d["notes"].as_array().unwrap();
    assert_eq!(notes.len(), 2, "{d}");
    assert_eq!(notes[0]["span"]["line"], 2);
    assert_eq!(notes[1]["span"]["line"], 4);
    assert!(
        notes
            .iter()
            .all(|note| note["message"].as_str().unwrap().contains("Affine"))
    );

    let source = source.replace("origin(Y)", "origin(X)");
    assert_eq!(check(&request(&source))["ok"], true);
}

#[test]
fn generative_constructions_keep_their_own_introduction_reason() {
    let examples = [
        (
            "fn create() -> Scheme { Affine(QQ, 2) }\nfn main() -> Int {\n let X = create();\n let Y = create();\n let p: Point<X, Base(QQ)> = origin(Y);\n 0\n}",
            "function call 'create'",
            3,
            4,
        ),
        (
            "fn main() -> Int {\n let X = Affine(QQ, 2);\n let package = pack { scheme: X, point: origin(X) };\n unpack package as { scheme: A, point: p };\n unpack package as { scheme: B, point: q };\n let r: Point<A, Base(QQ)> = q;\n 0\n}",
            "unpack",
            4,
            5,
        ),
        (
            "fn main() -> Int {\n let X = Affine(QQ, 2);\n let Y = Affine(QQ, 2);\n let Z = if true { X } else { Y };\n let p: Point<X, Base(QQ)> = origin(Z);\n 0\n}",
            "if merge of distinct objects",
            2,
            4,
        ),
    ];
    for (source, reason, first_line, second_line) in examples {
        let d = diagnostic(&check(&request(source)), "E_TYPE");
        let notes = d["notes"].as_array().unwrap();
        assert_eq!(notes.len(), 2, "{d}");
        assert_eq!(notes[0]["span"]["line"], first_line, "{d}");
        assert_eq!(notes[1]["span"]["line"], second_line, "{d}");
        assert!(
            notes
                .iter()
                .any(|note| note["message"].as_str().unwrap().contains(reason)),
            "{d}"
        );
    }
}

#[test]
fn anonymous_and_escaped_objects_have_source_locations() {
    let source = "fn main() -> Int {\n let p = origin(Affine(QQ, 2));\n let f = id(Affine(QQ, 2));\n let q = apply(f, p);\n 0\n}";
    let d = diagnostic(&check(&request(source)), "E_ENDPOINT");
    let message = d["message"].as_str().unwrap();
    assert!(message.contains("Scheme from Affine at 2:"), "{d}");
    assert!(message.contains("Scheme from Affine at 3:"), "{d}");
    assert!(!message.contains("Scheme#"), "{d}");
    assert_eq!(d["notes"].as_array().unwrap().len(), 2);

    let source =
        "fn main() -> Int {\n let p = {\n let Hidden = Affine(QQ, 2);\n origin(Hidden)\n };\n 0\n}";
    let d = diagnostic(&check(&request(source)), "E_ESCAPE");
    assert!(d["message"].as_str().unwrap().contains("Point<Hidden,"));
    let notes = d["notes"].as_array().unwrap();
    assert_eq!(notes.len(), 1);
    assert_eq!(notes[0]["span"]["line"], 3);
}

#[test]
fn dependent_parameter_notes_refer_to_the_parameter_declarations() {
    let source = "fn bad(X: Scheme, Y: Scheme) -> Point<X, Base(QQ)> { origin(Y) }";
    let d = diagnostic(&check(&request(source)), "E_TYPE");
    let notes = d["notes"].as_array().unwrap();
    assert_eq!(notes.len(), 2);
    for (note, name) in notes.iter().zip(["X", "Y"]) {
        assert!(note["message"].as_str().unwrap().contains("parameter"));
        assert_eq!(note["span"]["start"], source.find(name).unwrap());
    }
}
