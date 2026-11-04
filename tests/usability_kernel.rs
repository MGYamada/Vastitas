mod common;

use serde_json::{Value, json};

fn request(source: &str) -> Value {
    serde_json::to_value(vastitas::frontend::parse(source, "kernel-usability.vast").unwrap())
        .unwrap()
}

fn check(raw: &Value) -> Value {
    let response = common::kernel(raw, "check");
    assert_eq!(response["version"], raw["version"]);
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
fn checking_budget_diagnostic_does_not_depend_on_an_unrelated_generic() {
    let mut source = String::from("fn main() -> Int {\n");
    for i in 0..4095 {
        source.push_str(&format!("let x{i} = 1;\n"));
    }
    source.push_str("0\n}");
    let first = diagnostic(&check(&request(&source)), "E_LIMIT");
    source.push_str("\ngeneric unrelated() { domain; }");
    let second = diagnostic(&check(&request(&source)), "E_LIMIT");
    assert_eq!(first["message"], second["message"]);
    assert_eq!(first["span"], second["span"]);
    assert!(
        first["message"]
            .as_str()
            .unwrap()
            .contains("checking budget of 4096 units")
    );
}

#[test]
fn frontend_and_kernel_use_the_same_name_violation_codes() {
    let base = "fn f(x: Int) -> Int { let y = x; y }";
    for (source, field, name, code) in [
        (
            "fn f(x: Int) -> Int { let f = x; f }",
            "binder",
            "f",
            "E_SHADOW",
        ),
        (
            "fn f(x: Int) -> Int { let int = x; x }",
            "binder",
            "int",
            "E_RESERVED",
        ),
        (
            "fn f(x: Int) -> Int { let y = absent; y }",
            "value",
            "absent",
            "E_NAME",
        ),
    ] {
        assert_eq!(
            vastitas::frontend::parse(source, "source").unwrap_err()[0].code,
            code
        );
        let mut raw = request(base);
        if field == "binder" {
            raw["functions"][0]["body"]["statements"][0]["name"] = json!(name);
        } else {
            raw["functions"][0]["body"]["statements"][0]["value"]["name"] = json!(name);
        }
        diagnostic(&check(&raw), code);
    }
    let mut raw = request("generic present(x) { domain; } method present(x: Int) -> Int { x }");
    raw["methods"][0]["name"] = json!("missing");
    diagnostic(&check(&raw), "E_NAME");
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
        let d = diagnostic(&check(&raw), "E_RESERVED");
        assert!(d["message"].as_str().unwrap().contains("reserved"));
    }
}

#[test]
fn named_endpoint_notes_are_deduplicated_and_aliases_keep_identity() {
    let source = "fn main() -> Int {\n let X = Affine(QQ, 2);\n let Alias = X;\n let Y = Affine(QQ, 2);\n let p = apply(id(Alias), origin(Y));\n 0\n}";
    let d = diagnostic(&check(&request(source)), "E_ENDPOINT");
    assert_eq!(
        d["message"],
        "apply requires a point with target X (the map's source), but the supplied point has target Y",
        "{d}"
    );
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
    let notes = d["notes"].as_array().unwrap();
    assert_eq!(notes.len(), 3);
    assert!(
        notes[2]["message"]
            .as_str()
            .unwrap()
            .contains("bind the object once")
    );

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

fn explained(source: &str) -> Value {
    diagnostic(&check(&request(source)), "E_ENDPOINT")
}

#[test]
fn rejected_apply_names_the_point_target_and_the_map_source() {
    // The #602 reproduction: equal dimensions never identify X and Y.
    let source = "fn main() -> Int {\n    let X = Affine(QQ, 3);\n    let Y = Affine(QQ, 3);\n    let point_x = origin(X);\n    let crossed = apply(id(Y), point_x);\n    0\n}";
    let d = explained(source);
    assert_eq!(
        d["message"],
        "apply requires a point with target Y (the map's source), but the supplied point has target X",
        "{d}"
    );
    assert_eq!(d["span"]["line"], 5, "{d}");
    assert_eq!(d["span"]["column"], 19, "{d}");
    let notes = d["notes"].as_array().unwrap();
    assert_eq!(notes.len(), 2, "{d}");
    for (note, (name, line)) in notes.iter().zip([("Y", 3), ("X", 2)]) {
        assert_eq!(note["span"]["line"], line, "{d}");
        assert_eq!(
            note["message"],
            format!("object {name} was introduced here by Affine"),
            "{d}"
        );
    }
    assert_eq!(
        check(&request(&source.replace("id(Y)", "id(X)")))["ok"],
        true
    );
}

#[test]
fn rejected_compose_names_the_disagreeing_intermediate_endpoints() {
    let d = explained(
        "fn main() -> Int { let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let f = compose(id(X), id(Y)); 0 }",
    );
    assert_eq!(
        d["message"],
        "compose requires a second map with target X (the first map's source), but the supplied second map has target Y",
        "{d}"
    );
    assert_eq!(d["notes"].as_array().unwrap().len(), 2, "{d}");
    // Objects over different coefficient markers also name that difference.
    let d = explained(
        "fn main() -> Int { let X = Affine(QQ, 2); let Y = Affine(CInfReal, 2); let f = compose(id(X), id(Y)); 0 }",
    );
    assert_eq!(
        d["message"],
        "compose requires a second map with target X (the first map's source), but the supplied second map has target Y, whose coefficient marker CInfReal differs from QQ",
        "{d}"
    );
}

#[test]
fn family_failures_are_not_reported_as_endpoint_disagreements() {
    for (call, message, notes) in [
        (
            "apply(origin(X), origin(X))",
            "apply requires a map of family Morphism, but the supplied map has family Point",
            1,
        ),
        // Every check fails here; the first operand's family is reported first.
        (
            "apply(origin(X), id(Y))",
            "apply requires a map of family Morphism, but the supplied map has family Point",
            2,
        ),
        (
            "apply(id(X), id(Y))",
            "apply requires a point of family Point, but the supplied point has family Morphism",
            2,
        ),
        (
            "compose(id(X), origin(Y))",
            "compose requires a second map of family Morphism, but the supplied second map has family Point",
            2,
        ),
    ] {
        let d = explained(&format!(
            "fn main() -> Int {{ let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let p = {call}; 0 }}"
        ));
        assert_eq!(d["message"], message, "{d}");
        assert_eq!(d["notes"].as_array().unwrap().len(), notes, "{d}");
    }
}

#[test]
fn tampered_primitive_calls_remain_rejected_with_the_same_explanation() {
    let mut raw = request(
        "fn main() -> Int { let X = Affine(QQ, 2); let Y = Affine(QQ, 2); let p = apply(id(X), origin(X)); 0 }",
    );
    assert_eq!(check(&raw)["ok"], true);
    let call = "/functions/0/body/statements/2/value";
    let point = raw.pointer_mut(&format!("{call}/args/1/args/0")).unwrap();
    assert_eq!(point["name"], "X");
    point["name"] = json!("Y");
    let d = diagnostic(&check(&raw), "E_ENDPOINT");
    assert_eq!(
        d["message"],
        "apply requires a point with target X (the map's source), but the supplied point has target Y",
        "{d}"
    );
    raw.pointer_mut(call).unwrap()["callee"] = json!("compose");
    let d = diagnostic(&check(&raw), "E_ENDPOINT");
    assert_eq!(
        d["message"],
        "compose requires a second map of family Morphism, but the supplied second map has family Point",
        "{d}"
    );
}
