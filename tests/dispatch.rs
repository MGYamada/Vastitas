//! Stage 1a source declarations must be independently resolved by the Lean kernel.
use serde_json::{Value, json};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static SERIAL: AtomicU64 = AtomicU64::new(0);

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "vastitas dispatch tests {} {}",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn source(&self, source: &str) -> PathBuf {
        let path = self.0.join("dispatch input.vast");
        fs::write(&path, source).unwrap();
        path
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn cli() -> Command {
    Command::new(env!("CARGO_BIN_EXE_vastitas"))
}

fn success(output: &Output) {
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn check(source: &str) -> Output {
    let scratch = Scratch::new();
    cli()
        .arg("check")
        .arg(scratch.source(source))
        .output()
        .unwrap()
}

fn reject(source: &str, code: &str) -> String {
    let output = check(source);
    assert!(
        !output.status.success(),
        "accepted invalid source: {source}"
    );
    let message = String::from_utf8(output.stderr).unwrap();
    assert!(
        message.contains(&format!(": {code}: ")),
        "expected {code}: {message}"
    );
    assert!(message.contains("dispatch input.vast:"));
    message
}

fn native(source: &str, libraries: &[PathBuf], expected: &str) {
    let scratch = Scratch::new();
    let output_path = scratch.0.join("dispatch program");
    let mut command = cli();
    command
        .arg("build")
        .arg(scratch.source(source))
        .arg("-o")
        .arg(&output_path);
    for library in libraries {
        command.arg("--lib").arg(library);
    }
    success(&command.output().unwrap());
    let output = Command::new(output_path).output().unwrap();
    success(&output);
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        format!("{expected}\n")
    );
}

fn request(source: &str) -> Value {
    serde_json::to_value(vastitas::frontend::parse(source, "forged-dispatch.vast").unwrap())
        .unwrap()
}

fn kernel(request: Value) -> Value {
    let executable = root().join("lean-kernel/.lake/build/bin/vastitas-kernel");
    assert!(executable.is_file(), "build the Lean kernel before tests");
    let mut child = Command::new(executable)
        .arg("emit")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let input = serde_json::to_vec(&request).unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let writer = std::thread::spawn(move || stdin.write_all(&input));
    let output = child.wait_with_output().unwrap();
    writer.join().unwrap().unwrap();
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "invalid kernel response: {error}; stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

fn assert_rejected(request: Value, code: &str) {
    let response = kernel(request);
    assert_eq!(response["version"], 2, "{response}");
    assert_eq!(response["ok"], false, "{response}");
    assert_eq!(response["diagnostics"][0]["code"], code, "{response}");
    assert!(response.get("lean_source").is_none(), "{response}");
}

#[test]
fn native_generic_arithmetic_uses_explicit_source_libraries() {
    let libraries = ["generic.vast", "nat.vast", "int.vast"]
        .map(|file| root().join("stdlib/src/arithmetic").join(file));
    native(
        include_str!("../examples/dispatch-arithmetic.vast"),
        &libraries,
        "42",
    );
}

#[test]
fn unused_specializations_are_checked_but_not_emitted() {
    let response = kernel(request(
        "generic wide(a,b,c,d,e,f) { domain; }
method wide(a: Any,b: Any,c: Any,d: Any,e: Any,f: Any) -> Int { 0 }
fn unused() -> Int { 7 }
fn main() -> Int { 42 }",
    ));
    assert_eq!(response["ok"], true, "{response}");
    let source = response["lean_source"].as_str().unwrap();
    assert_eq!(source.matches("\ndef f_").count(), 1);
    reject(
        "generic wide(x) { domain; }
method wide(x: Any) -> Int { x + 1 }
fn main() -> Int { 0 }",
        "E_TYPE",
    );
}

#[test]
fn specialization_cycles_use_readable_names() {
    let message = reject(
        "generic recursive(x) { domain (Int); }
method recursive(x: Int) -> Int { recursive(x) }",
        "E_RECURSION",
    );
    assert!(
        message.contains("recursive(Int) → recursive(Int)"),
        "{message}"
    );
    assert!(!message.contains("__vastitas_"), "{message}");
}

#[test]
fn native_dispatch_lowering_preserves_dependent_geometry_and_packages() {
    native(
        "generic scalar_dimension(n) { domain (Nat); }
method scalar_dimension(n: Nat) -> Int { int(n) }
fn make_ordinary(n: Nat) -> Pointed<Scheme, QQ> {
    let A = Affine(QQ, n);
    pack { scheme: A, point: origin(A) }
}
fn make_smooth(n: Nat) -> Pointed<CInfScheme, CInfReal> {
    let B = Affine(CInfReal, n);
    pack { scheme: B, point: origin(B) }
}
fn keep_ordinary(X: Scheme, p: Point<X, Base(QQ)>) -> Point<X, Base(QQ)> {
    apply(id(X), p)
}
fn keep_smooth(Y: CInfScheme, p: Point<Y, Base(CInfReal)>) -> Point<Y, Base(CInfReal)> {
    apply(compose(id(Y), id(Y)), p)
}
fn main() -> Int {
    unpack make_ordinary(3) as { scheme: X, point: p };
    let q: Point<X, Base(QQ)> = keep_ordinary(X, p);
    let ordinary = pack { scheme: X, point: apply(id(X), q) };
    unpack ordinary as { scheme: Z, point: r };
    let checked: Point<Z, Base(QQ)> = keep_ordinary(Z, r);
    unpack make_smooth(4) as { scheme: Y, point: s };
    let t: Point<Y, Base(CInfReal)> = keep_smooth(Y, s);
    scalar_dimension(dimension(Z)) + scalar_dimension(dimension(Y)) + 35
}",
        &[],
        "42",
    );
}

#[test]
fn library_method_diagnostics_keep_original_files_and_lines_after_lowering() {
    let scratch = Scratch::new();
    let application =
        scratch.source("generic broken(x) { domain (Int); }\nfn main() -> Int { broken(0) }");
    let library = scratch.0.join("method body.vast");
    fs::write(
        &library,
        "// library declaration\n\nmethod broken(x: Int) -> Int {\n    true\n}\n",
    )
    .unwrap();
    let output = cli()
        .arg("check")
        .arg(&application)
        .arg("--lib")
        .arg(&library)
        .output()
        .unwrap();
    assert!(!output.status.success());
    let message = String::from_utf8(output.stderr).unwrap();
    assert!(
        message.contains(&format!("{}:4:5: E_TYPE: ", library.display())),
        "{message}"
    );

    fs::write(
        &application,
        "generic cross(x) { domain (Int); }\nfn main() -> Int { cross(0) }",
    )
    .unwrap();
    let broad = scratch.0.join("broad method.vast");
    let ordered = scratch.0.join("ordered method.vast");
    fs::write(&broad, "// broad\nmethod cross(x: Number) -> Int { 1 }\n").unwrap();
    fs::write(
        &ordered,
        "// capability method\n\nmethod cross(x: Any) -> Int requires (HasOrder) { 2 }\n",
    )
    .unwrap();
    let output = cli()
        .arg("check")
        .arg(&application)
        .arg("--lib")
        .arg(&broad)
        .arg("--lib")
        .arg(&ordered)
        .output()
        .unwrap();
    assert!(!output.status.success());
    let message = String::from_utf8(output.stderr).unwrap();
    assert!(message.contains(": E_DISPATCH_AMBIGUOUS: "), "{message}");
    assert!(
        message.contains(&format!("{}:2:1: note: ", broad.display())),
        "{message}"
    );
    assert!(
        message.contains(&format!("{}:3:1: note: ", ordered.display())),
        "{message}"
    );
}

#[test]
fn native_nominal_and_capability_selection_is_declaration_order_independent() {
    let families = "generic choose(value) { domain (Int), (Nat), (Bool), (Unit); }
generic rank(value) { domain (Int), (Nat), (Bool), (Unit); }";
    let methods = [
        "method choose(x: Any) -> Int { 10 }",
        "method choose(x: Number) -> Int { 20 }",
        "method choose(x: Int) -> Int { 30 }",
        "method rank(x: Any) -> Int requires (HasEq) { 1 }",
        "method rank(x: Any) -> Int requires (HasOrder) { 2 }",
    ];
    let main = "fn main() -> Int {
    let n: Nat = 0;
    let selection = choose(0) == 30 && choose(n) == 20 && choose(true) == 10 && choose(()) == 10;
    let capabilities = rank(0) == 2 && rank(n) == 2 && rank(false) == 1 && rank(()) == 1;
    if selection && capabilities { 42 } else { -1 }
}";
    for ordered in [methods.to_vec(), methods.into_iter().rev().collect()] {
        native(
            &format!("{families}\n{}\n{main}", ordered.join("\n")),
            &[],
            "42",
        );
    }
}

#[test]
fn empty_families_and_zero_argument_domains_have_distinct_meanings() {
    native(
        "generic empty(x) { domain; }
generic constant() { domain (); }
method constant() -> Int { 42 }
fn main() -> Int { constant() }",
        &[],
        "42",
    );
    reject(
        "generic empty(x) { domain; }
method empty(x: Int) -> Int { 42 }
fn main() -> Int { empty(0) }",
        "E_DISPATCH_DOMAIN",
    );
    reject(
        "generic constant() { domain (); }
method constant() -> Int requires (HasEq) { 42 }",
        "E_CAPABILITY",
    );
}

#[test]
fn coverage_is_checked_without_call_sites() {
    reject(
        "generic missing(x) { domain (Int); }",
        "E_DISPATCH_COVERAGE",
    );
    reject(
        "generic partial(x) { domain (Int), (Nat); }
method partial(x: Int) -> Int { x }",
        "E_DISPATCH_COVERAGE",
    );
}

#[test]
fn ambiguity_outside_the_callable_domain_cannot_be_hidden() {
    let message = reject(
        "generic cross(x, y) { domain (Bool, Bool); }
method cross(x: Any, y: Any) -> Int { 0 }
method cross(x: Number, y: Any) -> Int { 1 }
method cross(x: Any, y: Number) -> Int { 2 }",
        "E_DISPATCH_AMBIGUOUS",
    );
    assert!(message.contains("cross"), "{message}");
}

#[test]
fn specificity_uses_the_product_order_not_current_inhabitants() {
    reject(
        "generic cross(x) { domain (Int), (Nat); }
method cross(x: Number) -> Int { 1 }
method cross(x: Any) -> Int requires (HasOrder) { 2 }",
        "E_DISPATCH_AMBIGUOUS",
    );
    let message = reject(
        "generic describe(x) { domain (Int), (Nat); }
method describe(x: Number) -> Int requires (HasOrder) { 1 }
method describe(x: Int) -> Int { 2 }",
        "E_DISPATCH_AMBIGUOUS",
    );
    for expected in [
        "describe(Number) requires (HasOrder)",
        "describe(Int)",
        "has narrower selectors",
        "does not require HasOrder",
        "has stronger requirements",
        "help: declare `describe(Int) requires (HasOrder)`",
    ] {
        assert!(message.contains(expected), "missing {expected}: {message}");
    }
}

#[test]
fn pairwise_repairs_do_not_discharge_a_triple_ambiguity() {
    reject(
        "generic triple(x, y, z) { domain (Int, Int, Int); }
method triple(x: Int, y: Any, z: Any) -> Int { 1 }
method triple(x: Any, y: Int, z: Any) -> Int { 2 }
method triple(x: Any, y: Any, z: Int) -> Int { 3 }
method triple(x: Int, y: Int, z: Any) -> Int { 4 }
method triple(x: Int, y: Any, z: Int) -> Int { 5 }
method triple(x: Any, y: Int, z: Int) -> Int { 6 }",
        "E_DISPATCH_AMBIGUOUS",
    );
}

#[test]
fn canonical_capability_duplicates_and_impossible_requirements_are_rejected() {
    reject(
        "generic duplicate(x) { domain (Int); }
method duplicate(x: Int) -> Int requires (HasOrder) { 1 }
method duplicate(x: Int) -> Int requires (HasEq, HasOrder) { 2 }",
        "E_DUPLICATE",
    );
    reject(
        "generic impossible(x) { domain (Bool); }
method impossible(x: Bool) -> Int requires (HasOrder) { 1 }",
        "E_CAPABILITY",
    );
    reject(
        "generic unknown(x) { domain (Int); }
method unknown(x: Int) -> Int requires (HasMetric) { 1 }",
        "E_CAPABILITY",
    );
}

#[test]
fn key_limit_applies_to_the_whole_universe_even_for_an_empty_domain() {
    success(&check(
        "generic boundary(p0, p1, p2, p3, p4, p5) { domain; }",
    ));
    reject(
        "generic excessive(p0, p1, p2, p3, p4, p5, p6) { domain; }",
        "E_LIMIT",
    );
}

#[test]
fn every_applicable_body_is_checked_including_nonwinners_and_unexported_keys() {
    reject(
        "generic hidden(x) { domain (Int), (Nat); }
method hidden(x: Number) -> Int { x }
method hidden(x: Int) -> Int { 1 }
method hidden(x: Nat) -> Int { 2 }",
        "E_TYPE",
    );
    reject(
        "generic hidden(x) { domain (Int); }
method hidden(x: Number) -> Int { x }
method hidden(x: Int) -> Int { 1 }",
        "E_TYPE",
    );
}

#[test]
fn expected_result_types_do_not_select_a_different_overload() {
    reject(
        "generic identity(x) { domain (Int), (Nat); }
method identity(x: Int) -> Int { x }
method identity(x: Nat) -> Nat { x }
fn main() -> Int { let n: Nat = identity(1); 0 }",
        "E_TYPE",
    );
    reject(
        "generic add(x, y) { domain (Int, Int), (Nat, Nat); }
method add(x: Int, y: Int) -> Int { x + y }
method add(x: Nat, y: Nat) -> Nat { x + y }
fn main() -> Int { let n: Nat = 1; add(n, 1) }",
        "E_DISPATCH_DOMAIN",
    );
}

#[test]
fn recursion_is_checked_after_concrete_method_selection() {
    reject(
        "generic recursive(x) { domain (Int); }
method recursive(x: Int) -> Int { recursive(x) }",
        "E_RECURSION",
    );
    native(
        "generic promote(x) { domain (Int), (Nat); }
method promote(x: Nat) -> Int { promote(int(x)) }
method promote(x: Int) -> Int { x + 1 }
fn main() -> Int { let n: Nat = 41; promote(n) }",
        &[],
        "42",
    );
}

#[test]
fn forged_protocol_capabilities_and_candidate_hints_cannot_bypass_the_kernel() {
    let valid = request(
        "generic pick(x) { domain (Bool); }
method pick(x: Bool) -> Int requires (HasEq) { 42 }
fn main() -> Int { pick(true) }",
    );
    assert_eq!(kernel(valid.clone())["ok"], true);
    let mut old_protocol = valid.clone();
    old_protocol["version"] = json!(1);
    assert_rejected(old_protocol, "E_PROTOCOL");

    let mut forged_facts = valid;
    forged_facts["methods"][0]["requires"] = json!(["HasOrder"]);
    forged_facts["capabilities"] = json!({"Bool": ["HasEq", "HasOrder"]});
    forged_facts["generics"][0]["available_capabilities"] = json!(["HasOrder"]);
    forged_facts["methods"][0]["capability_evidence"] = json!({"HasOrder": true});
    assert_rejected(forged_facts, "E_CAPABILITY");

    let mut ambiguous = request(
        "generic cross(x) { domain (Int); }
method cross(x: Number) -> Int { 1 }
method cross(x: Any) -> Int requires (HasOrder) { 2 }
fn main() -> Int { cross(0) }",
    );
    ambiguous["generics"][0]["selected_method"] = json!(0);
    ambiguous["functions"][0]["body"]["result"]["candidate"] = json!(0);
    ambiguous["dispatch_certificate"] = json!({"coherent": true, "covered": true});
    assert_rejected(ambiguous, "E_DISPATCH_AMBIGUOUS");
}

#[test]
fn forged_private_names_and_dispatch_types_are_independently_rejected() {
    let valid = request(
        "generic pick(x) { domain (Int); }
method pick(x: Int) -> Int { x }
fn main() -> Int { pick(42) }",
    );
    let mut private_call = valid.clone();
    private_call["functions"][0]["body"]["result"]["callee"] = json!("__vastitas_method_0_0");
    assert_rejected(private_call, "E_RESERVED");
    let mut private_binding = valid.clone();
    private_binding["methods"][0]["params"][0]["name"] = json!("__vastitas_parameter");
    assert_rejected(private_binding, "E_RESERVED");
    let mut private_variable = valid.clone();
    private_variable["methods"][0]["body"]["result"]["name"] = json!("__vastitas_parameter");
    assert_rejected(private_variable, "E_RESERVED");

    let mut invalid_domain = valid.clone();
    invalid_domain["generics"][0]["domain"][0][0]["name"] = json!("Number");
    assert_rejected(invalid_domain, "E_TYPE");
    let mut invalid_selector = valid;
    invalid_selector["methods"][0]["params"][0]["ty"]["name"] = json!("Scheme");
    assert_rejected(invalid_selector, "E_TYPE");
}
