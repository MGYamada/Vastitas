mod common;
use common::{Scratch, success};

const STORAGE: &str = "resource fn main() -> Int {
    allocate data: F64[1];
    borrow init = write(data, layout(0, 1, 1, 1, false));
    fill(init, f64(1));
    release(init);
    borrow reader = read(data, layout(0, 1, 1, 1, false));
    release(reader);
    drop(data);
    value { 42 }
}";

const NUMERICAL: &str = "mod profiles;
resource fn main() -> Int {
    space v = linear(profiles::RealSmooth, 2);
    space u = linear(profiles::RealSmooth, 2);
    basis bv = basis(v);
    basis bu = basis(u);
    basis bv2 = basis(v);
    allocate data: F64[4];
    allocate result: F64[4];
    borrow init = write(data, layout(0, 2, 2, 2, false));
    fill(init, f64(1));
    release(init);
    borrow input = read(data, layout(0, 2, 2, 2, false));
    borrow output = write(result, layout(0, 2, 2, 2, false));
    map left = view(input, bv, bv);
    map right = view(input, bv, bv);
    map destination = view(output, bv, bv);
    gemm(left, right, destination, overwrite, NativeFast);
    release(output);
    release(input);
    drop(data);
    drop(result);
    value { 42 }
}";

fn fixture(source: &str) -> Scratch {
    let scratch = Scratch::empty("resource diagnostics");
    scratch.write(
        "Vastitas.toml",
        "[package]\nname = \"diagnostics\"\nversion = \"0.1.0\"\nroot = \"src/main.vast\"\n",
    );
    scratch.write("src/main.vast", source);
    scratch.write(
        "src/profiles/mod.vast",
        include_str!("../examples/packages/numerical/src/profiles/mod.vast"),
    );
    scratch
}

fn run(scratch: &Scratch, mode: &str) -> std::process::Output {
    let mut command = common::manifest_command(mode, scratch.0.join("Vastitas.toml"));
    if mode == "build" {
        command.arg("-o").arg(scratch.0.join("rejected-output"));
    }
    command.output().unwrap()
}

fn location(file: &str, source: &str, marker: &str) -> String {
    let before = &source[..source.find(marker).unwrap()];
    let line = before.bytes().filter(|&byte| byte == b'\n').count() + 1;
    let column = before.rsplit('\n').next().unwrap().chars().count() + 1;
    format!("{file}:{line}:{column}")
}

fn assert_primary(message: &str, file: &str, source: &str, marker: &str, code: &str) {
    let expected = format!("{}: {code}: ", location(file, source, marker));
    assert!(
        message.lines().next().unwrap().contains(&expected),
        "{message}"
    );
}

fn assert_note(message: &str, file: &str, source: &str, marker: &str, note: &str) {
    let expected = format!("{}: note: {note}", location(file, source, marker));
    assert!(message.contains(&expected), "missing {expected}\n{message}");
}

fn rejection(scratch: &Scratch, mode: &str) -> String {
    let output = run(scratch, mode);
    assert!(
        !output.status.success(),
        "unexpected acceptance: {output:?}"
    );
    assert!(!scratch.0.join("rejected-output").exists());
    String::from_utf8(output.stderr).unwrap()
}

#[test]
fn storage_errors_locate_the_operation_and_name_the_actual_allocation_or_loan() {
    for (source, marker, code, notes) in [
        (
            STORAGE.replace("    fill(init, f64(1));\n", ""),
            "borrow reader",
            "E_RESOURCE_INIT",
            vec![(
                "allocate data",
                "borrowed allocation is `data`, introduced here",
            )],
        ),
        (
            STORAGE.replace("    release(reader);\n", ""),
            "drop(data)",
            "E_RESOURCE_LOAN",
            vec![
                (
                    "borrow reader",
                    "live loan preventing drop is `reader`, introduced here",
                ),
                (
                    "allocate data",
                    "allocation owner is `data`, introduced here",
                ),
            ],
        ),
        (
            STORAGE.replace(
                "    release(reader);",
                "    borrow writer = write(data, layout(0, 1, 1, 1, false));\n    release(reader);",
            ),
            "borrow writer",
            "E_RESOURCE_ALIAS",
            vec![
                (
                    "borrow reader",
                    "conflicting loan is `reader`, introduced here",
                ),
                (
                    "allocate data",
                    "borrowed allocation is `data`, introduced here",
                ),
            ],
        ),
    ] {
        // Source offsets remain correct with non-ASCII text before the body.
        let source = format!("// 日本語の診断位置\n{source}");
        let scratch = fixture(&source);
        for mode in ["check", "build"] {
            let message = rejection(&scratch, mode);
            assert_primary(&message, "main.vast", &source, marker, code);
            for (declaration, note) in &notes {
                assert_note(&message, "main.vast", &source, declaration, note);
            }
        }
    }
}

#[test]
fn nested_unselected_arms_and_failed_joins_keep_their_own_locations() {
    let source = "resource fn main() -> Int {
    allocate data: F64[1];
    if true {
        if true { } else {
            borrow missing = read(data, layout(0, 1, 1, 1, false));
            release(missing);
        }
    } else { }
    drop(data);
    value { 42 }
}";
    let message = rejection(&fixture(source), "check");
    assert_primary(
        &message,
        "main.vast",
        source,
        "borrow missing",
        "E_RESOURCE_INIT",
    );
    assert_note(
        &message,
        "main.vast",
        source,
        "allocate data",
        "borrowed allocation is `data`, introduced here",
    );

    let source = "resource fn main() -> Int {
    allocate data: F64[1];
    if true { drop(data); } else { }
    value { 42 }
}";
    let message = rejection(&fixture(source), "check");
    assert_primary(&message, "main.vast", source, "if true", "E_RESOURCE_JOIN");
}

#[test]
fn numerical_mismatches_name_distinct_objects_and_bases_of_equal_dimension() {
    success(&run(&fixture(NUMERICAL), "check"));
    for (source, notes) in [
        (
            NUMERICAL.replace(
                "map right = view(input, bv, bv);",
                "map right = view(input, bu, bu);",
            ),
            vec![
                ("basis bv =", "left source basis is `bv`, introduced here"),
                ("basis bu =", "right target basis is `bu`, introduced here"),
                ("space v =", "left source space is `v`, introduced here"),
                ("space u =", "right target space is `u`, introduced here"),
            ],
        ),
        (
            NUMERICAL.replace(
                "map destination = view(output, bv, bv);",
                "map destination = view(output, bv2, bv2);",
            ),
            vec![
                (
                    "basis bv2 =",
                    "output source basis is `bv2`, introduced here",
                ),
                ("basis bv =", "right source basis is `bv`, introduced here"),
            ],
        ),
    ] {
        let scratch = fixture(&source);
        for mode in ["check", "build"] {
            let message = rejection(&scratch, mode);
            assert_primary(
                &message,
                "main.vast",
                &source,
                "gemm(left",
                "E_NUMERICAL_TYPE",
            );
            for (declaration, note) in &notes {
                assert_note(&message, "main.vast", &source, declaration, note);
            }
        }
    }
}

#[test]
fn imported_callee_body_failure_keeps_the_call_trace_and_unused_body_location() {
    let source = "mod helper;\nresource fn main() -> Int {\n    call helper::broken() -> ();\n    value { 42 }\n}";
    let helper = "pub resource fn broken() -> Unit {\n    allocate hidden: F64[1];\n    borrow bad = read(hidden, layout(0, 1, 1, 1, false));\n    value { () }\n}";
    let scratch = fixture(source);
    scratch.write("src/helper/mod.vast", helper);
    let message = rejection(&scratch, "check");
    assert_primary(
        &message,
        "helper/mod.vast",
        helper,
        "borrow bad",
        "E_RESOURCE_INIT",
    );
    assert_note(
        &message,
        "main.vast",
        source,
        "call helper",
        "resource callee was invoked here",
    );
    assert_note(
        &message,
        "helper/mod.vast",
        helper,
        "allocate hidden",
        "borrowed allocation is `hidden`, introduced here",
    );

    let unused = source.replace("    call helper::broken() -> ();\n", "");
    scratch.write("src/main.vast", &unused);
    let message = rejection(&scratch, "check");
    assert_primary(
        &message,
        "helper/mod.vast",
        helper,
        "borrow bad",
        "E_RESOURCE_INIT",
    );
    assert!(
        !message.contains("resource callee was invoked here"),
        "{message}"
    );
}

#[test]
fn callee_input_contract_errors_point_at_the_actual_call() {
    let source = "resource fn main() -> Int {
    allocate data: F64[2];
    borrow init = write(data, layout(0, 2, 1, 2, false));
    fill(init, f64(1)); release(init);
    borrow input = read(data, layout(0, 2, 1, 2, false));
    call consume(input) -> ();
    release(input); drop(data);
    value { 42 }
}
resource fn consume(input: Read<F64, 1, 1>) -> Unit { value { () } }";
    let message = rejection(&fixture(source), "check");
    assert_primary(
        &message,
        "main.vast",
        source,
        "call consume",
        "E_RESOURCE_TYPE",
    );
    assert_note(
        &message,
        "main.vast",
        source,
        "borrow input",
        "call argument is `input`, introduced here",
    );
    assert_note(
        &message,
        "main.vast",
        source,
        "resource fn consume",
        "while checking resource function `consume`",
    );
}

#[test]
fn unreturned_owner_points_to_the_function_result() {
    let source =
        "resource fn main() -> Int {\n    allocate forgotten: F64[1];\n    value { 42 }\n}";
    let message = rejection(&fixture(source), "check");
    assert_primary(&message, "main.vast", source, "{ 42 }", "E_RESOURCE_ESCAPE");
}

#[test]
fn real_caller_layout_failure_names_the_callee_borrow_and_caller() {
    let source = "resource fn main() -> Int {
    allocate data: F64[8];
    borrow init = write(data, layout(0, 8, 1, 8, false));
    fill(init, f64(1)); release(init);
    borrow input = read(data, layout(8, 2, 2, 4, false));
    call inspect(input) -> ();
    release(input); drop(data);
    value { 42 }
}
resource fn inspect(input: Read<F64, 2, 2>) -> Unit {
    borrow child = read(input, layout(0, 2, 2, 2, false));
    release(child);
    value { () }
}";
    let message = rejection(&fixture(source), "check");
    assert_primary(
        &message,
        "main.vast",
        source,
        "borrow child",
        "E_RESOURCE_REGION",
    );
    assert_note(
        &message,
        "main.vast",
        source,
        "call inspect",
        "resource callee was invoked here",
    );
    assert_note(
        &message,
        "main.vast",
        source,
        "input: Read",
        "parent loan is `input`, introduced here",
    );
}

#[test]
fn vector_role_errors_report_the_actual_dual_and_primal_bases() {
    let source = "mod profiles;
resource fn main() -> Int {
    space v = linear(profiles::RealSmooth, 1);
    basis bv = basis(v);
    space vd = dual(v);
    basis bvd = derived(bv, vd);
    allocate input: F64[1];
    allocate output: F64[1];
    borrow init = write(input, layout(0, 1, 1, 1, false));
    fill(init, f64(1)); release(init);
    borrow reader = read(input, layout(0, 1, 1, 1, false));
    vector x = view(reader, bv);
    vector phi = view(reader, bvd);
    borrow out = write(output, layout(0, 1, 1, 1, false));
    evaluate(phi, x, out, overwrite, NativeFast);
    release(out); release(reader);
    drop(input); drop(output);
    value { 42 }
}";
    success(&run(&fixture(source), "check"));
    let swapped = source.replace("evaluate(phi, x,", "evaluate(x, phi,");
    let message = rejection(&fixture(&swapped), "check");
    assert_primary(
        &message,
        "main.vast",
        &swapped,
        "evaluate(x",
        "E_NUMERICAL_TYPE",
    );
    assert_note(
        &message,
        "main.vast",
        &swapped,
        "basis bv =",
        "left vector basis is `bv`, introduced here",
    );
    assert_note(
        &message,
        "main.vast",
        &swapped,
        "basis bvd =",
        "right vector basis is `bvd`, introduced here",
    );

    let wrong_basis = source.replace("view(reader, bvd)", "view(reader, bv)");
    let message = rejection(&fixture(&wrong_basis), "check");
    assert_primary(
        &message,
        "main.vast",
        &wrong_basis,
        "evaluate(phi",
        "E_NUMERICAL_TYPE",
    );
    assert_note(
        &message,
        "main.vast",
        &wrong_basis,
        "basis bv =",
        "left vector basis is `bv`, introduced here",
    );
    assert_note(
        &message,
        "main.vast",
        &wrong_basis,
        "vector phi",
        "left vector is `phi`, introduced here",
    );
}

#[test]
fn runtime_ownership_errors_also_keep_source_names() {
    let source = "resource fn main() -> Int {
    let n: Nat = value { 2 };
    runtime_allocate data: F64[n] runtime_layout(n, 1, n, false);
    runtime_borrow uninitialized = read(data);
    runtime_release(uninitialized); runtime_drop(data);
    value { 42 }
}";
    let message = rejection(&fixture(source), "check");
    assert_primary(
        &message,
        "main.vast",
        source,
        "runtime_borrow",
        "E_RUNTIME_SHAPE",
    );
    assert_note(
        &message,
        "main.vast",
        source,
        "runtime_allocate",
        "borrowed runtime allocation is `data`, introduced here",
    );
}

#[test]
fn wide_call_argument_notes_do_not_hide_the_callee_context() {
    let values = (0..40)
        .map(|i| format!("    let n{i}: Nat = value {{ 0 }};\n"))
        .collect::<String>();
    let arguments = (0..40)
        .map(|i| format!("n{i}"))
        .collect::<Vec<_>>()
        .join(", ");
    let parameters = (0..40)
        .map(|i| format!("p{i}: Nat"))
        .collect::<Vec<_>>()
        .join(", ");
    let source = format!(
        "resource fn main() -> Int {{\n{values}
    allocate data: F64[2];
    borrow init = write(data, layout(0, 2, 1, 2, false));
    fill(init, f64(1)); release(init);
    borrow input = read(data, layout(0, 2, 1, 2, false));
    call consume_many({arguments}, input) -> ();
    release(input); drop(data);
    value {{ 42 }}
}}
resource fn consume_many({parameters}, input: Read<F64, 1, 1>) -> Unit {{ value {{ () }} }}"
    );
    let message = rejection(&fixture(&source), "check");
    assert_primary(
        &message,
        "main.vast",
        &source,
        "call consume_many",
        "E_RESOURCE_TYPE",
    );
    assert_note(
        &message,
        "main.vast",
        &source,
        "resource fn consume_many",
        "while checking resource function `consume_many`",
    );
    assert!(
        message
            .lines()
            .filter(|line| line.contains(": note: "))
            .count()
            <= 32
    );
}

#[test]
fn deep_rejected_calls_keep_the_failing_statement_with_bounded_notes() {
    let mut source = "resource fn main() -> Int { call f0() -> (); value { 42 } }\n".to_owned();
    for i in 0..40 {
        source.push_str(&format!(
            "resource fn f{i}() -> Unit {{ call f{}() -> (); value {{ () }} }}\n",
            i + 1
        ));
    }
    source.push_str("resource fn f40() -> Unit {\n    allocate data: F64[1];\n    borrow bad = read(data, layout(0, 1, 1, 1, false));\n    value { () }\n}");
    let message = rejection(&fixture(&source), "check");
    assert_primary(
        &message,
        "main.vast",
        &source,
        "borrow bad",
        "E_RESOURCE_INIT",
    );
    assert!(
        message.contains("borrowed allocation is `data`, introduced here"),
        "{message}"
    );
    assert!(
        message
            .lines()
            .filter(|line| line.contains(": note: "))
            .count()
            <= 32
    );
}
