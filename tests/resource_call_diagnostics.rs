//! A resource call whose argument is in another basis than its parameter
//! requires names the argument, the parameter, the endpoint and both bases
//! (#684). The names are those of the caller, and each basis has a note at its
//! declaration. Bases have nominal identity: two bases of one space are
//! different bases, whatever their dimension.
//!
//! The arguments are a map, an owned map, an owned-map package, a vector, a
//! metric and a runtime map. An owned result goes through the check of an
//! owned map: it has no argument and no parameter, and its notes name the
//! bases.
//!
//! The text is presentation only. The tests therefore also pin what stays as it
//! was: the matching call is accepted, and a rejection that establishes no
//! basis mismatch keeps the message that states no cause.
mod common;
use common::{Scratch, assert_source_names, checked_replace, cli, message_text, success};

const PROFILES: &str = "indexed marker RealCoefficients;
indexed implementation SmoothScalar(RealCoefficients, scalar_base(smooth, real)) capabilities();
indexed global SmoothBase(SmoothScalar);
indexed implementation RealSmooth(RealCoefficients, linear_descriptor(SmoothBase, real)) capabilities();
";

/// The program of the issue: `measured` has the target basis `alternate_basis`,
/// and `measurement` requires `sensor_basis` at both endpoints.
const MAP: &str = "
resource fn consume(
    sensor_space: Space<RealSmooth, 1>, basis_arg: Basis<sensor_space>,
    measurement: ReadMap<basis_arg, basis_arg>
) -> Unit {
    value { () }
}

resource fn main() -> Int {
    space sensors = linear(RealSmooth, 1);
    basis sensor_basis = basis(sensors);
    basis alternate_basis = basis(sensors);
    allocate data: F64[1];
    borrow writer = write(data, layout(0, 1, 1, 1, false));
    fill(writer, f64(1.0));
    release(writer);
    borrow input = read(data, layout(0, 1, 1, 1, false));
    map measured = view(input, sensor_basis, alternate_basis);
    call consume(sensors, sensor_basis, measured) -> ();
    release(input);
    drop(data);
    value { 0 }
}
";
const MAP_VIEW: &str = "view(input, sensor_basis, alternate_basis)";
const MAP_CALL: &str = "call consume(sensors, sensor_basis, measured) -> ();";

const VECTOR: &str = "
resource fn consume(
    sensor_space: Space<RealSmooth, 1>, basis_arg: Basis<sensor_space>,
    sample: ReadVector<basis_arg>
) -> Unit {
    value { () }
}

resource fn main() -> Int {
    space sensors = linear(RealSmooth, 1);
    basis sensor_basis = basis(sensors);
    basis alternate_basis = basis(sensors);
    allocate data: F64[1];
    borrow writer = write(data, layout(0, 1, 1, 1, false));
    fill(writer, f64(1.0));
    release(writer);
    borrow input = read(data, layout(0, 1, 1, 1, false));
    vector measured = view(input, alternate_basis);
    call consume(sensors, sensor_basis, measured) -> ();
    release(input);
    drop(data);
    value { 0 }
}
";

const OWNED: &str = "
resource fn consume(
    sensor_space: Space<RealSmooth, 1>, basis_arg: Basis<sensor_space>,
    measurement: OwnedMap<basis_arg, basis_arg>
) returns (measurement: OwnedMap<basis_arg, basis_arg>) -> Unit {
    value { () }
}

resource fn main() -> Int {
    space sensors = linear(RealSmooth, 1);
    basis sensor_basis = basis(sensors);
    basis alternate_basis = basis(sensors);
    allocate data: F64[1];
    borrow writer = write(data, layout(0, 1, 1, 1, false));
    fill(writer, f64(1.0));
    release(writer);
    map measured = owned(data, layout(0, 1, 1, 1, false), sensor_basis, alternate_basis);
    call consume(sensors, sensor_basis, measured) -> (returned);
    drop(returned);
    value { 0 }
}
";

/// `measured` goes from `alternate_basis`, and `boxed` requires a package
/// whose source basis is `sensor_basis`.
const PACKAGE: &str = "
resource fn consume(
    sensor_space: Space<RealSmooth, 1>, basis_arg: Basis<sensor_space>,
    boxed: OwnedMapTo<basis_arg, 1>
) returns (boxed: OwnedMapTo<basis_arg, 1>) -> Unit {
    value { () }
}

resource fn main() -> Int {
    space sensors = linear(RealSmooth, 1);
    basis sensor_basis = basis(sensors);
    basis alternate_basis = basis(sensors);
    allocate data: F64[1];
    borrow writer = write(data, layout(0, 1, 1, 1, false));
    fill(writer, f64(1.0));
    release(writer);
    map measured = owned(data, layout(0, 1, 1, 1, false), alternate_basis, sensor_basis);
    map packed = pack(measured);
    call consume(sensors, sensor_basis, packed) -> (returned);
    drop(returned);
    value { 0 }
}
";

/// `measured` is a metric on `alternate_basis`, and `form` requires a metric
/// on `sensor_basis`.
const METRIC: &str = "
resource fn consume(
    sensor_space: Space<RealSmooth, 1>, basis_arg: Basis<sensor_space>,
    sigma_arg: Involution<sensor_space>, form: Metric<basis_arg, sigma_arg>
) -> Unit {
    value { () }
}

resource fn main() -> Int {
    space sensors = linear(RealSmooth, 1);
    basis sensor_basis = basis(sensors);
    basis alternate_basis = basis(sensors);
    involution sigma = canonical(sensors);
    metric measured = orthonormal(alternate_basis, sigma);
    call consume(sensors, sensor_basis, sigma, measured) -> ();
    value { 0 }
}
";

/// The body of `produce` makes an owned map to `other_arg`, and its result
/// type requires `basis_arg` at both endpoints.
const RESULT: &str = "
resource fn produce(
    sensor_space: Space<RealSmooth, 1>, basis_arg: Basis<sensor_space>,
    other_arg: Basis<sensor_space>
) returns (made: OwnedMap<basis_arg, basis_arg>) -> Unit {
    allocate data: F64[1];
    borrow writer = write(data, layout(0, 1, 1, 1, false));
    fill(writer, f64(1.0));
    release(writer);
    map made = owned(data, layout(0, 1, 1, 1, false), basis_arg, other_arg);
    value { () }
}

resource fn main() -> Int {
    space sensors = linear(RealSmooth, 1);
    basis sensor_basis = basis(sensors);
    basis alternate_basis = basis(sensors);
    call produce(sensors, sensor_basis, alternate_basis) -> (made);
    drop(made);
    value { 0 }
}
";

const RUNTIME: &str = "
resource fn consume(
    n: Nat, sensor_space: RuntimeSpace<RealSmooth, n>, basis_arg: RuntimeBasis<sensor_space>,
    measurement: RuntimeMap<basis_arg, basis_arg, read>
) -> Unit {
    value { () }
}

resource fn main() -> Int {
    let n: Nat = value { 2 };
    let capacity: Nat = value { n * n };
    runtime_space sensors = linear(RealSmooth, n);
    runtime_basis sensor_basis = basis(sensors);
    runtime_basis alternate_basis = basis(sensors);
    runtime_allocate data: F64[capacity] runtime_layout(n, n, n, false);
    runtime_borrow writer = write(data);
    runtime_fill(writer, f64(1.0));
    runtime_release(writer);
    runtime_borrow input = read(data);
    runtime_map measured = view(input, sensor_basis, alternate_basis);
    call consume(n, sensors, sensor_basis, measured) -> ();
    runtime_release(input);
    runtime_drop(data);
    value { 0 }
}
";

fn program(body: &str) -> String {
    format!("{PROFILES}{body}")
}

/// `source` after each replacement in turn. A replacement whose target is
/// absent fails, so that no mutation is silently ineffective.
#[track_caller]
fn replaced(source: &str, replacements: &[(&str, &str)]) -> String {
    let mut source = source.to_owned();
    for (from, to) in replacements {
        source = checked_replace(&source, from, to);
    }
    source
}

fn fixture(source: &str) -> Scratch {
    let scratch = Scratch::empty("resource call diagnostics");
    scratch.write(
        "Vastitas.toml",
        "[package]\nname = \"basis_diagnostic\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n",
    );
    scratch.write("main.vast", source);
    scratch
}

fn run(scratch: &Scratch, mode: &str) -> std::process::Output {
    let mut command = cli();
    command
        .args([mode, "--manifest-path"])
        .arg(scratch.0.join("Vastitas.toml"));
    if mode == "build" {
        command.arg("-o").arg(scratch.0.join("program"));
    }
    command.output().unwrap()
}

/// Rejects `source` as [`rejected`] rejects a package.
#[track_caller]
fn rejection(source: &str) -> String {
    rejected(&fixture(source))
}

/// Rejects the package under `check` and `build` with the same diagnostics,
/// makes no executable and returns the rendered diagnostics. No message may
/// hold an internal symbol in place of a source name.
#[track_caller]
fn rejected(scratch: &Scratch) -> String {
    let mut rendered = Vec::new();
    for mode in ["check", "build"] {
        let output = run(scratch, mode);
        assert!(
            !output.status.success(),
            "{mode} accepted the program: {output:?}"
        );
        assert!(!scratch.0.join("program").exists());
        rendered.push(String::from_utf8(output.stderr).unwrap());
    }
    assert_eq!(rendered[0], rendered[1], "check and build differ");
    assert_source_names(&message_text(&rendered[0]));
    rendered.swap_remove(0)
}

/// `check` accepts `source`, and the built executable prints `expected`.
#[track_caller]
fn accepted(source: &str, expected: &str) {
    let scratch = fixture(source);
    success(&run(&scratch, "check"));
    success(&run(&scratch, "build"));
    let output = std::process::Command::new(scratch.0.join("program"))
        .output()
        .unwrap();
    success(&output);
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        format!("{expected}\n")
    );
}

/// The diagnostics without their `path:line:column: ` locations.
fn text(rendered: &str) -> Vec<String> {
    message_text(rendered).lines().map(str::to_owned).collect()
}

fn location(source: &str, marker: &str) -> String {
    location_in("main.vast", source, marker)
}

/// The place of `marker` in the text `source` of `file`.
fn location_in(file: &str, source: &str, marker: &str) -> String {
    let before = &source[..source.find(marker).expect(marker)];
    let line = before.bytes().filter(|&byte| byte == b'\n').count() + 1;
    let column = before.rsplit('\n').next().unwrap().chars().count() + 1;
    format!("{file}:{line}:{column}: ")
}

/// The first line is `message` at the place of `marker` in `source`.
#[track_caller]
fn assert_primary(rendered: &str, source: &str, marker: &str, message: &str) {
    let expected = format!("{}{message}", location(source, marker));
    let first = rendered.lines().next().unwrap();
    assert!(
        first.ends_with(&expected),
        "expected {expected}\n{rendered}"
    );
}

/// Some line is the note `note` at the place of `marker` in `source`.
#[track_caller]
fn assert_note(rendered: &str, source: &str, marker: &str, note: &str) {
    let expected = format!("{}note: {note}", location(source, marker));
    assert!(
        rendered.lines().any(|line| line.ends_with(&expected)),
        "missing {expected}\n{rendered}"
    );
}

/// No line names a basis by a role of this diagnostic or marks a parameter.
#[track_caller]
fn assert_no_basis_names(rendered: &str) {
    let text = message_text(rendered);
    for absent in ["actual ", "required ", "but requires", "is declared here"] {
        assert!(!text.contains(absent), "{absent:?} in\n{rendered}");
    }
}

const FALLBACK: &str =
    "E_NUMERICAL_TYPE: numerical argument violates its nominal, shape or live-loan contract";

#[test]
fn a_map_in_another_target_basis_names_the_argument_the_parameter_and_both_bases() {
    let source = program(MAP);
    let rendered = rejection(&source);
    // The complete text: the call-site and callee context stays, and the two
    // bases precede the arguments of the call.
    assert_eq!(
        text(&rendered),
        [
            "E_NUMERICAL_TYPE: argument `measured` for parameter `measurement` has target basis `alternate_basis` but requires `sensor_basis`",
            "note: while checking resource function `consume`",
            "note: while checking resource function `main`",
            "note: parameter `measurement` is declared here",
            "note: actual target basis is `alternate_basis`, introduced here",
            "note: required target basis is `sensor_basis`, introduced here",
            "note: call argument is `sensors`, introduced here",
            "note: call argument is `sensor_basis`, introduced here",
            "note: call argument is `measured`, introduced here",
        ]
    );
    assert_primary(
        &rendered,
        &source,
        MAP_CALL,
        "E_NUMERICAL_TYPE: argument `measured` for parameter `measurement` has target basis `alternate_basis` but requires `sensor_basis`",
    );
    for (marker, note) in [
        (
            "resource fn consume",
            "while checking resource function `consume`",
        ),
        (
            "measurement: ReadMap",
            "parameter `measurement` is declared here",
        ),
        (
            "basis alternate_basis",
            "actual target basis is `alternate_basis`, introduced here",
        ),
        (
            "basis sensor_basis",
            "required target basis is `sensor_basis`, introduced here",
        ),
        (
            "map measured",
            "call argument is `measured`, introduced here",
        ),
    ] {
        assert_note(&rendered, &source, marker, note);
    }
}

#[test]
fn the_matching_arguments_are_accepted_and_run() {
    for (body, from, to) in [
        (MAP, MAP_VIEW, "view(input, sensor_basis, sensor_basis)"),
        (
            VECTOR,
            "view(input, alternate_basis)",
            "view(input, sensor_basis)",
        ),
        (
            OWNED,
            "sensor_basis, alternate_basis);",
            "sensor_basis, sensor_basis);",
        ),
        (
            PACKAGE,
            "alternate_basis, sensor_basis);",
            "sensor_basis, sensor_basis);",
        ),
        (
            METRIC,
            "orthonormal(alternate_basis, sigma)",
            "orthonormal(sensor_basis, sigma)",
        ),
        (RESULT, "basis_arg, other_arg);", "basis_arg, basis_arg);"),
        (RUNTIME, MAP_VIEW, "view(input, sensor_basis, sensor_basis)"),
    ] {
        accepted(&checked_replace(&program(body), from, to), "0");
    }
}

#[test]
fn the_source_endpoint_and_both_endpoints_are_named_by_their_roles() {
    let source = checked_replace(
        &program(MAP),
        MAP_VIEW,
        "view(input, alternate_basis, sensor_basis)",
    );
    let rendered = rejection(&source);
    assert_primary(
        &rendered,
        &source,
        MAP_CALL,
        "E_NUMERICAL_TYPE: argument `measured` for parameter `measurement` has source basis `alternate_basis` but requires `sensor_basis`",
    );
    assert_note(
        &rendered,
        &source,
        "basis alternate_basis",
        "actual source basis is `alternate_basis`, introduced here",
    );
    assert_note(
        &rendered,
        &source,
        "basis sensor_basis",
        "required source basis is `sensor_basis`, introduced here",
    );
    assert!(!rendered.contains("target basis"), "{rendered}");

    let source = checked_replace(
        &program(MAP),
        MAP_VIEW,
        "view(input, alternate_basis, alternate_basis)",
    );
    let rendered = rejection(&source);
    assert_primary(
        &rendered,
        &source,
        MAP_CALL,
        "E_NUMERICAL_TYPE: argument `measured` for parameter `measurement` has source basis `alternate_basis` but requires `sensor_basis` and has target basis `alternate_basis` but requires `sensor_basis`",
    );
    for role in ["source", "target"] {
        assert_note(
            &rendered,
            &source,
            "basis alternate_basis",
            &format!("actual {role} basis is `alternate_basis`, introduced here"),
        );
        assert_note(
            &rendered,
            &source,
            "basis sensor_basis",
            &format!("required {role} basis is `sensor_basis`, introduced here"),
        );
    }
}

#[test]
fn each_endpoint_is_compared_with_the_basis_of_its_own_parameter() {
    // `transfer` goes from `from_basis` to `to_basis`. The caller passes the
    // bases in that order and a map in the opposite direction, between spaces
    // of equal dimension.
    let source = replaced(
        &program(MAP),
        &[
            (
                "basis_arg: Basis<sensor_space>,\n    measurement: ReadMap<basis_arg, basis_arg>",
                "from_basis: Basis<sensor_space>,\n    image: Space<RealSmooth, 1>, to_basis: Basis<image>,\n    transfer: ReadMap<from_basis, to_basis>",
            ),
            (
                "basis alternate_basis = basis(sensors);",
                "space images = linear(RealSmooth, 1);\n    basis alternate_basis = basis(images);",
            ),
            (MAP_VIEW, "view(input, alternate_basis, sensor_basis)"),
            (
                MAP_CALL,
                "call consume(sensors, sensor_basis, images, alternate_basis, measured) -> ();",
            ),
        ],
    );
    let rendered = rejection(&source);
    assert_primary(
        &rendered,
        &source,
        "call consume",
        "E_NUMERICAL_TYPE: argument `measured` for parameter `transfer` has source basis `alternate_basis` but requires `sensor_basis` and has target basis `sensor_basis` but requires `alternate_basis`",
    );
    assert_note(
        &rendered,
        &source,
        "transfer: ReadMap",
        "parameter `transfer` is declared here",
    );
    // The map in the direction of the parameter is accepted.
    accepted(
        &checked_replace(
            &source,
            "view(input, alternate_basis, sensor_basis)",
            "view(input, sensor_basis, alternate_basis)",
        ),
        "0",
    );
}

#[test]
fn a_caller_with_parameters_names_its_own_parameters() {
    // The compiler checks `relay` on its own with a different basis for each
    // `Basis` parameter. The names are those of `relay`, not of `main` and not
    // of `consume`.
    let source = replaced(
        &program(MAP),
        &[
            (
                MAP_CALL,
                "call relay(sensors, sensor_basis, alternate_basis, measured) -> ();",
            ),
            (
                "resource fn main() -> Int {",
                "resource fn relay(
    relay_space: Space<RealSmooth, 1>, first: Basis<relay_space>, second: Basis<relay_space>,
    relayed: ReadMap<first, second>
) -> Unit {
    call consume(relay_space, first, relayed) -> ();
    value { () }
}

resource fn main() -> Int {",
            ),
        ],
    );
    let rendered = rejection(&source);
    assert_primary(
        &rendered,
        &source,
        "call consume",
        "E_NUMERICAL_TYPE: argument `relayed` for parameter `measurement` has target basis `second` but requires `first`",
    );
    assert_note(
        &rendered,
        &source,
        "second: Basis",
        "actual target basis is `second`, introduced here",
    );
    assert_note(
        &rendered,
        &source,
        "first: Basis",
        "required target basis is `first`, introduced here",
    );
    for foreign in ["sensor_basis", "alternate_basis", "basis_arg"] {
        assert!(!rendered.contains(foreign), "{foreign} in\n{rendered}");
    }
}

#[test]
fn a_call_that_binds_a_scalar_result_names_the_bases_too() {
    let source = replaced(
        &program(MAP),
        &[
            (
                ") -> Unit {\n    value { () }",
                ") -> Int {\n    value { 7 }",
            ),
            (
                MAP_CALL,
                "let seven: Int = call consume(sensors, sensor_basis, measured) -> ();",
            ),
        ],
    );
    let rendered = rejection(&source);
    assert_primary(
        &rendered,
        &source,
        "let seven",
        "E_NUMERICAL_TYPE: argument `measured` for parameter `measurement` has target basis `alternate_basis` but requires `sensor_basis`",
    );
}

#[test]
fn a_callee_in_another_module_has_its_parameter_note_in_its_own_file() {
    let (consume, main) = MAP.split_at(MAP.find("resource fn main").unwrap());
    let helper = replaced(
        consume.trim_start(),
        &[
            ("resource fn consume", "pub resource fn consume"),
            ("Space<RealSmooth, 1>", "Space<super::RealSmooth, 1>"),
        ],
    );
    let main = checked_replace(
        main,
        MAP_CALL,
        "call helper::consume(sensors, sensor_basis, measured) -> ();",
    );
    let source = format!(
        "mod helper;\n{}\n{main}",
        PROFILES.replace("indexed ", "pub indexed ")
    );
    let scratch = fixture(&source);
    scratch.write("helper/mod.vast", &helper);
    let rendered = rejected(&scratch);
    assert_primary(
        &rendered,
        &source,
        "call helper::consume",
        "E_NUMERICAL_TYPE: argument `measured` for parameter `measurement` has target basis `alternate_basis` but requires `sensor_basis`",
    );
    for (marker, note) in [
        (
            "resource fn consume",
            "while checking resource function `consume`",
        ),
        (
            "measurement: ReadMap",
            "parameter `measurement` is declared here",
        ),
    ] {
        let expected = format!(
            "{}note: {note}",
            location_in("helper/mod.vast", &helper, marker)
        );
        assert!(
            rendered.lines().any(|line| line.ends_with(&expected)),
            "missing {expected}\n{rendered}"
        );
    }
    assert_note(
        &rendered,
        &source,
        "basis alternate_basis",
        "actual target basis is `alternate_basis`, introduced here",
    );
    assert_note(
        &rendered,
        &source,
        "basis sensor_basis",
        "required target basis is `sensor_basis`, introduced here",
    );
}

#[test]
fn one_map_for_two_parameters_names_the_parameter_that_rejects_it() {
    // `measured` fits `first` and not `second`. The argument is named by its
    // position in the call, and the parameter is the one at that position.
    let source = replaced(
        &program(MAP),
        &[
            (
                "basis_arg: Basis<sensor_space>,\n    measurement: ReadMap<basis_arg, basis_arg>",
                "basis_arg: Basis<sensor_space>, other_arg: Basis<sensor_space>,\n    first: ReadMap<basis_arg, basis_arg>, second: ReadMap<other_arg, other_arg>",
            ),
            (MAP_VIEW, "view(input, sensor_basis, sensor_basis)"),
            (
                MAP_CALL,
                "call consume(sensors, sensor_basis, alternate_basis, measured, measured) -> ();",
            ),
        ],
    );
    let rendered = rejection(&source);
    assert_primary(
        &rendered,
        &source,
        "call consume",
        "E_NUMERICAL_TYPE: argument `measured` for parameter `second` has source basis `sensor_basis` but requires `alternate_basis` and has target basis `sensor_basis` but requires `alternate_basis`",
    );
    assert_note(
        &rendered,
        &source,
        "second: ReadMap",
        "parameter `second` is declared here",
    );
    assert!(!message_text(&rendered).contains("`first`"), "{rendered}");
    // Both parameters accept the map when the call passes one basis for both.
    accepted(
        &checked_replace(
            &source,
            "call consume(sensors, sensor_basis, alternate_basis, measured, measured)",
            "call consume(sensors, sensor_basis, sensor_basis, measured, measured)",
        ),
        "0",
    );
}

#[test]
fn many_call_arguments_do_not_hide_the_bases_or_the_parameter() {
    // A diagnostic has at most 32 notes. The parameter and the two bases
    // precede the notes on the 43 arguments of the call.
    let values = (0..40)
        .map(|i| format!("    let n{i}: Nat = value {{ 0 }};\n"))
        .collect::<String>();
    let arguments = (0..40).map(|i| format!("n{i}, ")).collect::<String>();
    let parameters = (0..40).map(|i| format!("p{i}: Nat, ")).collect::<String>();
    let source = replaced(
        &program(MAP),
        &[
            (
                "resource fn consume(\n    sensor_space",
                &format!("resource fn consume(\n    {parameters}sensor_space"),
            ),
            ("    space sensors", &format!("{values}    space sensors")),
            (
                MAP_CALL,
                &format!("call consume({arguments}sensors, sensor_basis, measured) -> ();"),
            ),
        ],
    );
    let rendered = rejection(&source);
    assert_primary(
        &rendered,
        &source,
        "call consume",
        "E_NUMERICAL_TYPE: argument `measured` for parameter `measurement` has target basis `alternate_basis` but requires `sensor_basis`",
    );
    for (marker, note) in [
        (
            "resource fn consume",
            "while checking resource function `consume`",
        ),
        (
            "measurement: ReadMap",
            "parameter `measurement` is declared here",
        ),
        (
            "basis alternate_basis",
            "actual target basis is `alternate_basis`, introduced here",
        ),
        (
            "basis sensor_basis",
            "required target basis is `sensor_basis`, introduced here",
        ),
    ] {
        assert_note(&rendered, &source, marker, note);
    }
    let notes = rendered
        .lines()
        .filter(|line| line.contains(": note: "))
        .count();
    assert_eq!(notes, 32, "{rendered}");
}

#[test]
fn a_vector_in_another_basis_names_both_bases() {
    let source = program(VECTOR);
    let rendered = rejection(&source);
    assert_eq!(
        text(&rendered),
        [
            "E_NUMERICAL_TYPE: argument `measured` for parameter `sample` has basis `alternate_basis` but requires `sensor_basis`",
            "note: while checking resource function `consume`",
            "note: while checking resource function `main`",
            "note: parameter `sample` is declared here",
            "note: actual basis is `alternate_basis`, introduced here",
            "note: required basis is `sensor_basis`, introduced here",
            "note: call argument is `sensors`, introduced here",
            "note: call argument is `sensor_basis`, introduced here",
            "note: call argument is `measured`, introduced here",
        ]
    );
    assert_primary(
        &rendered,
        &source,
        "call consume",
        "E_NUMERICAL_TYPE: argument `measured` for parameter `sample` has basis `alternate_basis` but requires `sensor_basis`",
    );
    assert_note(
        &rendered,
        &source,
        "basis alternate_basis",
        "actual basis is `alternate_basis`, introduced here",
    );
    assert_note(
        &rendered,
        &source,
        "sample: ReadVector",
        "parameter `sample` is declared here",
    );
}

#[test]
fn an_owned_map_in_another_basis_names_both_bases() {
    let source = program(OWNED);
    let rendered = rejection(&source);
    assert_primary(
        &rendered,
        &source,
        "call consume",
        "E_NUMERICAL_TYPE: argument `measured` for parameter `measurement` has target basis `alternate_basis` but requires `sensor_basis`",
    );
    assert_note(
        &rendered,
        &source,
        "basis alternate_basis",
        "actual target basis is `alternate_basis`, introduced here",
    );
    assert_note(
        &rendered,
        &source,
        "basis sensor_basis",
        "required target basis is `sensor_basis`, introduced here",
    );
    assert_note(
        &rendered,
        &source,
        "measurement: OwnedMap",
        "parameter `measurement` is declared here",
    );
}

#[test]
fn an_owned_map_package_from_another_basis_names_both_bases() {
    let source = program(PACKAGE);
    let rendered = rejection(&source);
    assert_primary(
        &rendered,
        &source,
        "call consume",
        "E_NUMERICAL_TYPE: argument `packed` for parameter `boxed` has source basis `alternate_basis` but requires `sensor_basis`",
    );
    assert_note(
        &rendered,
        &source,
        "basis alternate_basis",
        "actual source basis is `alternate_basis`, introduced here",
    );
    assert_note(
        &rendered,
        &source,
        "basis sensor_basis",
        "required source basis is `sensor_basis`, introduced here",
    );
    assert_note(
        &rendered,
        &source,
        "boxed: OwnedMapTo",
        "parameter `boxed` is declared here",
    );
    // The package hides its target basis, and no note names one.
    assert!(!rendered.contains("target basis"), "{rendered}");
}

#[test]
fn a_metric_on_another_basis_names_both_bases() {
    let source = program(METRIC);
    let rendered = rejection(&source);
    assert_primary(
        &rendered,
        &source,
        "call consume",
        "E_NUMERICAL_TYPE: argument `measured` for parameter `form` has basis `alternate_basis` but requires `sensor_basis`",
    );
    assert_note(
        &rendered,
        &source,
        "basis alternate_basis",
        "actual basis is `alternate_basis`, introduced here",
    );
    assert_note(
        &rendered,
        &source,
        "basis sensor_basis",
        "required basis is `sensor_basis`, introduced here",
    );
    assert_note(
        &rendered,
        &source,
        "form: Metric",
        "parameter `form` is declared here",
    );
}

#[test]
fn an_owned_result_in_another_basis_names_both_bases_at_the_result() {
    // The same check serves an owned result. It has no argument and no
    // parameter, so the message speaks of a value and its contract, and the
    // notes name the bases of the callee.
    let source = program(RESULT);
    let rendered = rejection(&source);
    assert_eq!(
        text(&rendered),
        [
            "E_NUMERICAL_TYPE: numerical value has a basis other than the basis that its contract requires",
            "note: while checking resource function `produce`",
            "note: actual target basis is `other_arg`, introduced here",
            "note: required target basis is `basis_arg`, introduced here",
        ]
    );
    assert_primary(
        &rendered,
        &source,
        "{ () }",
        "E_NUMERICAL_TYPE: numerical value has a basis other than the basis that its contract requires",
    );
    assert_note(
        &rendered,
        &source,
        "other_arg: Basis",
        "actual target basis is `other_arg`, introduced here",
    );
    assert_note(
        &rendered,
        &source,
        "basis_arg: Basis",
        "required target basis is `basis_arg`, introduced here",
    );
}

#[test]
fn a_runtime_map_in_another_basis_names_both_bases() {
    let source = program(RUNTIME);
    let rendered = rejection(&source);
    assert_eq!(
        text(&rendered),
        [
            "E_RUNTIME_CALL: argument `measured` for parameter `measurement` has target basis `alternate_basis` but requires `sensor_basis`",
            "note: while checking resource function `consume`",
            "note: while checking resource function `main`",
            "note: parameter `measurement` is declared here",
            "note: actual target basis is `alternate_basis`, introduced here",
            "note: required target basis is `sensor_basis`, introduced here",
            "note: call argument is `n`, introduced here",
            "note: call argument is `sensors`, introduced here",
            "note: call argument is `sensor_basis`, introduced here",
            "note: call argument is `measured`, introduced here",
        ]
    );
    assert_primary(
        &rendered,
        &source,
        "call consume",
        "E_RUNTIME_CALL: argument `measured` for parameter `measurement` has target basis `alternate_basis` but requires `sensor_basis`",
    );
    assert_note(
        &rendered,
        &source,
        "runtime_basis alternate_basis",
        "actual target basis is `alternate_basis`, introduced here",
    );
    assert_note(
        &rendered,
        &source,
        "runtime_basis sensor_basis",
        "required target basis is `sensor_basis`, introduced here",
    );
    assert_note(
        &rendered,
        &source,
        "measurement: RuntimeMap",
        "parameter `measurement` is declared here",
    );

    let source = checked_replace(
        &source,
        MAP_VIEW,
        "view(input, alternate_basis, sensor_basis)",
    );
    let rendered = rejection(&source);
    assert_primary(
        &rendered,
        &source,
        "call consume",
        "E_RUNTIME_CALL: argument `measured` for parameter `measurement` has source basis `alternate_basis` but requires `sensor_basis`",
    );
}

#[test]
fn a_rejection_of_another_kind_keeps_the_message_without_a_cause() {
    // A basis of another space for `Basis<sensor_space>`: the map has the
    // bases that the call passes, and the space of the basis differs.
    let other_space = replaced(
        &program(MAP),
        &[
            (
                "basis alternate_basis = basis(sensors);",
                "space others = linear(RealSmooth, 1);\n    basis alternate_basis = basis(others);",
            ),
            (MAP_VIEW, "view(input, alternate_basis, alternate_basis)"),
            (
                MAP_CALL,
                "call consume(sensors, alternate_basis, measured) -> ();",
            ),
        ],
    );
    // A map whose loan has ended, in the bases that its parameter requires.
    let stale = replaced(
        &program(MAP),
        &[
            (MAP_VIEW, "view(input, sensor_basis, sensor_basis)"),
            (
                &format!("    {MAP_CALL}\n    release(input);"),
                &format!("    release(input);\n    {MAP_CALL}"),
            ),
        ],
    );
    // A vector where the parameter requires a map.
    let other_kind = checked_replace(
        &program(MAP),
        "map measured = view(input, sensor_basis, alternate_basis);",
        "vector measured = view(input, alternate_basis);",
    );
    // A package to a space of another dimension, from the basis that its
    // parameter requires.
    let other_dimension = replaced(
        &program(PACKAGE),
        &[
            (
                "alternate_basis, sensor_basis);",
                "sensor_basis, sensor_basis);",
            ),
            (
                "boxed: OwnedMapTo<basis_arg, 1>\n) returns (boxed: OwnedMapTo<basis_arg, 1>)",
                "boxed: OwnedMapTo<basis_arg, 2>\n) returns (boxed: OwnedMapTo<basis_arg, 2>)",
            ),
        ],
    );
    // A metric with other Gram data, on the basis that its parameter requires.
    let other_gram = replaced(
        &program(METRIC),
        &[
            (
                "form: Metric<basis_arg, sigma_arg>",
                "form: OrthonormalMetric<basis_arg, sigma_arg>",
            ),
            (
                "orthonormal(alternate_basis, sigma)",
                "scaled_identity(sensor_basis, sigma, 2)",
            ),
        ],
    );
    for (source, binding, argument) in [
        (other_space, "map measured", "measured"),
        (stale, "map measured", "measured"),
        (other_kind, "vector measured", "measured"),
        (other_dimension, "map packed", "packed"),
        (other_gram, "metric measured", "measured"),
    ] {
        let rendered = rejection(&source);
        assert_primary(&rendered, &source, "call consume", FALLBACK);
        assert_no_basis_names(&rendered);
        assert_note(
            &rendered,
            &source,
            "resource fn consume",
            "while checking resource function `consume`",
        );
        assert_note(
            &rendered,
            &source,
            binding,
            &format!("call argument is `{argument}`, introduced here"),
        );
    }

    // A runtime basis of another space keeps its own diagnostic.
    let source = replaced(
        &program(RUNTIME),
        &[
            (
                "runtime_basis alternate_basis = basis(sensors);",
                "runtime_space others = linear(RealSmooth, n);\n    runtime_basis alternate_basis = basis(others);",
            ),
            (MAP_VIEW, "view(input, alternate_basis, alternate_basis)"),
            (
                "call consume(n, sensors, sensor_basis, measured) -> ();",
                "call consume(n, sensors, alternate_basis, measured) -> ();",
            ),
        ],
    );
    let rendered = rejection(&source);
    assert_primary(
        &rendered,
        &source,
        "call consume",
        "E_RUNTIME_CALL: RuntimeBasis belongs to a distinct nominal space",
    );
    assert_no_basis_names(&rendered);
}
