//! The exit status of a native program and the interim built-in `show!` of
//! `fn main` (#836): the frontend and the kernel each check where `show!`
//! stands and what it displays, and native execution pins the lines, their
//! order and the exit status.
mod common;
use common::{
    Run, Scratch, captured_wire, checked_replace, cli, exits, expect_code, kernel, native, shows,
    success,
};
use serde_json::{Value, json};

const FILE: &str = "show.vast";

fn run(source: &str, expected: Run) {
    native(source, &[], expected, FILE);
}

#[track_caller]
fn reject(source: &str, code: &str) -> String {
    let message = common::reject(source, code, FILE);
    assert!(!message.contains("legacy_flat::"), "{message}");
    message
}

/// The wire request that checking the flat program `source` sends, which must
/// use protocol `version`.
fn flat_wire(source: &str, version: u64) -> Value {
    let scratch = Scratch::empty("show wire");
    let path = scratch.write(FILE, source);
    let mut command = cli();
    command.arg("check").arg(path);
    captured_wire(command, version)
}

/// The functions of the root module of a request.
fn functions(wire: &mut Value) -> &mut Vec<Value> {
    wire["packages"][0]["modules"][0]["functions"]
        .as_array_mut()
        .unwrap()
}

fn function<'a>(wire: &'a mut Value, name: &str) -> &'a mut Value {
    functions(wire)
        .iter_mut()
        .find(|function| function["name"] == name)
        .unwrap()
}

#[test]
fn the_result_of_main_is_the_exit_status_modulo_256() {
    for (result, status) in [
        ("0", 0),
        ("42", 42),
        ("300", 44),
        ("0 - 1", 255),
        ("0 - 256", 0),
        ("255 + 256 * 1000000000000000000000000000000", 255),
    ] {
        run(&format!("fn main() -> Int {{ {result} }}"), exits(status));
    }
}

#[test]
fn a_resource_entry_returns_its_exit_status() {
    for (result, status) in [("300", 44), ("0 - 1", 255)] {
        let scratch = Scratch::empty("show resource");
        scratch.write_package(
            "app",
            &format!("resource fn main() -> Int {{ value {{ {result} }} }}"),
            "",
        );
        assert_eq!(
            scratch.check_build_and_run("app/Vastitas.toml"),
            exits(status)
        );
    }
}

#[test]
fn shown_values_print_once_in_order_and_are_used_later() {
    run(
        "fn twice(x: Int) -> Int { x + x }
fn main() -> Int {
    let a = show!(twice(21));
    let n: Nat = show!(3 - 5);
    let b = show!(a < 50 && !(a == 43));
    let u = show!(());
    let p: Pair<Int> = show!(pair(a, -3));
    let q = show!(pair(n, n + 7));
    let total = show!(pair_first(p) + pair_second(p) + a);
    total - 81
}",
        shows(&[
            "twice(21) = 42",
            "3 - 5 = 0",
            "a < 50 && !(a == 43) = true",
            "() = ()",
            "pair(a, -3) = (42, -3)",
            "pair(n, n + 7) = (0, 7)",
            "pair_first(p) + pair_second(p) + a = 81",
        ]),
    );
    // Evaluated once: a value used many times is written once, and the
    // statements without `show!` write nothing. The result is still the
    // exit status.
    run(
        "fn main() -> Int {
    let x = show!(10 * 10 * 10);
    let y = x + x + x;
    let z = show!(y - x);
    z + x - 3000 + 300
}",
        Run {
            status: 44,
            ..shows(&["10 * 10 * 10 = 1000", "y - x = 2000"])
        },
    );
}

#[test]
fn a_label_is_the_source_text_with_runs_of_whitespace_as_one_space() {
    run(
        "fn add(a: Int, b: Int) -> Int { a + b }
fn main() -> Int {
    let shown = show!(  add(1,
            2)   +   3 );
    0
}",
        shows(&["add(1, 2) + 3 = 6"]),
    );
}

#[test]
fn shown_names_do_not_collide_with_generated_names() {
    // The generated entry point binds Core symbols, never source names, and
    // writes the label as a string literal.
    run(
        "fn main() -> Int {
    let v_0 = 7;
    let status = show!(v_0 + 1);
    let toString = show!(status * 2);
    let pure = show!(toString - status);
    pure - 8
}",
        shows(&["v_0 + 1 = 8", "status * 2 = 16", "toString - status = 8"]),
    );
}

#[test]
fn show_stands_only_in_the_top_level_lets_of_main() {
    for source in [
        "fn other() -> Int { let x = show!(1); x } fn main() -> Int { other() }",
        "fn main() -> Int { let x = { let y = show!(1); y }; x }",
        "fn main() -> Int { let x = if true { let y = show!(1); y } else { 0 }; x }",
        "fn main() -> Int { let f = fn(a: Int) -> Int { let b = show!(a); b }; f(1) }",
        "fn add(a: Int, b: Int) -> Int { a + b } fn main() -> Int { let x = add(show!(1), 2); x }",
        "fn main() -> Int { let x = show!(1) + 1; x }",
        "fn main() -> Int { let x = (show!(1)); x }",
        "fn main() -> Int { show!(1) }",
    ] {
        let message = reject(source, "E_UNSUPPORTED");
        assert!(message.contains("`show!` is allowed only"), "{message}");
    }
    let message = reject("fn main() -> Int { let x = dbg!(1); x }", "E_UNSUPPORTED");
    assert!(message.contains("`dbg!` is not supported"), "{message}");
    // A function value and a value of a legacy geometric type are not shown.
    reject(
        "fn main() -> Int { let f = show!(fn(a: Int) -> Int { a }); 0 }",
        "E_TYPE",
    );
    let message = reject(
        "fn main() -> Int { let X = Affine(QQ, 2); let p = show!(origin(X)); 0 }",
        "E_TYPE",
    );
    assert!(
        message.contains("`show!` cannot display a value of type"),
        "{message}"
    );
}

/// A flat unit has the legacy geometry with `show!` as without it, also from
/// a `--lib` input (#533): every flat request carries `legacy_geometry`, which
/// lifts the restriction of #836.
#[test]
fn show_stands_beside_legacy_geometry_in_flat_input() {
    let geometry = "fn carry(X: Scheme, p: Point<X, Base(QQ)>) -> Point<X, Base(QQ)> {
    apply(compose(id(X), id(X)), p)
}";
    let main = "fn main() -> Int {
    let X = Affine(QQ, 3);
    let q: Point<X, Base(QQ)> = carry(X, origin(X));
    let d = show!(dim(X));
    let n = show!(int(d) - 3);
    n
}";
    run(
        &format!("{geometry}\n{main}"),
        shows(&["dim(X) = 3", "int(d) - 3 = 0"]),
    );
    let library = Scratch::empty("show geometry library");
    let path = library.write("geometry.vast", geometry);
    native(
        main,
        &[path],
        shows(&["dim(X) = 3", "int(d) - 3 = 0"]),
        FILE,
    );
    let wire = flat_wire(&format!("{geometry}\n{main}"), common::CURRENT_PROTOCOL);
    assert_eq!(wire["legacy_geometry"], true, "{wire}");
}

#[test]
fn show_is_refused_outside_the_entry_point_of_packages() {
    let scratch = Scratch::empty("show packages");
    scratch.write_package(
        "dep",
        "pub fn value() -> Int { 1 }\nfn main() -> Int { let x = show!(1); x }",
        "",
    );
    scratch.write_package(
        "app",
        "fn main() -> Int { let x = show!(dep::value()); 0 }",
        "dep = { path = '../dep' }",
    );
    let output = scratch.check_manifest("app/Vastitas.toml");
    let message = expect_code(&output, "E_UNSUPPORTED");
    assert!(message.contains("dep/main.vast:2:"), "{message}");
    for source in [
        "mod inner { fn main() -> Int { let x = show!(1); x } }\nfn main() -> Int { 0 }",
        "resource fn main() -> Int { value { let x = show!(1); x } }",
    ] {
        let scratch = Scratch::empty("show modules");
        scratch.write_package("app", source, "");
        expect_code(
            &scratch.check_manifest("app/Vastitas.toml"),
            "E_UNSUPPORTED",
        );
    }
    // A package with the legacy geometry and no `[geometry_compat]` export
    // cannot use `show!`: its request carries no `legacy_geometry`, the
    // kernel rejects the legacy form, and the driver adds a note that names
    // `show!` as the cause.
    let scratch = Scratch::empty("show legacy package");
    scratch.write_package(
        "app",
        "fn main() -> Int {\n    let X = Affine(QQ, 2);\n    let n = show!(int(dim(X)));\n    0\n}",
        "",
    );
    let message = expect_code(&scratch.check_manifest("app/Vastitas.toml"), "E_TYPE");
    assert!(
        message.contains("main.vast:2:")
            && message.contains("note: help: a package that uses `show!` has the legacy geometry only with a `[geometry_compat]` export"),
        "{message}"
    );
    // Without `show!` the same package checks.
    scratch.write_package(
        "app",
        "fn main() -> Int {\n    let X = Affine(QQ, 2);\n    int(dim(X)) - 2\n}",
        "",
    );
    success(&scratch.check_manifest("app/Vastitas.toml"));
    // An object is no displayable value; the kernel names its type.
    let scratch = Scratch::empty("show object");
    scratch.copy_sources(
        &common::root().join("examples/packages/geometry/indexed"),
        "app",
        &[],
    );
    scratch.write(
        "app/main.vast",
        &checked_replace(
            &common::read(&common::root().join("examples/packages/geometry/indexed/main.vast")),
            "let packed = make(41);",
            "let object = show!(geo::affine(3));\n    let packed = make(41);",
        ),
    );
    let message = expect_code(&scratch.check_manifest("app/Vastitas.toml"), "E_TYPE");
    assert!(
        message.contains("`show!` cannot display a value of type"),
        "{message}"
    );
}

#[test]
fn show_adds_observations_to_the_flat_request_and_check_is_unchanged() {
    // Every flat unit is one package with the legacy geometry (#533); only
    // `show!` adds observations.
    let plain = flat_wire(
        "fn main() -> Int { let x = 1 + 1; x }",
        common::CURRENT_PROTOCOL,
    );
    assert!(plain.get("input").is_none(), "{plain}");
    assert_eq!(plain["legacy_geometry"], true);
    assert!(plain.to_string().find("observations").is_none());
    let mut observed = flat_wire(
        "fn helper() -> Int { 1 }\nfn main() -> Int { let x = helper(); let y = show!(x + 1); y }",
        common::CURRENT_PROTOCOL,
    );
    assert!(observed.get("input").is_none(), "{observed}");
    assert_eq!(
        function(&mut observed, "main")["observations"],
        json!([{ "statement": 1, "label": "x + 1" }])
    );
    // `vastitas check` prints its status line and nothing of the program.
    let scratch = Scratch::empty("show check");
    let path = scratch.write(FILE, "fn main() -> Int { let x = show!(41 + 1); 0 }");
    let output = cli().arg("check").arg(&path).output().unwrap();
    success(&output);
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        format!("checked {}\n", path.display())
    );
}

#[test]
fn the_kernel_refuses_tampered_observations() {
    let source = "fn helper() -> Int { let h = 1 + 1; h }\nfn main() -> Int { let f = helper; let x = show!(f() + 1); x }";
    let wire = flat_wire(source, common::CURRENT_PROTOCOL);
    for mode in ["check", "emit"] {
        assert_eq!(kernel(&wire, mode)["ok"], true, "{mode}");
    }
    let tampered = |change: &dyn Fn(&mut Value)| {
        let mut wire = wire.clone();
        change(&mut wire);
        wire
    };
    let cases: [(&str, Value, &str); 5] = [
        (
            "an observation outside main",
            tampered(&|wire| {
                let observations = function(wire, "main")
                    .as_object_mut()
                    .unwrap()
                    .remove("observations")
                    .unwrap();
                function(wire, "helper")["observations"] = observations;
                function(wire, "helper")["observations"][0]["statement"] = json!(0);
            }),
            "E_UNSUPPORTED",
        ),
        (
            "a function value",
            tampered(&|wire| function(wire, "main")["observations"][0]["statement"] = json!(0)),
            "E_TYPE",
        ),
        (
            "no such statement",
            tampered(&|wire| function(wire, "main")["observations"][0]["statement"] = json!(2)),
            "E_PROTOCOL",
        ),
        (
            "an empty list",
            tampered(&|wire| function(wire, "main")["observations"] = json!([])),
            "E_PROTOCOL",
        ),
        (
            "a foreign field",
            tampered(&|wire| function(wire, "main")["observations"][0]["type"] = json!("Int")),
            "E_PROTOCOL",
        ),
    ];
    for (name, wire, code) in cases {
        for mode in ["check", "emit"] {
            let response = kernel(&wire, mode);
            assert_eq!(response["ok"], false, "{name}: {response}");
            assert_eq!(
                response["diagnostics"][0]["code"], code,
                "{name}: {response}"
            );
            assert!(response.get("lean_source").is_none(), "{name}");
        }
    }
}

#[test]
fn observations_name_the_position_of_their_statement_among_all_statements() {
    let module = vastitas::frontend::parse(
        "fn main() -> Int {
    let a = 1;
    unpack a as { scheme: X, point: p };
    let b = show!(a   +
        1);
    let c = b;
    let d: Int = show!(c);
    0
}",
        FILE,
    )
    .unwrap();
    let observations: Vec<(usize, &str)> = module.functions[0]
        .observations
        .iter()
        .map(|observation| (observation.statement, observation.label.as_str()))
        .collect();
    assert_eq!(observations, [(2, "a + 1"), (4, "c")]);
    // The request sends the statements without `show!`.
    let request = serde_json::to_value(&module).unwrap();
    let statements = &request["functions"][0]["body"]["statements"];
    assert_eq!(statements[2]["value"]["kind"], "binary");
    assert_eq!(statements[4]["value"]["kind"], "variable");
}

/// #533 (#762): a package source that begins with `vastitas:compat:` is
/// reserved. The kernel accepts one only in the request of a flat unit that
/// `packages::flat_request` writes: its one package `legacy_flat`, which is the
/// root, without dependencies or `geometry_compat`, with one public root
/// module. Every other use, in that request or in a package request, is
/// `E_PROTOCOL`.
#[test]
fn compatibility_package_identities_are_reserved_for_the_flat_unit() {
    common::prepare_stdlib_package();
    let flat = flat_wire(
        "fn main() -> Int { let x = show!(1 + 1); x }",
        common::CURRENT_PROTOCOL,
    );
    assert_eq!(flat["packages"][0]["source"], "vastitas:compat:flat");
    assert_eq!(kernel(&flat, "check")["ok"], true, "{flat}");
    let manifest =
        |name: &str| common::root().join(format!("examples/packages/{name}/Vastitas.toml"));
    let package = captured_wire(
        common::manifest_command("check", manifest("hello")),
        common::CURRENT_PROTOCOL,
    );
    assert_eq!(kernel(&package, "check")["ok"], true, "{package}");
    let geometry = captured_wire(
        common::manifest_command("check", manifest("geometry-compat")),
        common::CURRENT_PROTOCOL,
    );
    let profile = geometry["packages"]
        .as_array()
        .unwrap()
        .iter()
        .find_map(|package| package.get("geometry_compat").cloned())
        .expect("a geometry_compat export");
    let changed = |wire: &Value, change: &dyn Fn(&mut Value)| {
        let mut wire = wire.clone();
        change(&mut wire);
        wire
    };
    let root_module = flat["packages"][0]["modules"][0].clone();
    let cases = [
        (
            "another name",
            changed(&flat, &|wire| {
                wire["packages"][0]["name"] = json!("other_flat")
            }),
        ),
        (
            "another version",
            changed(&flat, &|wire| {
                wire["packages"][0]["version"] = json!("2.0.0")
            }),
        ),
        (
            "another root",
            changed(&flat, &|wire| {
                wire["root"] = json!("/elsewhere/Vastitas.toml")
            }),
        ),
        (
            "a dependency",
            changed(&flat, &|wire| {
                wire["packages"][0]["dependencies"] =
                    json!([{"alias": "dep", "target": "vastitas:compat:flat"}])
            }),
        ),
        (
            "a geometry_compat export",
            changed(&flat, &|wire| {
                wire["packages"][0]["geometry_compat"] = profile.clone()
            }),
        ),
        (
            "a second module",
            changed(&flat, &|wire| {
                let mut inner = root_module.clone();
                inner["path"] = json!(["inner"]);
                inner["functions"] = json!([]);
                wire["packages"][0]["modules"]
                    .as_array_mut()
                    .unwrap()
                    .push(inner);
            }),
        ),
        (
            "a private root module",
            changed(&flat, &|wire| {
                wire["packages"][0]["modules"][0]["public"] = json!(false)
            }),
        ),
        (
            "a second package",
            changed(&flat, &|wire| {
                let other = package["packages"][0].clone();
                wire["packages"].as_array_mut().unwrap().push(other);
            }),
        ),
        (
            "a package with the profile's source",
            changed(&package, &|wire| {
                wire["root"] = json!("vastitas:compat:2-6");
                wire["packages"][0]["source"] = json!("vastitas:compat:2-6");
            }),
        ),
        (
            "a root with the flat source",
            changed(&package, &|wire| {
                wire["root"] = json!("vastitas:compat:flat")
            }),
        ),
        (
            "a dependency on the profile",
            changed(&package, &|wire| {
                wire["packages"][0]["dependencies"] =
                    json!([{"alias": "stolen", "target": "vastitas:compat:2-6"}])
            }),
        ),
    ];
    for (name, wire) in cases {
        for mode in ["check", "emit"] {
            let response = kernel(&wire, mode);
            common::assert_wire_rejected(&response, "E_PROTOCOL");
            let message = response["diagnostics"][0]["message"].as_str().unwrap();
            assert!(
                message.contains("is reserved for the compatibility packages of the kernel"),
                "{name} ({mode}): {message}"
            );
        }
    }
}
