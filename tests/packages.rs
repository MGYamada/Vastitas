//! End-to-end path packages, logical modules, source protection and native code.
mod common;
use common::{Scratch, success};
use std::fs;
use std::os::unix::fs::symlink;
use std::process::Output;

impl Scratch {
    fn package(&self, path: &str, source: &str, deps: &str) {
        self.write(&format!("{path}/Vastitas.toml"), &format!("[package]\nname = 'same-name'\nversion = '0.1.0'\nroot = 'src/main.vast'\n[dependencies]\n{deps}\n"));
        self.write(&format!("{path}/src/main.vast"), source);
    }
    fn check(&self) -> Output {
        self.check_manifest("app/Vastitas.toml")
    }
    fn rejects(&self, code: &str) -> String {
        let output = self.check();
        assert!(!output.status.success(), "accepted invalid package");
        common::expect_code(&output, code)
    }
    fn native(&self, expected: &str) {
        let stdout = self.check_build_and_run("app/Vastitas.toml");
        assert_eq!(String::from_utf8(stdout).unwrap(), format!("{expected}\n"));
    }
}

#[test]
fn path_aliases_reexports_and_higher_order_dispatch_execute() {
    let s = Scratch::empty("packages");
    s.package("lib", "mod inner { pub generic add(x, y) { domain (Int, Int); } method add(x: Int, y: Int) -> Int { x + y } pub fn next(x: Int) -> Int { add(x, 1) } } pub use inner::next; pub fn invoke(f: Fn<Int, Int>, x: Int) -> Int { f(x) }", "");
    s.package("app", "use math::next as increment; fn main() -> Int { let package = 40; let f: Fn<Int, Int> = if true { increment } else { alias::next }; math::invoke(f, f(package)) }", "math = { path = '../lib' }\nalias = { path = '../lib/.' }");
    s.native("42");
}

#[test]
fn distinct_locations_and_versions_never_merge_owners() {
    let s = Scratch::empty("packages");
    s.package("left", "pub fn value() -> Int { 10 }", "");
    s.package("right", "pub fn value() -> Int { 32 }", "");
    s.package(
        "app",
        "fn main() -> Int { left::value() + right::value() }",
        "left = { path = '../left' }\nright = { path = '../right' }",
    );
    s.native("42");
    s.write(
        "app/src/main.vast",
        "fn main() -> Int { let f = if true { left::value } else { right::value }; f() }",
    );
    s.rejects("E_STATIC_CALL");
    let manifest = fs::read_to_string(s.0.join("right/Vastitas.toml"))
        .unwrap()
        .replace("0.1.0", "1.0.0-beta.2+test");
    s.write("right/Vastitas.toml", &manifest);
    s.rejects("E_STATIC_CALL");
}

#[test]
fn inline_and_external_layouts_and_declaration_order_are_equivalent() {
    let s = Scratch::empty("packages");
    let source = "use math::value as answer; fn main() -> Int { answer() } ";
    s.package(
        "app",
        &format!("{source} mod math {{ pub fn value() -> Int {{ 42 }} }}"),
        "",
    );
    s.native("42");
    s.write("app/src/main.vast", &format!("mod math; {source}"));
    s.write(
        "app/src/math.vast",
        "pub fn value() -> Int { deep::answer() } mod deep;",
    );
    s.write("app/src/math/deep.vast", "pub fn answer() -> Int { 42 }");
    s.native("42");
    fs::create_dir_all(s.0.join("app/src/math")).unwrap();
    fs::rename(
        s.0.join("app/src/math.vast"),
        s.0.join("app/src/math/mod.vast"),
    )
    .unwrap();
    s.native("42");
    s.write("app/src/math.vast", "pub fn value() -> Int { 0 }");
    s.rejects("E_INPUT");
}

#[test]
fn private_paths_reexports_parent_lookup_and_shadowing_are_checked() {
    let s = Scratch::empty("packages");
    for (source, code) in [
        (
            "mod a { fn hidden() -> Int { 1 } } fn main() -> Int { a::hidden() }",
            "E_VISIBILITY",
        ),
        (
            "mod a { fn hidden() -> Int { 1 } pub use hidden as exposed; }",
            "E_VISIBILITY",
        ),
        (
            "fn value() -> Int { 1 } mod child { fn f() -> Int { value() } }",
            "E_NAME",
        ),
        ("use a as b; use b as a;", "E_CYCLE"),
        ("fn f() -> Int { 0 } use f as f;", "E_DUPLICATE"),
        ("mod a {} mod a {}", "E_DUPLICATE"),
        (
            "fn f() -> Int { 0 } fn main() -> Int { let f = 1; f }",
            "E_SHADOW",
        ),
        (
            "fn main() -> Int { let x = 1; let x = 2; x }",
            "E_DUPLICATE",
        ),
        ("mod a {} fn main() -> Int { a }", "E_NAME"),
        ("fn main() -> Int { use package::f; 0 }", "E_PARSE"),
        (
            "mod a { fn hidden() -> Int { 1 } } mod b { fn f() -> Int { package::a::hidden() } }",
            "E_VISIBILITY",
        ),
    ] {
        s.package("app", source, "");
        s.rejects(code);
    }
    s.package("app", "fn value() -> Int { 42 } mod child { pub mod nested { pub fn call() -> Int { super::super::value() } } } fn main() -> Int { child::nested::call() }", "");
    s.native("42");
}

/// `package` is no name of a module either. The diagnostic is at the name; the
/// kernel had only the span of the module, its `mod` item.
#[test]
fn a_module_cannot_be_named_package() {
    let s = Scratch::empty("packages");
    for (source, place) in [
        ("fn main() -> Int { 42 }\nmod package { }", "2:5"),
        ("fn main() -> Int { 42 }\nmod package;", "2:5"),
        ("fn main() -> Int { 42 }\npub mod package { }", "2:9"),
    ] {
        s.package("app", source, "");
        let error = s.rejects("E_RESERVED");
        let reported = format!(
            "app/src/main.vast:{place}: E_RESERVED: `package` is reserved as a path prefix and cannot be the name of a module\n"
        );
        assert!(error.ends_with(&reported), "{source}: {error}");
        assert_eq!(error.lines().count(), 1, "{source}: {error}");
    }
}

/// `package` is reserved as a name that `use` binds, so `use package;` is the
/// reserved name (`E_RESERVED`) at that name and not a cycle of imports. As a
/// path of one segment `package` is an ordinary name: `use package as root;`
/// names nothing (`E_NAME`), or the declaration `package` of the module.
#[test]
fn a_use_cannot_bind_the_name_package() {
    let s = Scratch::empty("packages");
    for (source, place) in [
        ("fn main() -> Int { 42 }\nuse package;", "2:5"),
        ("mod a { use package; }", "1:13"),
        ("fn f() -> Int { 1 }\nuse self::f as package;", "2:16"),
        (
            "mod a { pub fn package() -> Int { 1 } }\npub use a::package;",
            "2:12",
        ),
        ("fn f() -> Int { 1 }\nuse self::missing as package;", "2:22"),
    ] {
        s.package("app", source, "");
        let error = s.rejects("E_RESERVED");
        let reported = format!(
            "app/src/main.vast:{place}: E_RESERVED: `package` is reserved as a path prefix and cannot be a name that `use` binds\n"
        );
        assert!(error.ends_with(&reported), "{source}: {error}");
        assert_eq!(error.lines().count(), 1, "{source}: {error}");
    }
    s.package("app", "use package as root;", "");
    let error = s.rejects("E_NAME");
    assert!(
        error.ends_with("app/src/main.vast:1:1: E_NAME: undefined name 'package' in this module\n"),
        "{error}"
    );
    // A function may be named `package`, and a path of one segment names it.
    s.package(
        "app",
        "fn package() -> Int { 42 }\nuse package as root;\nfn main() -> Int { root() }",
        "",
    );
    s.native("42");
    // The kernel keeps its own check of the name for a request that the
    // frontend did not write.
    s.package(
        "app",
        "fn f() -> Int { 1 }\nuse self::f as other;\nfn main() -> Int { other() }",
        "",
    );
    let mut raw = common::captured_wire(
        s.cli()
            .args(["check", "--manifest-path", "app/Vastitas.toml"]),
        3,
    );
    let import = "/packages/0/modules/0/imports/0";
    assert_eq!(raw.pointer(import).unwrap()["alias"], "other");
    raw.pointer_mut(import).unwrap()["alias"] = "package".into();
    common::assert_wire_rejected(&common::kernel(&raw, "check"), "E_RESERVED");
    // `use package;` itself: the kernel prices the import before it checks
    // the name, and rejects the request either way.
    raw.pointer_mut(import).unwrap()["path"] = serde_json::json!(["package"]);
    assert_eq!(common::kernel(&raw, "check")["ok"], false);
}

const GEOMETRIC_OPERATIONS: [&str; 7] = [
    "Affine",
    "Base",
    "origin",
    "id",
    "compose",
    "apply",
    "dimension",
];

/// A module may take the name of one of the seven geometric operations, as
/// `nature::dimension`. Paths through it resolve, and the bare name in a call
/// stays the operation, even in the module that declares the module.
#[test]
fn a_module_may_take_the_name_of_a_geometric_operation() {
    let s = Scratch::empty("packages");
    for name in GEOMETRIC_OPERATIONS {
        s.package(
            "app",
            &format!(
                "mod {name} {{ pub fn value() -> Int {{ 42 }} }}\nfn main() -> Int {{ {name}::value() }}"
            ),
            "",
        );
        success(&s.check());
    }
    // All seven modules next to calls of all seven operations.
    s.package(
        "app",
        "mod Affine { pub fn size() -> Nat { 2 } }
mod Base {}
mod origin {}
mod id {}
mod compose {}
mod apply {}
mod dimension { pub fn extra() -> Int { 40 } }
fn main() -> Int {
    let X = Affine(QQ, Affine::size());
    let p: Point<X, Base(QQ)> = origin(X);
    let f = compose(id(X), id(X));
    let q: Point<X, Base(QQ)> = apply(f, p);
    dimension::extra() + int(dimension(X))
}",
        "",
    );
    s.native("42");
    // Paths through `self`, `super`, `package` and a dependency, a `use` of
    // an item of the module, and a `use` of the module under another name.
    s.package(
        "lib",
        "pub mod dimension;\npub fn helper() -> Int { dimension::length() }",
        "",
    );
    s.write("lib/src/dimension.vast", "pub fn length() -> Int { 10 }");
    s.package(
        "app",
        "mod dimension { pub fn width() -> Int { 1 } }
mod child { pub fn twice() -> Int { super::dimension::width() + package::dimension::width() } }
use dep::dimension::length;
use dep::dimension as dim;
fn main() -> Int {
    let X = Affine(QQ, 9);
    length() + dim::length() + dep::dimension::length() + child::twice()
        + self::dimension::width() + int(dimension(X))
}",
        "dep = { path = '../lib' }",
    );
    s.native("42");
}

/// The seven names stay reserved for every other declaration and binding:
/// functions, `let`, parameters, the name that a `use` binds and dependency
/// aliases. Other reserved names are no names of modules either.
#[test]
fn geometric_operation_names_stay_reserved_outside_modules() {
    let s = Scratch::empty("packages");
    s.package(
        "lib",
        "pub mod dimension { pub fn length() -> Int { 42 } }",
        "",
    );
    let dep = "dep = { path = '../lib' }";
    for (source, place, message) in [
        (
            "mod dimension {\n    pub fn dimension() -> Int { 2 }\n}",
            "2:12",
            "`dimension` is reserved for builtin geometry operations",
        ),
        (
            "fn main() -> Int {\n    let origin = 1;\n    origin\n}",
            "2:9",
            "`origin` is reserved for builtin geometry operations",
        ),
        (
            "fn f(apply: Int) -> Int { apply }",
            "1:6",
            "`apply` is reserved for builtin geometry operations",
        ),
        (
            "use dep::dimension::length as id;",
            "1:31",
            "`id` is reserved for builtin geometry operations",
        ),
        (
            "mod int {}",
            "1:5",
            "`int` is reserved for builtin Nat-to-Int conversion",
        ),
        (
            "mod Nat {}",
            "1:5",
            "`Nat` is reserved and cannot be used as a declaration or binding name",
        ),
        (
            "mod QQ {}",
            "1:5",
            "`QQ` is reserved and cannot be used as a declaration or binding name",
        ),
    ] {
        s.package("app", source, dep);
        let error = s.rejects("E_RESERVED");
        assert!(
            error.contains(&format!("app/src/main.vast:{place}: E_RESERVED: {message}")),
            "{source}: {error}"
        );
        assert_eq!(error.lines().count(), 1, "{source}: {error}");
    }
    // A `use` of the module itself binds the reserved name. The path may name
    // a module or an `indexed` declaration, so the parser cannot decide. Once
    // the packages are loaded, the frontend follows the path through modules,
    // dependency aliases and imports and reports a module at the name
    // (#759), also in a program with `indexed` declarations.
    let reserved = "E_RESERVED: `dimension` is reserved for builtin geometry operations; choose another declaration or binding name";
    for lib in [
        "pub mod dimension { pub fn length() -> Int { 42 } }",
        "pub indexed marker M;\npub mod dimension { pub fn length() -> Int { 42 } }",
    ] {
        s.package("lib", lib, "");
        for (source, place) in [
            (
                "use dep::dimension;\nfn main() -> Int { dimension::length() }",
                "1:10",
            ),
            (
                "mod units { pub mod dimension {} }\nuse self::units::dimension;\nfn main() -> Int { 0 }",
                "2:18",
            ),
            (
                "mod units { pub mod dimension {} }\nmod child { use super::units::dimension; }\nfn main() -> Int { 0 }",
                "2:31",
            ),
            (
                "mod units { pub mod dimension {} }\nmod child { use package::units::dimension; }\nfn main() -> Int { 0 }",
                "2:33",
            ),
            // Through the import of a dependency, and through a re-export.
            (
                "use dep as library;\nuse library::dimension;\nfn main() -> Int { 0 }",
                "2:14",
            ),
            (
                "mod units { pub use dep as library; }\nmod child { use super::units::library::dimension; }\nfn main() -> Int { 0 }",
                "2:40",
            ),
        ] {
            s.package("app", source, dep);
            let error = s.rejects("E_RESERVED");
            assert!(
                error.contains(&format!("app/src/main.vast:{place}: {reserved}")),
                "{lib}\n{source}: {error}"
            );
            assert_eq!(error.lines().count(), 1, "{source}: {error}");
        }
    }
    // A `use` without `as` of an `indexed` declaration binds its name.
    s.package(
        "lib",
        "pub indexed marker origin;\npub mod dimension { pub fn length() -> Int { 42 } }",
        "",
    );
    s.package(
        "app",
        "use dep::origin;\nuse dep::dimension::length;\nfn main() -> Int { length() }",
        dep,
    );
    success(&s.check());
    for alias in GEOMETRIC_OPERATIONS {
        s.package("lib", "pub fn value() -> Int { 1 }", "");
        s.package(
            "app",
            "fn main() -> Int { 0 }",
            &format!("{alias} = {{ path = '../lib' }}"),
        );
        let error = s.rejects("E_MANIFEST");
        assert!(
            error.contains(&format!("dependency alias '{alias}' is reserved")),
            "{error}"
        );
    }
}

/// The frontend follows the path of a `use` of a reserved name through a
/// bounded number of imports (#759). A longer chain of distinct aliases is
/// left to the kernel, which checks every `use` itself within its own work
/// bounds, so the frontend never exhausts its stack on such a program.
#[test]
fn a_long_chain_of_imports_is_left_to_the_kernel() {
    let s = Scratch::empty("packages");
    const CHAIN: usize = 20_000;
    let mut source = String::from("mod units { pub mod dimension {} }\n");
    source.push_str(&format!("use self::units as a{CHAIN};\n"));
    for i in (0..CHAIN).rev() {
        source.push_str(&format!("use a{} as a{i};\n", i + 1));
    }
    source.push_str("use a0::dimension;\nfn main() -> Int { 0 }\n");
    s.package("app", &source, "");
    let output = s.check();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{stderr}");
    assert!(
        stderr.contains("E_RESERVED") || stderr.contains("E_LIMIT"),
        "{stderr}"
    );
}

/// The kernel decides module names independently of the frontend: it
/// accepts a module named after a geometric operation and rejects the other
/// reserved names of modules, a function of such a name and a `use` that binds
/// one, to a module or with `as` to an `indexed` declaration, in a request
/// that the frontend did not write.
#[test]
fn the_kernel_checks_geometric_module_names_independently() {
    let s = Scratch::empty("packages");
    s.package(
        "app",
        "mod dimension { pub fn value() -> Int { 42 } }\nmod units { pub mod length { pub fn value() -> Int { 1 } } }\nuse units::length as metres;\nfn main() -> Int { dimension::value() + metres::value() - 1 }",
        "",
    );
    let raw = common::captured_wire(
        s.cli()
            .args(["check", "--manifest-path", "app/Vastitas.toml"]),
        3,
    );
    assert_eq!(common::kernel(&raw, "check")["ok"], true, "{raw}");
    let modules = raw["packages"][0]["modules"].as_array().unwrap();
    let at = |path: serde_json::Value| {
        modules
            .iter()
            .position(|module| module["path"] == path)
            .unwrap()
    };
    let dimension = at(serde_json::json!(["dimension"]));
    let root = at(serde_json::json!([]));
    // Other reserved names of modules.
    for name in ["int", "Nat", "QQ", "self"] {
        let mut forged = raw.clone();
        forged["packages"][0]["modules"][dimension]["path"] = serde_json::json!([name]);
        common::assert_wire_rejected(&common::kernel(&forged, "check"), "E_RESERVED");
    }
    // A function of a geometric operation's name.
    let mut forged = raw.clone();
    forged["packages"][0]["modules"][dimension]["functions"][0]["name"] = "dimension".into();
    common::assert_wire_rejected(&common::kernel(&forged, "check"), "E_RESERVED");
    // A `use` that binds a geometric operation's name to a module.
    let mut forged = raw;
    let import = &mut forged["packages"][0]["modules"][root]["imports"][0];
    assert_eq!(import["alias"], "metres");
    import["alias"] = "origin".into();
    common::assert_wire_rejected(&common::kernel(&forged, "check"), "E_RESERVED");
    // #759: a `use … as` that binds a reserved spelling to an `indexed`
    // declaration. Only a `use` without `as`, whose alias is the last segment
    // of its path, binds such a name; the request has no other error.
    s.package("lib", "pub indexed marker dimension;", "");
    s.package(
        "app",
        "use dep::dimension as measure;\nfn main() -> Int { 42 }",
        "dep = { path = '../lib' }",
    );
    let raw = common::captured_wire(
        s.cli()
            .args(["check", "--manifest-path", "app/Vastitas.toml"]),
        7,
    );
    assert_eq!(common::kernel(&raw, "check")["ok"], true, "{raw}");
    let app = raw["packages"]
        .as_array()
        .unwrap()
        .iter()
        .position(|package| package["source"] == raw["root"])
        .unwrap();
    let root = raw["packages"][app]["modules"]
        .as_array()
        .unwrap()
        .iter()
        .position(|module| module["path"] == serde_json::json!([]))
        .unwrap();
    for alias in [
        "dimension",
        "origin",
        "compose",
        "id",
        "Base",
        "Point",
        "QQ",
    ] {
        let mut forged = raw.clone();
        let import = &mut forged["packages"][app]["modules"][root]["imports"][0];
        assert_eq!(import["alias"], "measure");
        import["alias"] = alias.into();
        for mode in ["check", "emit"] {
            let response = common::kernel(&forged, mode);
            if alias == "dimension" {
                // The request of `use dep::dimension;`.
                assert_eq!(response["ok"], true, "{response}");
            } else {
                common::assert_wire_rejected(&response, "E_RESERVED");
            }
        }
    }
}

#[test]
fn only_exact_generic_owner_can_add_methods() {
    let s = Scratch::empty("packages");
    s.package(
        "lib",
        "pub generic g() { domain (); } method g() -> Int { 42 }",
        "",
    );
    for source in [
        "method dep::g() -> Int { 1 }",
        "use dep::g as borrowed; method borrowed() -> Int { 1 }",
        "generic g() { domain (); } mod child { method super::g() -> Int { 1 } }",
        "fn f() -> Int { 0 } method f() -> Int { 1 }",
    ] {
        s.package("app", source, "dep = { path = '../lib' }");
        s.rejects("E_OWNER");
    }
    s.package("app", "pub generic g() { domain (); } use g as alias; method alias() -> Int { 21 } fn main() -> Int { g() + g() }", "");
    s.native("42");
}

#[test]
fn unused_inputs_captures_and_recursion_are_not_hidden() {
    let s = Scratch::empty("packages");
    s.package("lib", "fn unused() -> Int { true }", "");
    s.package("app", "fn main() -> Int { 0 }", "dep = { path = '../lib' }");
    let error = s.rejects("E_TYPE");
    assert!(error.contains("lib/src/main.vast:1:"), "{error}");
    for (source, code) in [
        (
            "fn main() -> Int { let x = 1; let f = fn() -> Int { x }; f() }",
            "E_CAPTURE",
        ),
        (
            "mod a { pub fn f() -> Int { super::main() } } fn main() -> Int { a::f() }",
            "E_RECURSION",
        ),
        (
            "generic g(x) { domain (Int); } method g(x: Any) -> Int { x + true } method g(x: Int) -> Int { x }",
            "E_TYPE",
        ),
        (
            "fn main() -> Int { let f: Fn<Scheme, Int> = fn(x: Scheme) -> Int { 0 }; 0 }",
            "E_TYPE",
        ),
    ] {
        s.package("app", source, "");
        s.rejects(code);
    }
}

#[test]
fn manifest_validation_and_cli_modes_are_explicit() {
    let s = Scratch::empty("packages");
    s.package("app", "fn helper() -> Int { 1 }", "");
    success(&s.check());
    let out = s
        .cli()
        .args([
            "build",
            "--manifest-path",
            "app/Vastitas.toml",
            "-o",
            "result",
        ])
        .output()
        .unwrap();
    common::expect_code(&out, "E_MAIN");
    for args in [
        vec!["check"],
        vec![
            "check",
            "--manifest-path",
            "app/Vastitas.toml",
            "app/src/main.vast",
        ],
        vec![
            "check",
            "--manifest-path",
            "app/Vastitas.toml",
            "--lib",
            "app/src/main.vast",
        ],
        vec![
            "check",
            "--manifest-path",
            "app/Vastitas.toml",
            "--manifest-path",
            "app/Vastitas.toml",
        ],
    ] {
        let out = s.cli().args(args).output().unwrap();
        common::expect_code(&out, "E_USAGE");
    }
    for text in [
        "[package]\nname='test'\nroot='src/main.vast'",
        "[package]\nname='test'\nversion='1.2'\nroot='src/main.vast'",
        "[package]\nname='test'\nversion='1.2.3'\nroot='src/main.vast'\n[dependencies]\na={git='https://example.invalid'}",
    ] {
        s.write("app/Vastitas.toml", text);
        s.rejects("E_MANIFEST");
    }
}

#[test]
fn dependency_cycles_collisions_and_main_selection_are_checked() {
    let s = Scratch::empty("packages");
    s.package("lib", "pub fn main() -> Int { 42 }", "");
    s.package("app", "use dep::main;", "dep = { path = '../lib' }");
    success(&s.check());
    let out = s
        .cli()
        .args([
            "build",
            "--manifest-path",
            "app/Vastitas.toml",
            "-o",
            "result",
        ])
        .output()
        .unwrap();
    common::expect_code(&out, "E_MAIN");
    s.write("app/src/main.vast", "mod dep {} ");
    s.rejects("E_DUPLICATE");
    s.package("lib", "", "app = { path = '../app' }");
    s.rejects("E_CYCLE");
}

#[test]
fn filesystem_escape_and_module_loading_cycles_are_rejected() {
    let s = Scratch::empty("packages");
    s.package("app", "mod escaped;", "");
    s.write("outside.vast", "pub fn value() -> Int { 42 }");
    symlink(s.0.join("outside.vast"), s.0.join("app/src/escaped.vast")).unwrap();
    s.rejects("E_INPUT");
    s.write("app/src/main.vast", "mod cycle;");
    fs::hard_link(
        s.0.join("app/src/main.vast"),
        s.0.join("app/src/cycle.vast"),
    )
    .unwrap();
    s.rejects("E_CYCLE");
    s.write(
        "app/Vastitas.toml",
        "[package]\nname='test'\nversion='1.2.3'\nroot='../outside.vast'",
    );
    s.rejects("E_INPUT");
}

#[test]
fn package_diagnostics_preserve_main_and_identify_the_declaring_manifest() {
    let s = Scratch::empty("packages");
    s.package("app", "fn main(x: Int) -> Int { x }", "");
    let error = s.rejects("E_MAIN");
    assert!(
        error.contains("entry point must have signature fn main() -> Int"),
        "{error}"
    );
    assert!(!error.contains("same-name::main"), "{error}");
    s.package("leaf", "pub fn value() -> Int { 1 }", "");
    for alias in [
        "int",
        "fn",
        "self",
        "Nat",
        "generic",
        "package",
        "__vastitas_hidden",
    ] {
        s.package(
            "lib",
            "pub fn value() -> Int { 1 }",
            &format!("{alias} = {{ path = '../leaf' }}"),
        );
        s.package("app", "fn main() -> Int { 0 }", "dep = { path = '../lib' }");
        let error = s.rejects("E_MANIFEST");
        assert!(error.contains("lib/Vastitas.toml:"), "{error}");
        assert!(
            error.contains(&format!("dependency alias '{alias}' is reserved")),
            "{error}"
        );
    }
}

#[test]
fn package_lambdas_preserve_the_enclosing_shadowing_ban() {
    let s = Scratch::empty("packages");
    for source in [
        "fn main() -> Int { let x = 41; let f = fn(x: Int) -> Int { x + 1 }; f(x) }",
        "fn main() -> Int { let x = 41; let f = fn() -> Int { let x = 1; x }; f() }",
    ] {
        s.package("app", source, "");
        s.rejects("E_SHADOW");
    }
}

#[test]
fn all_manifests_and_module_sources_are_protected_from_output() {
    let s = Scratch::empty("packages");
    s.package("lib", "pub fn value() -> Int { 42 }", "");
    s.package(
        "app",
        "mod math; fn main() -> Int { math::value() }",
        "dep = { path = '../lib' }",
    );
    s.write(
        "app/src/math.vast",
        "pub fn value() -> Int { dep::value() }",
    );
    for (i, input) in [
        "app/Vastitas.toml",
        "lib/Vastitas.toml",
        "app/src/main.vast",
        "app/src/math.vast",
        "lib/src/main.vast",
    ]
    .iter()
    .enumerate()
    {
        let before = fs::read(s.0.join(input)).unwrap();
        let link = format!("hard{i}");
        let symbolic = format!("symbolic{i}");
        fs::hard_link(s.0.join(input), s.0.join(&link)).unwrap();
        symlink(s.0.join(input), s.0.join(&symbolic)).unwrap();
        for output in [input.to_string(), format!("./{input}"), link, symbolic] {
            let out = s
                .cli()
                .args([
                    "build",
                    "--manifest-path",
                    "app/Vastitas.toml",
                    "-o",
                    &output,
                ])
                .env("VASTITAS_KERNEL", "/nonexistent/kernel")
                .output()
                .unwrap();
            assert!(
                String::from_utf8_lossy(&out.stderr).contains("E_OUTPUT:"),
                "{:?}",
                out
            );
            assert_eq!(fs::read(s.0.join(input)).unwrap(), before);
        }
    }
    // Protection precedes parsing, even when the protected input is malformed.
    for input in ["app/src/math.vast", "app/Vastitas.toml"] {
        s.write(input, "invalid input");
        let out = s
            .cli()
            .args(["build", "--manifest-path", "app/Vastitas.toml", "-o", input])
            .env("VASTITAS_KERNEL", "/nonexistent/kernel")
            .output()
            .unwrap();
        assert!(
            String::from_utf8_lossy(&out.stderr).contains("E_OUTPUT:"),
            "{:?}",
            out
        );
        assert_eq!(
            fs::read_to_string(s.0.join(input)).unwrap(),
            "invalid input"
        );
    }
}

#[test]
fn dependent_geometry_survives_namespaces_and_unpack() {
    let s = Scratch::empty("packages");
    s.package("app", "mod geometry { pub fn retain(X: Scheme, p: Point<X, Base(QQ)>) -> Pointed<Scheme, QQ> { pack { scheme: X, point: p } } } fn main() -> Int { let X = Affine(QQ, 42); let p = origin(X); let parcel = geometry::retain(X, p); unpack parcel as { scheme: Y, point: q }; int(dimension(Y)) }", "");
    s.native("42");
}

#[test]
fn namespace_diagnostics_render_source_names_and_keep_locations() {
    let s = Scratch::empty("packages");
    s.package(
        "app",
        "mod a { pub fn f() -> Int { super::main() } } fn main() -> Int { a::f() }",
        "",
    );
    let error = s.rejects("E_RECURSION");
    assert!(error.contains("same-name::a::f"), "{error}");
    assert!(!error.contains("ns_f_"), "{error}");
    s.write(
        "app/src/main.vast",
        "fn main() -> Int { let ns_b_x = 1; let f = fn() -> Int { ns_b_x }; f() }",
    );
    let error = s.rejects("E_CAPTURE");
    assert!(error.contains("'ns_b_x'"), "{error}");
    assert!(!error.contains("ns_b_ns_b_x"), "{error}");
    assert!(error.contains("main.vast:1:"), "{error}");
}

#[test]
fn package_requests_do_not_fall_back_to_a_protocol_two_backend() {
    use std::os::unix::fs::PermissionsExt;
    let s = Scratch::empty("packages");
    s.package("app", "fn main() -> Int { 42 }", "");
    let backend = s.0.join("old-backend");
    fs::write(
        &backend,
        "#!/bin/sh\ncat >/dev/null\nprintf '{\"version\":2,\"ok\":true}\\n'\n",
    )
    .unwrap();
    fs::set_permissions(&backend, fs::Permissions::from_mode(0o755)).unwrap();
    let out = s
        .cli()
        .args(["check", "--manifest-path", "app/Vastitas.toml"])
        .env("VASTITAS_KERNEL", backend)
        .output()
        .unwrap();
    assert!(!out.status.success());
    common::expect_code(&out, "E_PROTOCOL");
}

#[test]
fn duplicate_owners_point_to_the_declaring_external_source() {
    let s = Scratch::empty("packages");
    s.package("app", "mod math; fn main() -> Int { 0 }", "");
    s.write(
        "app/src/math.vast",
        "fn f() -> Int { 0 }\nfn f() -> Int { 1 }\n",
    );
    let error = s.rejects("E_DUPLICATE");
    assert!(error.contains("math.vast:2:1:"), "{error}");
}

/// #747: an error of the names of a module is at the second declaration of
/// the name, in the file that holds it, with a note at the first. It is not
/// at the declaration of the module in the parent's file.
#[test]
fn name_errors_of_a_module_point_to_the_second_declaration() {
    let s = Scratch::empty("packages");
    // Each case gives the root source, its module `a` if any, and the
    // expected lines: the place of the error and of its note, if any.
    let cases: &[(&str, Option<&str>, &str, &[&str])] = &[
        // A `use` after a function of its name, in a module file.
        (
            "fn main() -> Int { 42 }\nmod a;\n",
            Some(
                "\n\npub fn q() -> Int { 1 }\nmod m { pub fn f() -> Int { 1 } }\nuse m::f as q;\n",
            ),
            "E_DUPLICATE",
            &[
                "a.vast:5:1: E_DUPLICATE: 'q' is already the name of a function of this module",
                "a.vast:3:5: note: first declaration is here",
            ],
        ),
        // The same in an inline module.
        (
            "fn main() -> Int { 42 }\n\n  mod a {\n    pub fn q() -> Int { 1 }\n    mod m { pub fn f() -> Int { 1 } }\n    use m::f as q;\n  }\n",
            None,
            "E_DUPLICATE",
            &[
                "main.vast:6:5: E_DUPLICATE:",
                "main.vast:4:9: note: first declaration is here",
            ],
        ),
        // A function after a `use` of its name.
        (
            "fn main() -> Int { 42 }\nmod a;\n",
            Some("mod m { pub fn f() -> Int { 1 } }\nuse m::f as q;\n\npub fn q() -> Int { 1 }\n"),
            "E_DUPLICATE",
            &[
                "a.vast:4:5: E_DUPLICATE: 'q' is already the name of an import of this module",
                "a.vast:2:1: note: first declaration is here",
            ],
        ),
        // Two items of one name and of two kinds: at the second in the file.
        (
            "fn main() -> Int { 42 }\n\ngeneric g(x) { domain (Int); }\nmethod g(x: Int) -> Int { x }\nfn g() -> Int { 1 }\n",
            None,
            "E_DUPLICATE",
            &[
                "main.vast:5:1: E_DUPLICATE:",
                "main.vast:3:1: note: first declaration is here",
            ],
        ),
        (
            "fn main() -> Int { 42 }\nmod a;\n",
            Some("fn m() -> Int { 1 }\nmod m { pub fn f() -> Int { 1 } }\n"),
            "E_DUPLICATE",
            &[
                "a.vast:2:1: E_DUPLICATE:",
                "a.vast:1:1: note: first declaration is here",
            ],
        ),
        // A reserved name of an `indexed` declaration of a module file. The
        // frontend reports it at the name (#736).
        (
            "fn main() -> Int { 42 }\n\n  mod a;\n",
            Some("pub indexed marker QQ;\npub indexed marker Nat;\n"),
            "E_RESERVED",
            &[
                "a.vast:2:20: E_RESERVED: `Nat` is reserved and cannot be used as a declaration or binding name",
            ],
        ),
    ];
    for (root, module, code, expected) in cases {
        s.package("app", root, "");
        let _ = fs::remove_file(s.0.join("app/src/a.vast"));
        if let Some(module) = module {
            s.write("app/src/a.vast", module);
        }
        let error = s.rejects(code);
        let lines: Vec<&str> = error.lines().collect();
        assert_eq!(lines.len(), expected.len(), "{error}");
        for (line, expected) in lines.iter().zip(expected.iter()) {
            assert!(
                line.contains(&format!("/src/{expected}")),
                "{expected:?} in {error}"
            );
        }
    }
    // A function of the name of a dependency alias: at the function, and with
    // no note, because a manifest declares the alias.
    s.package("dep", "", "");
    s.package(
        "app",
        "fn main() -> Int { 42 }\nmod a;\n",
        "d = { path = '../dep' }",
    );
    s.write("app/src/a.vast", "\n\nfn d() -> Int { 1 }\n");
    let error = s.rejects("E_DUPLICATE");
    assert_eq!(error.lines().count(), 1, "{error}");
    assert!(
        error.contains(
            "/app/src/a.vast:3:1: E_DUPLICATE: 'd' is already the name of a dependency alias of this package"
        ),
        "{error}"
    );
}

/// #747: `mod`, `use`, `pub`, `self` and `super` are reserved in flat mode
/// too. The frontend reports them at the name, as in manifest mode, and the
/// kernel, which rejects them as well, is never reached. The cases of
/// `tests/fixtures/frontend-diagnostics.json` give the places without a
/// kernel; this test checks a declaration and a `let` with the kernel.
#[test]
fn reserved_module_words_in_flat_mode_point_to_the_name() {
    let s = Scratch::empty("packages");
    for (source, place, word) in [
        (
            "fn main() -> Int { 0 }\n\nfn mod() -> Int { 1 }\n",
            "3:4",
            "mod",
        ),
        (
            "fn main() -> Int {\n    let use = 1;\n    0\n}\n",
            "2:9",
            "use",
        ),
    ] {
        let file = s.write("flat.vast", source);
        let output = s.cli().arg("check").arg(&file).output().unwrap();
        let error = common::expect_code(&output, "E_RESERVED");
        assert!(
            error.starts_with(&format!(
                "{}:{place}: E_RESERVED: `{word}` is reserved",
                file.display()
            )),
            "{error}"
        );
    }
}
