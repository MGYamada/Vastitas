//! End-to-end path packages, logical modules, source protection and native code.
use std::fs;
use std::os::unix::fs::symlink;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static SERIAL: AtomicU64 = AtomicU64::new(0);
struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "vastitas packages {} {}",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, path: &str, text: &str) {
        let file = self.0.join(path);
        fs::create_dir_all(file.parent().unwrap()).unwrap();
        fs::write(file, text).unwrap();
    }
    fn package(&self, path: &str, source: &str, deps: &str) {
        self.write(&format!("{path}/Vastitas.toml"), &format!("[package]\nname = 'same-name'\nversion = '0.1.0'\nroot = 'src/main.vast'\n[dependencies]\n{deps}\n"));
        self.write(&format!("{path}/src/main.vast"), source);
    }
    fn cli(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_vastitas"));
        command.current_dir(&self.0);
        command
    }
    fn check(&self) -> Output {
        self.cli()
            .args(["check", "--manifest-path", "app/Vastitas.toml"])
            .output()
            .unwrap()
    }
    fn rejects(&self, code: &str) -> String {
        let output = self.check();
        assert!(!output.status.success(), "accepted invalid package");
        let error = String::from_utf8(output.stderr).unwrap();
        assert!(
            error.contains(&format!("{code}:")),
            "expected {code}: {error}"
        );
        error
    }
    fn native(&self, expected: &str) {
        success(&self.check());
        success(
            &self
                .cli()
                .args([
                    "build",
                    "--manifest-path",
                    "app/Vastitas.toml",
                    "-o",
                    "native",
                ])
                .output()
                .unwrap(),
        );
        let output = Command::new(self.0.join("native")).output().unwrap();
        success(&output);
        assert_eq!(
            String::from_utf8(output.stdout).unwrap(),
            format!("{expected}\n")
        );
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn success(output: &Output) {
    assert!(
        output.status.success(),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn path_aliases_reexports_and_higher_order_dispatch_execute() {
    let s = Scratch::new();
    s.package("lib", "mod inner { pub generic add(x, y) { domain (Int, Int); } method add(x: Int, y: Int) -> Int { x + y } pub fn next(x: Int) -> Int { add(x, 1) } } pub use inner::next; pub fn invoke(f: Fn<Int, Int>, x: Int) -> Int { f(x) }", "");
    s.package("app", "use math::next as increment; fn main() -> Int { let package = 40; let f: Fn<Int, Int> = if true { increment } else { alias::next }; math::invoke(f, f(package)) }", "math = { path = '../lib' }\nalias = { path = '../lib/.' }");
    s.native("42");
}

#[test]
fn distinct_locations_and_versions_never_merge_owners() {
    let s = Scratch::new();
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
    let s = Scratch::new();
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
    let s = Scratch::new();
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

#[test]
fn only_exact_generic_owner_can_add_methods() {
    let s = Scratch::new();
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
    let s = Scratch::new();
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
    let s = Scratch::new();
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
    assert!(String::from_utf8_lossy(&out.stderr).contains("E_MAIN"));
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
        assert!(String::from_utf8_lossy(&out.stderr).contains("E_USAGE"));
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
    let s = Scratch::new();
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
    assert!(String::from_utf8_lossy(&out.stderr).contains("E_MAIN"));
    s.write("app/src/main.vast", "mod dep {} ");
    s.rejects("E_DUPLICATE");
    s.package("lib", "", "app = { path = '../app' }");
    s.rejects("E_CYCLE");
}

#[test]
fn filesystem_escape_and_module_loading_cycles_are_rejected() {
    let s = Scratch::new();
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
fn all_manifests_and_module_sources_are_protected_from_output() {
    let s = Scratch::new();
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
    let s = Scratch::new();
    s.package("app", "mod geometry { pub fn retain(X: Scheme, p: Point<X, Base(QQ)>) -> Pointed<Scheme, QQ> { pack { scheme: X, point: p } } } fn main() -> Int { let X = Affine(QQ, 42); let p = origin(X); let parcel = geometry::retain(X, p); unpack parcel as { scheme: Y, point: q }; int(dimension(Y)) }", "");
    s.native("42");
}

#[test]
fn namespace_diagnostics_render_source_names_and_keep_locations() {
    let s = Scratch::new();
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
    let s = Scratch::new();
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
    assert!(String::from_utf8_lossy(&out.stderr).contains("E_PROTOCOL:"));
}

#[test]
fn duplicate_owners_point_to_the_declaring_external_source() {
    let s = Scratch::new();
    s.package("app", "mod math; fn main() -> Int { 0 }", "");
    s.write(
        "app/src/math.vast",
        "fn f() -> Int { 0 }\nfn f() -> Int { 1 }\n",
    );
    let error = s.rejects("E_DUPLICATE");
    assert!(error.contains("math.vast:2:1:"), "{error}");
}
