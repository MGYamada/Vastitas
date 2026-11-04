mod common;
use common::{Scratch, cli, success};

fn source(imports: usize, references: usize) -> String {
    let mut source = String::new();
    for i in 0..imports {
        source.push_str(&format!("use self::a{} as a{i};\n", i + 1));
    }
    source.push_str(&format!(
        "fn a{imports}(x: Int) -> Int {{ x + 1 }}\nfn main() -> Int {{\n"
    ));
    for i in 0..references {
        source.push_str(&format!("let v{i} = a0(41);\n"));
    }
    source.push_str(&format!("v{}\n}}\n", references - 1));
    source
}

fn fixture(source: &str) -> Scratch {
    let s = Scratch::empty("namespace scaling");
    s.write(
        "Vastitas.toml",
        "[package]\nname='scale'\nversion='0.1.0'\nroot='main.vast'\n",
    );
    s.write("main.vast", source);
    s
}

fn check(s: &Scratch) -> std::process::Output {
    cli()
        .args(["check", "--manifest-path"])
        .arg(s.0.join("Vastitas.toml"))
        .output()
        .unwrap()
}

#[test]
fn long_import_chains_preserve_static_targets_and_unused_body_checks() {
    for (imports, references) in [(250, 1), (500, 1), (1000, 1), (600, 300)] {
        let source = source(imports, references);
        let s = fixture(&source);
        success(&check(&s));
        if references == 300 {
            success(
                &cli()
                    .args(["build", "--manifest-path"])
                    .arg(s.0.join("Vastitas.toml"))
                    .arg("-o")
                    .arg(s.0.join("program"))
                    .output()
                    .unwrap(),
            );
            let output = std::process::Command::new(s.0.join("program"))
                .output()
                .unwrap();
            success(&output);
            assert_eq!(output.stdout, b"42\n");
            s.write("main.vast", &(source + "fn unused() -> Int { true }\n"));
            let output = check(&s);
            assert!(!output.status.success());
            common::expect_code(&output, "E_TYPE");
        }
    }
}

#[test]
fn long_cycles_and_resolution_depth_still_fail_closed() {
    let cyclic = source(1000, 1).replace(
        "fn a1000(x: Int) -> Int { x + 1 }",
        "use self::a0 as a1000;",
    );
    for (source, code) in [(cyclic, "E_CYCLE"), (source(1500, 1), "E_LIMIT")] {
        let output = check(&fixture(&source));
        assert!(!output.status.success());
        common::expect_code(&output, code);
    }
}

fn assert_limit(s: &Scratch, message: &str) {
    let output = check(s);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{stderr}");
    common::assert_first_code(&stderr, "E_LIMIT");
    assert!(stderr.contains(message), "{stderr}");
}

#[test]
fn separate_modules_share_the_import_validation_budget() {
    let mut source = String::new();
    for module in ["left", "right"] {
        source.push_str(&format!("mod {module} {{\n"));
        for i in 0..1050 {
            source.push_str(&format!("use self::a{} as a{i};\n", i + 1));
        }
        source.push_str("fn a1050() -> Int { 42 }\n}\n");
    }
    source.push_str("fn main() -> Int { 42 }\n");
    // The existing positive control admits a complete 1,000-link chain.
    for profile in [
        "",
        "indexed marker BudgetMarker;\n",
        "resource fn spare() -> Unit { value { () } }\n",
    ] {
        let package = fixture(&format!("{profile}{source}"));
        assert_limit(&package, "program-wide namespace import validation");
    }
}

#[test]
fn alias_queries_in_unused_functions_share_the_request_budget() {
    let mut program = source(600, 1);
    let mut body = String::new();
    for i in 0..100 {
        body.push_str(&format!("let v{i} = a0(41);\n"));
    }
    for i in 0..24 {
        program.push_str(&format!("fn f{i}() -> Int {{\n{body}v99\n}}\n"));
    }
    let s = fixture(&program);
    assert_limit(&s, "program-wide namespace resolution");
    let previous = s.write("program", "previous output");
    let output = cli()
        .args(["build", "--manifest-path"])
        .arg(s.0.join("Vastitas.toml"))
        .arg("-o")
        .arg(&previous)
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{stderr}");
    common::assert_first_code(&stderr, "E_LIMIT");
    assert_eq!(std::fs::read(previous).unwrap(), b"previous output");
}

// A root with many dependencies that all depend on one shared package. Each
// manifest is loaded once, with a constant-time loaded-package lookup (#532).
#[test]
fn wide_diamond_dependency_closures_load_shared_packages_once() {
    let width = 1000;
    let s = Scratch::empty("diamond scaling");
    let manifest = |name: &str, dependencies: &str| {
        format!(
            "[package]\nname='{name}'\nversion='0.1.0'\nroot='main.vast'\n[dependencies]\n{dependencies}"
        )
    };
    s.write("shared/Vastitas.toml", &manifest("shared", ""));
    s.write("shared/main.vast", "pub fn one() -> Int { 1 }\n");
    let mut dependencies = String::new();
    for i in 0..width {
        s.write(
            &format!("d{i}/Vastitas.toml"),
            &manifest(&format!("d{i}"), "shared = { path = '../shared' }\n"),
        );
        s.write(
            &format!("d{i}/main.vast"),
            &format!("pub fn value() -> Int {{ shared::one() + {i} }}\n"),
        );
        dependencies.push_str(&format!("d{i} = {{ path = '../d{i}/.' }}\n"));
    }
    s.write("app/Vastitas.toml", &manifest("app", &dependencies));
    s.write(
        "app/main.vast",
        &format!(
            "fn main() -> Int {{ d0::value() + d{}::value() - {} }}\n",
            width - 1,
            width - 41
        ),
    );
    let start = std::time::Instant::now();
    success(
        &cli()
            .args(["build", "--manifest-path"])
            .arg(s.0.join("app/Vastitas.toml"))
            .arg("-o")
            .arg(s.0.join("program"))
            .output()
            .unwrap(),
    );
    eprintln!("built a {width}-wide diamond in {:?}", start.elapsed());
    let output = std::process::Command::new(s.0.join("program"))
        .output()
        .unwrap();
    success(&output);
    assert_eq!(output.stdout, b"42\n");
}
