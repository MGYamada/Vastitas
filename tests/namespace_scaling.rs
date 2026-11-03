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
            assert!(String::from_utf8_lossy(&output.stderr).contains("E_TYPE"));
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
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(code),
            "expected {code}: {output:?}"
        );
    }
}
