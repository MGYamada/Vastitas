mod common;

use common::{Scratch, cli, success};
use std::fmt::Write;

fn fixture(runtime: bool, depth: usize, called: bool) -> Scratch {
    let project = Scratch::empty("resource work budget");
    project.write(
        "Vastitas.toml",
        "[package]\nname='work'\nversion='0.1.0'\nroot='main.vast'\n",
    );
    let mut source = String::from("resource fn leaf() -> Unit {\n");
    if runtime {
        source.push_str("runtime_allocate d: F64[1] runtime_layout(1,1,1,false);\n");
        source.push_str(
            "runtime_borrow w = write(d); runtime_fill(w, f64_bits(0)); runtime_release(w);\n",
        );
    } else {
        source.push_str("allocate d: F64[1]; borrow w = write(d, layout(0,1,1,1,false));\n");
        source.push_str("fill(w, f64_bits(0)); release(w);\n");
    }
    let prefix = if runtime { "runtime_" } else { "" };
    let view = if runtime {
        ""
    } else {
        ", layout(0,1,1,1,false)"
    };
    for i in 0..200 {
        writeln!(source, "{prefix}borrow r{i} = read(d{view});").unwrap();
    }
    for i in (0..200).rev() {
        writeln!(source, "{prefix}release(r{i});").unwrap();
    }
    writeln!(source, "{prefix}drop(d); value {{ () }} }}").unwrap();
    let mut callee = String::from("leaf");
    for i in 0..depth {
        writeln!(
            source,
            "resource fn wrap{i}() -> Unit {{ call {callee}() -> (); value {{ () }} }}"
        )
        .unwrap();
        callee = format!("wrap{i}");
    }
    source.push_str("resource fn main() -> Int { ");
    if called {
        write!(source, "call {callee}() -> (); ").unwrap();
    }
    source.push_str("value { 0 } }\n");
    project.write("main.vast", &source);
    project
}

#[test]
fn live_reads_through_thirty_forwarding_functions_fit_the_request_budget() {
    for runtime in [false, true] {
        let project = fixture(runtime, 30, true);
        success(
            &cli()
                .args(["check", "--manifest-path"])
                .arg(project.0.join("Vastitas.toml"))
                .output()
                .unwrap(),
        );
    }
}

#[test]
fn unused_probes_share_the_request_budget_under_check_and_build() {
    for (runtime, mode) in [(false, "check"), (true, "build")] {
        let project = fixture(runtime, 90, false);
        let mut command = cli();
        command
            .args([mode, "--manifest-path"])
            .arg(project.0.join("Vastitas.toml"));
        let product = project.0.join("program");
        project.write("program", "existing output");
        if mode == "build" {
            command.arg("-o").arg(&product);
        }
        let output = command.output().unwrap();
        assert!(!output.status.success());
        let diagnostic = String::from_utf8_lossy(&output.stderr);
        common::assert_first_code(&diagnostic, "E_LIMIT");
        assert!(
            diagnostic.contains("program-wide resource checking"),
            "{diagnostic}"
        );
        assert_eq!(std::fs::read(product).unwrap(), b"existing output");
    }
}
