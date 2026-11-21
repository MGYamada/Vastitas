//! Physical origins of ordinary singleton functions, even without a caller.
mod common;

use common::{CURRENT_PROTOCOL, Scratch, assert_wire_rejected, kernel};
use serde_json::json;

#[test]
fn unused_singletons_replay_bodies_signatures_visibility_and_spans_in_their_module() {
    let scratch = Scratch::empty("physical singleton functions");
    let manifest = "app/Vastitas.toml";
    scratch.write_package("app", "mod defs; fn main() -> Int { 7 }", "");
    let source = "// λ\r\npub fn first(b: Bool, q: Bool) -> Bool { b }";
    scratch.write("app/defs.vast", source);
    let original = scratch.captured(manifest, CURRENT_PROTOCOL);
    assert_eq!(kernel(&original, "check")["ok"], true);
    for (from, to) in [
        ("{ b }", "{ q }"),
        ("q: Bool", "q: Unit"),
        ("pub fn", "    fn"),
    ] {
        scratch.write("app/defs.vast", &common::checked_replace(source, from, to));
        let other = scratch.captured(manifest, CURRENT_PROTOCOL);
        assert_eq!(kernel(&other, "check")["ok"], true);
        let mut forged = original.clone();
        forged["root_source"] = other["root_source"].clone();
        for mode in ["check", "emit", "function-revision"] {
            let error = kernel(&forged, mode);
            assert_wire_rejected(&error, "E_FUNCTION_SOURCE");
            assert_eq!(error["diagnostics"][0]["span"]["line"], 2);
            if from == "{ b }" {
                assert_eq!(
                    error["diagnostics"][0]["span"]["column"],
                    source.lines().last().unwrap().find("b }").unwrap() + 1
                );
            }
        }
    }
    let mut missing = original.clone();
    let definitions = missing["packages"][0]["modules"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|m| m["path"] == json!(["defs"]))
        .unwrap();
    definitions["functions"] = json!([]);
    assert_wire_rejected(&kernel(missing, "emit"), "E_FUNCTION_SOURCE");
    let mut moved = original;
    let root = moved["packages"][0]["modules"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|m| m["path"] == json!([]))
        .unwrap();
    root["functions"][0]["body"]["result"]["span"]["column"] = json!(1);
    assert_wire_rejected(&kernel(moved, "function-revision"), "E_FUNCTION_SOURCE");
}

#[test]
fn raw_flat_singletons_require_the_physical_show_initializer_and_the_same_expression() {
    let source = "fn main() -> Int { let value = show!(7); value }";
    let observed = common::request(source, "main.vast");
    assert_eq!(kernel(&observed, "check")["ok"], true);
    let mut omitted = observed.clone();
    common::flat_module(&mut omitted)["functions"][0]
        .as_object_mut()
        .unwrap()
        .remove("observations");
    let mut stale = observed.clone();
    stale["root_source"]["text"] = json!(source.replace("show!(7)", "     (7)"));
    let mut changed = observed.clone();
    changed["root_source"]["text"] = json!(source.replace("show!(7)", "show!(8)"));
    for invalid in [omitted, stale, changed] {
        for mode in ["check", "emit"] {
            assert_wire_rejected(&kernel(&invalid, mode), "E_FUNCTION_SOURCE");
        }
    }
}

#[test]
fn empty_singleton_requirements_replay_on_each_side_of_the_arrow() {
    for header in [
        "fn first(b: Bool) requires() -> Bool",
        "fn first(b: Bool) -> Bool requires()",
    ] {
        let source =
            format!("{header} {{ b }} fn main() -> Int {{ if first(true) {{ 42 }} else {{ 7 }} }}");
        let raw = common::request(&source, "main.vast");
        assert_eq!(kernel(&raw, "check")["ok"], true);
        let mut forged = raw;
        forged["root_source"]["text"] = json!(source.replace("requires()", "requires(X)"));
        assert_wire_rejected(&kernel(forged, "emit"), "E_ASSEMBLY");
    }
}

#[test]
fn lean_singleton_regressions_replay_the_original_frontend_inputs() {
    let cases: serde_json::Map<String, serde_json::Value> =
        serde_json::from_str(include_str!("fixtures/singleton-source.json")).unwrap();
    for (name, mut expected) in cases {
        let source = expected["root_source"]["text"].as_str().unwrap().to_owned();
        if expected["root"] == "vastitas:compat:flat" {
            let filename = expected["file"].as_str().unwrap();
            assert_eq!(common::request(&source, filename), expected, "{name}");
        } else {
            let scratch = Scratch::empty("singleton kernel fixture");
            let files = expected["root_source"]["files"].as_array_mut().unwrap();
            for file in files {
                let relative = file["path"].as_str().unwrap().strip_prefix('/').unwrap();
                let real = scratch.write(relative, file["text"].as_str().unwrap_or(&source));
                file["path"] = json!(real.canonicalize().unwrap());
            }
            let relative = expected["root"]
                .as_str()
                .unwrap()
                .strip_prefix('/')
                .unwrap()
                .to_owned();
            let manifest = json!(scratch.0.join(&relative).canonicalize().unwrap());
            expected["file"] = manifest.clone();
            expected["root"] = manifest.clone();
            expected["packages"][0]["source"] = manifest;
            assert_eq!(
                scratch.captured(&relative, CURRENT_PROTOCOL),
                expected,
                "{name}"
            );
        }
        let result = kernel(&expected, "check");
        assert_eq!(result["ok"], true, "{name}: {result}");
    }
}

#[test]
fn flat_main_belongs_to_the_entry_file_on_every_kernel_route() {
    let scratch = Scratch::empty("flat main and library");
    let entry = "fn main() -> Int { 42 }";
    let library = "fn next() -> Int { 7 }";
    scratch.write("root.vast", entry);
    scratch.write("lib.vast", library);
    let mut command = scratch.cli();
    command.args(["check", "root.vast", "--lib", "lib.vast"]);
    let original = common::captured_wire(&mut command, CURRENT_PROTOCOL);

    // Move the name in both files and the decoded functions. Every span, body
    // and file offset still agrees. Only the physical origin of main changes.
    let entry = entry.replace("main", "next");
    let library = library.replace("next", "main");
    let mut moved = original.clone();
    moved["root_source"]["text"] = json!(entry);
    let files = moved["root_source"]["files"].as_array_mut().unwrap();
    let physical_lib = files.iter_mut().find(|f| f["path"] == "lib.vast").unwrap();
    physical_lib["text"] = json!(library);
    let functions = common::flat_module(&mut moved)["functions"]
        .as_array_mut()
        .unwrap();
    functions[0]["name"] = json!("next");
    functions[1]["name"] = json!("main");
    let main_span = functions[1]["span"].clone();

    scratch.write("root.vast", &entry);
    scratch.write("lib.vast", &library);
    let output = scratch
        .cli()
        .args(["check", "root.vast", "--lib", "lib.vast"])
        .output()
        .unwrap();
    common::expect_code(&output, "E_LIBRARY");
    assert!(String::from_utf8_lossy(&output.stderr).contains("lib.vast:1:1"));
    let triple = "aarch64-apple-darwin";
    let layout = "e-m:o-i64:64-n32:64-S128";
    for args in [
        &["check"][..],
        &["emit"],
        &["function-revision"],
        &["llvm-check", triple, layout],
        &["llvm-build", triple, layout],
    ] {
        let valid = common::kernel_with_args(&original, args);
        assert_eq!(valid["ok"], true, "{args:?}: {valid}");
        let result = common::kernel_with_args(&moved, args);
        assert_wire_rejected(&result, "E_LIBRARY");
        assert_eq!(result["diagnostics"][0]["span"], main_span);
        assert!(result.get("llvm").is_none());
    }
}

#[test]
fn complete_llvm_requires_valid_physical_item_boundaries() {
    let source = "//AAA\nfn main() -> Int { 42 }\n//BBB\n";
    let project = Scratch::empty("physical module items");
    project.write_package("app", source, "");
    let manifest = "app/Vastitas.toml";
    let flat = common::request(source, "entry.vast");
    let package = project.captured(manifest, CURRENT_PROTOCOL);
    let triple = "x86_64-unknown-linux-gnu";
    let layout = "e-p:64:64";
    for wire in [flat, package] {
        let original = common::kernel_with_args(&wire, &["llvm-check", triple, layout]);
        assert_eq!(original["ok"], true, "{original}");
        assert!(original["llvm"]["ir"].as_str().unwrap().contains("@main"));
        for (comment, replacement, line) in [
            ("//AAA", "oops;", 1),
            ("//BBB", "oops;", 3),
            ("//BBB", "pub  ", 3),
            ("//BBB", ";    ", 3),
        ] {
            let mut changed = wire.clone();
            changed["root_source"]["text"] = json!(source.replace(comment, replacement));
            for args in [
                &["check"][..],
                &["emit"],
                &["function-revision"],
                &["llvm-check", triple, layout],
                &["llvm-build", triple, layout],
            ] {
                let response = common::kernel_with_args(&changed, args);
                assert_wire_rejected(&response, "E_MODULE_SOURCE");
                let span = &response["diagnostics"][0]["span"];
                assert_eq!(span["line"], line);
                assert_eq!(span["column"], 1);
                assert!(response.get("llvm").is_none());
            }
        }
    }
}

#[test]
fn physical_indexed_headers_include_unreferenced_external_declarations() {
    let project = Scratch::empty("indexed declarations in an external module");
    project.write_package("app", "mod defs; fn main() -> Int { 42 }", "");
    let source = "indexed marker First      ;\n// indexed marker Ghost;\n";
    project.write("app/defs.vast", source);
    let wire = project.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    assert_eq!(kernel(&wire, "check")["ok"], true);
    for (from, to, line) in [
        ("marker First", "marker Other", 1),
        ("marker First", "xxxxxx First", 1),
        ("First      ;", "First = bad;", 1),
        ("// indexed", "   indexed", 2),
    ] {
        let mut changed = wire.clone();
        let file = changed["root_source"]["files"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|f| f["text"].as_str() == Some(source))
            .unwrap();
        file["text"] = json!(common::checked_replace(source, from, to));
        let response = kernel(&changed, "function-revision");
        assert_wire_rejected(&response, "E_MODULE_SOURCE");
        assert_eq!(response["diagnostics"][0]["span"]["line"], line);
    }
}

#[test]
fn inline_modules_and_empty_flat_libraries_check_item_boundaries() {
    let project = Scratch::empty("boundaries of nested and empty source files");
    let inline = "mod inner {\n //AAA\n}\nfn main() -> Int { 42 }";
    project.write_package("app", inline, "");
    let mut package = project.captured("app/Vastitas.toml", CURRENT_PROTOCOL);
    assert_eq!(kernel(&package, "check")["ok"], true);
    package["root_source"]["text"] = json!(inline.replace("//AAA", "oops;"));

    project.write("root.vast", "fn main() -> Int { 42 }");
    project.write("lib.vast", "\n //AAA\n");
    let mut command = project.cli();
    command.args(["check", "root.vast", "--lib", "lib.vast"]);
    let mut flat = common::captured_wire(command, CURRENT_PROTOCOL);
    assert_eq!(kernel(&flat, "check")["ok"], true);
    let library = flat["root_source"]["files"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|f| f["path"] == "lib.vast")
        .unwrap();
    library["text"] = json!("\n oops;\n");
    for changed in [package, flat] {
        let response = kernel(changed, "check");
        assert_wire_rejected(&response, "E_MODULE_SOURCE");
        assert_eq!(response["diagnostics"][0]["span"]["line"], 2);
        assert_eq!(response["diagnostics"][0]["span"]["column"], 2);
    }
}
