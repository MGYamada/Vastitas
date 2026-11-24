//! Root-authored methods retain their writing scope when the family is owned by a dependency.
mod common;

use common::{Scratch, expect_code, success};
use std::process::Output;

const MANIFEST: &str = "app/Vastitas.toml";

fn package(base: &str, contribution: &str, applied: bool) -> Scratch {
    let project = Scratch::empty("root contribution to unused dependency");
    project.write_package(
        "lib",
        &format!(
            "pub fn choose(b: Bool) -> Bool {{ {base} }}\n\
             pub grant write : choose to app {{ domain (Bool); }}"
        ),
        "",
    );
    let assembly = if applied {
        "assemble lib::choose { borrow lib::write { apply local; } }"
    } else {
        ""
    };
    project.write_package(
        "app",
        &format!(
            "contribution local : lib::choose {{\n\
               fn lib::choose(b: Bool) requires (HasEq) -> Bool {{ {contribution} }}\n\
             }}\n{assembly}\nfn main() -> Int {{ 7 }}"
        ),
        "lib={path='../lib'}",
    );
    project
}

fn preview(project: &Scratch) -> Output {
    project
        .command("check", MANIFEST)
        .args([
            "--llvm-preview",
            "--target-triple",
            "aarch64-apple-darwin",
            "--data-layout",
            "e-m:o-i64:64-n32:64-S128",
        ])
        .output()
        .unwrap()
}

#[test]
fn uncalled_root_contribution_and_its_foreign_family_sibling_are_linked() {
    let project = package("false", "b && b", true);
    success(&project.check_manifest(MANIFEST));
    let result = preview(&project);
    success(&result);
    let llvm = String::from_utf8(result.stdout).unwrap();
    assert_eq!(llvm.matches("define internal i1 @").count(), 2, "{llvm}");
    assert!(llvm.contains("and i1"), "{llvm}");
    assert!(llvm.contains("or i1 0 , 0"), "{llvm}");
    assert_eq!(llvm.matches("call i1").count(), 0, "{llvm}");
}

#[test]
fn an_uninvoked_borrowed_integer_family_keeps_both_bodies_and_the_revision() {
    let entry = include_str!("../llvm/fixtures/uncalled-operator/main.vast");
    let project = common::example_package(
        "uncalled boxed methods",
        "examples/packages/authority/edit-borrow",
        &[("app/main.vast", entry)],
    );
    let output = preview(&project);
    success(&output);
    let llvm = String::from_utf8(output.stdout).unwrap();
    assert_eq!(llvm.matches("define internal ptr @vq_f").count(), 6);
    assert_eq!(llvm.matches("call ptr @vq_f").count(), 1, "{llvm}");
    assert!(llvm.contains("call ptr @vastitas_int_add_v1"), "{llvm}");

    let revision = project
        .command("check", MANIFEST)
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&revision);
    let saved = project.0.join("revision.json");
    std::fs::write(&saved, revision.stdout).unwrap();
    let replay = || {
        project
            .command("check", MANIFEST)
            .args([
                "--llvm-preview",
                "--target-triple",
                "aarch64-apple-darwin",
                "--data-layout",
                "e-m:o-i64:64-n32:64-S128",
                "--expect-function-revision",
            ])
            .arg(&saved)
            .output()
            .unwrap()
    };
    let matched = replay();
    success(&matched);
    assert_eq!(matched.stdout, llvm.as_bytes());
    let base = std::fs::read_to_string(project.0.join("lib/main.vast")).unwrap();
    project.write(
        "lib/main.vast",
        &common::checked_replace(&base, "{ 0 }", "{ 1 }"),
    );
    let stale = replay();
    expect_code(&stale, "E_FUNCTION_REVISION");
    assert!(stale.stdout.is_empty());
    let revised = preview(&project);
    success(&revised);
    assert_ne!(revised.stdout, llvm.as_bytes());
}

#[test]
fn unsupported_root_contribution_or_foreign_sibling_rejects_the_closed_package() {
    for (base, implementation) in [
        ("false", "let empty = (); let p = pair(1, 2); b"),
        ("let empty = (); let p = pair(1, 2); b", "b"),
    ] {
        let project = package(base, implementation, true);
        success(&project.check_manifest(MANIFEST));
        let output = preview(&project);
        expect_code(&output, "E_UNSUPPORTED");
        assert!(output.stdout.is_empty());
    }
}

#[test]
fn unapplied_root_contribution_is_audited_without_linking_foreign_family() {
    let project = package("false", "!b", false);
    success(&project.check_manifest(MANIFEST));
    let output = preview(&project);
    success(&output);
    assert!(
        !String::from_utf8(output.stdout)
            .unwrap()
            .contains("define internal i1 @")
    );

    let invalid = package("false", "missing", false);
    expect_code(&preview(&invalid), "E_NAME");
}

#[test]
fn an_empty_explicit_seal_retains_the_unused_foreign_family() {
    for (body, expected) in [
        ("!b", "define internal i1 @"),
        ("let p = pair(1, 2); b", "call ptr @vastitas_int_pair_v1"),
    ] {
        let project = package(body, "b && b", false);
        project.write(
            "app/main.vast",
            "assemble lib::choose {} fn main() -> Int { 7 }",
        );
        success(&project.check_manifest(MANIFEST));
        let output = preview(&project);
        success(&output);
        let llvm = String::from_utf8(output.stdout).unwrap();
        assert_eq!(llvm.matches(expected).count(), 1, "{llvm}");
    }
}

#[test]
fn explicit_seal_without_a_concrete_specialization_rejects_the_preview() {
    let project = Scratch::empty("seal of an unused higher-order dependency");
    project.write_package("lib", "pub fn invoke(f: Fn<Int, Int>) -> Int { f(1) }", "");
    project.write_package(
        "app",
        "assemble lib::invoke {} fn main() -> Int { 7 }",
        "lib={path='../lib'}",
    );
    success(&project.check_manifest(MANIFEST));
    let result = preview(&project);
    expect_code(&result, "E_UNSUPPORTED");
    assert!(result.stdout.is_empty());
}

#[test]
fn root_borrow_and_apply_retains_a_wholly_foreign_family_and_implementation() {
    let project = Scratch::empty("explicit external package seal");
    project.write_package(
        "lib",
        "pub fn choose(b: Bool) -> Bool { false } pub grant write : choose to addon { domain (Bool); }",
        "",
    );
    project.write_package(
        "addon",
        "pub contribution other : lib::choose { fn lib::choose(b: Bool) requires (HasEq) -> Bool { b && b } }",
        "lib={path='../lib'}",
    );
    project.write_package(
        "app",
        "assemble lib::choose { borrow lib::write { apply addon::other; } } fn main() -> Int { 7 }",
        "lib={path='../lib'}\naddon={path='../addon'}",
    );
    success(&project.check_manifest(MANIFEST));
    let result = preview(&project);
    success(&result);
    let llvm = String::from_utf8(result.stdout).unwrap();
    assert_eq!(llvm.matches("define internal i1 @").count(), 2, "{llvm}");
    assert!(llvm.contains("and i1"), "{llvm}");
    assert_eq!(llvm.matches("call i1").count(), 0, "{llvm}");
}

#[test]
fn assembled_predicate_and_nominal_multi_axis_lookup_share_the_checked_module() {
    const SOURCE: &str = include_str!("../llvm/fixtures/StructuredLookup.vast");
    let project = Scratch::empty("assembled predicate over a finite table");
    project.write_package("app", SOURCE, "");
    let revision = project
        .command("check", MANIFEST)
        .arg("--print-function-revision")
        .output()
        .unwrap();
    success(&revision);
    std::fs::write(project.0.join("checked.json"), &revision.stdout).unwrap();
    for (source, expected) in [
        (SOURCE.to_owned(), 42),
        (
            SOURCE.replace("(hi, middle, on) => d9", "(hi, middle, on) => d8"),
            7,
        ),
        (SOURCE.replace("!a || b", "!a && b"), 7),
        (SOURCE.replace("apply selected;", ""), 7),
    ] {
        project.write("app/main.vast", &source);
        assert_eq!(
            project.check_build_and_run(MANIFEST),
            common::exits(expected)
        );
        let pin = project
            .command("check", MANIFEST)
            .args([
                "--llvm-preview",
                "--expect-function-revision",
                "checked.json",
                "--target-triple",
                "aarch64-apple-darwin",
                "--data-layout",
                "e-m:o-i64:64-n32:64-S128",
            ])
            .output()
            .unwrap();
        if expected == 42 {
            success(&pin);
        } else {
            expect_code(&pin, "E_FUNCTION_REVISION");
            assert!(pin.stdout.is_empty());
        }
        let result = preview(&project);
        success(&result);
        let ll = std::str::from_utf8(&result.stdout).unwrap();
        assert_eq!(ll.matches("define internal i1 @").count(), 2);
        assert!(ll.contains("switch i32 0 , label %miss"));
        assert_eq!(ll.matches("icmp ult i32").count(), 3);
        assert_eq!(ll.matches("mul i32").count(), 2);
        #[cfg(feature = "llvm-native")]
        {
            let result = project
                .command("build", MANIFEST)
                .args(["--llvm-preview", "-o", "result"])
                .output()
                .unwrap();
            success(&result);
            let status = std::process::Command::new(project.0.join("result"))
                .status()
                .unwrap();
            assert_eq!(status.code(), Some(expected));
        }
    }
    project.write(
        "app/main.vast",
        &SOURCE.replace(
            "Row::hi, Column::middle, Bit::on",
            "Row::hi, Bit::on, Column::middle",
        ),
    );
    expect_code(&project.check_manifest(MANIFEST), "E_TYPE");
}

#[test]
fn all_admitted_lookup_arities_reach_llvm_in_declared_axis_order() {
    use std::fmt::Write;
    let mut source = String::from("indexed finite Bit { zero; one; }\n");
    let mut observations = Vec::new();
    for arity in 0..=6 {
        let size = 1usize << arity;
        let digits = (0..size)
            .map(|i| format!("d{i};"))
            .collect::<Vec<_>>()
            .join(" ");
        writeln!(source, "indexed finite Out{arity} {{ {digits} }}").unwrap();
        let axes = vec!["Bit"; arity].join(",");
        writeln!(source, "indexed table t{arity}({axes}) -> Out{arity} {{").unwrap();
        // Reverse source row order. Each output identifies the entire tuple.
        for value in (0..size).rev() {
            let args = (0..arity)
                .rev()
                .map(|b| if (value >> b) & 1 == 1 { "one" } else { "zero" })
                .collect::<Vec<_>>();
            writeln!(source, "({}) => d{value};", args.join(",")).unwrap();
        }
        source.push_str("}\n");
        let params = (0..arity)
            .map(|i| format!("a{i}:Bit<>"))
            .collect::<Vec<_>>()
            .join(",");
        let args = (0..arity)
            .map(|i| format!("a{i}"))
            .collect::<Vec<_>>()
            .join(",");
        writeln!(
            source,
            "fn lookup{arity}({params}) -> Out{arity}<> {{ finite::lookup::<t{arity}>({args}) }}"
        )
        .unwrap();
        // Exercise zero and every individual coordinate through real nested calls.
        for value in std::iter::once(0).chain((0..arity).map(|b| 1 << b)) {
            let args = (0..arity)
                .rev()
                .map(|b| {
                    if (value >> b) & 1 == 1 {
                        "Bit::one"
                    } else {
                        "Bit::zero"
                    }
                })
                .collect::<Vec<_>>()
                .join(",");
            observations.push(format!("lookup{arity}({args}) == Out{arity}::d{value}"));
        }
    }
    writeln!(
        source,
        "fn main() -> Int {{ if {} {{ 42 }} else {{ 7 }} }}",
        observations.join(" && ")
    )
    .unwrap();
    let project = Scratch::empty("finite lookup at every supported arity");
    project.write_package("app", &source, "");
    assert_eq!(project.check_build_and_run(MANIFEST), common::exits(42));
    let result = preview(&project);
    success(&result);
    let ll = std::str::from_utf8(&result.stdout).unwrap();
    assert_eq!(ll.matches("switch i32").count(), 7);
    assert!(ll.contains("icmp ult i32 %axis5 , 2"));
    #[cfg(feature = "llvm-native")]
    {
        success(
            &project
                .command("build", MANIFEST)
                .args(["--llvm-preview", "-o", "all-arities"])
                .output()
                .unwrap(),
        );
        let status = std::process::Command::new(project.0.join("all-arities"))
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(42));
    }
}
