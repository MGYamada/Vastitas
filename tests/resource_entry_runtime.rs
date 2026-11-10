//! The storage runtime requirement of a resource entry follows from its
//! checked operations (#681). An entry without an operation on an arena keeps
//! its value flow and its result. Its generated program imports no storage
//! runtime and creates no arena, and its build neither verifies nor links the
//! storage package. An entry with such an operation keeps the arenas that its
//! operations use, and its build verifies the storage package and links it.
mod common;
use common::runtime_inputs::header_imports;
use common::{
    Scratch, captured_wire, cli, copy_runtime_inputs, expect_code, kernel, kernel_path, success,
};
use serde_json::{Value, json};
use std::ffi::OsString;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const PINNED: &str = include_str!("../lean-kernel/lean-toolchain");

/// The reproduction of #681.
const SCALAR: &str = "resource fn main() -> Int { value { 42 } }";
const SCALAR_MAIN: &str = "
def main : IO Unit := do
  IO.println (VastitasGenerated.f_0)
";

/// Every scalar statement of a resource function: values, a branch on a
/// scalar slot, a literal branch and a call of a scalar resource function.
/// None is an operation on an arena. The entry returns 42.
const SCALAR_FLOW: &str = "resource fn pick(flag: Bool, base: Int) -> Int {
    let next: Int = value { base + 1 };
    value { if flag { next } else { base } }
}
resource fn main() -> Int {
    let flag: Bool = value { true };
    let base: Int = value { 40 };
    if flag {
        let unused: Int = value { base + 100 };
    } else {
    }
    if true {} else {}
    let picked: Int = call pick(flag, base) -> ();
    value { picked + 1 }
}";
const SCALAR_FLOW_MAIN: &str = "
def main : IO Unit := do
  let resourceValue_0 := VastitasGenerated.f_2
  let resourceValue_1 := VastitasGenerated.f_3 resourceValue_0
  if resourceValue_0 then
    let resourceValue_2 := VastitasGenerated.f_4 resourceValue_0 resourceValue_1
    pure ()
  else
    pure ()
  if true then
    pure ()
  else
    pure ()
  let resourceValue_5 := VastitasGenerated.f_0 resourceValue_0 resourceValue_1
  let resourceValue_6 := VastitasGenerated.f_1 resourceValue_0 resourceValue_1 resourceValue_5
  IO.println (VastitasGenerated.f_5 resourceValue_0 resourceValue_1 resourceValue_6)
";

/// Numerical declarations without an allocation. Spaces and bases are
/// nominal metadata of the checker and lower to no instruction, so the entry
/// has the generated `main` of `SCALAR`.
const DECLARATIONS: &str = "mod profiles;
resource fn main() -> Int {
    space u = linear(profiles::RealSmooth, 2);
    space v = linear(profiles::RealSmooth, 3);
    basis bu = basis(u);
    basis bv = basis(v);
    value { 42 }
}";
const PROFILES: &str = include_str!("../examples/packages/numerical/src/profiles/mod.vast");

/// Operations on a statically sized allocation.
const STATIC: &str = "    allocate data: F64[1];
    borrow output = write(data, layout(0, 1, 1, 1, false));
    store(output, 0, 0, f64_bits(4631107791820423168));
    release(output);
    borrow input = read(data, layout(0, 1, 1, 1, false));
    expect(input, 0, 0, f64_bits(4631107791820423168));
    release(input);
    drop(data);
";
const STATIC_MAIN: &str = "
open VastitasStorageNative

def main : IO Unit := do
  let arena ← newArena 9223372036854775807
  try
    allocate arena 0 0 1
    store arena 0 0 1 1 1 false 0 0 0 4631107791820423168 0
    expect arena 0 0 1 1 1 false 0 0 0 4631107791820423168 0
    drop arena 0
    IO.println (VastitasGenerated.f_0)
  catch cleanupError =>
    close arena
    throw cleanupError
  close arena
";

/// Operations on an allocation whose extent is a scalar slot.
const SHAPED: &str = "    let n: Nat = value { 2 + 1 };
    runtime_allocate dynamic: F64[n] runtime_layout(n, 1, n, false);
    runtime_borrow target = write(dynamic);
    runtime_fill(target, f64_bits(4607182418800017408));
    runtime_release(target);
    runtime_drop(dynamic);
";

/// A branch on a scalar slot. It lowers to the markers of a branch alone.
const SCALAR_BRANCH: &str = "    let flag: Bool = value { true };
    if flag {
        let unused: Int = value { 1 };
    } else {
    }
";

fn entry(body: &str) -> String {
    format!("resource fn main() -> Int {{\n{body}    value {{ 42 }}\n}}\n")
}

fn package(source: &str) -> Scratch {
    let s = Scratch::empty("resource entry runtime");
    s.write(
        "Vastitas.toml",
        "[package]\nname = \"entry\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n",
    );
    s.write("main.vast", source);
    // The module that `DECLARATIONS` declares; no other source names it.
    s.write("profiles/mod.vast", PROFILES);
    s
}

fn manifest(s: &Scratch) -> PathBuf {
    s.0.join("Vastitas.toml")
}

/// The kernel's answer to the request that the frontend sends for `s`.
fn emit(s: &Scratch) -> Value {
    let wire = captured_wire(cli().args(["check", "--manifest-path"]).arg(manifest(s)), 8);
    let response = kernel(&wire, "emit");
    assert_eq!(response["ok"], true, "{response}");
    response
}

fn generated(response: &Value) -> &str {
    response["lean_source"].as_str().unwrap()
}

/// The generated text after the pure functions: the entry `main`, with the
/// `open` of the storage runtime before it when there is one.
fn generated_main(source: &str) -> &str {
    source
        .split_once("\nend VastitasGenerated\n")
        .expect("generated pure library")
        .1
}

/// The arenas that the generated program creates, in order.
fn arenas(source: &str) -> Vec<&str> {
    source
        .lines()
        .filter_map(|line| line.trim_start().strip_prefix("let "))
        .filter_map(|line| line.strip_suffix(" ← newArena 9223372036854775807"))
        .collect()
}

fn executable(path: &Path, source: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, source).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
}

fn run(program: &Path) -> String {
    let output = Command::new(program).output().unwrap();
    success(&output);
    String::from_utf8(output.stdout).unwrap()
}

/// A scratch kernel root with the runtime inputs of the kernel package and,
/// when `optional`, of the storage and numerical packages.
fn kernel_root(s: &Scratch, name: &str, optional: bool) -> PathBuf {
    let kernel = s.0.join(name);
    copy_runtime_inputs(&kernel, optional, optional);
    fs::write(kernel.join("lean-toolchain"), PINNED).unwrap();
    kernel
}

/// A Lake that records its start, keeps the generated project in `project`
/// and installs a program printing `mocked`.
struct MockedLake {
    path: OsString,
    ran: PathBuf,
    project: PathBuf,
}

impl MockedLake {
    fn new(s: &Scratch) -> Self {
        executable(
            &s.0.join("bin/lake"),
            "#!/bin/sh\nset -eu\n: > \"$LAKE_RAN\"\ncp lakefile.toml Main.lean \"$LAKE_PROJECT/\"\nmkdir -p .lake/build/bin\nprintf '#!/bin/sh\\necho mocked\\n' > .lake/build/bin/program\nchmod +x .lake/build/bin/program\n",
        );
        let mut paths = vec![s.0.join("bin")];
        paths.extend(std::env::split_paths(
            &std::env::var_os("PATH").unwrap_or_default(),
        ));
        let project = s.0.join("project");
        fs::create_dir_all(&project).unwrap();
        Self {
            path: std::env::join_paths(paths).unwrap(),
            ran: s.0.join("lake-ran"),
            project,
        }
    }

    /// Builds the package of `s` to `s/program` with `backend` as the checker.
    fn build(&self, s: &Scratch, kernel_root: &Path, backend: &Path) -> Output {
        let _ = fs::remove_file(&self.ran);
        let _ = fs::remove_file(s.0.join("program"));
        cli()
            .args(["build", "--manifest-path"])
            .arg(manifest(s))
            .arg("-o")
            .arg(s.0.join("program"))
            .env("VASTITAS_KERNEL", backend)
            .env("VASTITAS_KERNEL_ROOT", kernel_root)
            .env("PATH", &self.path)
            .env("LAKE_RAN", &self.ran)
            .env("LAKE_PROJECT", &self.project)
            .output()
            .unwrap()
    }

    /// The Lake packages that the generated project requires.
    fn required(&self) -> Vec<String> {
        let lakefile: toml::Value =
            toml::from_str(&fs::read_to_string(self.project.join("lakefile.toml")).unwrap())
                .unwrap();
        lakefile["require"]
            .as_array()
            .unwrap()
            .iter()
            .map(|entry| entry["name"].as_str().unwrap().to_string())
            .collect()
    }

    /// The build stopped with `code` before Lake started and installed nothing.
    #[track_caller]
    fn assert_refused(&self, s: &Scratch, result: &Output, code: &str) -> String {
        let error = expect_code(result, code);
        assert!(!self.ran.exists(), "Lake started: {error}");
        assert!(!s.0.join("program").exists(), "installed an output");
        error
    }
}

// The emitted source and the runtime requirement of an entry without an
// operation on an arena. The checker accepts it as before.
#[test]
fn scalar_only_entry_emits_its_value_flow_and_requires_no_storage_runtime() {
    for (source, main) in [
        (SCALAR, SCALAR_MAIN),
        (SCALAR_FLOW, SCALAR_FLOW_MAIN),
        (DECLARATIONS, SCALAR_MAIN),
    ] {
        let s = package(source);
        success(
            &cli()
                .args(["check", "--manifest-path"])
                .arg(manifest(&s))
                .output()
                .unwrap(),
        );
        let response = emit(&s);
        assert_eq!(response["storage_runtime"], false, "{response}");
        assert_eq!(response["numerical_runtime"], false, "{response}");
        let lean = generated(&response);
        assert_eq!(header_imports(lean), ["VastitasKernel.IndexedRuntime"]);
        // The value calls, the branches and the result, directly in `main`.
        assert_eq!(generated_main(lean), main, "{lean}");
        assert!(arenas(lean).is_empty(), "{lean}");
        for absent in [
            "VastitasStorageNative",
            "arena",
            "Arena",
            "cleanupError",
            "try\n",
        ] {
            assert!(!lean.contains(absent), "{absent}: {lean}");
        }
    }
}

// The build and the result. The kernel root holds no storage package, so the
// program cannot have been compiled against it or linked with it.
#[test]
fn scalar_only_entry_builds_and_runs_in_a_root_without_the_storage_package() {
    let s = package(SCALAR);
    let kernel = kernel_root(&s, "kernel", false);
    assert!(!kernel.join("native").exists());
    let build = |output: &str| {
        cli()
            .args(["build", "--manifest-path"])
            .arg(manifest(&s))
            .arg("-o")
            .arg(s.0.join(output))
            .env("VASTITAS_KERNEL", kernel_path())
            .env("VASTITAS_KERNEL_ROOT", &kernel)
            .output()
            .unwrap()
    };
    success(&build("scalar"));
    assert_eq!(run(&s.0.join("scalar")), "42\n");
    for (output, source) in [("flow", SCALAR_FLOW), ("declarations", DECLARATIONS)] {
        s.write("main.vast", source);
        success(&build(output));
        assert_eq!(run(&s.0.join(output)), "42\n");
    }
    assert!(!kernel.join("native").exists());
    // An entry that allocates still needs the storage package of the root.
    s.write("main.vast", &entry(STATIC));
    let error = expect_code(&build("static"), "E_BUILD");
    assert!(
        error.contains("requires storage runtime inputs ")
            && error.contains("VastitasStorageNative.lean (missing)"),
        "{error}"
    );
    assert!(!s.0.join("static").exists(), "installed an output");
}

// An entry with an operation on an arena keeps the arenas that its operations
// use and the import of the storage runtime. The source of an entry with
// static operations is the one that the kernel generated before #681.
#[test]
fn entries_with_storage_operations_keep_their_arenas_and_the_storage_runtime() {
    let nested = format!("{STATIC}{SHAPED}");
    // The branch adds no operation on the static arena.
    let branched = format!("{SCALAR_BRANCH}{SHAPED}");
    for (body, expected) in [
        (STATIC, vec!["arena"]),
        (SHAPED, vec!["shapeArena"]),
        (nested.as_str(), vec!["arena", "shapeArena"]),
        (branched.as_str(), vec!["shapeArena"]),
    ] {
        let response = emit(&package(&entry(body)));
        assert_eq!(response["storage_runtime"], true, "{response}");
        assert_eq!(response["numerical_runtime"], false, "{response}");
        let lean = generated(&response);
        assert_eq!(
            header_imports(lean),
            ["VastitasStorageNative", "VastitasKernel.IndexedRuntime"]
        );
        assert!(
            generated_main(lean).starts_with("\nopen VastitasStorageNative\n\ndef main"),
            "{lean}"
        );
        assert_eq!(arenas(lean), expected, "{lean}");
        // Each arena is closed once on either path.
        for arena in expected {
            assert_eq!(lean.matches(&format!("  close {arena}\n")).count(), 2);
        }
    }
    let response = emit(&package(&entry(STATIC)));
    assert_eq!(generated_main(generated(&response)), STATIC_MAIN);
}

// The build of an entry with storage verifies the storage package of the
// selected root and requires it in the generated project. The build of a
// scalar-only entry does neither.
#[test]
fn storage_runtime_is_verified_and_required_exactly_for_entries_that_use_it() {
    let scalar = package(SCALAR);
    let stored = package(&entry(STATIC));
    let lake = MockedLake::new(&scalar);
    let untouched = kernel_root(&scalar, "untouched", true);
    let changed = kernel_root(&scalar, "changed", true);
    let mut source = fs::read(changed.join("native/storage.c")).unwrap();
    source.push(b'\n');
    fs::write(changed.join("native/storage.c"), source).unwrap();

    success(&lake.build(&stored, &untouched, &kernel_path()));
    assert!(lake.ran.exists(), "the build did not reach Lake");
    assert_eq!(
        lake.required(),
        ["vastitas_kernel", "vastitas_storage_native"]
    );
    // Lake compiles the source that the kernel returned.
    assert_eq!(
        fs::read_to_string(lake.project.join("Main.lean")).unwrap(),
        generated(&emit(&stored))
    );
    let result = lake.build(&stored, &changed, &kernel_path());
    let error = lake.assert_refused(&stored, &result, "E_BUILD");
    assert!(
        error.contains("requires storage runtime inputs ") && error.contains("storage.c (changed)"),
        "{error}"
    );

    for kernel in [&untouched, &changed] {
        success(&lake.build(&scalar, kernel, &kernel_path()));
        assert!(lake.ran.exists(), "the build did not reach Lake");
        assert_eq!(lake.required(), ["vastitas_kernel"]);
        assert_eq!(
            fs::read_to_string(lake.project.join("Main.lean")).unwrap(),
            generated(&emit(&scalar))
        );
    }
}

// The driver takes the requirement from the response and holds the generated
// source to it: a response that does not select the storage runtime cannot
// import it, whatever the entry is.
#[test]
fn a_response_cannot_import_the_storage_runtime_without_selecting_it() {
    let scalar = package(SCALAR);
    let stored = package(&entry(STATIC));
    let lake = MockedLake::new(&scalar);
    let kernel = kernel_root(&scalar, "kernel", true);
    // A backend that answers with the response in `$RESPONSE`.
    let backend = scalar.0.join("backend");
    executable(&backend, "#!/bin/sh\ncat >/dev/null\ncat \"$RESPONSE\"\n");
    let answer = |s: &Scratch, response: &Value| {
        let path = scalar.write("response.json", &response.to_string());
        let _ = fs::remove_file(&lake.ran);
        let _ = fs::remove_file(s.0.join("program"));
        cli()
            .args(["build", "--manifest-path"])
            .arg(manifest(s))
            .arg("-o")
            .arg(s.0.join("program"))
            .env("VASTITAS_KERNEL", &backend)
            .env("VASTITAS_KERNEL_ROOT", &kernel)
            .env("PATH", &lake.path)
            .env("LAKE_RAN", &lake.ran)
            .env("LAKE_PROJECT", &lake.project)
            .env("RESPONSE", path)
            .output()
            .unwrap()
    };
    // The kernel's own responses pass.
    let honest = emit(&stored);
    success(&answer(&stored, &honest));
    assert_eq!(
        lake.required(),
        ["vastitas_kernel", "vastitas_storage_native"]
    );
    success(&answer(&scalar, &emit(&scalar)));
    assert_eq!(lake.required(), ["vastitas_kernel"]);

    // The source of an entry with storage under a withdrawn requirement.
    let mut withdrawn = honest.clone();
    withdrawn["storage_runtime"] = json!(false);
    let mut omitted = honest.clone();
    omitted.as_object_mut().unwrap().remove("storage_runtime");
    // A storage import added to the source of a scalar-only entry.
    let mut added = emit(&scalar);
    added["lean_source"] = json!(format!(
        "import VastitasStorageNative\n{}",
        generated(&added)
    ));
    for (s, response) in [
        (&stored, &withdrawn),
        (&stored, &omitted),
        (&scalar, &added),
    ] {
        let error = lake.assert_refused(s, &answer(s, response), "E_PROTOCOL");
        assert!(
            error.contains("imports VastitasStorageNative, which is not a runtime module that this compiler verifies for this build"),
            "{error}"
        );
    }
    // The numerical runtime is built on the storage runtime.
    let mut numerical = emit(&scalar);
    numerical["numerical_runtime"] = json!(true);
    let error = lake.assert_refused(&scalar, &answer(&scalar, &numerical), "E_PROTOCOL");
    assert!(
        error.contains("numerical runtime requires the checked storage runtime"),
        "{error}"
    );
}

// An entry with storage still links the storage runtime of the kernel root:
// its program calls the arena and gives its result.
#[test]
fn entry_with_storage_builds_and_runs_with_the_storage_runtime() {
    let nested = format!("{STATIC}{SHAPED}");
    let branched = format!("{SCALAR_BRANCH}{SHAPED}");
    for body in [STATIC, SHAPED, nested.as_str(), branched.as_str()] {
        let s = package(&entry(body));
        success(
            &cli()
                .args(["build", "--manifest-path"])
                .arg(manifest(&s))
                .arg("-o")
                .arg(s.0.join("program"))
                .output()
                .unwrap(),
        );
        assert_eq!(run(&s.0.join("program")), "42\n");
    }
}
