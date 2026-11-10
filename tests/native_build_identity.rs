//! A native build compiles the runtime of the selected kernel root, so that
//! root must hold the runtime inputs that this compiler and its checked kernel
//! were built with (#679). The kernel's build identity alone accepts a stale
//! checker in a changed tree and a separately selected checker.
mod common;
use common::runtime_inputs::{self, KERNEL, NUMERICAL, Package, STORAGE};
use common::{
    Scratch, checked_replace, cli, copy_runtime_inputs, expect_code, kernel_identity, kernel_path,
    root, success,
};
use std::ffi::OsString;
use std::fs;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const PINNED: &str = include_str!("../lean-kernel/lean-toolchain");
const RESOURCE_MAIN: &str = "resource fn main() -> Int {
    allocate data: F64[1];
    borrow output = write(data, layout(0, 1, 1, 1, false));
    store(output, 0, 0, f64_bits(4631107791820423168));
    release(output);
    borrow input = read(data, layout(0, 1, 1, 1, false));
    expect(input, 0, 0, f64_bits(4631107791820423168));
    release(input);
    drop(data);
    value { 42 }
}";

/// A scratch copy of the kernel root: its runtime inputs and its toolchain pin.
fn kernel_copy(s: &Scratch, name: &str) -> PathBuf {
    let kernel = s.0.join(name);
    copy_runtime_inputs(&kernel, true, true);
    fs::write(kernel.join("lean-toolchain"), PINNED).unwrap();
    kernel
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

#[derive(Clone, Copy, PartialEq, Debug)]
enum Program {
    Pure,
    Storage,
    Numerical,
}

#[derive(Clone, Copy)]
enum Change {
    Append,
    Replace(&'static str),
    Remove,
}

impl Change {
    /// Applies the change to `path` and returns how the diagnostic names it.
    fn apply(self, path: &Path) -> &'static str {
        match self {
            Change::Append => {
                let mut bytes = fs::read(path).unwrap();
                bytes.push(b'\n');
                fs::write(path, bytes).unwrap();
                "changed"
            }
            Change::Replace(text) => {
                assert!(path.is_file());
                fs::write(path, text).unwrap();
                "changed"
            }
            Change::Remove => {
                fs::remove_file(path).unwrap();
                "missing"
            }
        }
    }
}

/// Builds with the built checker selected separately (`VASTITAS_KERNEL`) and a
/// Lake that records its start and installs a program printing 42.
struct Mocked {
    s: Scratch,
    path: OsString,
    lake_ran: PathBuf,
}

impl Mocked {
    fn new() -> Self {
        let s = Scratch::empty("runtime identity");
        executable(
            &s.0.join("bin/lake"),
            "#!/bin/sh\nset -eu\n: > \"$LAKE_RAN\"\nmkdir -p .lake/build/bin\nprintf '#!/bin/sh\\necho 42\\n' > .lake/build/bin/program\nchmod +x .lake/build/bin/program\n",
        );
        s.write("pure.vast", "fn main() -> Int { 42 }");
        s.write(
            "storage/Vastitas.toml",
            "[package]\nname = \"stored\"\nversion = \"0.1.0\"\nroot = \"main.vast\"\n",
        );
        s.write("storage/main.vast", RESOURCE_MAIN);
        let mut paths = vec![s.0.join("bin")];
        paths.extend(std::env::split_paths(
            &std::env::var_os("PATH").unwrap_or_default(),
        ));
        let path = std::env::join_paths(paths).unwrap();
        let lake_ran = s.0.join("lake-ran");
        Self { s, path, lake_ran }
    }

    fn command(&self, kernel: &Path, program: Program, output: &str) -> Command {
        let _ = fs::remove_file(&self.lake_ran);
        let mut command = cli();
        command.arg("build");
        match program {
            Program::Pure => command.arg(self.s.0.join("pure.vast")),
            Program::Storage => command
                .arg("--manifest-path")
                .arg(self.s.0.join("storage/Vastitas.toml")),
            // The mocked Lake needs no OpenBLAS; the driver only resolves the prefix.
            Program::Numerical => command
                .arg("--manifest-path")
                .arg(root().join("examples/packages/numerical/Vastitas.toml"))
                .arg("--openblas-prefix")
                .arg(&self.s.0),
        };
        command
            .arg("-o")
            .arg(self.s.0.join(output))
            .env("VASTITAS_KERNEL", kernel_path())
            .env("VASTITAS_KERNEL_ROOT", kernel)
            .env("PATH", &self.path)
            .env("LAKE_RAN", &self.lake_ran);
        command
    }

    fn build(&self, kernel: &Path, program: Program, output: &str) -> Output {
        self.command(kernel, program, output).output().unwrap()
    }

    #[track_caller]
    fn assert_built(&self, result: &Output, output: &str) {
        success(result);
        assert!(self.lake_ran.exists(), "the build did not reach Lake");
        assert_eq!(run(&self.s.0.join(output)), "42\n");
        fs::remove_file(self.s.0.join(output)).unwrap();
    }

    /// The build stopped with `E_BUILD` naming `package` and `input`, before
    /// Lake started and without installing `output`.
    #[track_caller]
    fn assert_rejected(&self, result: &Output, output: &str, package: &Package, input: &str) {
        let error = expect_code(result, "E_BUILD");
        assert!(
            error.contains(&format!("provides {} inputs ", package.name))
                && error.contains(&format!("requires {} inputs ", package.name))
                && error.contains(input),
            "expected {} and {input}: {error}",
            package.name
        );
        assert!(!self.lake_ran.exists(), "Lake started: {error}");
        assert!(
            !self.s.0.join(output).exists(),
            "installed an output: {error}"
        );
    }
}

/// The digest that a diagnostic prints for the inputs of `package` in `kernel`.
fn summary(kernel: &Path, package: &Package) -> String {
    let inputs = runtime_inputs::inputs(&package.directory_in(kernel), package).unwrap();
    runtime_inputs::summary(
        inputs
            .iter()
            .map(|(path, digest)| (path.as_str(), digest.as_str())),
    )
}

// The issue's reproduction, on the real path: a scratch copy of the kernel root
// keeps the built checker, and one runtime definition changes under it.
#[test]
fn changed_runtime_source_under_an_unchanged_checker_is_rejected_before_lake() {
    let s = Scratch::empty("runtime identity");
    let kernel = kernel_copy(&s, "lean-kernel");
    let checker = kernel.join(".lake/build/bin/vastitas-kernel");
    fs::create_dir_all(checker.parent().unwrap()).unwrap();
    fs::copy(kernel_path(), &checker).unwrap();
    let build = |output: &str| {
        cli()
            .arg("build")
            .arg(root().join("examples/pointed.vast"))
            .arg("-o")
            .arg(s.0.join(output))
            .env_remove("VASTITAS_KERNEL")
            .env("VASTITAS_KERNEL_ROOT", &kernel)
            .output()
            .unwrap()
    };
    // The untouched copy is a working root: Lake compiles its runtime.
    success(&build("pointed"));
    assert_eq!(run(&s.0.join("pointed")), "42\n");
    let compiled = kernel.join(".lake/build/lib/lean/VastitasKernel/IndexedRuntime.olean");
    let compiled_at = fs::metadata(&compiled).unwrap().modified().unwrap();

    let runtime = kernel.join("VastitasKernel/IndexedRuntime.lean");
    let original = fs::read_to_string(&runtime).unwrap();
    let expected = summary(&kernel, &KERNEL);
    assert_eq!(expected, summary(&root().join("lean-kernel"), &KERNEL));
    fs::write(
        &runtime,
        checked_replace(&original, "⟨dimension⟩", "⟨dimension + 1⟩"),
    )
    .unwrap();
    let rejected = build("changed");
    let error = expect_code(&rejected, "E_BUILD");
    // Both sides are named, with the input that differs.
    assert!(
        error.contains(&format!(
            "provides kernel runtime inputs {}, but this compiler requires kernel runtime inputs {expected}",
            summary(&kernel, &KERNEL)
        )) && error.contains("VastitasKernel/IndexedRuntime.lean (changed)"),
        "{error}"
    );
    assert!(error.contains("VASTITAS_KERNEL_ROOT"), "{error}");
    assert!(!s.0.join("changed").exists(), "installed an output");
    assert_eq!(
        fs::metadata(&compiled).unwrap().modified().unwrap(),
        compiled_at,
        "Lake compiled the changed runtime"
    );
    assert_eq!(run(&s.0.join("pointed")), "42\n");

    // The same root with its source restored builds again.
    fs::write(&runtime, original).unwrap();
    success(&build("restored"));
    assert_eq!(run(&s.0.join("restored")), "42\n");
}

// A separately selected checker passes the identity check for any root, so the
// root's own kernel package is compared: sources, their imports and the files
// that configure Lake.
#[test]
fn separately_selected_checker_requires_the_matching_kernel_root() {
    let m = Mocked::new();
    let untouched = kernel_copy(&m.s, "untouched");
    m.assert_built(&m.build(&untouched, Program::Pure, "program"), "program");
    for (index, (input, change)) in [
        ("VastitasKernel/IndexedRuntime.lean", Change::Append),
        ("VastitasKernel/SmoothRuntime.lean", Change::Append),
        ("VastitasKernel/AlgebraRuntime.lean", Change::Remove),
        ("lakefile.toml", Change::Append),
        ("lake-manifest.json", Change::Append),
        ("compiler-limits.json", Change::Append),
    ]
    .into_iter()
    .enumerate()
    {
        let kernel = kernel_copy(&m.s, &format!("kernel {index}"));
        let named = format!("{input} ({})", change.apply(&kernel.join(input)));
        let result = m.build(&kernel, Program::Pure, "program");
        m.assert_rejected(&result, "program", &KERNEL, &named);
    }
    // A module that a runtime source imports is an input as well.
    let kernel = kernel_copy(&m.s, "imported");
    let runtime = kernel.join("VastitasKernel/IndexedRuntime.lean");
    let source = fs::read_to_string(&runtime).unwrap();
    fs::write(&runtime, format!("import VastitasKernel.Added\n{source}")).unwrap();
    fs::write(kernel.join("VastitasKernel/Added.lean"), "").unwrap();
    let result = m.build(&kernel, Program::Pure, "program");
    m.assert_rejected(
        &result,
        "program",
        &KERNEL,
        "VastitasKernel/Added.lean (unexpected)",
    );
    // A file that no runtime module imports is not an input.
    fs::write(untouched.join("VastitasKernel/Unused.lean"), "").unwrap();
    fs::write(untouched.join("notes.txt"), "").unwrap();
    m.assert_built(&m.build(&untouched, Program::Pure, "program"), "program");
    // An input that cannot be read stops the build as well.
    // SAFETY: geteuid has no preconditions and cannot fail.
    if unsafe { nix::libc::geteuid() } != 0 {
        let unreadable = untouched.join("VastitasKernel/IndexedRuntime.lean");
        fs::set_permissions(&unreadable, fs::Permissions::from_mode(0o000)).unwrap();
        let result = m.build(&untouched, Program::Pure, "program");
        let error = expect_code(&result, "E_BUILD");
        assert!(
            error.contains("cannot read the kernel runtime inputs"),
            "{error}"
        );
        assert!(!m.lake_ran.exists() && !m.s.0.join("program").exists());
    }
}

/// A package, the programs that select it and changes to its inputs.
type PackageCases = (
    &'static Package,
    &'static [Program],
    &'static [(&'static str, Change)],
);

// The storage and numerical packages are compared exactly when the checked
// program selects them. A numerical program selects both.
#[test]
fn optional_runtime_packages_are_verified_when_selected() {
    let m = Mocked::new();
    let untouched = kernel_copy(&m.s, "untouched");
    for program in [Program::Pure, Program::Storage, Program::Numerical] {
        m.assert_built(&m.build(&untouched, program, "program"), "program");
    }
    const NEWER: &str = "leanprover/lean4:v99.98.97\n";
    let cases: [PackageCases; 2] = [
        (
            &STORAGE,
            &[Program::Storage, Program::Numerical],
            &[
                ("storage.c", Change::Append),
                ("ffi_result.h", Change::Remove),
                ("VastitasStorageNative/Runtime.lean", Change::Append),
                // Lake restarts itself with a direct dependency's newer toolchain.
                ("lean-toolchain", Change::Replace(NEWER)),
            ],
        ),
        (
            &NUMERICAL,
            &[Program::Numerical],
            &[
                ("gemm.c", Change::Append),
                ("VastitasGemmNative.lean", Change::Append),
                ("lake-manifest.json", Change::Append),
                ("lean-toolchain", Change::Replace(NEWER)),
            ],
        ),
    ];
    for (package, selecting, changes) in cases {
        for (index, (input, change)) in changes.iter().enumerate() {
            let kernel = kernel_copy(&m.s, &format!("{} {index}", package.directory));
            let path = kernel.join(package.directory).join(input);
            let named = format!("{input} ({})", change.apply(&path));
            for program in [Program::Pure, Program::Storage, Program::Numerical] {
                let result = m.build(&kernel, program, "program");
                if selecting.contains(&program) {
                    m.assert_rejected(&result, "program", package, &named);
                } else {
                    m.assert_built(&result, "program");
                }
            }
        }
    }
    // A source in a package directory for a module of another package's
    // library is not an input: Lake compiles that module from its own package.
    // The numerical adapter imports the storage library.
    let stray = untouched.join("numerical/VastitasStorageNative.lean");
    fs::write(stray, "").unwrap();
    let result = m.build(&untouched, Program::Numerical, "program");
    m.assert_built(&result, "program");
}

// A package has one Lake configuration, under the name that the lists give,
// and the other name must not exist in a root: Lake prefers `lakefile.lean`.
// The driver refuses the name by rule. It does not compare it with a value
// recorded when the compiler was built, and it does not advise a rebuild,
// which cannot accept the name.
#[test]
fn forbidden_configuration_names_are_refused_by_rule() {
    let m = Mocked::new();
    for (package, program) in [
        (&KERNEL, Program::Pure),
        (&STORAGE, Program::Storage),
        (&NUMERICAL, Program::Numerical),
    ] {
        let [name] = package.forbidden else {
            panic!("{}: one forbidden name expected", package.name)
        };
        for kind in ["file", "directory", "dangling link"] {
            let kernel = kernel_copy(&m.s, &format!("{} {kind}", package.name));
            let path = package.directory_in(&kernel).join(name);
            match kind {
                "file" => fs::write(&path, "").unwrap(),
                "directory" => fs::create_dir(&path).unwrap(),
                _ => symlink("absent", &path).unwrap(),
            }
            let result = m.build(&kernel, program, "program");
            let named = format!(": {name} (unexpected)\n");
            m.assert_rejected(&result, "program", package, &named);
            let error = String::from_utf8_lossy(&result.stderr);
            assert!(
                error.contains(&format!("note: {name} must not exist in "))
                    && error.contains("a rebuilt compiler rejects it as well. Remove it."),
                "{kind}: {error}"
            );
            assert!(
                !error.contains("rebuild this compiler and the kernel"),
                "{kind}: {error}"
            );
            // A program that does not select the package is built.
            if package.directory != KERNEL.directory {
                m.assert_built(&m.build(&kernel, Program::Pure, "program"), "program");
            }
        }
    }
    // With another difference, the advice for that difference is kept.
    let kernel = kernel_copy(&m.s, "mixed");
    fs::write(kernel.join("lakefile.lean"), "").unwrap();
    Change::Append.apply(&kernel.join("lakefile.toml"));
    let result = m.build(&kernel, Program::Pure, "program");
    m.assert_rejected(
        &result,
        "program",
        &KERNEL,
        ": lakefile.lean (unexpected), lakefile.toml (changed)\n",
    );
    let error = String::from_utf8_lossy(&result.stderr);
    assert!(
        error.contains("note: lakefile.lean must not exist in ")
            && error.contains("rebuild this compiler and the kernel"),
        "{error}"
    );
}

/// A change that makes the sources of a package differ from its lists.
type Difference = (&'static Package, fn(&Path), &'static str);

// `build.rs` builds the compiler's table with `required_inputs`. Sources that
// differ from the lists are an error there. The table therefore records no
// absence, and it names only files that exist and that Cargo watches: a file
// that is created later cannot make it stale.
#[test]
fn required_inputs_reject_sources_that_differ_from_the_lists() {
    use runtime_inputs::{inputs, module_file, required_inputs};
    // The sources of the repository match the lists.
    for package in [&KERNEL, &STORAGE, &NUMERICAL] {
        let directory = package.directory_in(&root().join("lean-kernel"));
        let entries = required_inputs(&directory, package).unwrap();
        assert_eq!(entries, inputs(&directory, package).unwrap());
        for (path, digest) in &entries {
            assert!(directory.join(path).is_file(), "{path} is not a file");
            assert!(
                digest.len() == 16 && digest.bytes().all(|byte| byte.is_ascii_hexdigit()),
                "{path} is recorded as {digest}"
            );
            assert!(!package.forbidden.contains(&path.as_str()), "{path}");
        }
        let listed = package.files.iter().map(|file| file.to_string());
        for path in listed.chain(package.modules.iter().map(|module| module_file(module))) {
            assert!(
                entries.iter().any(|(entry, _)| *entry == path),
                "{}: no entry for {path}",
                package.name
            );
        }
    }
    let prepend = |path: &Path, line: &str| {
        let source = fs::read_to_string(path).unwrap();
        fs::write(path, format!("{line}\n{source}")).unwrap();
    };
    let differences: [Difference; 9] = [
        (
            &STORAGE,
            |directory| fs::remove_file(directory.join("diagonal.h")).unwrap(),
            "diagonal.h is missing",
        ),
        (
            &KERNEL,
            |directory| fs::remove_file(directory.join("lakefile.toml")).unwrap(),
            "lakefile.toml is missing",
        ),
        (
            &KERNEL,
            |directory| fs::write(directory.join("lakefile.lean"), "").unwrap(),
            "lakefile.lean must not exist",
        ),
        (
            &NUMERICAL,
            |directory| fs::write(directory.join("lakefile.toml"), "").unwrap(),
            "lakefile.toml must not exist",
        ),
        (
            &KERNEL,
            |directory| {
                fs::remove_file(directory.join("VastitasKernel/SmoothRuntime.lean")).unwrap()
            },
            "module VastitasKernel.SmoothRuntime has no source VastitasKernel/SmoothRuntime.lean",
        ),
        (
            &STORAGE,
            |directory| {
                fs::remove_file(directory.join("VastitasStorageNative/Runtime.lean")).unwrap()
            },
            "VastitasStorageNative.lean imports VastitasStorageNative.Runtime, which has no source VastitasStorageNative/Runtime.lean",
        ),
        // A module of the package's library that has no source yet.
        (
            &KERNEL,
            |directory| {
                let runtime = directory.join("VastitasKernel/IndexedRuntime.lean");
                let source = fs::read_to_string(&runtime).unwrap();
                fs::write(runtime, format!("import VastitasKernel.Later\n{source}")).unwrap();
            },
            "VastitasKernel/IndexedRuntime.lean imports VastitasKernel.Later, which has no source VastitasKernel/Later.lean",
        ),
        // A module of a library that is neither the package's own nor the
        // toolchain's nor another runtime package's, with or without a source.
        (
            &KERNEL,
            |directory| {
                let runtime = directory.join("VastitasKernel/IndexedRuntime.lean");
                let source = fs::read_to_string(&runtime).unwrap();
                fs::write(runtime, format!("import Main\n{source}")).unwrap();
                fs::write(directory.join("Main.lean"), "").unwrap();
            },
            "VastitasKernel/IndexedRuntime.lean imports Main, which is not a module of this package's runtime library",
        ),
        (
            &STORAGE,
            |directory| {
                let runtime = directory.join("VastitasStorageNative/Runtime.lean");
                let source = fs::read_to_string(&runtime).unwrap();
                fs::write(runtime, format!("import Elsewhere.Module\n{source}")).unwrap();
            },
            "VastitasStorageNative/Runtime.lean imports Elsewhere.Module, which is not a module of this package's runtime library",
        ),
    ];
    let s = Scratch::empty("runtime identity");
    for (index, (package, change, problem)) in differences.into_iter().enumerate() {
        let kernel = kernel_copy(&s, &format!("kernel {index}"));
        let directory = package.directory_in(&kernel);
        required_inputs(&directory, package).unwrap();
        change(&directory);
        let error = required_inputs(&directory, package).unwrap_err();
        assert!(error.to_string().contains(problem), "{problem}: {error}");
        // A selected root is read without this rule; the driver compares it.
        inputs(&directory, package).unwrap();
    }
    // An import of a toolchain module names no file of the package. Once the
    // package gains a directory of the library's name, the sources no longer
    // match: a library of that name in the package would hold an input.
    let kernel = kernel_copy(&s, "toolchain import");
    prepend(
        &kernel.join("VastitasKernel/IndexedRuntime.lean"),
        "import Lean.Data.Json",
    );
    let before = required_inputs(&kernel, &KERNEL).unwrap();
    fs::create_dir(kernel.join("Lean")).unwrap();
    let error = required_inputs(&kernel, &KERNEL).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("imports Lean.Data.Json, whose source is in this package"),
        "{error}"
    );
    assert_eq!(inputs(&kernel, &KERNEL).unwrap(), before);
}

// The comparison covers the modules that generated programs import. A backend
// response that imports any other module is refused instead of being compiled
// against sources that nothing compared.
#[test]
fn generated_imports_outside_the_verified_runtime_are_refused() {
    let m = Mocked::new();
    let kernel = kernel_copy(&m.s, "kernel");
    let backend = m.s.0.join("backend");
    for (imports, refused) in [
        ("import VastitasKernel.IndexedRuntime\\n", None),
        (
            "import VastitasKernel.IndexedRuntime\\nimport VastitasKernel.IndexedCodegen\\n",
            Some("VastitasKernel.IndexedCodegen"),
        ),
        // The storage runtime is verified only for a response that selects it.
        (
            "import VastitasStorageNative\\n",
            Some("VastitasStorageNative"),
        ),
    ] {
        executable(
            &backend,
            &format!(
                "#!/bin/sh\ncat >/dev/null\nprintf '%s\\n' '{{\"version\":2,\"ok\":true,\"kernel\":{},\"lean_source\":\"{imports}def main : IO Unit := pure ()\"}}'\n",
                kernel_identity()
            ),
        );
        let result = m
            .command(&kernel, Program::Pure, "program")
            .env("VASTITAS_KERNEL", &backend)
            .output()
            .unwrap();
        match refused {
            None => m.assert_built(&result, "program"),
            Some(module) => {
                let error = expect_code(&result, "E_PROTOCOL");
                assert!(error.contains(&format!("imports {module},")), "{error}");
                assert!(!m.lake_ran.exists(), "Lake started: {error}");
                assert!(!m.s.0.join("program").exists(), "installed an output");
            }
        }
    }
}

// The verified lists name what the Lake configurations make Lake read: every
// C source and header of the optional packages, their Lean libraries and the
// inputs that the kernel library needs.
#[test]
fn verified_inputs_cover_the_lake_configurations() {
    let kernel = root().join("lean-kernel");
    for package in [&STORAGE, &NUMERICAL] {
        let lakefile =
            fs::read_to_string(kernel.join(package.directory).join("lakefile.lean")).unwrap();
        let declared: Vec<&str> = lakefile
            .lines()
            .filter(|line| line.starts_with("input_file "))
            .filter_map(|line| line.split_once("path := \""))
            .map(|(_, rest)| rest.split('"').next().unwrap())
            .collect();
        assert!(!declared.is_empty(), "{}: no inputs found", package.name);
        for path in &declared {
            let (owner, name) = match path.strip_prefix("../native/") {
                Some(name) => (&STORAGE, name),
                None => (package, *path),
            };
            assert!(
                owner.files.contains(&name),
                "{}: input {path} is not verified",
                package.name
            );
        }
        for file in package
            .files
            .iter()
            .filter(|file| file.ends_with(".c") || file.ends_with(".h"))
        {
            assert!(
                declared.contains(file),
                "{}: {file} is verified but not a Lake input",
                package.name
            );
        }
        let libraries: Vec<&str> = lakefile
            .lines()
            .filter_map(|line| line.strip_prefix("lean_lib "))
            .map(str::trim)
            .collect();
        assert_eq!(libraries, package.modules, "{}", package.name);
    }
    let manifest: toml::Value =
        toml::from_str(&fs::read_to_string(kernel.join("lakefile.toml")).unwrap()).unwrap();
    let named = |table: &str, name: &toml::Value| {
        manifest[table]
            .as_array()
            .unwrap()
            .iter()
            .find(|entry| entry["name"] == *name)
            .unwrap_or_else(|| panic!("no {table} named {name}"))
            .clone()
    };
    let library = named("lean_lib", &toml::Value::from("VastitasKernel"));
    for need in library["needs"].as_array().unwrap() {
        let path = named("input_file", need)["path"]
            .as_str()
            .unwrap()
            .to_string();
        assert!(
            KERNEL.files.contains(&path.as_str()),
            "kernel library input {path} is not verified"
        );
    }
    for module in KERNEL.modules {
        assert!(module.starts_with("VastitasKernel."), "{module}");
    }
    // Each package has one Lake configuration. The lists name it as an input
    // and forbid the other name.
    for package in [&KERNEL, &STORAGE, &NUMERICAL] {
        let directory = package.directory_in(&kernel);
        let names = ["lakefile.lean", "lakefile.toml"];
        let present: Vec<&str> = names
            .into_iter()
            .filter(|name| fs::symlink_metadata(directory.join(name)).is_ok())
            .collect();
        let [configuration] = present[..] else {
            panic!(
                "{}: one Lake configuration expected, found {present:?}",
                package.name
            )
        };
        let other = names.into_iter().find(|name| *name != configuration);
        assert!(
            package.files.contains(&configuration),
            "{}: {configuration} is not a listed input",
            package.name
        );
        assert_eq!(
            package.forbidden.first().copied(),
            other,
            "{}: the forbidden name",
            package.name
        );
        assert_eq!(package.forbidden.len(), 1, "{}", package.name);
    }
}
