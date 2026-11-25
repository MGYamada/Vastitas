use std::{env, fs, path::Path, path::PathBuf};

// Shared with the driver, which digests the same files in the selected root.
#[allow(dead_code)]
#[path = "src/runtime_inputs.rs"]
mod runtime_inputs;
use runtime_inputs::{Package, executable_digest, executable_inputs, required_inputs};

fn main() {
    #[cfg(feature = "llvm-native")]
    {
        check_native_llvm();
        for file in [
            "lean-kernel/native/storage.c",
            "lean-kernel/native/storage.h",
            "lean-kernel/native/diagonal.c",
            "lean-kernel/native/diagonal.h",
            "lean-kernel/native/diagonal_kernels.inc",
            "lean-kernel/numerical/gemm.h",
            "llvm/runtime/storage.c",
            "llvm/runtime/storage_abi.h",
            "llvm/runtime/gemm.c",
        ] {
            println!("cargo:rerun-if-changed={file}");
        }
        cc::Build::new()
            .cargo_metadata(false)
            .std("c11")
            .opt_level(2)
            .include("lean-kernel/native")
            .include("lean-kernel/numerical")
            .files([
                "lean-kernel/native/storage.c",
                "lean-kernel/native/diagonal.c",
                "llvm/runtime/storage.c",
                "llvm/runtime/gemm.c",
            ])
            .compile("vastitas_llvm_storage");
    }
    let path = "lean-kernel/compiler-limits.json";
    println!("cargo:rerun-if-changed={path}");
    let limits: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(path).expect("read compiler limits"))
            .expect("parse compiler limits");
    let mut source = String::new();
    for (key, name) in [
        ("parseNesting", "MAX_PARSE_NESTING"),
        ("astDepth", "MAX_AST_DEPTH"),
        ("moduleNesting", "MAX_MODULE_NESTING"),
        ("packageNesting", "MAX_PACKAGE_NESTING"),
        ("requestBytes", "MAX_REQUEST_BYTES"),
        ("algebraNesting", "MAX_ALGEBRA_NESTING"),
        ("algebraCoefficientDigits", "MAX_ALGEBRA_DIGITS"),
        ("algebraGenerators", "MAX_ALGEBRA_GENERATORS"),
        ("assemblyEvents", "MAX_ASSEMBLY_EVENTS"),
        ("datasetPoints", "MAX_DATASET_POINTS"),
        ("recordTextBytes", "MAX_RECORD_TEXT_BYTES"),
    ] {
        let value = limits[key]
            .as_u64()
            .expect("positive integer compiler limit");
        assert!(value > 0 && usize::try_from(value).is_ok());
        source.push_str(&format!("pub const {name}: usize = {value};\n"));
    }
    let output = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo output directory"));
    fs::write(output.join("compiler_limits.rs"), source).expect("write compiler limits");
    fs::write(output.join("kernel_identity.rs"), kernel_identity()).expect("write kernel identity");
}

/// Select the qualified static LLVM toolchain explicitly in a source build.
/// The native adapter independently checks the linked library at runtime.
#[cfg(feature = "llvm-native")]
fn check_native_llvm() {
    const PREFIX: &str = "LLVM_SYS_231_PREFIX";
    println!("cargo:rerun-if-env-changed={PREFIX}");
    let root =
        env::var_os(PREFIX).expect("llvm-native requires LLVM_SYS_231_PREFIX for LLVM 23.1.4");
    let config = Path::new(&root).join("bin/llvm-config");
    let version = std::process::Command::new(&config)
        .arg("--version")
        .output()
        .expect("cannot run LLVM_SYS_231_PREFIX/bin/llvm-config --version");
    assert!(
        version.status.success() && version.stdout.trim_ascii() == b"23.1.4",
        "llvm-native requires LLVM 23.1.4, llvm-config reported {:?}",
        String::from_utf8_lossy(&version.stdout).trim()
    );
    println!("cargo:rerun-if-changed={}", config.display());
}

/// The kernel executable reports the digest of `Main.lean`, of every module it
/// imports from the kernel package and of the compiler limits that those
/// modules read while they are elaborated, with its Lean version. Compute the
/// same identity from the files this driver is built with.
fn kernel_identity() -> String {
    let root = Path::new("lean-kernel");
    let toolchain_path = root.join("lean-toolchain");
    println!("cargo:rerun-if-changed={}", toolchain_path.display());
    let toolchain = fs::read_to_string(&toolchain_path).expect("read kernel lean-toolchain");
    let toolchain = toolchain.trim();
    let release = toolchain.rsplit(':').next().unwrap_or_default();
    let lean = release.strip_prefix('v').unwrap_or(release);
    let files = executable_inputs(root).expect("read the inputs of the kernel executable");
    for relative in files.keys() {
        println!("cargo:rerun-if-changed={}", root.join(relative).display());
    }
    let sources = executable_digest(&files);
    let mut identity = format!(
        "pub const SOURCES: &str = \"{sources}\";\npub const LEAN: &str = {lean:?};\npub const TOOLCHAIN: &str = {toolchain:?};\npub const PROTOCOL: u32 = {};\n",
        kernel_protocol(root)
    );
    for (name, package) in [
        ("KERNEL_RUNTIME", &runtime_inputs::KERNEL),
        ("STORAGE_RUNTIME", &runtime_inputs::STORAGE),
        ("NUMERICAL_RUNTIME", &runtime_inputs::NUMERICAL),
    ] {
        identity.push_str(&runtime_table(root, name, package));
    }
    identity
}

/// The wire schema epoch of the kernel: the value of the one definition
/// `def currentProtocol : Nat := N` in `VastitasKernel/Protocol.lean` (#533).
/// `ir::PROTOCOL` must equal it; a constant assertion in `src/ir.rs` fails the
/// build otherwise.
fn kernel_protocol(root: &Path) -> u32 {
    let path = root.join("VastitasKernel/Protocol.lean");
    println!("cargo:rerun-if-changed={}", path.display());
    let source = fs::read_to_string(&path).expect("read the kernel protocol definition");
    let values: Vec<u32> = source
        .lines()
        .filter_map(|line| line.strip_prefix("def currentProtocol : Nat := "))
        .map(|value| {
            value
                .trim()
                .parse()
                .expect("currentProtocol is a decimal natural number")
        })
        .collect();
    match values.as_slice() {
        [value] => *value,
        _ => panic!(
            "{} must define `def currentProtocol : Nat := N` exactly once",
            path.display()
        ),
    }
}

/// The runtime inputs of one package in the sources this driver is built with,
/// as a table of relative paths and digests. A native build compares it with
/// the same files of the selected kernel root before Lake compiles them.
///
/// Every entry is a file that exists, and Cargo watches each one. Cargo cannot
/// watch for a file that does not exist yet: it reruns this script on every
/// build for a missing path, and it scans a watched directory with its build
/// products. The table therefore records no absence. The sources must hold
/// exactly what the lists of `src/runtime_inputs.rs` name, or the build fails
/// here, and the driver applies the rule on forbidden names to the selected
/// root itself.
fn runtime_table(root: &Path, name: &str, package: &Package) -> String {
    let directory = package.directory_in(root);
    let entries = required_inputs(&directory, package).unwrap_or_else(|error| {
        panic!(
            "the {} inputs in {} do not match the lists of src/runtime_inputs.rs: {error}. \
             Restore the package, or change its lists together with its Lake configuration.",
            package.name,
            directory.display()
        )
    });
    let mut table = format!("pub const {name}: &[(&str, &str)] = &[\n");
    for (relative, digest) in &entries {
        println!(
            "cargo:rerun-if-changed={}",
            directory.join(relative).display()
        );
        table.push_str(&format!("    ({relative:?}, {digest:?}),\n"));
    }
    table.push_str("];\n");
    table
}
