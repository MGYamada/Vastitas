use std::collections::BTreeMap;
use std::{env, fs, path::Path, path::PathBuf};

// Shared with the driver, which digests the same files in the selected root.
#[allow(dead_code)]
#[path = "src/runtime_inputs.rs"]
mod runtime_inputs;
use runtime_inputs::{ABSENT, Package, digest, header_imports, inputs};

fn main() {
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
        ("algebraNesting", "MAX_ALGEBRA_NESTING"),
        ("algebraCoefficientDigits", "MAX_ALGEBRA_DIGITS"),
        ("algebraGenerators", "MAX_ALGEBRA_GENERATORS"),
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

/// The kernel executable reports the digest of `Main.lean` and every module it
/// imports from the kernel package, with its Lean version. Compute the same
/// identity from the sources this driver is built with.
fn kernel_identity() -> String {
    let root = Path::new("lean-kernel");
    let toolchain_path = root.join("lean-toolchain");
    println!("cargo:rerun-if-changed={}", toolchain_path.display());
    let toolchain = fs::read_to_string(&toolchain_path).expect("read kernel lean-toolchain");
    let toolchain = toolchain.trim();
    let release = toolchain.rsplit(':').next().unwrap_or_default();
    let lean = release.strip_prefix('v').unwrap_or(release);
    let mut files = BTreeMap::new();
    let mut pending = vec!["Main.lean".to_string()];
    while let Some(relative) = pending.pop() {
        let path = root.join(&relative);
        // Toolchain modules (Init, Lean, Std, ...) are not kernel sources.
        if files.contains_key(&relative) || !path.is_file() {
            continue;
        }
        println!("cargo:rerun-if-changed={}", path.display());
        let bytes = fs::read(&path).expect("read kernel source");
        let source = std::str::from_utf8(&bytes).expect("UTF-8 kernel source");
        for module in header_imports(source) {
            pending.push(format!("{}.lean", module.replace('.', "/")));
        }
        files.insert(relative, bytes);
    }
    let sources = digest(
        files
            .iter()
            .map(|(relative, bytes)| (relative.as_str(), bytes.as_slice())),
    );
    let mut identity = format!(
        "pub const SOURCES: &str = \"{sources}\";\npub const LEAN: &str = {lean:?};\npub const TOOLCHAIN: &str = {toolchain:?};\n"
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

/// The runtime inputs of one package in the sources this driver is built with,
/// as a table of relative paths and digests. A native build compares it with
/// the same files of the selected kernel root before Lake compiles them.
fn runtime_table(root: &Path, name: &str, package: &Package) -> String {
    let directory = package.directory_in(root);
    let entries = inputs(&directory, package).expect("read runtime inputs");
    let mut table = format!("pub const {name}: &[(&str, &str)] = &[\n");
    for (relative, digest) in &entries {
        // Cargo treats a missing path as always changed, so name present files only.
        if digest != ABSENT {
            println!(
                "cargo:rerun-if-changed={}",
                directory.join(relative).display()
            );
        }
        table.push_str(&format!("    ({relative:?}, {digest:?}),\n"));
    }
    for module in package.modules {
        let file = runtime_inputs::module_file(module);
        assert!(
            entries
                .iter()
                .any(|(relative, digest)| *relative == file && digest != ABSENT),
            "runtime module {module} has no source in {}",
            directory.display()
        );
    }
    table.push_str("];\n");
    table
}
