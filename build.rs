use std::collections::BTreeMap;
use std::{env, fs, path::Path, path::PathBuf};

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

/// Modules named by a Lean file header (`import`, optionally `public`/`meta`
/// and `import all`). Lean allows imports only before the first command.
fn header_imports(source: &str) -> Vec<String> {
    let mut rest = source;
    let mut modules = Vec::new();
    let mut importing = false;
    loop {
        rest = rest.trim_start();
        if let Some(comment) = rest.strip_prefix("--") {
            rest = comment.split_once('\n').map_or("", |(_, next)| next);
            continue;
        }
        if rest.starts_with("/-") {
            // Lean block comments nest.
            let bytes = rest.as_bytes();
            let (mut depth, mut index) = (0usize, 0usize);
            rest = "";
            while index + 1 < bytes.len() {
                match &bytes[index..index + 2] {
                    b"/-" => {
                        depth += 1;
                        index += 2;
                    }
                    b"-/" => {
                        depth -= 1;
                        index += 2;
                        if depth == 0 {
                            rest = &source[source.len() - bytes.len() + index..];
                            break;
                        }
                    }
                    _ => index += 1,
                }
            }
            continue;
        }
        let end = rest.find(char::is_whitespace).unwrap_or(rest.len());
        let token = &rest[..end];
        rest = &rest[end..];
        match (importing, token) {
            (_, "") => break,
            (true, "all") => {}
            (true, module) => {
                modules.push(module.to_string());
                importing = false;
            }
            (false, "module" | "prelude" | "public" | "meta" | "private") => {}
            (false, "import") => importing = true,
            (false, _) => break,
        }
    }
    modules
}

/// FNV-1a, 64-bit; `VastitasKernel/BuildIdentity.lean` uses the same function.
fn fnv1a(mut hash: u64, bytes: &[u8]) -> u64 {
    for byte in bytes {
        hash = (hash ^ u64::from(*byte)).wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
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
    let mut hash = 0xcbf2_9ce4_8422_2325;
    for (relative, bytes) in &files {
        hash = fnv1a(hash, relative.as_bytes());
        hash = fnv1a(hash, &[0]);
        hash = fnv1a(hash, bytes.len().to_string().as_bytes());
        hash = fnv1a(hash, &[0]);
        hash = fnv1a(hash, bytes);
    }
    format!(
        "pub const SOURCES: &str = \"{hash:016x}\";\npub const LEAN: &str = {lean:?};\npub const TOOLCHAIN: &str = {toolchain:?};\n"
    )
}
