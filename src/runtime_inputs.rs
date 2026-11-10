//! Runtime inputs of a native build: the files that Lake reads from the kernel
//! root and from the optional runtime packages when it compiles a generated
//! program. `build.rs` digests them in the sources this compiler is built
//! from, and the driver digests them again in the selected kernel root before
//! it runs Lake, so both sides come from the files and never from a value that
//! a root states about itself. `build.rs`, the driver and the test harness
//! share this file; it uses only the standard library.
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::{fs, io};

/// One Lake package that a generated program can depend on.
pub struct Package {
    /// Name used in diagnostics.
    pub name: &'static str,
    /// Directory relative to the kernel root; empty for the root itself.
    pub directory: &'static str,
    /// Files that Lake reads by name. Both configuration names are listed:
    /// Lake prefers `lakefile.lean`, so an added one replaces `lakefile.toml`.
    /// A direct dependency's `lean-toolchain` and manifest can make Lake
    /// restart itself with another toolchain.
    pub files: &'static [&'static str],
    /// Modules that generated programs import. Their import closure inside the
    /// package directory is an input as well.
    pub modules: &'static [&'static str],
}

impl Package {
    /// The package directory inside `kernel_root`.
    pub fn directory_in(&self, kernel_root: &Path) -> PathBuf {
        if self.directory.is_empty() {
            kernel_root.to_path_buf()
        } else {
            kernel_root.join(self.directory)
        }
    }
}

/// The kernel package. Its `lean-toolchain` is not listed: the driver compares
/// that file's pin with the compiler's, ignoring surrounding whitespace, and
/// copies the file into the generated project.
pub const KERNEL: Package = Package {
    name: "kernel runtime",
    directory: "",
    files: &[
        "lakefile.lean",
        "lakefile.toml",
        "lake-manifest.json",
        "compiler-limits.json",
    ],
    modules: &[
        "VastitasKernel.IndexedRuntime",
        "VastitasKernel.AlgebraRuntime",
        "VastitasKernel.SmoothRuntime",
    ],
};

/// The storage runtime, selected by a checked resource program.
pub const STORAGE: Package = Package {
    name: "storage runtime",
    directory: "native",
    files: &[
        "lakefile.lean",
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
        "storage.h",
        "storage.c",
        "ffi.c",
        "ffi_result.h",
        "diagonal.c",
        "diagonal.h",
    ],
    modules: &["VastitasStorageNative"],
};

/// The numerical adapter, selected with the storage runtime by a checked
/// numerical program. Its configuration also reads headers of the storage
/// runtime, which is compared whenever this package is. The OpenBLAS prefix is
/// an explicit build argument and has its own checks.
pub const NUMERICAL: Package = Package {
    name: "numerical runtime",
    directory: "numerical",
    files: &[
        "lakefile.lean",
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
        "gemm.h",
        "gemm.c",
        "ffi.c",
    ],
    modules: &["VastitasGemmNative"],
};

/// Digest text of an input that is not a regular file in a package.
pub const ABSENT: &str = "absent";

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;

/// FNV-1a, 64-bit; `VastitasKernel/BuildIdentity.lean` uses the same function.
/// It detects stale and mixed source trees; it is not collision resistant.
pub fn fnv1a(mut hash: u64, bytes: &[u8]) -> u64 {
    for byte in bytes {
        hash = (hash ^ u64::from(*byte)).wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

/// Digest of named byte strings in the given order, each hashed as
/// `name NUL size NUL bytes`. The kernel's build identity uses this encoding.
pub fn digest<'a>(entries: impl IntoIterator<Item = (&'a str, &'a [u8])>) -> String {
    let mut hash = FNV_OFFSET;
    for (name, bytes) in entries {
        hash = fnv1a(hash, name.as_bytes());
        hash = fnv1a(hash, &[0]);
        hash = fnv1a(hash, bytes.len().to_string().as_bytes());
        hash = fnv1a(hash, &[0]);
        hash = fnv1a(hash, bytes);
    }
    format!("{hash:016x}")
}

/// Modules named by a Lean file header (`import`, optionally `public`/`meta`
/// and `import all`). Lean allows imports only before the first command.
pub fn header_imports(source: &str) -> Vec<String> {
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

/// The source file of a module, relative to its package directory.
pub fn module_file(module: &str) -> String {
    format!("{}.lean", module.replace('.', "/"))
}

/// The bytes of a regular file, or `None` where there is none.
fn regular_file(path: &Path) -> io::Result<Option<Vec<u8>>> {
    match fs::metadata(path) {
        Ok(metadata) if metadata.is_file() => fs::read(path).map(Some),
        Ok(_) => Ok(None),
        Err(error)
            if matches!(
                error.kind(),
                io::ErrorKind::NotFound | io::ErrorKind::NotADirectory
            ) =>
        {
            Ok(None)
        }
        Err(error) => Err(error),
    }
}

/// The inputs of `package` in `directory`, in path order: each listed file and
/// each module file in the import closure, with the digest of its bytes. A
/// listed file or a listed module that is missing is reported as `ABSENT`. An
/// imported module without a source in the directory belongs to the toolchain
/// or to another package and is not an input of this one.
pub fn inputs(directory: &Path, package: &Package) -> io::Result<Vec<(String, String)>> {
    let mut found = BTreeMap::new();
    let entry = |bytes: Option<&[u8]>| {
        bytes.map_or_else(|| ABSENT.to_string(), |bytes| digest([("", bytes)]))
    };
    for name in package.files {
        let bytes = regular_file(&directory.join(name))?;
        found.insert(name.to_string(), entry(bytes.as_deref()));
    }
    let mut pending: Vec<(String, bool)> = package
        .modules
        .iter()
        .map(|module| (module_file(module), true))
        .collect();
    while let Some((relative, listed)) = pending.pop() {
        if found.contains_key(&relative) {
            continue;
        }
        let Some(bytes) = regular_file(&directory.join(&relative))? else {
            if listed {
                found.insert(relative, entry(None));
            }
            continue;
        };
        for module in header_imports(&String::from_utf8_lossy(&bytes)) {
            // Only a plain module name can name a file of this package; any
            // other spelling must not lead the walk out of the directory.
            if module
                .split('.')
                .all(|part| !part.is_empty() && !part.contains('/'))
            {
                pending.push((module_file(&module), false));
            }
        }
        found.insert(relative, entry(Some(&bytes)));
    }
    Ok(found.into_iter().collect())
}

/// One digest for a list of inputs, for diagnostics that name both sides.
pub fn summary<'a>(inputs: impl IntoIterator<Item = (&'a str, &'a str)>) -> String {
    digest(
        inputs
            .into_iter()
            .map(|(path, digest)| (path, digest.as_bytes())),
    )
}
