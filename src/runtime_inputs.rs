//! Runtime inputs of a native build: the files that Lake reads from the kernel
//! root and from the optional runtime packages when it compiles a generated
//! program. `build.rs` digests them in the sources this compiler is built
//! from, and the driver digests them again in the selected kernel root before
//! it runs Lake, so both sides come from the files and never from a value that
//! a root states about itself. The file also names what the kernel executable
//! is elaborated from (`executable_inputs`): `build.rs` digests those files
//! into the build identity that the driver expects from the kernel.
//! `build.rs`, the driver and the test harness share this file; it uses only
//! the standard library.
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::{fs, io};

/// One Lake package that a generated program can depend on.
pub struct Package {
    /// Name used in diagnostics.
    pub name: &'static str,
    /// Directory relative to the kernel root; empty for the root itself.
    pub directory: &'static str,
    /// Files that Lake reads by name. Each exists in the compiler's own
    /// sources: `build.rs` fails without one. A direct dependency's
    /// `lean-toolchain` and manifest can make Lake restart itself with another
    /// toolchain.
    pub files: &'static [&'static str],
    /// Names that must not exist in the package directory: the other name of
    /// its Lake configuration. Lake prefers `lakefile.lean`, so an added one
    /// replaces a listed `lakefile.toml`. This is a rule of the list and not a
    /// recorded value: Cargo cannot watch for a file that does not exist yet,
    /// so a recorded absence would outlive the creation of the file.
    pub forbidden: &'static [&'static str],
    /// Modules that generated programs import. Their import closure inside the
    /// package's own library is an input as well.
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

    /// Whether `module` belongs to the library of the listed modules: a plain
    /// module name with the same first component. Lake compiles such a module
    /// from the package directory, so its source is an input. Any other
    /// import names a module of the toolchain or of another package.
    fn owns(&self, module: &str) -> bool {
        let library = module.split('.').next();
        module
            .split('.')
            .all(|part| !part.is_empty() && !part.contains('/'))
            && self
                .modules
                .iter()
                .any(|listed| listed.split('.').next() == library)
    }
}

/// The kernel package. Its `lean-toolchain` is not listed: the driver compares
/// that file's pin with the compiler's, ignoring surrounding whitespace, and
/// copies the file into the generated project.
pub const KERNEL: Package = Package {
    name: "kernel runtime",
    directory: "",
    files: &[
        "lakefile.toml",
        "lake-manifest.json",
        "compiler-limits.json",
    ],
    forbidden: &["lakefile.lean"],
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
        "lake-manifest.json",
        "lean-toolchain",
        "storage.h",
        "storage.c",
        "ffi.c",
        "ffi_result.h",
        "diagonal.c",
        "diagonal.h",
    ],
    forbidden: &["lakefile.toml"],
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
        "lake-manifest.json",
        "lean-toolchain",
        "gemm.h",
        "gemm.c",
        "ffi.c",
    ],
    forbidden: &["lakefile.toml"],
    modules: &["VastitasGemmNative"],
};

/// Digest text of a forbidden name that exists and is not a regular file.
pub const IRREGULAR: &str = "not a regular file";

/// Libraries of the toolchain. A runtime source may import their modules.
const TOOLCHAIN_LIBRARIES: &[&str] = &["Init", "Std", "Lean", "Lake"];

/// Whether `library` is outside every package that imports it here: a library
/// of the toolchain, or the library of a runtime package, whose sources are
/// compared as that package's inputs.
fn external(library: &str) -> bool {
    TOOLCHAIN_LIBRARIES.contains(&library)
        || [&KERNEL, &STORAGE, &NUMERICAL].iter().any(|package| {
            package
                .modules
                .iter()
                .any(|module| module.split('.').next() == Some(library))
        })
}

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

/// Files of the kernel root, other than Lean sources, that a module of the
/// kernel executable reads while it is elaborated: `Limits.lean` reads the
/// compiler limits (`compiler_limit%`). `VastitasKernel/BuildIdentity.lean`
/// holds the same list.
pub const ELABORATION_INPUTS: &[&str] = &["compiler-limits.json"];

/// The files that the kernel executable of `kernel_root` is elaborated from,
/// by relative path: `Main.lean`, each module of its import closure that has a
/// source in the root, and `ELABORATION_INPUTS`. An imported module without a
/// source there belongs to the toolchain.
// `build.rs` and the tests call this; the compiler embeds the result.
#[allow(dead_code)]
pub fn executable_inputs(kernel_root: &Path) -> io::Result<BTreeMap<String, Vec<u8>>> {
    let mut files = BTreeMap::new();
    let mut pending = vec!["Main.lean".to_string()];
    while let Some(relative) = pending.pop() {
        let path = kernel_root.join(&relative);
        if files.contains_key(&relative) || !path.is_file() {
            continue;
        }
        let bytes = fs::read(&path)?;
        let source = std::str::from_utf8(&bytes).map_err(|error| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("{}: {error}", path.display()),
            )
        })?;
        for module in header_imports(source) {
            pending.push(module_file(&module));
        }
        files.insert(relative, bytes);
    }
    for name in ELABORATION_INPUTS {
        files.insert(name.to_string(), fs::read(kernel_root.join(name))?);
    }
    Ok(files)
}

/// The `sources` digest of the kernel's build identity for the files that
/// `executable_inputs` returns. The kernel computes it from the same files
/// while `Main` is elaborated (`kernel_source_digest%`).
#[allow(dead_code)]
pub fn executable_digest(inputs: &BTreeMap<String, Vec<u8>>) -> String {
    digest(
        inputs
            .iter()
            .map(|(relative, bytes)| (relative.as_str(), bytes.as_slice())),
    )
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

/// What `directory` holds for `package`: its inputs by relative path, each
/// with the digest of its bytes, and what the directory lacks or adds against
/// the lists. The inputs are the listed files, the listed modules and the
/// modules of the package's library that those import. A forbidden name that
/// exists is recorded as well, so that a comparison reports it. An import of
/// any other module is not followed. With `strict`, such an import is a
/// problem unless its library is `external`, and also when a file or a
/// directory of the package has the library's name: its source could be an
/// input that the lists do not name.
fn survey(
    directory: &Path,
    package: &Package,
    strict: bool,
) -> io::Result<(BTreeMap<String, String>, Vec<String>)> {
    let mut found = BTreeMap::new();
    let mut problems = Vec::new();
    let entry = |bytes: &[u8]| digest([("", bytes)]);
    for name in package.files {
        match regular_file(&directory.join(name))? {
            Some(bytes) => {
                found.insert(name.to_string(), entry(&bytes));
            }
            None => problems.push(format!("{name} is missing")),
        }
    }
    for name in package.forbidden {
        let path = directory.join(name);
        // A dangling link is present too: nothing may have this name.
        if fs::symlink_metadata(&path).is_ok() {
            let state =
                regular_file(&path)?.map_or_else(|| IRREGULAR.to_string(), |bytes| entry(&bytes));
            found.insert(name.to_string(), state);
            problems.push(format!(
                "{name} must not exist: it is the other name of the package's Lake configuration"
            ));
        }
    }
    let mut visited = BTreeSet::new();
    let mut pending: Vec<(String, Option<String>)> = package
        .modules
        .iter()
        .map(|module| (module.to_string(), None))
        .collect();
    while let Some((module, importer)) = pending.pop() {
        let relative = module_file(&module);
        if !visited.insert(relative.clone()) {
            continue;
        }
        let Some(bytes) = regular_file(&directory.join(&relative))? else {
            problems.push(match importer {
                None => format!("module {module} has no source {relative}"),
                Some(importer) => {
                    format!("{importer} imports {module}, which has no source {relative}")
                }
            });
            continue;
        };
        for import in header_imports(&String::from_utf8_lossy(&bytes)) {
            if package.owns(&import) {
                pending.push((import, Some(relative.clone())));
            } else if strict {
                let library = import.split('.').next().unwrap_or_default();
                if !external(library) {
                    problems.push(format!(
                        "{relative} imports {import}, which is not a module of this package's runtime library, of another runtime package or of the toolchain"
                    ));
                } else if directory.join(library).exists()
                    || directory.join(format!("{library}.lean")).exists()
                {
                    problems.push(format!(
                        "{relative} imports {import}, whose source is in this package and outside its runtime library"
                    ));
                }
            }
        }
        found.insert(relative, entry(&bytes));
    }
    Ok((found, problems))
}

/// The inputs of `package` that `directory` holds, in path order. A selected
/// kernel root is read this way: a listed file or module that it lacks has no
/// entry, and a forbidden name that it adds has one, so the comparison with
/// the compiler's table reports the first as missing and the second as
/// unexpected.
pub fn inputs(directory: &Path, package: &Package) -> io::Result<Vec<(String, String)>> {
    Ok(survey(directory, package, false)?.0.into_iter().collect())
}

/// The inputs of `package` in the compiler's own sources, in path order.
/// `build.rs` builds its table from them and registers every one with Cargo.
/// It is an error for `directory` to differ from the lists: a listed file or
/// module without a source, a forbidden name, an import of the package's
/// library without a source, or an import of any other module that is not
/// external or whose library has a source in the package. Every entry
/// therefore names a file that exists. The paths of the table follow from the
/// lists and from the imports in files that are in it, so the creation of a
/// file cannot change what the table has to hold: Lake compiles a module from
/// a package only for a library of that package's configuration, which is in
/// the table.
// `build.rs` and the tests call this; the compiler embeds the result.
#[allow(dead_code)]
pub fn required_inputs(directory: &Path, package: &Package) -> io::Result<Vec<(String, String)>> {
    let (found, problems) = survey(directory, package, true)?;
    if problems.is_empty() {
        Ok(found.into_iter().collect())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidData,
            problems.join("; "),
        ))
    }
}

/// One digest for a list of inputs, for diagnostics that name both sides.
pub fn summary<'a>(inputs: impl IntoIterator<Item = (&'a str, &'a str)>) -> String {
    digest(
        inputs
            .into_iter()
            .map(|(path, digest)| (path, digest.as_bytes())),
    )
}
