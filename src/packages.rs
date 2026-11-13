//! Explicit path-package loading. Namespace references remain unresolved in the
//! wire request: only Lean can accept them and assign function identities.
use crate::frontend;
use crate::ir::{
    ABSTRACT_PROTOCOL_VERSION, AbstractMethod, AbstractType, Function, Generic, Method, Span,
    Subtype,
};
use crate::limits::{MAX_MODULE_NESTING, MAX_PACKAGE_NESTING};
use crate::sources::{OutputIdentity, Sources, shown, shown_text};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::ffi::OsString;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};

pub(crate) const PROTOCOL: u32 = 3;
pub(crate) const EDIT_PROTOCOL: u32 = 5;
pub(crate) const AUTHORITY_PROTOCOL: u32 = 6;
pub(crate) const INDEXED_PROTOCOL: u32 = 7;
pub(crate) const RESOURCE_PROTOCOL: u32 = 8;
pub(crate) const NAMED_RECIPIENT_PROTOCOL: u32 = 9;
pub(crate) const PUBLIC_PROTOCOLS: [u32; 8] = [
    crate::ir::PROTOCOL_VERSION,
    PROTOCOL,
    ABSTRACT_PROTOCOL_VERSION,
    EDIT_PROTOCOL,
    AUTHORITY_PROTOCOL,
    INDEXED_PROTOCOL,
    RESOURCE_PROTOCOL,
    NAMED_RECIPIENT_PROTOCOL,
];

#[derive(Debug, Serialize)]
pub(crate) struct Grant {
    pub name: String,
    pub target: Vec<String>,
    pub grantee_package: String,
    pub grantee_path: Vec<String>,
    pub region: Vec<Vec<String>>,
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub delegable: bool,
    pub span: Span,
}

#[derive(Debug, Serialize)]
pub(crate) struct Transfer {
    pub name: String,
    pub target: Vec<String>,
    pub grantee_package: String,
    pub grantee_path: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Serialize)]
pub(crate) struct Contribution {
    pub name: String,
    pub target: Vec<String>,
    pub methods: Vec<Method>,
    pub span: Span,
}

#[derive(Debug, Serialize)]
pub(crate) struct Assembly {
    pub events: Vec<EditEvent>,
    pub span: Span,
}

#[derive(Debug, Serialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub(crate) enum EditEvent {
    Borrow {
        grant: Vec<String>,
        loan: String,
        span: Span,
    },
    Apply {
        contribution: Vec<String>,
        loan: Option<String>,
        span: Span,
    },
    Return {
        loan: String,
        span: Span,
    },
    Seal {
        target: Vec<String>,
        span: Span,
    },
    Reborrow {
        parent: String,
        delegation: Vec<String>,
        loan: String,
        span: Span,
    },
    Transfer {
        declaration: Vec<String>,
        span: Span,
    },
}

#[derive(Debug, Serialize)]
pub(crate) struct Public<T> {
    #[serde(flatten)]
    pub declaration: T,
    pub public: bool,
}

#[derive(Debug, Serialize)]
pub(crate) struct Import {
    pub path: Vec<String>,
    pub alias: String,
    pub public: bool,
    pub span: Span,
    /// The place of the name that a `use` without `as` binds, when that name
    /// is a compatibility spelling: the parser cannot tell whether the path
    /// names an `indexed` declaration, which may take it, or a module, which
    /// may not (`reserved_module_uses`). Not part of the request.
    #[serde(skip)]
    pub deferred_name: Option<Span>,
}

#[derive(Debug, Serialize)]
pub(crate) struct Module {
    pub path: Vec<String>,
    pub public: bool,
    pub imports: Vec<Import>,
    pub functions: Vec<Public<Function>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub resource_functions: Vec<Public<crate::storage::source::Function>>,
    pub generics: Vec<Public<Generic>>,
    pub methods: Vec<Method>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub indexed_declarations: Vec<Public<crate::indexed::Declaration>>,
    #[serde(skip)]
    pub uses_indexed: bool,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub abstract_types: Vec<Public<AbstractType>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub subtypes: Vec<Subtype>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub abstract_methods: Vec<AbstractMethod>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub grants: Vec<Public<Grant>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub delegations: Vec<Public<Grant>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub transfers: Vec<Public<Transfer>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub contributions: Vec<Public<Contribution>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub assembly: Option<Assembly>,
    pub span: Span,
}

pub(crate) struct External {
    pub path: Vec<String>,
    pub public: bool,
    pub span: Span,
}

pub(crate) struct Parsed {
    pub modules: Vec<Module>,
    pub external: Vec<External>,
}

#[derive(Debug, Serialize)]
struct Dependency {
    alias: String,
    target: String,
}

#[derive(Debug, Serialize)]
struct Package {
    source: String,
    name: String,
    version: String,
    dependencies: Vec<Dependency>,
    modules: Vec<Module>,
    #[serde(skip_serializing_if = "Option::is_none")]
    geometry_compat: Option<crate::indexed::GeometryProfile>,
}

#[derive(Debug, Serialize)]
pub(crate) struct Program {
    pub version: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    input: Option<String>,
    file: String,
    root: String,
    packages: Vec<Package>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    package: Metadata,
    #[serde(default)]
    dependencies: BTreeMap<String, PathDependency>,
    geometry_compat: Option<crate::indexed::GeometryProfile>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Metadata {
    name: String,
    version: String,
    root: PathBuf,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct PathDependency {
    path: PathBuf,
}

struct Loader {
    sources: Sources,
    packages: Vec<Package>,
    // Sources of `packages`, so a shared dependency is found in constant time.
    loaded: HashSet<String>,
    active: HashSet<PathBuf>,
    output: Option<OutputIdentity>,
    module_count: usize,
    /// On-disk entry names per directory, read once for exact-name lookup.
    listings: HashMap<PathBuf, HashSet<OsString>>,
}

// Count logical modules across the selected closure, including inline modules
// and independent uses of the same file. A depth limit alone cannot bound fanout.
const MAX_LOADED_MODULES: usize = 4096;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Existence {
    Missing,
    Exact,
    /// The path resolves, but some component's on-disk name differs (in case).
    CaseMismatch,
}

/// Whether `base` joined with `names` exists with exactly these entry names.
/// Case-insensitive filesystems (default macOS APFS) would otherwise resolve
/// `mod Math;` to `math.vast`, or load one file for both `mod a;` and `mod A;`.
/// Directory listings are cached, so sibling modules cost one `read_dir`.
fn existence(
    listings: &mut HashMap<PathBuf, HashSet<OsString>>,
    base: &Path,
    names: &[OsString],
) -> std::io::Result<Existence> {
    let path = names
        .iter()
        .fold(base.to_path_buf(), |path, name| path.join(name));
    if !path.try_exists()? {
        return Ok(Existence::Missing);
    }
    let mut directory = base.to_path_buf();
    for name in names {
        if !listings.contains_key(&directory) {
            let entries = std::fs::read_dir(&directory)?
                .map(|entry| entry.map(|entry| entry.file_name()))
                .collect::<std::io::Result<HashSet<_>>>()?;
            listings.insert(directory.clone(), entries);
        }
        if !listings[&directory].contains(name) {
            return Ok(Existence::CaseMismatch);
        }
        directory.push(name);
    }
    Ok(Existence::Exact)
}

/// The message of a TOML error as an `E_MANIFEST` error shows it. toml puts
/// the parts of a message on lines of their own, and a message can quote a key
/// or a string of the manifest. A key or a string holds a line feed only
/// through an escape or in a multi-line string. So in a manifest without a
/// backslash and without a multi-line string, every line feed of the message
/// is toml's own and stays a line break. In any other manifest a line feed may
/// be manifest text, and each one is named like every other control.
fn shown_message(source: &str, message: &str) -> String {
    if source.contains('\\') || source.contains("\"\"\"") || source.contains("'''") {
        shown_text(message)
    } else {
        let lines: Vec<String> = message.split('\n').map(shown_text).collect();
        lines.join("\n")
    }
}

/// The four lines that toml writes ahead of the message of an error with a
/// position, shown as `shown_text` shows manifest text:
///
/// ```text
/// TOML parse error at line 4, column 22
///   |
/// 4 | root = "main.vast" # …
///   |                      ^
/// ```
///
/// The third quotes the line of the manifest, and the carets of the fourth
/// mark the place in it. A name such as `<U+001B>` is wider than the character
/// it replaces. The carets therefore move right by what the names ahead of the
/// place add, and widen by what the names under them add. A line without such
/// characters is shown as toml renders it: toml counts the place in bytes, so
/// its carets run past a place that holds characters of several bytes, and
/// they still do. The carriage return of a CR LF line end is no part of the
/// quoted line. `None` when `rendered` has another shape or does not quote
/// the line of `source` that it numbers.
fn shown_position(source: &str, rendered: &str) -> Option<String> {
    let mut lines = rendered.splitn(5, '\n');
    let (header, bar, quoted, marks) = (lines.next()?, lines.next()?, lines.next()?, lines.next()?);
    // The message follows.
    lines.next()?;
    let (number, line) = quoted.split_once(" | ")?;
    let (margin, marks) = marks.split_once('|')?;
    let carets = marks.trim_start_matches(' ');
    // The caret under the first character of the line follows one space.
    let column = (marks.len() - carets.len()).checked_sub(1)?;
    let index = number.parse::<usize>().ok()?.checked_sub(1)?;
    if !header.starts_with(&format!("TOML parse error at line {number}, column "))
        || bar.trim_start_matches(' ') != "|"
        || !margin.bytes().all(|byte| byte == b' ')
        || carets.is_empty()
        || !carets.bytes().all(|byte| byte == b'^')
        || source.split('\n').nth(index) != Some(line)
    {
        return None;
    }
    let line = line.strip_suffix('\r').unwrap_or(line);
    let ahead: String = line.chars().take(column).collect();
    let marked: String = line.chars().skip(column).take(carets.len()).collect();
    let widening = |text: &str| shown_text(text).chars().count() - text.chars().count();
    Some(format!(
        "{}\n{bar}\n{number} | {}\n{margin}|{}{}",
        shown_text(header),
        shown_text(line),
        " ".repeat(column + 1 + widening(&ahead)),
        "^".repeat(carets.len() + widening(&marked)),
    ))
}

/// A TOML error as an `E_MANIFEST` error shows it: toml's rendering, with the
/// text of the manifest shown as `shown_text` shows it. A manifest without a
/// character that `shown_text` names prints as toml renders it, apart from
/// the carriage returns of CR LF line ends.
fn manifest_error(source: &str, error: &toml::de::Error) -> String {
    let rendered = error.to_string();
    let position = error.span().and_then(|_| shown_position(source, &rendered));
    match position {
        Some(position) => format!("{position}\n{}\n", shown_message(source, error.message())),
        // Without a position toml writes the message and the keys that lead
        // to the place, which are manifest text as well.
        None => {
            let text = rendered.strip_suffix('\n').unwrap_or(&rendered);
            format!("{}\n", shown_message(source, text))
        }
    }
}

fn canonical(path: &Path) -> Result<PathBuf, String> {
    path.canonicalize()
        .map_err(|error| format!("E_INPUT: cannot read {}: {error}", shown(path)))
}

fn identifier(name: &str) -> bool {
    let mut chars = name.chars();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

impl Loader {
    fn package(&mut self, manifest: &Path) -> Result<String, String> {
        if manifest
            .file_name()
            .is_none_or(|name| name != "Vastitas.toml")
        {
            return Err("E_INPUT: package manifest must be named Vastitas.toml".into());
        }
        let manifest = canonical(manifest)?;
        let source = manifest
            .to_str()
            .ok_or("E_INPUT: manifest path must be UTF-8")?
            .to_owned();
        if self.active.contains(&manifest) {
            return Err(format!(
                "E_CYCLE: cyclic package dependency at {}",
                shown(&manifest)
            ));
        }
        if self.loaded.contains(&source) {
            return Ok(source);
        }
        if self.active.len() >= MAX_PACKAGE_NESTING {
            return Err(format!(
                "E_LIMIT: package dependency nesting exceeds {MAX_PACKAGE_NESTING}"
            ));
        }
        self.active.insert(manifest.clone());
        let input = self.sources.add(&manifest, self.output.as_ref())?;
        let parsed: Manifest = toml::from_str(input.source).map_err(|error| {
            format!(
                "{}: E_MANIFEST: {}",
                shown(&manifest),
                manifest_error(input.source, &error)
            )
        })?;
        if parsed.package.name.is_empty() {
            return Err(format!(
                "{}: E_MANIFEST: package name must not be empty",
                shown(&manifest)
            ));
        }
        semver::Version::parse(&parsed.package.version).map_err(|error| {
            format!(
                "{}: E_MANIFEST: invalid SemVer: {}",
                shown(&manifest),
                shown_text(&error.to_string())
            )
        })?;
        let directory = manifest.parent().unwrap();
        let root = canonical(&directory.join(&parsed.package.root))?;
        self.inside(&root, directory)?;
        let mut dependencies = Vec::new();
        for (alias, dep) in parsed.dependencies {
            if !identifier(&alias) {
                return Err(format!(
                    "{}: E_MANIFEST: dependency alias must be an ASCII identifier",
                    shown(&manifest)
                ));
            }
            if frontend::reserved(&alias)
                || matches!(
                    alias.as_str(),
                    "mod" | "use" | "pub" | "self" | "super" | "package"
                )
            {
                return Err(format!(
                    "{}: E_MANIFEST: dependency alias '{alias}' is reserved",
                    shown(&manifest)
                ));
            }
            let target = self.package(&directory.join(dep.path).join("Vastitas.toml"))?;
            dependencies.push(Dependency { alias, target });
        }
        let mut modules = Vec::new();
        let mut seen = HashSet::new();
        self.module_file(
            &root,
            root.parent().unwrap(),
            directory,
            Vec::new(),
            true,
            None,
            &mut seen,
            &mut modules,
        )?;
        self.loaded.insert(source.clone());
        self.packages.push(Package {
            source: source.clone(),
            name: parsed.package.name,
            version: parsed.package.version,
            dependencies,
            modules,
            geometry_compat: parsed.geometry_compat,
        });
        self.active.remove(&manifest);
        Ok(source)
    }

    fn inside(&self, source: &Path, package: &Path) -> Result<(), String> {
        if !source.starts_with(package) {
            return Err(format!(
                "E_INPUT: module file escapes package directory: {}",
                shown(source)
            ));
        }
        if source.extension().is_none_or(|ext| ext != "vast") {
            return Err(format!(
                "E_INPUT: module filename must have the .vast extension: {}",
                shown(source)
            ));
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn module_file(
        &mut self,
        file: &Path,
        base: &Path,
        package: &Path,
        path: Vec<String>,
        public: bool,
        declaration: Option<Span>,
        seen: &mut HashSet<(u64, u64)>,
        modules: &mut Vec<Module>,
    ) -> Result<(), String> {
        if self.module_count >= MAX_LOADED_MODULES {
            return Err(format!(
                "E_LIMIT: package closure exceeds {MAX_LOADED_MODULES} logical modules"
            ));
        }
        if path.len() > MAX_MODULE_NESTING {
            return Err(format!(
                "E_LIMIT: module nesting exceeds {MAX_MODULE_NESTING}"
            ));
        }
        let file = canonical(file)?;
        self.inside(&file, package)?;
        let metadata = std::fs::metadata(&file)
            .map_err(|error| format!("E_INPUT: cannot inspect {}: {error}", shown(&file)))?;
        let identity = (metadata.dev(), metadata.ino());
        if !seen.insert(identity) {
            return Err(format!("E_CYCLE: cyclic module loading: {}", shown(&file)));
        }
        let input = self.sources.add(&file, self.output.as_ref())?;
        let parsed =
            frontend::parse_module_source(input, path, public, declaration).map_err(|error| {
                self.sources
                    .diagnostic(&error.code, &error.message, error.span)
            })?;
        if parsed.modules.len() > MAX_LOADED_MODULES - self.module_count {
            return Err(format!(
                "E_LIMIT: package closure exceeds {MAX_LOADED_MODULES} logical modules"
            ));
        }
        self.module_count += parsed.modules.len();
        modules.extend(parsed.modules);
        for external in parsed.external {
            let logical = external
                .path
                .iter()
                .fold(base.to_path_buf(), |dir, part| dir.join(part));
            let flat = logical.with_extension("vast");
            let nested = logical.join("mod.vast");
            let (leaf, parents) = external.path.split_last().expect("module path");
            let flat_names: Vec<OsString> = parents
                .iter()
                .map(OsString::from)
                .chain([OsString::from(format!("{leaf}.vast"))])
                .collect();
            let nested_names: Vec<OsString> = external
                .path
                .iter()
                .map(OsString::from)
                .chain([OsString::from("mod.vast")])
                .collect();
            use Existence::{CaseMismatch, Exact, Missing};
            let file = match (
                existence(&mut self.listings, base, &flat_names).ok(),
                existence(&mut self.listings, base, &nested_names).ok(),
            ) {
                (Some(Exact), Some(Missing | CaseMismatch)) => flat,
                (Some(Missing | CaseMismatch), Some(Exact)) => nested,
                (Some(flat_state), Some(nested_state))
                    if flat_state == CaseMismatch || nested_state == CaseMismatch =>
                {
                    let spelled = if flat_state == CaseMismatch {
                        &flat
                    } else {
                        &nested
                    };
                    return Err(self.sources.diagnostic(
                        "E_INPUT",
                        &format!(
                            "module path {} matches a file only case-insensitively; module names are case-sensitive",
                            shown(spelled)
                        ),
                        external.span,
                    ));
                }
                (Some(Exact), Some(Exact)) => {
                    return Err(self.sources.diagnostic(
                        "E_INPUT",
                        &format!(
                            "ambiguous module: both {} and {} exist",
                            shown(&flat),
                            shown(&nested)
                        ),
                        external.span,
                    ));
                }
                (Some(Missing), Some(Missing)) => {
                    return Err(self.sources.diagnostic(
                        "E_INPUT",
                        &format!("module requires {} or {}", shown(&flat), shown(&nested)),
                        external.span,
                    ));
                }
                _ => {
                    return Err(self.sources.diagnostic(
                        "E_INPUT",
                        "cannot inspect module candidates",
                        external.span,
                    ));
                }
            };
            self.module_file(
                &file,
                base,
                package,
                external.path,
                external.public,
                Some(external.span),
                seen,
                modules,
            )?;
        }
        seen.remove(&identity);
        Ok(())
    }
}

/// The import paths of every module of the loaded packages: package source,
/// then module path, then the alias of each `use` with its path. An alias
/// keeps its first `use`, as the kernel's index does.
type ModuleImports<'a> = HashMap<&'a str, HashMap<&'a [String], HashMap<&'a str, &'a [String]>>>;

/// A module, as its package and its path.
type ModuleTarget<'a> = (&'a Package, Vec<String>);

/// A name that `use` binds is reserved in a `use` of a module (#759),
/// and so is every compatibility spelling, which only an `indexed` declaration
/// and a `use` without `as` of one may take. The parser cannot tell what the
/// path of such a `use` names. Once every package is loaded, a path that names
/// a module through modules, dependency aliases and imports is rejected here,
/// with the diagnostic at the name. A path that names anything else, or that
/// runs into a cycle of imports, is left to the kernel, which checks every
/// `use` itself (`NamespaceChecker.validateWithWork`).
fn reserved_module_uses(packages: &[Package], sources: &Sources) -> Result<(), String> {
    let mut modules: ModuleImports = HashMap::new();
    for package in packages {
        let paths = modules.entry(package.source.as_str()).or_default();
        for module in &package.modules {
            let imports = paths.entry(module.path.as_slice()).or_default();
            for import in &module.imports {
                imports
                    .entry(import.alias.as_str())
                    .or_insert(import.path.as_slice());
            }
        }
    }
    let mut uses = UseTargets {
        packages: packages.iter().map(|p| (p.source.as_str(), p)).collect(),
        modules,
        resolved: HashMap::new(),
    };
    for package in packages {
        for module in &package.modules {
            for import in &module.imports {
                let Some(place) = import.deferred_name else {
                    continue;
                };
                if uses.resolve(package, &module.path, &import.path).is_none() {
                    continue;
                }
                frontend::check_binding_name(&import.alias, place)
                    .map_err(|error| sources.diagnostic(&error.code, &error.message, error.span))?;
            }
        }
    }
    Ok(())
}

/// The modules that `use` paths name, as the kernel's `resolveAt` resolves
/// them, restricted to modules. Visibility is not checked: a `use` that binds
/// a reserved name is an error whether or not its target is visible, as for
/// `use … as`. Each `use` is followed once, so the check is linear in the
/// imports of the program.
struct UseTargets<'a> {
    packages: HashMap<&'a str, &'a Package>,
    modules: ModuleImports<'a>,
    /// The module that a `use` names, by package, module and alias, once it
    /// is followed: `None` while it is followed, so a cycle of imports ends.
    resolved: HashMap<(&'a str, &'a [String], &'a str), Option<ModuleTarget<'a>>>,
}

impl<'a> UseTargets<'a> {
    /// The module that `path` names in the module `scope` of `package`, or
    /// `None` when it names something else or runs into a cycle of imports.
    fn resolve(
        &mut self,
        package: &'a Package,
        scope: &[String],
        path: &[String],
    ) -> Option<ModuleTarget<'a>> {
        let (first, rest) = path.split_first()?;
        let (mut at, rest) = match first.as_str() {
            "package" if !rest.is_empty() => ((package, Vec::new()), rest),
            "self" => ((package, scope.to_vec()), rest),
            "super" => {
                let supers = path.iter().take_while(|name| *name == "super").count();
                let parent = scope.len().checked_sub(supers)?;
                ((package, scope[..parent].to_vec()), &path[supers..])
            }
            _ => match package.dependencies.iter().find(|d| &d.alias == first) {
                Some(dependency) => {
                    let target = *self.packages.get(dependency.target.as_str())?;
                    ((target, Vec::new()), rest)
                }
                None => (self.member(package, scope, first)?, rest),
            },
        };
        for name in rest {
            at = self.member(at.0, &at.1, name)?;
        }
        Some(at)
    }

    /// The child module `name` of the module `scope` of `package`, or the
    /// module that its `use` of alias `name` names. The kernel's `memberAt`
    /// looks at the declarations of the scope first, and a module is one.
    fn member(
        &mut self,
        package: &'a Package,
        scope: &[String],
        name: &str,
    ) -> Option<ModuleTarget<'a>> {
        let modules = self.modules.get(package.source.as_str())?;
        let mut child = scope.to_vec();
        child.push(name.to_owned());
        if modules.contains_key(child.as_slice()) {
            return Some((package, child));
        }
        let (&scope, imports) = modules.get_key_value(scope)?;
        let (&alias, &path) = imports.get_key_value(name)?;
        let key = (package.source.as_str(), scope, alias);
        if let Some(target) = self.resolved.get(&key) {
            return target.clone();
        }
        self.resolved.insert(key, None);
        let target = self.resolve(package, scope, path);
        self.resolved.insert(key, target.clone());
        target
    }
}

pub(crate) fn load(manifest: &Path, output: Option<&Path>) -> Result<(Sources, Program), String> {
    let mut loader = Loader {
        sources: Sources::empty(),
        packages: Vec::new(),
        loaded: HashSet::new(),
        active: HashSet::new(),
        output: output.map(OutputIdentity::inspect).transpose()?.flatten(),
        module_count: 0,
        listings: HashMap::new(),
    };
    let root = loader.package(manifest)?;
    reserved_module_uses(&loader.packages, &loader.sources)?;
    // The kernel bounds the `value` blocks of all resource functions of the
    // program, and refuses more without a place in the source. The frontend
    // counts the same blocks in the order of the request and reports the
    // function at which the count passes the bound (#704).
    let mut blocks = 0;
    for function in loader
        .packages
        .iter()
        .flat_map(|package| &package.modules)
        .flat_map(|module| &module.resource_functions)
    {
        blocks += frontend::value_blocks(&function.declaration);
        if blocks > frontend::MAX_RESOURCE_VALUE_BLOCKS {
            return Err(loader.sources.diagnostic(
                "E_RESOURCE_LIMIT",
                &format!(
                    "the resource functions of the program exceed the limit of {} `value` blocks",
                    frontend::MAX_RESOURCE_VALUE_BLOCKS
                ),
                function.declaration.span,
            ));
        }
    }
    // Preserve recipient names verbatim. The kernel alone resolves them in the
    // selected closure; a grant must neither resolve a path nor load a package.
    let named_recipients = loader
        .packages
        .iter()
        .flat_map(|p| &p.modules)
        .any(|m| !m.grants.is_empty() || !m.delegations.is_empty() || !m.transfers.is_empty());
    let authority = loader.packages.iter().flat_map(|p| &p.modules).any(|m| {
        !m.delegations.is_empty()
            || !m.transfers.is_empty()
            || m.grants.iter().any(|g| g.declaration.delegable)
            || m.assembly.as_ref().is_some_and(|a| {
                a.events.iter().any(|event| {
                    matches!(
                        event,
                        EditEvent::Reborrow { .. } | EditEvent::Transfer { .. }
                    )
                })
            })
    });
    let editable =
        authority
            || loader.packages.iter().flat_map(|p| &p.modules).any(|m| {
                !m.grants.is_empty() || !m.contributions.is_empty() || m.assembly.is_some()
            });
    let extended = loader.packages.iter().flat_map(|p| &p.modules).any(|m| {
        !m.abstract_types.is_empty() || !m.subtypes.is_empty() || !m.abstract_methods.is_empty()
    });
    let indexed = loader
        .packages
        .iter()
        .flat_map(|p| &p.modules)
        .any(|m| m.uses_indexed)
        || loader.packages.iter().any(|p| p.geometry_compat.is_some());
    // Stage 2 algebraic forms exist only in the current schema epoch (#533).
    let algebraic = loader
        .packages
        .iter()
        .flat_map(|p| &p.modules)
        .flat_map(|m| &m.indexed_declarations)
        .any(|d| d.declaration.body.is_algebraic());
    let program = Program {
        version: if named_recipients || algebraic {
            NAMED_RECIPIENT_PROTOCOL
        } else if loader.packages.iter().flat_map(|p| &p.modules).any(|m| {
            !m.resource_functions.is_empty()
                || m.indexed_declarations.iter().any(|d| {
                    matches!(&d.declaration.body, crate::indexed::DeclarationBody::Implementation {
                    representation, ..
                } if !matches!(representation, crate::indexed::Representation::AffineDescriptor))
                })
        }) {
            RESOURCE_PROTOCOL
        } else if indexed {
            INDEXED_PROTOCOL
        } else if authority {
            AUTHORITY_PROTOCOL
        } else if editable {
            EDIT_PROTOCOL
        } else if extended {
            ABSTRACT_PROTOCOL_VERSION
        } else {
            PROTOCOL
        },
        input: (indexed
            || extended
            || editable
            || loader
                .packages
                .iter()
                .flat_map(|p| &p.modules)
                .any(|m| !m.resource_functions.is_empty()))
        .then(|| "package".into()),
        file: root.clone(),
        root,
        packages: loader.packages,
    };
    Ok((loader.sources, program))
}

#[cfg(test)]
mod tests {
    use super::*;

    const HEAD: &str = "[package]\nname = \"probe\"\nversion = \"0.1.0\"\n";

    fn rejected(source: &str) -> toml::de::Error {
        toml::from_str::<Manifest>(source)
            .err()
            .unwrap_or_else(|| panic!("an accepted manifest: {source:?}"))
    }

    /// The part of the quoted line that the carets are under.
    fn marked(shown: &str) -> String {
        let lines: Vec<&str> = shown.split('\n').collect();
        let start = lines[3].find('^').unwrap();
        let width = lines[3].len() - start;
        lines[2].chars().skip(start).take(width).collect()
    }

    #[test]
    fn manifest_errors_without_named_characters_print_as_toml_renders_them() {
        for source in [
            // No table, a missing key, and a value that is absent at the end
            // of a line and at the end of the file.
            "".to_string(),
            HEAD.to_string(),
            format!("{HEAD}root = \n"),
            format!("{HEAD}root = \"main.vast"),
            format!("{HEAD}root ="),
            // Keys and values that the message quotes.
            format!("{HEAD}root = \"main.vast\"\nextra = 1\n"),
            format!("{HEAD}name = \"again\"\n"),
            format!("{HEAD}root = 1\n"),
            format!("{HEAD}root = \"main.vast\"\ngeometry_compat = \"none\"\n"),
            // A message of two lines, and a place after the first line of
            // an inline table.
            format!("{HEAD}root = \"main.vast\"\n[dependencies]\ndep = {{ path = 1,\n}}\n"),
            // Characters of more than one byte ahead of the place, in it and
            // as the place itself.
            format!("{HEAD}root = \"数学.vast\" x\n"),
            format!("{HEAD}root = \"main.vast\"\n\"数学\" = 1\n"),
            format!("{HEAD}root = 数\n"),
            // A backslash that spells no named character, with a message of
            // one line.
            format!("{HEAD}root = \"main.vast\"\n\"a\\\\b\" = 1\n"),
        ] {
            let error = rejected(&source);
            assert_eq!(
                manifest_error(&source, &error),
                error.to_string(),
                "{source:?}"
            );
        }
    }

    #[test]
    fn manifest_errors_name_controls_and_keep_the_carets_under_the_place() {
        // toml marks the first control of the comment.
        let source = format!("{HEAD}root = \"main.vast\" # \u{1b}[2J\u{1b}[H\n");
        let shown = manifest_error(&source, &rejected(&source));
        assert_eq!(
            shown,
            concat!(
                "TOML parse error at line 4, column 22\n",
                "  |\n",
                "4 | root = \"main.vast\" # <U+001B>[2J<U+001B>[H\n",
                "  |                      ^^^^^^^^\n",
                "expected newline, `#`\n",
            )
        );
        assert_eq!(marked(&shown), "<U+001B>");
        // Names ahead of the place: a tab, a right-to-left override and a
        // zero-width space.
        let source = format!("{HEAD}\troot = \"a\u{202e}b\u{200b}.vast\" x\n");
        let shown = manifest_error(&source, &rejected(&source));
        assert_eq!(marked(&shown), "x");
        assert_eq!(
            shown.split('\n').nth(2),
            Some("4 | <U+0009>root = \"a<U+202E>b<U+200B>.vast\" x")
        );
        // Names in the place: the carets cover the whole key.
        let source = format!("{HEAD}root = \"main.vast\"\n\"a\tb\" = 1\n");
        let shown = manifest_error(&source, &rejected(&source));
        assert_eq!(marked(&shown), "\"a<U+0009>b\"");
        assert!(
            shown.ends_with(
                "\nunknown field `a<U+0009>b`, expected one of `name`, `version`, `root`\n"
            ),
            "{shown:?}"
        );
        // The carriage return of a CR LF line end is not quoted.
        let source = "[package]\r\nname = \r\n";
        let shown = manifest_error(source, &rejected(source));
        assert_eq!(
            shown,
            concat!(
                "TOML parse error at line 2, column 8\n",
                "  |\n",
                "2 | name = \n",
                "  |        ^\n",
                "invalid string\n",
                "expected `\"`, `'`\n",
            )
        );
    }

    #[test]
    fn manifest_error_messages_name_the_line_feeds_that_a_manifest_can_spell() {
        // The key holds a line feed. Without the name, the message would
        // start a line of its own choice.
        let source = format!("{HEAD}root = \"main.vast\"\n\"k\\nE_FORGED: x\" = 1\n");
        let shown = manifest_error(&source, &rejected(&source));
        assert!(
            shown.ends_with("\nunknown field `k<U+000A>E_FORGED: x`, expected one of `name`, `version`, `root`\n"),
            "{shown:?}"
        );
        assert_eq!(shown.split('\n').count(), 6, "{shown:?}");
        // A backslash or a string of several lines anywhere in the manifest:
        // the line feed between the two parts of toml's message is named as
        // well, because the message does not say which line feeds are its own.
        for root in [
            "\"a\\\\b.vast\"",
            "'''a\nb.vast'''",
            "\"\"\"a\nb.vast\"\"\"",
        ] {
            let source = format!("{HEAD}root = {root}\nextra = \n");
            let shown = manifest_error(&source, &rejected(&source));
            assert!(
                shown.ends_with("\ninvalid string<U+000A>expected `\"`, `'`\n"),
                "{shown:?}"
            );
        }
        // An error without a position has no quoted line.
        let custom = <toml::de::Error as serde::de::Error>::custom("a\u{1b}\nb");
        assert_eq!(manifest_error("", &custom), "a<U+001B>\nb\n");
        assert_eq!(manifest_error("\\", &custom), "a<U+001B><U+000A>b\n");
    }

    #[test]
    fn another_rendering_of_the_position_is_not_reshaped() {
        let source = format!("{HEAD}root = \n");
        let rendered = rejected(&source).to_string();
        assert!(shown_position(&source, &rendered).is_some());
        // Another shape, and a quoted line that is not the numbered line.
        assert_eq!(shown_position(&source, "one line"), None);
        assert_eq!(
            shown_position(&source, &rendered.replace("  |", "  :")),
            None
        );
        assert_eq!(
            shown_position(&source.replace("root", "main"), &rendered),
            None
        );
    }
}
