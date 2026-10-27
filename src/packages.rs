//! Explicit path-package loading. Namespace references remain unresolved in the
//! wire request: only Lean can accept them and assign function identities.
use crate::frontend;
use crate::ir::{
    ABSTRACT_PROTOCOL_VERSION, AbstractType, Function, Generic, Method, Span, Subtype,
};
use crate::sources::{OutputIdentity, Sources};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashSet};
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};

pub(crate) const PROTOCOL: u32 = 3;

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
}

#[derive(Debug, Serialize)]
pub(crate) struct Module {
    pub path: Vec<String>,
    pub public: bool,
    pub imports: Vec<Import>,
    pub functions: Vec<Public<Function>>,
    pub generics: Vec<Public<Generic>>,
    pub methods: Vec<Method>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub abstract_types: Vec<Public<AbstractType>>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub subtypes: Vec<Subtype>,
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
    active: HashSet<PathBuf>,
    output: Option<OutputIdentity>,
}

fn canonical(path: &Path) -> Result<PathBuf, String> {
    path.canonicalize()
        .map_err(|error| format!("E_INPUT: cannot read {}: {error}", path.display()))
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
                manifest.display()
            ));
        }
        if self.packages.iter().any(|package| package.source == source) {
            return Ok(source);
        }
        if self.active.len() >= 64 {
            return Err("E_LIMIT: package dependency nesting exceeds 64".into());
        }
        self.active.insert(manifest.clone());
        let input = self.sources.add(&manifest, self.output.as_ref())?;
        let parsed: Manifest = toml::from_str(input.source)
            .map_err(|error| format!("{}: E_MANIFEST: {error}", manifest.display()))?;
        if parsed.package.name.is_empty() {
            return Err(format!(
                "{}: E_MANIFEST: package name must not be empty",
                manifest.display()
            ));
        }
        semver::Version::parse(&parsed.package.version).map_err(|error| {
            format!(
                "{}: E_MANIFEST: invalid SemVer: {error}",
                manifest.display()
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
                    manifest.display()
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
                    manifest.display()
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
        self.packages.push(Package {
            source: source.clone(),
            name: parsed.package.name,
            version: parsed.package.version,
            dependencies,
            modules,
        });
        self.active.remove(&manifest);
        Ok(source)
    }

    fn inside(&self, source: &Path, package: &Path) -> Result<(), String> {
        if !source.starts_with(package) {
            return Err(format!(
                "E_INPUT: module file escapes package directory: {}",
                source.display()
            ));
        }
        if source.extension().is_none_or(|ext| ext != "vast") {
            return Err(format!(
                "E_INPUT: module filename must have the .vast extension: {}",
                source.display()
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
        if path.len() > 64 {
            return Err("E_LIMIT: module nesting exceeds 64".into());
        }
        let file = canonical(file)?;
        self.inside(&file, package)?;
        let metadata = std::fs::metadata(&file)
            .map_err(|error| format!("E_INPUT: cannot inspect {}: {error}", file.display()))?;
        let identity = (metadata.dev(), metadata.ino());
        if !seen.insert(identity) {
            return Err(format!(
                "E_CYCLE: cyclic module loading: {}",
                file.display()
            ));
        }
        let input = self.sources.add(&file, self.output.as_ref())?;
        let parsed =
            frontend::parse_module_source(input, path, public, declaration).map_err(|error| {
                self.sources
                    .diagnostic(&error.code, &error.message, error.span)
            })?;
        modules.extend(parsed.modules);
        for external in parsed.external {
            let logical = external
                .path
                .iter()
                .fold(base.to_path_buf(), |dir, part| dir.join(part));
            let flat = logical.with_extension("vast");
            let nested = logical.join("mod.vast");
            let file = match (flat.try_exists(), nested.try_exists()) {
                (Ok(true), Ok(false)) => flat,
                (Ok(false), Ok(true)) => nested,
                (Ok(true), Ok(true)) => {
                    return Err(self.sources.diagnostic(
                        "E_INPUT",
                        &format!(
                            "ambiguous module: both {} and {} exist",
                            flat.display(),
                            nested.display()
                        ),
                        external.span,
                    ));
                }
                (Ok(false), Ok(false)) => {
                    return Err(self.sources.diagnostic(
                        "E_INPUT",
                        &format!("module requires {} or {}", flat.display(), nested.display()),
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

pub(crate) fn load(manifest: &Path, output: Option<&Path>) -> Result<(Sources, Program), String> {
    let mut loader = Loader {
        sources: Sources::empty(),
        packages: Vec::new(),
        active: HashSet::new(),
        output: output.map(OutputIdentity::inspect).transpose()?.flatten(),
    };
    let root = loader.package(manifest)?;
    let extended = loader
        .packages
        .iter()
        .flat_map(|p| &p.modules)
        .any(|m| !m.abstract_types.is_empty() || !m.subtypes.is_empty());
    let program = Program {
        version: if extended {
            ABSTRACT_PROTOCOL_VERSION
        } else {
            PROTOCOL
        },
        input: extended.then(|| "package".into()),
        file: root.clone(),
        root,
        packages: loader.packages,
    };
    Ok((loader.sources, program))
}
