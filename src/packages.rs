//! Explicit path-package loading. Namespace references remain unresolved in the
//! wire request: only Lean can accept them and assign function identities.
use crate::frontend;
use crate::ir::{
    ABSTRACT_PROTOCOL_VERSION, AbstractMethod, AbstractType, Function, Generic, Method, Span,
    Subtype,
};
use crate::limits::{MAX_MODULE_NESTING, MAX_PACKAGE_NESTING};
use crate::sources::{OutputIdentity, Sources};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashSet};
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};

pub(crate) const PROTOCOL: u32 = 3;
pub(crate) const EDIT_PROTOCOL: u32 = 5;
pub(crate) const AUTHORITY_PROTOCOL: u32 = 6;
pub(crate) const INDEXED_PROTOCOL: u32 = 7;

#[derive(Debug, Serialize)]
pub(crate) struct Grant {
    pub name: String,
    pub target: Vec<String>,
    pub grantee_source: String,
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
    pub grantee_source: String,
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
        if self.active.len() >= MAX_PACKAGE_NESTING {
            return Err(format!(
                "E_LIMIT: package dependency nesting exceeds {MAX_PACKAGE_NESTING}"
            ));
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
        if path.len() > MAX_MODULE_NESTING {
            return Err(format!(
                "E_LIMIT: module nesting exceeds {MAX_MODULE_NESTING}"
            ));
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
    let selected: HashSet<_> = loader.packages.iter().map(|p| p.source.clone()).collect();
    // Grants only name inputs in the closure already selected by dependencies.
    // Canonicalizing the location never loads an additional package.
    for package in &mut loader.packages {
        let directory = Path::new(&package.source).parent().unwrap();
        for module in &mut package.modules {
            let grants = module
                .grants
                .iter_mut()
                .chain(&mut module.delegations)
                .map(|g| (&mut g.declaration.grantee_source, g.declaration.span));
            let transfers = module
                .transfers
                .iter_mut()
                .map(|t| (&mut t.declaration.grantee_source, t.declaration.span));
            for (source, span) in grants.chain(transfers) {
                let target = canonical(&directory.join(&*source))?;
                let target = target
                    .to_str()
                    .ok_or("E_INPUT: grant manifest path must be UTF-8")?;
                if !selected.contains(target) {
                    return Err(loader.sources.diagnostic(
                        "E_OWNER",
                        "grant grantee must belong to the selected dependency closure",
                        span,
                    ));
                }
                *source = target.into();
            }
        }
    }
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
        .any(|m| m.uses_indexed);
    let program = Program {
        version: if indexed {
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
        input: (indexed || extended || editable).then(|| "package".into()),
        file: root.clone(),
        root,
        packages: loader.packages,
    };
    Ok((loader.sources, program))
}
