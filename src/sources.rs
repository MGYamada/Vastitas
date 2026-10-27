//! Explicit compilation inputs and their diagnostic locations.
//!
//! Each input is parsed separately, but byte offsets occupy disjoint intervals
//! in the compilation unit. Lines and columns remain local to each file. The
//! backend can therefore return its usual spans without knowing filesystem paths.
use crate::frontend::{self, SourceInput};
use crate::ir::{Module, Span};
use std::collections::HashSet;
use std::fs;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};

struct SourceFile {
    path: PathBuf,
    canonical: PathBuf,
    identity: (u64, u64),
    name: String,
    text: String,
    offset: usize,
}

pub(crate) struct Sources {
    files: Vec<SourceFile>,
}

impl Sources {
    pub(crate) fn empty() -> Self {
        Self { files: Vec::new() }
    }

    /// Every manifest and module participates in the same protection/location
    /// table. Package loading has already checked file reuse and graph cycles.
    pub(crate) fn add(
        &mut self,
        path: &Path,
        output: Option<&Path>,
    ) -> Result<SourceInput<'_>, String> {
        let canonical = path
            .canonicalize()
            .map_err(|error| format!("E_INPUT: cannot read {}: {error}", path.display()))?;
        let text = fs::read_to_string(&canonical)
            .map_err(|error| format!("E_INPUT: cannot read {}: {error}", path.display()))?;
        let metadata = fs::metadata(&canonical)
            .map_err(|error| format!("E_INPUT: cannot inspect {}: {error}", path.display()))?;
        let offset = self
            .files
            .last()
            .map_or(Some(0), |file| {
                file.offset.checked_add(file.text.len())?.checked_add(1)
            })
            .ok_or("E_INPUT: compilation unit is too large")?;
        offset
            .checked_add(text.len())
            .and_then(|end| end.checked_add(1))
            .ok_or("E_INPUT: compilation unit is too large")?;
        self.files.push(SourceFile {
            path: path.to_path_buf(),
            canonical,
            identity: (metadata.dev(), metadata.ino()),
            name: path.to_string_lossy().into_owned(),
            text,
            offset,
        });
        if let Some(output) = output {
            self.protect_output(output)?;
        }
        let file = self.files.last().unwrap();
        Ok(SourceInput {
            source: &file.text,
            file: &file.name,
            offset,
        })
    }

    pub(crate) fn load(input: &Path, libraries: &[PathBuf]) -> Result<Self, String> {
        let mut seen = HashSet::new();
        let mut files = Vec::new();
        let mut offset = 0usize;
        for path in std::iter::once(input).chain(libraries.iter().map(PathBuf::as_path)) {
            if path.extension().is_none_or(|extension| extension != "vast") {
                return Err(format!(
                    "E_INPUT: source filename must have the .vast extension: {}",
                    path.display()
                ));
            }
            let canonical = path
                .canonicalize()
                .map_err(|error| format!("E_INPUT: cannot read {}: {error}", path.display()))?;
            if !seen.insert(canonical.clone()) {
                return Err(format!(
                    "E_INPUT: source file supplied more than once: {}",
                    path.display()
                ));
            }
            let text = fs::read_to_string(path)
                .map_err(|error| format!("E_INPUT: cannot read {}: {error}", path.display()))?;
            let metadata = fs::metadata(path)
                .map_err(|error| format!("E_INPUT: cannot inspect {}: {error}", path.display()))?;
            let next_offset = offset
                .checked_add(text.len())
                .and_then(|end| end.checked_add(1))
                .ok_or_else(|| "E_INPUT: compilation unit is too large".to_string())?;
            files.push(SourceFile {
                path: path.to_path_buf(),
                canonical,
                identity: (metadata.dev(), metadata.ino()),
                name: path.to_string_lossy().into_owned(),
                text,
                offset,
            });
            offset = next_offset;
        }
        Ok(Self { files })
    }

    pub(crate) fn protect_output(&self, output: &Path) -> Result<(), String> {
        let canonical = match output.canonicalize() {
            Ok(path) => path,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
            Err(error) => {
                return Err(format!(
                    "E_OUTPUT: cannot inspect {}: {error}",
                    output.display()
                ));
            }
        };
        let metadata = fs::metadata(output)
            .map_err(|error| format!("E_OUTPUT: cannot inspect {}: {error}", output.display()))?;
        if let Some(source) = self.files.iter().find(|source| {
            source.canonical == canonical || source.identity == (metadata.dev(), metadata.ino())
        }) {
            return Err(format!(
                "E_OUTPUT: output would overwrite input file {}",
                source.path.display()
            ));
        }
        Ok(())
    }

    pub(crate) fn parse(&self) -> Result<Module, String> {
        let inputs: Vec<_> = self
            .files
            .iter()
            .map(|source| SourceInput {
                source: &source.text,
                file: &source.name,
                offset: source.offset,
            })
            .collect();
        let module = frontend::parse_sources(&inputs).map_err(|diagnostics| {
            diagnostics
                .iter()
                .map(|diagnostic| {
                    self.diagnostic(&diagnostic.code, &diagnostic.message, diagnostic.span)
                })
                .collect::<Vec<_>>()
                .join("\n")
        })?;
        if let Some(function) = module
            .functions
            .iter()
            .find(|function| function.name == "main" && self.file_index(function.span.start) != 0)
        {
            return Err(self.diagnostic(
                "E_LIBRARY",
                "a --lib file cannot provide main; define the entrypoint in the input file",
                function.span,
            ));
        }
        Ok(module)
    }

    fn file_index(&self, offset: usize) -> usize {
        self.files
            .iter()
            .rposition(|file| file.offset <= offset)
            .unwrap_or(0)
    }

    pub(crate) fn diagnostic(&self, code: &str, message: &str, span: Span) -> String {
        let file = &self.files[self.file_index(span.start)];
        format!(
            "{}:{}:{}: {code}: {message}",
            file.path.display(),
            span.line,
            span.column
        )
    }
}
