//! Explicit compilation inputs and their diagnostic locations.
//!
//! Each input is parsed separately, but byte offsets occupy disjoint intervals
//! in the compilation unit. Lines and columns remain local to each file. The
//! backend can therefore return its usual spans without knowing filesystem paths.
use crate::frontend::{self, SourceInput};
use crate::ir::{Module, Span};
use std::collections::HashSet;
use std::fs::{self, OpenOptions};
use std::io::Read;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};

/// Text as the compiler shows it on the terminal. A manifest, a file name and
/// the names a manifest gives reach diagnostics, and a TOML escape or a file
/// name can spell any character. A character that source diagnostics name by
/// code point instead of echoing (`frontend::character`) is named the same
/// way here, as `<U+001B>`, so neither a terminal control nor a forged line
/// reaches the terminal. A space stays as it is, and so does every other
/// character.
pub(crate) fn shown_text(text: &str) -> String {
    let mut named = String::with_capacity(text.len());
    for ch in text.chars() {
        if ch == ' ' || frontend::echoable(ch) {
            named.push(ch);
        } else {
            named.push_str(&format!("<{}>", frontend::character(ch)));
        }
    }
    named
}

/// A path as a diagnostic or a status line shows it; see `shown_text`. Every
/// path is shown this way, whether a manifest, the command line or the
/// environment chose it.
pub(crate) fn shown(path: &Path) -> String {
    shown_text(&path.to_string_lossy())
}

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
    bytes: usize,
}

// Host input budgets apply before parsing or serializing the public request.
// Reused files count on every load because each logical module retains its text.
const MAX_INPUT_FILES: usize = 8192;
const MAX_FILE_BYTES: usize = 16 * 1024 * 1024;
const MAX_INPUT_BYTES: usize = 64 * 1024 * 1024;

/// The output's identity is stable for a loading pass. Check each newly loaded
/// input once, then refresh the identity before the final atomic installation.
pub(crate) struct OutputIdentity {
    canonical: PathBuf,
    identity: (u64, u64),
}

impl OutputIdentity {
    pub(crate) fn inspect(output: &Path) -> Result<Option<Self>, String> {
        let canonical = match output.canonicalize() {
            Ok(path) => path,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(error) => {
                return Err(format!(
                    "E_OUTPUT: cannot inspect {}: {error}",
                    shown(output)
                ));
            }
        };
        let metadata = fs::metadata(output)
            .map_err(|error| format!("E_OUTPUT: cannot inspect {}: {error}", shown(output)))?;
        Ok(Some(Self {
            canonical,
            identity: (metadata.dev(), metadata.ino()),
        }))
    }

    fn protect(&self, source: &SourceFile) -> Result<(), String> {
        if source.canonical == self.canonical || source.identity == self.identity {
            return Err(format!(
                "E_OUTPUT: output would overwrite input file {}",
                shown(&source.path)
            ));
        }
        Ok(())
    }
}

impl Sources {
    pub(crate) fn empty() -> Self {
        Self {
            files: Vec::new(),
            bytes: 0,
        }
    }

    /// Every manifest and module participates in the same protection/location
    /// table. Package loading checks cycles but permits reuse by distinct owners.
    pub(crate) fn add(
        &mut self,
        path: &Path,
        output: Option<&OutputIdentity>,
    ) -> Result<SourceInput<'_>, String> {
        let canonical = path
            .canonicalize()
            .map_err(|error| format!("E_INPUT: cannot read {}: {error}", shown(path)))?;
        self.push_file(path, canonical)?;
        let file = self.files.last().unwrap();
        if let Some(output) = output {
            output.protect(file)?;
        }
        Ok(SourceInput {
            source: &file.text,
            file: &file.name,
            offset: file.offset,
        })
    }

    fn push_file(&mut self, path: &Path, canonical: PathBuf) -> Result<(), String> {
        crate::process::check().map_err(|_| "E_INTERRUPTED: compilation interrupted")?;
        if self.files.len() >= MAX_INPUT_FILES {
            return Err(format!(
                "E_LIMIT: compilation inputs exceed {MAX_INPUT_FILES} files"
            ));
        }
        // Opening a FIFO must not block before we can inspect its type. Inspect
        // the opened descriptor, not just the path, before reading any bytes.
        let mut file = OpenOptions::new()
            .read(true)
            .custom_flags(nix::libc::O_NONBLOCK)
            .open(&canonical)
            .map_err(|error| format!("E_INPUT: cannot read {}: {error}", shown(path)))?;
        let metadata = file
            .metadata()
            .map_err(|error| format!("E_INPUT: cannot inspect {}: {error}", shown(path)))?;
        if !metadata.is_file() {
            return Err(format!(
                "E_INPUT: input must be a regular file: {}",
                shown(path)
            ));
        }
        let available = MAX_FILE_BYTES.min(MAX_INPUT_BYTES - self.bytes);
        let too_large = || {
            format!(
                "E_LIMIT: input {} exceeds the 16 MiB file or 64 MiB compilation input budget",
                shown(path)
            )
        };
        if metadata.len() > available as u64 {
            return Err(too_large());
        }
        let mut bytes = Vec::new();
        let mut buffer = [0; 65536];
        loop {
            crate::process::check().map_err(|_| "E_INTERRUPTED: compilation interrupted")?;
            let count = match file.read(&mut buffer) {
                Ok(count) => count,
                Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
                Err(error) => {
                    return Err(format!("E_INPUT: cannot read {}: {error}", shown(path)));
                }
            };
            if count == 0 {
                break;
            }
            // Recheck while reading: the file may grow after fstat.
            if count > available - bytes.len() {
                return Err(too_large());
            }
            bytes.extend_from_slice(&buffer[..count]);
        }
        let text = String::from_utf8(bytes)
            .map_err(|error| format!("E_INPUT: cannot read {}: {error}", shown(path)))?;
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
        self.bytes += text.len();
        self.files.push(SourceFile {
            path: path.to_path_buf(),
            canonical,
            identity: (metadata.dev(), metadata.ino()),
            name: path.to_string_lossy().into_owned(),
            text,
            offset,
        });
        Ok(())
    }

    pub(crate) fn load(input: &Path, libraries: &[PathBuf]) -> Result<Self, String> {
        let mut seen = HashSet::new();
        let mut sources = Self::empty();
        for path in std::iter::once(input).chain(libraries.iter().map(PathBuf::as_path)) {
            if path.extension().is_none_or(|extension| extension != "vast") {
                return Err(format!(
                    "E_INPUT: source filename must have the .vast extension: {}",
                    shown(path)
                ));
            }
            let canonical = path
                .canonicalize()
                .map_err(|error| format!("E_INPUT: cannot read {}: {error}", shown(path)))?;
            if !seen.insert(canonical.clone()) {
                return Err(format!(
                    "E_INPUT: source file supplied more than once: {}",
                    shown(path)
                ));
            }
            sources.push_file(path, canonical)?;
        }
        Ok(sources)
    }

    pub(crate) fn protect_output(&self, output: &Path) -> Result<(), String> {
        if let Some(identity) = OutputIdentity::inspect(output)? {
            for source in &self.files {
                identity.protect(source)?;
            }
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

    /// One diagnostic line. The message of a kernel diagnostic can name a
    /// package as its manifest does, so the message is shown like the path.
    pub(crate) fn diagnostic(&self, code: &str, message: &str, span: Span) -> String {
        let file = &self.files[self.file_index(span.start)];
        format!(
            "{}:{}:{}: {code}: {}",
            shown(&file.path),
            span.line,
            span.column,
            shown_text(message)
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;

    #[test]
    fn shown_text_names_controls_formats_and_whitespace_other_than_spaces() {
        let plain = "a b/é数 → `c`.vast";
        assert_eq!(shown_text(plain), plain);
        assert_eq!(
            shown_text(
                "\u{1b}[2J\u{7}\n\r\t\u{7f}\u{9b}\u{a0}\u{2028}\u{3000}\u{202e}\u{200b}\u{feff}"
            ),
            "<U+001B>[2J<U+0007><U+000A><U+000D><U+0009><U+007F><U+009B><U+00A0><U+2028><U+3000><U+202E><U+200B><U+FEFF>"
        );
        // A name holds no character that is named again.
        let named = shown_text("x\u{1b}\u{e0001}y");
        assert_eq!(named, "x<U+001B><U+E0001>y");
        assert_eq!(shown_text(&named), named);
        assert_eq!(
            shown(Path::new("d\u{1b}[2J/a b.vast")),
            "d<U+001B>[2J/a b.vast"
        );
        // A path that is not UTF-8 is shown with replacement characters.
        assert_eq!(
            shown(Path::new(OsStr::from_bytes(b"a\xff\x1b"))),
            "a\u{fffd}<U+001B>"
        );
    }
}
