//! Scratch copies of the repository's packages: the example packages, the
//! stdlib and the `nature` package.
use super::process::{Scratch, prepare_stdlib_package, root};
use std::fs;
use std::path::Path;

/// The text of the file `path`.
pub fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap()
}

/// The stdlib directories that an application's copy of the stdlib holds:
/// the generated `std` entrypoint package and the geometry and differential
/// packages.
pub const STDLIB_PACKAGES: [&str; 3] = ["target/package", "src/geometry", "src/differential"];

impl Scratch {
    /// Copies every `.vast` and `.toml` file under `from` to the same relative
    /// path under `to` in this directory (`""` for the directory itself). The
    /// directories and files whose path relative to `from` is in `skip` are
    /// left out.
    pub fn copy_sources(&self, from: &Path, to: &str, skip: &[&str]) {
        let mut stack = vec![from.to_path_buf()];
        while let Some(directory) = stack.pop() {
            for entry in fs::read_dir(&directory).unwrap() {
                let path = entry.unwrap().path();
                let relative = path.strip_prefix(from).unwrap().to_str().unwrap();
                if skip.contains(&relative) {
                    continue;
                }
                if path.is_dir() {
                    stack.push(path.clone());
                } else if matches!(
                    path.extension().and_then(|e| e.to_str()),
                    Some("vast" | "toml")
                ) {
                    let target = Path::new(to).join(relative);
                    self.write(target.to_str().unwrap(), &read(&path));
                }
            }
        }
    }
    /// Copies the repository's stdlib to `stdlib/`: its manifest and the
    /// sources of its directories `directories`, without the directories and
    /// files whose path relative to the stdlib is in `skip`. The `std`
    /// entrypoint package (`target/package`) is generated first.
    pub fn copy_stdlib(&self, directories: &[&str], skip: &[&str]) {
        prepare_stdlib_package();
        let stdlib = root().join("stdlib");
        self.write("stdlib/Vastitas.toml", &read(&stdlib.join("Vastitas.toml")));
        for directory in directories {
            let skip: Vec<&str> = skip
                .iter()
                .filter_map(|path| path.strip_prefix(directory)?.strip_prefix('/'))
                .collect();
            self.copy_sources(
                &stdlib.join(directory),
                &format!("stdlib/{directory}"),
                &skip,
            );
        }
    }
    /// Copies the repository's `nature` package to `nature/`.
    pub fn copy_nature(&self) {
        self.copy_sources(&root().join("nature"), "nature", &[]);
    }
}

/// A scratch directory, named after `prefix`, that holds a copy of the
/// example package `example` (a directory of the repository): its `.vast`
/// and `.toml` files, read when the test runs, with the files `files` (paths
/// and texts) written over them.
pub fn example_package(prefix: &str, example: &str, files: &[(&str, &str)]) -> Scratch {
    let s = Scratch::empty(prefix);
    s.copy_sources(&root().join(example), "", &[]);
    for (path, text) in files {
        s.write(path, text);
    }
    s
}

/// An application in `app/` with the manifest text `manifest` and the root
/// module `main`, next to a copy of the stdlib in `stdlib/` with all of
/// [`STDLIB_PACKAGES`] but the stdlib paths in `skip`. This is the layout of
/// the repository, so the manifest names the stdlib `../stdlib`; a test that
/// needs the nature package adds it with [`Scratch::copy_nature`].
pub fn stdlib_app(prefix: &str, manifest: &str, main: &str, skip: &[&str]) -> Scratch {
    let s = Scratch::empty(prefix);
    s.copy_stdlib(&STDLIB_PACKAGES, skip);
    s.write("app/Vastitas.toml", manifest);
    s.write("app/main.vast", main);
    s
}
