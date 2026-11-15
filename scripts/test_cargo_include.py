"""The crate file list of Cargo.toml leaves out the files that .gitignore ignores in included directories.

Cargo's `package.include` selects whole directories and does not read
.gitignore, so an ignored environment file or Finder metadata under `src/`
would enter the crate (#796). The test copies the repository's include list
into a throwaway crate outside any Git checkout, places such files next to
ordinary sources, and reads `cargo package --list`. The files are empty
placeholders.
"""
import shutil
import subprocess
import tempfile
import tomllib
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
KEPT = ("src/main.rs", "src/frontend/mod.rs", "tests/examples.rs", "examples/hello/main.vast",
        "lean-kernel/VastitasKernel/Check.lean", "stdlib/src/lib.vast", "nature/lib.vast")
DROPPED = ("src/.env", "src/.env.local", "src/frontend/.env.example", "src/.DS_Store",
           "tests/.DS_Store", "examples/hello/.env", "lean-kernel/.DS_Store",
           "lean-kernel/.lake/build/Check.olean", "stdlib/src/.DS_Store", "nature/.env.local")


@unittest.skipUnless(shutil.which("cargo"), "requires cargo")
class CargoIncludeTests(unittest.TestCase):
    def test_ignored_files_stay_out_of_the_crate(self):
        include = tomllib.loads((ROOT / "Cargo.toml").read_text())["package"]["include"]
        with tempfile.TemporaryDirectory() as temp:
            crate = Path(temp) / "probe"
            for name in KEPT + DROPPED:
                path = crate / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("fn main() {}\n" if name == "src/main.rs" else "")
            manifest = ['[package]', 'name = "include-probe"', 'version = "0.0.0"',
                        'edition = "2021"', 'publish = false',
                        "include = [" + ", ".join(f'"{pattern}"' for pattern in include) + "]"]
            (crate / "Cargo.toml").write_text("\n".join(manifest) + "\n")
            result = subprocess.run(["cargo", "package", "--list", "--offline", "--allow-dirty"],
                                    cwd=crate, capture_output=True, text=True, timeout=300, check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        listed = set(result.stdout.split())
        for name in KEPT:
            self.assertIn(name, listed)
        for name in DROPPED:
            self.assertNotIn(name, listed)


if __name__ == "__main__":
    unittest.main()
