"""The Lake libraries of the kernel, the oracle and the bridge, as the Python scripts name them.

The lakefiles declare the libraries. `scripts/check_spec.py` and
`scripts/check_axiom_audit.py` copy their names, because they run without
Lake or before it reads a package, so these tests keep the copies equal.
"""
import ast
from pathlib import Path
import tomllib
import unittest

import check_axiom_audit
import check_spec


ROOT = Path(__file__).resolve().parents[1]
PACKAGES = ("lean-kernel", "lean", "lean-bridge")


def lakefile(package):
    with open(ROOT / package / "lakefile.toml", "rb") as file:
        return tomllib.load(file)


def libraries(package):
    return {entry["name"] for entry in lakefile(package).get("lean_lib", [])}


class LibraryNameTests(unittest.TestCase):
    def test_check_spec_finds_the_source_directory_of_every_library(self):
        self.assertIn("VastitasAlgebraTest", libraries("lean-kernel"))
        for package in PACKAGES:
            with self.subTest(package=package):
                self.assertEqual({name for name, directory in check_spec.SOURCES.items() if directory == package},
                                 libraries(package))
        self.assertEqual(set(check_spec.SOURCES.values()), set(PACKAGES))

    def test_the_axiom_audit_overlays_every_kernel_and_oracle_library(self):
        # The overlay also links the root module of the kernel executable, Main.
        executables = {entry["root"].split(".")[0] for entry in lakefile("lean-kernel").get("lean_exe", [])}
        modules = libraries("lean-kernel") | libraries("lean")
        self.assertEqual(executables - modules, {"Main"})
        self.assertEqual(sorted(check_axiom_audit.GROUPS), sorted(modules | executables))

    def test_the_axiom_audit_plants_an_axiom_in_every_kernel_and_oracle_library(self):
        tree = ast.parse((ROOT / "scripts/check_axiom_audit.py").read_text(encoding="utf-8"))
        main = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == "main")
        loops = [node.iter for node in ast.walk(main) if isinstance(node, ast.For)
                 and isinstance(node.target, ast.Name) and node.target.id == "group"]
        self.assertEqual(len(loops), 1)
        self.assertEqual(sorted(ast.literal_eval(loops[0])), sorted(libraries("lean-kernel") | libraries("lean")))


if __name__ == "__main__":
    unittest.main()
