#!/usr/bin/env python3
"""Test actual runtime result lifetime/publication through generated Lean callers."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
NATIVE = ROOT / "lean-kernel/native"


def main():
    with tempfile.TemporaryDirectory(prefix="vastitas-ffi-result-") as directory:
        work = Path(directory)
        shutil.copyfile(NATIVE / "test_ffi_result.lean", work / "Main.lean")
        shutil.copyfile(NATIVE / "test_ffi_result.c", work / "probe.c")
        shutil.copyfile(NATIVE / "lean-toolchain", work / "lean-toolchain")
        (work / "lakefile.lean").write_text(f'''import Lake
open Lake DSL System
package ffi_result_test
require vastitas_storage_native from {json.dumps(str(NATIVE))}
input_file probeSource where path := "probe.c"
target probeObject pkg : FilePath := do
  let source ← probeSource.fetch
  buildLeanO (pkg.buildDir / "probe.o") source #[]
    #["-std=c11", "-O3", "-Wall", "-Wextra", "-Werror", {json.dumps("-I" + str(NATIVE))}]
extern_lib probeNative pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "probe_native") #[← probeObject.fetch]
lean_exe fixture where
  root := `Main
''')
        subprocess.run(["lake", "build", "fixture"], cwd=work, check=True)
        for _ in range(4):
            subprocess.run([str(work / ".lake/build/bin/fixture")], cwd=work,
                           check=True, timeout=60)


if __name__ == "__main__":
    main()
