#!/usr/bin/env python3
"""Execute checked internal storage IR through the optional native runtime.

This is a regression harness, not public protocol 8 or a user-facing interpreter.
"""
import copy
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
NATIVE = ROOT / "lean-kernel/native"
EMITTER = ROOT / "lean-kernel/.lake/build/bin/storage-native-fixture"


def run(args, *, cwd=ROOT, success=True, env=None):
    result = subprocess.run([str(arg) for arg in args], cwd=cwd, text=True, capture_output=True, env=env)
    if (result.returncode == 0) != success:
        raise RuntimeError(f"{args}: exit {result.returncode}\n{result.stdout}\n{result.stderr}")
    return result


def main():
    run(["lake", "-d", "lean-kernel", "build", "storage-native-fixture"])
    fixture = json.loads((ROOT / "tests/fixtures/storage.json").read_text())
    with tempfile.TemporaryDirectory(prefix="vastitas-storage-") as directory:
        work = Path(directory)
        sanitizer = work / "sanitizer"
        run([*shlex.split(os.environ.get("CC", "cc")), "-std=c11", "-O3", "-Wall", "-Wextra", "-Werror",
             "-fsanitize=address,undefined", "-fno-omit-frame-pointer",
             NATIVE / "storage.c", NATIVE / "test_storage.c", "-o", sanitizer])
        print(run([sanitizer]).stdout.strip())
        blocks = work / "regroup-blocks-sanitizer"
        run([*shlex.split(os.environ.get("CC", "cc")), "-std=c11", "-O3", "-Wall", "-Wextra", "-Werror",
             "-fsanitize=address,undefined", "-fno-omit-frame-pointer",
             NATIVE / "test_regroup_blocks.c", "-o", blocks])
        print(run([blocks]).stdout.strip())
        diagonal = work / "diagonal-sanitizer"
        run([*shlex.split(os.environ.get("CC", "cc")), "-std=c11", "-O3", "-Wall", "-Wextra", "-Werror",
             "-fsanitize=address,undefined", "-fno-omit-frame-pointer",
             NATIVE / "storage.c", NATIVE / "diagonal.c", NATIVE / "test_diagonal.c", "-o", diagonal])
        print(run([diagonal]).stdout.strip())
        # A standalone consumer depends only on this optional runtime package.
        # Lake builds and links the real generated FFI declarations and C adapter.
        runtime = work / "runtime"
        shutil.copytree(NATIVE, runtime, ignore=shutil.ignore_patterns(".lake"))
        (work / "lean-toolchain").write_text((NATIVE / "lean-toolchain").read_text())
        (work / "lakefile.toml").write_text(
            'name = "storage_fixture"\nversion = "0.1.0"\n'
            '[[require]]\nname = "vastitas_storage_native"\npath = ' + json.dumps(str(runtime)) + '\n'
            '[[lean_exe]]\nname = "fixture"\nroot = "Main"\n')

        for name, budget, failure, expected in [
            ("success", 128, None, [3, 3, 0, 128, 176, 64]),
            ("assertion_failure", 128, "E_NATIVE_EXPECT", [1, 1, 0, 64, 32, 0]),
            ("allocation_failure", 64, "E_NATIVE_ALLOCATION", [2, 2, 0, 64, 112, 0]),
        ]:
            source = copy.deepcopy(fixture)
            if name == "assertion_failure":
                source["statements"][6]["action"]["value"]["bits"] = 0
            path = work / "input.json"
            path.write_text(json.dumps(source))
            run([EMITTER, path, work / "Main.lean", budget])
            generated = (work / "Main.lean").read_text()
            assert "borrow " not in generated and "transpose " not in generated
            assert "copy arena 1 0 2 2 2 false 2 0 2 2 2 false" in generated
            run(["lake", "build", "fixture"], cwd=work)
            result = run([work / ".lake/build/bin/fixture"], cwd=work, success=failure is None)
            if failure:
                assert failure in result.stderr, result
            match = re.search(r"#\[([\d, ]+)\]", result.stdout)
            assert match, result
            counters = [int(item) for item in match[1].split(",")]
            assert len(counters) == 8 and counters[:6] == expected, (name, counters)
            assert counters[6] == 2 and counters[7] > 0, (name, counters)
            print(f"{name}: allocations/frees/live/peak/written/copied = {counters[:6]}; "
                  f"metadata allocations/bytes = {counters[6:]}")

        (work / "Metadata.lean").write_text('''import VastitasStorageNative
def main : IO Unit := do
  for malformed in ["0", "gg", "00xz"] do
    unless (VastitasStorageNative.diagonalData malformed).isEmpty do
      throw (IO.userError "malformed diagonal metadata admitted")
  let encoded := String.join (List.replicate 4096 "0000000000000040")
  let decoded := VastitasStorageNative.diagonalData encoded
  unless decoded.size == 32768 do throw (IO.userError "large diagonal metadata truncated")
  for index in [:decoded.size] do
    unless decoded[index]! == (if index % 8 == 7 then 64 else 0) do
      throw (IO.userError "diagonal metadata byte changed")
  IO.println "diagonal metadata: malformed inputs and full 4096-entry linear decoding passed"
''')
        print(run(["lake", "env", "lean", "--run", "Metadata.lean"], cwd=work).stdout.strip())

        # Test-only comparison of actual native arithmetic helpers with the
        # concrete checker. This dependency is never added to the runtime.
        audit_env = os.environ.copy()
        audit_env["LEAN_PATH"] = os.pathsep.join([
            str(ROOT / "lean-kernel/.lake/build/lib/lean"),
            str(runtime / ".lake/build/lib/lean"),
        ])
        print(run(["lean", ROOT / "scripts/check_runtime_shape_guards.lean"],
                  cwd=work, env=audit_env).stdout.strip())

        functions = json.loads((ROOT / "tests/fixtures/storage-functions.json").read_text())
        for name, budget, failure, expected in [
            ("functions", 128, None, [3, 3, 0, 128, 128, 64]),
            ("function_assertion_failure", 128, "E_NATIVE_EXPECT", [2, 2, 0, 128, 96, 64]),
            ("function_allocation_failure", 64, "E_NATIVE_ALLOCATION", [1, 1, 0, 64, 32, 0]),
        ]:
            source = copy.deepcopy(functions)
            if name == "function_assertion_failure":
                function = next(f for f in source["functions"] if f["id"] == 3)
                function["body"][1]["action"]["value"]["bits"] = 0
            path.write_text(json.dumps(source))
            run([EMITTER, path, work / "Main.lean", budget])
            generated = (work / "Main.lean").read_text()
            # Both branch arms appear in source; only one runs. Synthetic
            # all-body probes and the unused complex function must not be emitted.
            assert generated.count("allocate arena ") == 4, generated
            run(["lake", "build", "fixture"], cwd=work)
            result = run([work / ".lake/build/bin/fixture"], cwd=work, success=failure is None)
            if failure:
                assert failure in result.stderr, result
            match = re.search(r"#\[([\d, ]+)\]", result.stdout)
            assert match, result
            counters = [int(item) for item in match[1].split(",")]
            assert len(counters) == 8 and counters[:6] == expected, (name, counters)
            assert counters[6] == 2 and counters[7] > 0, (name, counters)
            print(f"{name}: allocations/frees/live/peak/written/copied = {counters[:6]}")

        # Header-only changes must invalidate both C objects, including the FFI.
        # Exercise this in the isolated package, never by editing the checkout.
        objects = [runtime / ".lake/build" / name for name in ["storage.o", "ffi.o"]]
        previous = [path.stat().st_mtime_ns for path in objects]
        header = runtime / "storage.h"
        header.write_text(header.read_text() + "\n/* header dependency regression */\n")
        run(["lake", "build", "fixture"], cwd=work)
        assert all(path.stat().st_mtime_ns != before for path, before in zip(objects, previous))

        # Invalid source schedules cannot be laundered by native code generation.
        source = copy.deepcopy(fixture)
        del source["statements"][2]  # required fill: later read is uninitialized
        path.write_text(json.dumps(source))
        invalid_output = work / "Rejected.lean"
        result = run([EMITTER, path, invalid_output, 128], success=False)
        assert "resource component rejected" in result.stderr and not invalid_output.exists()
    print("checked storage IR: native success, failure cleanup and uninitialized-input rejection passed")


if __name__ == "__main__":
    main()
