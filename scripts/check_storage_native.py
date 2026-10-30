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


def run(args, *, cwd=ROOT, success=True):
    result = subprocess.run([str(arg) for arg in args], cwd=cwd, text=True, capture_output=True)
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
