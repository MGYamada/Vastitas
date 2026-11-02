#!/usr/bin/env python3
"""Execute exact public generated cleanup with test-only native fault injection.

This checks failure semantics, not native refinement or performance. The normal
public check/build/run precedes the copied runtime's fault-injection executions.
"""
if not __debug__:
    raise RuntimeError("verification requires Python assertions; remove -O / PYTHONOPTIMIZE")

import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


class Runner:
    """Standalone test runner: the no-mathlib checkout excludes experiments."""

    def __init__(self, env):
        self.env = env

    def run(self, args, *, cwd=ROOT, env=None, input=None, required=True):
        command = [str(arg) for arg in args]
        result = subprocess.run(command, cwd=cwd, env=self.env if env is None else env,
                                input=input, text=True, capture_output=True)
        observation = dict(command=command, returncode=result.returncode,
                           stdout=result.stdout, stderr=result.stderr)
        if required and result.returncode:
            raise RuntimeError(observation)
        return observation


def capture_wire(runner, frontend, package):
    """Capture real frontend output with a rejecting adapter, then check it."""
    capture, wire = package / "capture.py", package / "wire.json"
    capture.write_text(f'''#!{sys.executable}
import json, pathlib, sys
pathlib.Path({str(wire)!r}).write_text(sys.stdin.read())
print(json.dumps({{"version":8,"ok":False,"diagnostics":[{{"code":"E_CAPTURED","message":"capture only"}}]}}))
sys.exit(1)
''')
    capture.chmod(0o755)
    result = runner.run([frontend, "check", "--manifest-path", package / "Vastitas.toml"],
                        env=dict(runner.env, VASTITAS_KERNEL=str(capture)), required=False)
    assert result["returncode"] == 1 and "E_CAPTURED" in result["stderr"], result
    assert json.loads(wire.read_text())["version"] == 8
    return wire.read_text()

STATIC = """    allocate data: F64[1];
    borrow output = write(data, layout(0, 1, 1, 1, false));
    fill(output, f64_bits(4607182418800017408));
    release(output);
    drop(data);
"""
SHAPED = """    let n: Nat = value { 2 + 1 };
    runtime_allocate dynamic: F64[n] runtime_layout(n, 1, n, false);
    runtime_borrow target = write(dynamic);
    runtime_fill(target, f64_bits(4607182418800017408));
    runtime_release(target);
    runtime_drop(dynamic);
"""

FAULTS = r'''
#include <stdio.h>
#include <stdlib.h>
static VStorageArena *cleanup_arenas[3];
static unsigned cleanup_closed[3], cleanup_new_count, cleanup_fill_count;
static unsigned cleanup_setting(const char *name) {
    const char *value = getenv(name);
    return value ? (unsigned)strtoul(value, NULL, 10) : 0;
}
static unsigned cleanup_id(void *data) {
    for (unsigned n = 1; n <= 2; ++n)
        if (cleanup_arenas[n] == data) return n;
    abort();
}
static lean_obj_res cleanup_error(const char *operation, unsigned id) {
    char message[80];
    snprintf(message, sizeof(message), "E_CLEANUP_%s_%u", operation, id);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}
'''


def once(source, before, after):
    if source.count(before) != 1:
        raise ValueError("unexpected native fault-injection site: " + before)
    return source.replace(before, after)


def instrument(source):
    source = once(source, "#include <stdatomic.h>", "#include <stdatomic.h>\n" + FAULTS)
    source = once(source, "static void finalize(void *data) { vstorage_delete(data); }", r'''
static void finalize(void *data) {
    unsigned n = cleanup_id(data);
    if (cleanup_closed[n] != 1 || vstorage_stats(data).live_bytes != 0) abort();
    fprintf(stderr, "CLEANUP final %u\n", n);
    vstorage_delete(data);
}''')
    source = once(source, "    initialize_class();", r'''
    unsigned n = ++cleanup_new_count;
    if (n > 2) abort();
    if (cleanup_setting("VASTITAS_CLEANUP_NEW") == n) return cleanup_error("NEW", n);
    initialize_class();''')
    source = once(source, "    if (!arena) return result(VS_ALLOCATION);", r'''
    if (!arena) return result(VS_ALLOCATION);
    cleanup_arenas[n] = arena;
    fprintf(stderr, "CLEANUP new %u\n", n);''')
    source = once(source, "    vstorage_close(arena_data(arena));", r'''
    unsigned n = cleanup_id(arena_data(arena));
    if (cleanup_closed[n]++) abort();
    fprintf(stderr, "CLEANUP close %u\n", n);
    vstorage_close(arena_data(arena));
    if (vstorage_stats(arena_data(arena)).live_bytes != 0) abort();
    if (cleanup_setting("VASTITAS_CLEANUP_CLOSE") & (1u << n)) return cleanup_error("CLOSE", n);''')
    before = "    return result(vstorage_fill(arena_data(arena), id,"
    source = once(source, before, r'''
    unsigned n = ++cleanup_fill_count;
    if (cleanup_setting("VASTITAS_CLEANUP_BODY") == n) return cleanup_error("BODY", n);
''' + before)
    return source


def main():
    frontend = ROOT / "target/debug/vastitas"
    kernel = ROOT / "lean-kernel/.lake/build/bin/vastitas-kernel"
    env = dict(os.environ, VASTITAS_KERNEL=str(kernel), VASTITAS_KERNEL_ROOT=str(ROOT / "lean-kernel"))
    cc = os.environ.get("LEAN_CC", os.environ.get("CC", "cc"))
    for key in ("VASTITAS_CLEANUP_NEW", "VASTITAS_CLEANUP_BODY", "VASTITAS_CLEANUP_CLOSE"):
        env.pop(key, None)
    with tempfile.TemporaryDirectory(prefix="vastitas-resource-cleanup-") as directory:
        work = Path(directory)
        runner = Runner(env)
        lean_prefix = Path(runner.run(["lean", "--print-prefix"])["stdout"].strip())
        runtime = work / "native"
        shutil.copytree(ROOT / "lean-kernel/native", runtime, ignore=shutil.ignore_patterns(".lake"))
        ffi = runtime / "ffi.c"
        ffi.write_text(instrument(ffi.read_text()))
        shutil.copyfile(ROOT / "lean-kernel/lean-toolchain", work / "lean-toolchain")
        (work / "lakefile.toml").write_text(
            'name = "cleanup_test"\nmoreLinkArgs = ["-L", ' + json.dumps(str(lean_prefix / "lib")) + ']\n'
            '[[require]]\nname = "vastitas_storage_native"\npath = "native"\n'
            '[[require]]\nname = "vastitas_kernel"\npath = ' + json.dumps(str(ROOT / "lean-kernel")) + '\n'
            '[[lean_exe]]\nname = "cleanup"\nroot = "Main"\n')
        executions = 0
        for name, body, arenas in (("static", STATIC, 1), ("shape", SHAPED, 1),
                                   ("nested", STATIC + SHAPED, 2)):
            package = work / name
            (package / "src").mkdir(parents=True)
            (package / "Vastitas.toml").write_text(
                '[package]\nname = "cleanup"\nversion = "0.1.0"\nroot = "src/main.vast"\n')
            (package / "src/main.vast").write_text("resource fn main() -> Int {\n" + body + "    value { 42 }\n}\n")
            wire = capture_wire(runner, frontend, package)
            runner.run([frontend, "check", "--manifest-path", package / "Vastitas.toml"])
            canonical = package / "program"
            runner.run([frontend, "build", "--manifest-path", package / "Vastitas.toml",
                        "-o", canonical])
            assert runner.run([canonical])["stdout"] == "42\n"
            response = json.loads(runner.run([kernel, "emit"], input=wire)["stdout"])
            assert response["ok"] and response["version"] == 8 and not response["numerical_runtime"]
            generated = response["lean_source"]
            assert generated.count("catch cleanupError =>") == arenas and "finally" not in generated
            (work / "Main.lean").write_text(generated)  # exact returned source
            runner.run(["lake", "build", "cleanup"], cwd=work, env=dict(env, LEAN_CC=cc))
            # All combinations include creation failures, failures in either body,
            # either cleanup, and outer cleanup overriding an inner error.
            scenarios = [(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 2), (0, 1, 2)]
            if arenas == 2:
                scenarios += [(2, 0, 0), (2, 0, 2), (0, 2, 0), (0, 0, 4),
                              (0, 1, 4), (0, 2, 4), (0, 0, 6), (0, 2, 6)]
            for failed_new, failed_body, failed_close in scenarios:
                created = list(range(1, failed_new if failed_new else arenas + 1))
                close_order = created[::-1]
                error = f"E_CLEANUP_NEW_{failed_new}" if failed_new else (
                    f"E_CLEANUP_BODY_{failed_body}" if failed_body else None)
                for n in close_order:
                    if failed_close & (1 << n):
                        error = f"E_CLEANUP_CLOSE_{n}"
                observation = runner.run([work / ".lake/build/bin/cleanup"], required=False, env=dict(
                    env, VASTITAS_CLEANUP_NEW=str(failed_new), VASTITAS_CLEANUP_BODY=str(failed_body),
                    VASTITAS_CLEANUP_CLOSE=str(failed_close)))
                stderr = observation["stderr"]
                assert (observation["returncode"] == 0) == (error is None), observation
                diagnostics = re.findall(r"E_CLEANUP_[A-Z]+_\d+", stderr)
                assert diagnostics == ([error] if error else []), observation
                assert observation["stdout"] == ("" if failed_new or failed_body else "42\n"), observation
                events = re.findall(r"^CLEANUP (new|close|final) (\d+)$", stderr, re.MULTILINE)
                observed = lambda operation: [int(n) for op, n in events if op == operation]
                assert observed("new") == created and observed("close") == close_order, observation
                assert sorted(observed("final")) == created, observation
                for n in created:
                    assert events.index(("close", str(n))) < events.index(("final", str(n))), observation
                executions += 1
            print(f"{name}: exact public source, {len(scenarios)} native cleanup/failure scenarios passed")
        print(f"resource cleanup: {executions} fault-injection executions; no BLAS")


if __name__ == "__main__":
    main()
