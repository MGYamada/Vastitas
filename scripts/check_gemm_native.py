#!/usr/bin/env python3
"""Validate the optional GEMM adapter against a pinned OpenBLAS installation."""

import argparse
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile
from native_sanitizers import FLAGS as SANITIZER_FLAGS

ROOT = Path(__file__).resolve().parent.parent


def run(command: list[str], **kwargs: object) -> None:
    subprocess.run(command, check=True, **kwargs)


def check(prefix: Path, valgrind: bool) -> None:
    prefix = prefix.resolve()
    native = ROOT / "lean-kernel/native"
    numerical = ROOT / "lean-kernel/numerical"
    archive = prefix / "lib/libopenblas.a"
    if not archive.is_file():
        raise ValueError(f"missing pinned OpenBLAS static archive: {archive}")
    flags = [*shlex.split(os.environ.get("CC", "cc")), "-std=c11", "-Wall", "-Wextra", "-Werror",
             f"-I{native}", f"-I{prefix / 'include'}"]
    # Neither normal compiler tests nor the storage-only suite call this script.
    with tempfile.TemporaryDirectory(prefix="vastitas-gemm-") as temporary:
        directory = Path(temporary)
        sources = [str(native / "storage.c"), str(native / "diagonal.c"), str(numerical / "gemm.c"), str(numerical / "test_gemm.c")]
        libraries = [str(archive), "-lm", "-lpthread"]
        executable = directory / "test-gemm"
        run(flags + ["-O2", "-g", *sources, *libraries, "-o", str(executable)])
        run([str(executable)])
        sanitized = directory / "test-gemm-sanitized"
        run(flags + ["-O1", "-g", *SANITIZER_FLAGS,
                     *sources, *libraries, "-o", str(sanitized)])
        run([str(sanitized)])
        # Exercise concurrent first use with the actual backend and count exact
        # provider calls with mocks. Fresh processes isolate each bad config;
        # the actual CBLAS symbols stay linked in every variant.
        backend_sources = [*sources[:-1], str(numerical / "test_backend.c")]
        threaded = directory / "test-threaded"
        for mocked in (False, True):
            definitions = (["-DVGEMM_TEST_BACKEND", "-Dopenblas_get_config=vgemm_test_config",
                            "-Dopenblas_get_parallel=vgemm_test_parallel"] if mocked else [])
            for sanitized_mode in (False, True):
                backend = directory / (f"test-backend-{mocked}-{sanitized_mode}") if mocked or sanitized_mode else threaded
                run(flags + ["-O1", *definitions, *(SANITIZER_FLAGS if sanitized_mode else []),
                             *backend_sources, *libraries, "-o", str(backend)])
                run([str(backend)], timeout=120)
        rejected = subprocess.run(flags + ["-DOPENBLAS_USE64BITINT=1", "-c", str(numerical / "gemm.c"),
                                          "-o", str(directory / "bad-abi.o")], capture_output=True, text=True)
        if rejected.returncode == 0 or "LP64 integer ABI required" not in rejected.stderr:
            raise AssertionError(f"ILP64 header rejection did not run: {rejected.stderr}")
        if valgrind:
            tool = shutil.which("valgrind")
            if tool is None:
                raise ValueError("--valgrind requested but valgrind is unavailable")
            # Instrument the actual OpenBLAS machine code, including reads from
            # uninitialized malloc output. Sanitizing only our shim cannot do that.
            run([tool, "--error-exitcode=97", "--track-origins=yes", "--leak-check=full", str(executable)])
            run([tool, "--error-exitcode=97", "--track-origins=yes", "--leak-check=full", str(threaded)])
    print("Optional GEMM adapter checks passed; source/type integration is a separate obligation.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True)
    parser.add_argument("--valgrind", action="store_true")
    args = parser.parse_args()
    check(args.prefix, args.valgrind)


if __name__ == "__main__":
    main()
