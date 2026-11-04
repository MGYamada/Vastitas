#!/usr/bin/env python3
"""Build the optional, pinned sequential LP64 BLAS dependency in an explicit prefix."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tarfile
import tempfile
import urllib.request

VERSION = "0.3.34"
URL = f"https://github.com/OpenMathLib/OpenBLAS/releases/download/v{VERSION}/OpenBLAS-{VERSION}.tar.gz"
SHA256 = "cd7e129868320cc2d033afa920e31202dfe0b8066a5b66661900ccc0f197dfed"
OPTIONS = ["USE_THREAD=0", "USE_LOCKING=1", "NO_LAPACK=1", "NOFORTRAN=1", "INTERFACE64=0",
           "NO_SHARED=1", "BINARY=64", "DYNAMIC_ARCH=0", "NO_AFFINITY=1"]
# Report the linked library's own profile, as the GEMM adapter reads it at run time.
PROFILE_PROBE = r"""#include <cblas.h>
#include <stdio.h>
int main(void) {
    const char *configuration = openblas_get_config();
    printf("%d\n%s\n", openblas_get_parallel(), configuration ? configuration : "");
    return 0;
}
"""


# Make imports every environment variable as a variable, and OpenBLAS reads
# many of them (NO_AVX2, NUM_THREADS, BUFFERSIZE, LDFLAGS, CPPFLAGS, ...). The
# supported profile is therefore built from an allow-list, not by removing
# known names. CC stays selectable; check_profile verifies the result.
BUILD_ENVIRONMENT = ("PATH", "HOME", "TMPDIR", "LANG", "LC_ALL", "LC_CTYPE", "CC", "SDKROOT", "DEVELOPER_DIR",
                     "MACOSX_DEPLOYMENT_TARGET")


def build_environment(source) -> dict[str, str]:
    return {name: source[name] for name in BUILD_ENVIRONMENT if name in source}


def check_profile(prefix: Path, work: Path, env: dict[str, str]) -> str:
    """Fail closed unless the installed archive is sequential, locked and LP64.

    A sequential 0.3.34 build serializes its shared buffer pool only with
    USE_LOCKING=1, and the GEMM adapter rejects any build that does not report it.
    """
    probe, executable = work / "profile.c", work / "profile"
    probe.write_text(PROFILE_PROBE)
    subprocess.run([*shlex.split(env.get("CC", "cc")), "-std=c11", f"-I{prefix / 'include'}", str(probe),
                    str(prefix / "lib/libopenblas.a"), "-lm", "-lpthread", "-o", str(executable)],
                   env=env, check=True)
    output = subprocess.run([str(executable)], env=env, check=True, capture_output=True, text=True).stdout
    parallel, _, configuration = output.removesuffix("\n").partition("\n")
    head = f"OpenBLAS {VERSION} "
    if (parallel != "0" or not configuration.startswith(head) or "USE64BITINT" in configuration or
            " USE_LOCKING " not in configuration[len(head) - 1:]):
        raise ValueError(f"built OpenBLAS is not the sequential locked LP64 profile: "
                         f"parallel={parallel!r}, configuration={configuration!r}")
    return configuration


def build(prefix: Path, archive: Path | None, jobs: int, target: str | None) -> None:
    prefix = prefix.resolve()
    if prefix.exists() and any(prefix.iterdir()):
        raise ValueError(f"refusing to replace a nonempty prefix: {prefix}")
    with tempfile.TemporaryDirectory(prefix="vastitas-openblas-") as temporary:
        root = Path(temporary)
        if archive is None:
            archive = root / "source.tar.gz"
            with urllib.request.urlopen(URL, timeout=120) as response, archive.open("wb") as output:
                shutil.copyfileobj(response, output)
        digest = hashlib.sha256(archive.read_bytes()).hexdigest()
        if digest != SHA256:
            raise ValueError(f"OpenBLAS source checksum mismatch: {digest}")
        # Reject archive traversal and special files, even after verifying the pin.
        with tarfile.open(archive) as source:
            source.extractall(root, filter="data")
        source = root / f"OpenBLAS-{VERSION}"
        env = build_environment(os.environ)
        options = OPTIONS + ([f"TARGET={target}"] if target else [])
        subprocess.run(["make", f"-j{jobs}", *options], cwd=source, env=env, check=True)
        subprocess.run(["make", *options, f"PREFIX={prefix}", "install"], cwd=source, env=env, check=True)
        print(f"verified OpenBLAS profile: {check_profile(prefix, root, env)}")
        license_dir = prefix / "share/licenses/OpenBLAS"
        license_dir.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source / "LICENSE", license_dir / "LICENSE")
        (prefix / "vastitas-openblas.json").write_text(json.dumps({
            "version": VERSION, "source": URL, "sha256": SHA256,
            "make_options": options, "cpu_target": target or "build-host auto-detection",
            "integer_abi": "LP64", "threading": "sequential with locking",
            "scope": "BLAS/CBLAS only; no LAPACK; host-specific static archive",
        }, indent=2) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", required=True, type=Path)
    parser.add_argument("--archive", type=Path, help="use an already downloaded, checksum-verified release archive")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--target", choices=["HASWELL", "ARMV8"], help="explicit CPU profile; default is build-host detection")
    args = parser.parse_args()
    if not 1 <= args.jobs <= 64:
        parser.error("--jobs must be between 1 and 64")
    build(args.prefix, args.archive, args.jobs, args.target)


if __name__ == "__main__":
    main()
