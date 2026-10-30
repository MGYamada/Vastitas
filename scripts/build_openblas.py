#!/usr/bin/env python3
"""Build the optional, pinned sequential LP64 BLAS dependency in an explicit prefix."""

import argparse
import hashlib
import json
import os
from pathlib import Path
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
        env = os.environ.copy()
        # The supported profile is explicit, not inherited from a user's Make flags.
        for name in ("MAKEFLAGS", "MFLAGS", "GNUMAKEFLAGS", "USE_OPENMP", "SYMBOLSUFFIX", "SYMBOLPREFIX",
                     "LIBNAMESUFFIX", "LIBPREFIX", "TARGET", "TARGET_CORE", "NO_CBLAS", "NO_STATIC",
                     "CFLAGS", "COMMON_OPT", "FC"):
            env.pop(name, None)
        options = OPTIONS + ([f"TARGET={target}"] if target else [])
        subprocess.run(["make", f"-j{jobs}", *options], cwd=source, env=env, check=True)
        subprocess.run(["make", *options, f"PREFIX={prefix}", "install"], cwd=source, env=env, check=True)
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
