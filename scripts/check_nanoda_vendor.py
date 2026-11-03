#!/usr/bin/env python3
"""Compare the bundled audit implementation to its pinned upstream Git objects."""
from pathlib import Path
import subprocess
import sys

REVISION = "8de7e0c4ed3052745a7f8725164efd9e76d84c56"
VENDOR = Path(__file__).resolve().parents[1] / "src/vendor/nanoda"
HEADER = b"// Modified for Vastitas to keep upstream module paths and macros private.\n"
MODULES = "debug_printer env expr inductive level name parser pretty_printer quot tc unique_hasher util".split()


def upstream(checkout, path):
    return subprocess.check_output(["git", "-C", checkout, "show", f"{REVISION}:{path}"])


def check(checkout):
    if {p.stem for p in VENDOR.glob("*.rs")} != {*MODULES, "mod"}:
        raise ValueError("unexpected set of bundled modules")
    for name in MODULES:
        original = upstream(checkout, f"src/{name}.rs")
        local = original.replace(b"crate::", b"crate::nanoda::").replace(b"#[macro_export]\n", b"")
        if name == "util":
            marker = b"/// The implementation of natural number subtraction"
            local = local.replace(marker, b"pub(super) use hash64;\n\n" + marker)
        if local != original:
            local = HEADER + local
        if (VENDOR / f"{name}.rs").read_bytes() != local:
            raise ValueError(f"{name}.rs differs from the adapted pinned source")
    if (VENDOR / "LICENSE").read_bytes() != upstream(checkout, "LICENSE"):
        raise ValueError("upstream license differs")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("usage: check_nanoda_vendor.py PATH_TO_UPSTREAM_GIT_CHECKOUT")
    check(sys.argv[1])
    print(f"Verified {len(MODULES)} production modules and the license against {REVISION}")
