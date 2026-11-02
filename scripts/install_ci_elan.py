#!/usr/bin/env python3
"""Install the checksum-pinned CI bootstrap without changing the user's profile.

Digests are the release asset SHA-256 values published by leanprover/elan:
https://github.com/leanprover/elan/releases/tag/v4.2.4
The archive is verified before extracting or executing its installer. Lean's
version remains selected by the repository's checked-in lean-toolchain files.
"""
from __future__ import annotations

import argparse
import hashlib
import io
import os
from pathlib import Path
import platform
import subprocess
import tarfile
import tempfile
import urllib.request

VERSION = "4.2.4"
ASSETS = {
    "aarch64-apple-darwin": "7ad829861392c718dfebde3a83b5c8508df47be02af68894b094b0b3952616e5",
    "x86_64-apple-darwin": "8a340b309d8ed2e96f930761fa223b3af57a38f5d253b53ac90293c9516f8cd4",
    "aarch64-unknown-linux-gnu": "05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9",
    "x86_64-unknown-linux-gnu": "42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63",
}
ARCHIVE_LIMIT = 32 * 1024 * 1024
INSTALLER_LIMIT = 64 * 1024 * 1024


def host_target(system: str, machine: str) -> str:
    architecture = {"arm64": "aarch64", "aarch64": "aarch64", "x86_64": "x86_64"}.get(machine)
    operating_system = {"Darwin": "apple-darwin", "Linux": "unknown-linux-gnu"}.get(system)
    target = f"{architecture}-{operating_system}"
    if target not in ASSETS:
        raise ValueError(f"unsupported CI elan platform: {system}/{machine}")
    return target


def extract_verified(data: bytes, expected: str, directory: Path) -> Path:
    if len(data) > ARCHIVE_LIMIT or hashlib.sha256(data).hexdigest() != expected:
        raise ValueError("elan archive SHA-256 mismatch or size limit exceeded")
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as archive:
        members = archive.getmembers()
        if (len(members) != 1 or members[0].name != "elan-init"
                or not members[0].isfile() or not 0 < members[0].size <= INSTALLER_LIMIT):
            raise ValueError("elan archive must contain exactly one regular elan-init executable")
        source = archive.extractfile(members[0])
        if source is None:
            raise ValueError("elan installer payload is missing")
        payload = source.read(INSTALLER_LIMIT + 1)
        if len(payload) != members[0].size:
            raise ValueError("elan installer payload has an invalid size")
    installer = directory / "elan-init"
    with installer.open("xb") as output:
        output.write(payload)
    installer.chmod(0o700)
    return installer


def install(destination: Path, archive_path: Path | None = None) -> Path:
    destination = destination.resolve()
    if "\n" in str(destination) or "\r" in str(destination):
        raise ValueError("elan destination must fit a single CI environment line")
    if destination.exists():
        raise ValueError("CI elan destination must be new; existing installations are not modified")
    target = host_target(platform.system(), platform.machine())
    if archive_path is None:
        url = f"https://github.com/leanprover/elan/releases/download/v{VERSION}/elan-{target}.tar.gz"
        with urllib.request.urlopen(url, timeout=60) as response:
            data = response.read(ARCHIVE_LIMIT + 1)
    else:
        with archive_path.open("rb") as source:
            data = source.read(ARCHIVE_LIMIT + 1)
    with tempfile.TemporaryDirectory(prefix="vastitas-elan-installer-") as temporary:
        installer = extract_verified(data, ASSETS[target], Path(temporary))
        environment = {**os.environ, "ELAN_HOME": str(destination)}
        subprocess.run([str(installer), "-y", "--no-modify-path", "--default-toolchain", "none"],
                       env=environment, check=True)
    binary = destination / "bin" / "elan"
    version = subprocess.check_output([str(binary), "--version"], env=environment, text=True).strip()
    if version.split()[:2] != ["elan", VERSION]:
        raise ValueError(f"unexpected installed elan version: {version}")
    # Publish only after both the release digest and installed version match.
    for variable, line in [("GITHUB_ENV", f"ELAN_HOME={destination}"),
                           ("GITHUB_PATH", str(destination / "bin"))]:
        if path := os.environ.get(variable):
            with Path(path).open("a", encoding="utf-8") as output:
                output.write(line + "\n")
    print(version)
    return binary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--destination", type=Path, required=True)
    parser.add_argument("--archive", type=Path, help="offline release archive; the same digest is required")
    arguments = parser.parse_args()
    install(arguments.destination, arguments.archive)


if __name__ == "__main__":
    main()
