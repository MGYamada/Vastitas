"""Fail-closed tests for the CI tool installer, without executing fetched code."""
import hashlib
import io
from pathlib import Path
import tarfile
import tempfile
import sys
import unittest
from unittest import mock

import install_ci_elan as bootstrap


def archive(name="elan-init", kind=tarfile.REGTYPE, duplicate=False):
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode="w:gz") as tar:
        member = tarfile.TarInfo(name)
        member.type = kind
        member.linkname = "elsewhere"
        member.size = 4 if member.isfile() else 0
        tar.addfile(member, io.BytesIO(b"test") if member.isfile() else None)
        if duplicate:
            tar.addfile(member, io.BytesIO(b"test"))
    return output.getvalue()


class BootstrapTests(unittest.TestCase):
    def test_ci_python_clears_only_its_known_loader_override(self):
        script = Path(__file__).with_name("check_ci_python.sh")
        for override in ["", str(Path(sys.prefix) / "lib"), "/unexpected/loader/path"]:
            with self.subTest(override=override), tempfile.TemporaryDirectory() as temporary:
                target = Path(temporary) / "environment"
                target.write_text("preserved=value\n")
                environment = dict(bootstrap.os.environ, GITHUB_ENV=str(target),
                                   pythonLocation=sys.prefix, LD_LIBRARY_PATH=override)
                result = bootstrap.subprocess.run(["bash", str(script)], env=environment,
                                                  capture_output=True, text=True)
                if override == "/unexpected/loader/path":
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("unexpected loader override", result.stderr)
                    self.assertEqual(target.read_text(), "preserved=value\n")
                else:
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertIn("Python ", result.stdout)
                    self.assertEqual(target.read_text(), "preserved=value\nLD_LIBRARY_PATH=\n")

    def test_platforms_are_explicit(self):
        self.assertEqual(bootstrap.host_target("Darwin", "arm64"), "aarch64-apple-darwin")
        self.assertEqual(bootstrap.host_target("Linux", "x86_64"), "x86_64-unknown-linux-gnu")
        self.assertEqual(bootstrap.host_target("Linux", "aarch64"), "aarch64-unknown-linux-gnu")
        self.assertEqual(bootstrap.host_target("Darwin", "x86_64"), "x86_64-apple-darwin")
        for system, machine in [("Windows", "AMD64"), ("Linux", "riscv64")]:
            with self.assertRaisesRegex(ValueError, "unsupported"):
                bootstrap.host_target(system, machine)

    def test_checksum_is_required_before_extraction(self):
        data = archive()
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            with self.assertRaisesRegex(ValueError, "SHA-256"):
                bootstrap.extract_verified(data, "0" * 64, directory)
            self.assertEqual(list(directory.iterdir()), [])
            binary = bootstrap.extract_verified(data, hashlib.sha256(data).hexdigest(), directory)
            self.assertEqual(binary.read_bytes(), b"test")
            self.assertEqual(binary.stat().st_mode & 0o777, 0o700)

    def test_archive_shape_does_not_allow_paths_links_or_duplicate_members(self):
        cases = [archive("../elan-init"), archive("nested/elan-init"),
                 archive(kind=tarfile.SYMTYPE), archive(kind=tarfile.LNKTYPE), archive(duplicate=True)]
        for data in cases:
            with self.subTest(data=data[:20]), tempfile.TemporaryDirectory() as temporary:
                directory = Path(temporary)
                with self.assertRaisesRegex(ValueError, "exactly one regular"):
                    bootstrap.extract_verified(data, hashlib.sha256(data).hexdigest(), directory)
                self.assertEqual(list(directory.iterdir()), [])

    def test_modified_release_never_runs_or_publishes_environment(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "release.tar.gz"
            source.write_bytes(archive())
            with mock.patch.object(bootstrap.subprocess, "run") as run:
                with mock.patch.dict(bootstrap.os.environ, {"GITHUB_ENV": str(root / "env"),
                                                           "GITHUB_PATH": str(root / "path")}):
                    with self.assertRaisesRegex(ValueError, "SHA-256"):
                        bootstrap.install(root / "installation", source)
            run.assert_not_called()
            self.assertFalse((root / "installation").exists())
            self.assertFalse((root / "env").exists())
            self.assertFalse((root / "path").exists())

    def test_existing_installation_is_preserved_without_network(self):
        with tempfile.TemporaryDirectory() as temporary:
            with mock.patch.object(bootstrap.urllib.request, "urlopen") as download:
                with self.assertRaisesRegex(ValueError, "existing installations"):
                    bootstrap.install(Path(temporary))
            download.assert_not_called()

    def test_installer_failure_or_version_mismatch_does_not_publish(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "release.tar.gz"
            source.write_bytes(archive())
            with mock.patch.object(bootstrap, "extract_verified", return_value=root / "elan-init"):
                with mock.patch.dict(bootstrap.os.environ, {"GITHUB_ENV": str(root / "env"),
                                                           "GITHUB_PATH": str(root / "path")}):
                    with mock.patch.object(bootstrap.subprocess, "run", side_effect=RuntimeError("installer failed")):
                        with self.assertRaisesRegex(RuntimeError, "installer failed"):
                            bootstrap.install(root / "installation", source)
                    with mock.patch.object(bootstrap.subprocess, "run") as run:
                        with mock.patch.object(bootstrap.subprocess, "check_output", return_value="elan 0.0.0"):
                            with self.assertRaisesRegex(ValueError, "unexpected installed"):
                                bootstrap.install(root / "installation", source)
                    self.assertIn("--no-modify-path", run.call_args.args[0])
                    self.assertEqual(run.call_args.kwargs["env"]["ELAN_HOME"], str((root / "installation").resolve()))
            self.assertFalse((root / "env").exists())
            self.assertFalse((root / "path").exists())


if __name__ == "__main__":
    unittest.main()
