"""Fail-closed tests for the CI tool installer, without executing fetched code."""
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import sys
import unittest
from unittest import mock

import install_ci_elan as bootstrap
from spec_workflows import yaml_load


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
    def test_setup_action_inputs_are_in_each_sparse_checkout(self):
        root = Path(__file__).resolve().parents[1]
        dependencies = {
            "./.github/actions/run-numerical-experiment": [],
            "./.github/actions/setup-elan": ["scripts/install_ci_elan.py"],
            "./.github/actions/setup-python": ["scripts/check_ci_python.sh"],
            "./.github/actions/setup-rust": ["rust-toolchain.toml"],
            "./.github/actions/setup-openblas": ["scripts/build_openblas.py"],
        }
        for path in sorted((root / ".github/workflows").glob("*.yml")):
            for name, job in yaml_load(path.read_text())["jobs"].items():
                steps = job.get("steps", [])
                for index, step in enumerate(steps):
                    action = step.get("uses")
                    if action not in dependencies:
                        continue
                    inputs = [f"{action[2:]}/action.yml", *dependencies[action]]
                    if action == "./.github/actions/run-numerical-experiment":
                        inputs.append(step["with"]["harness"])
                        self.assertTrue((root / inputs[-1]).is_file())
                    with self.subTest(workflow=path.name, job=name, action=action):
                        checkout = next(s for s in reversed(steps[:index])
                                        if s.get("uses", "").startswith("actions/checkout@"))
                        patterns = checkout.get("with", {}).get("sparse-checkout")
                        if patterns is None:
                            continue
                        with tempfile.TemporaryDirectory() as directory:
                            rules = Path(directory) / "rules"
                            rules.write_text(patterns)
                            result = subprocess.run(
                                ["git", "sparse-checkout", "check-rules", "--no-cone",
                                 "--rules-file", str(rules)], cwd=root, input="\n".join(inputs) + "\n",
                                text=True, capture_output=True, check=True)
                        self.assertEqual(result.stdout.splitlines(), inputs)

    def test_numerical_action_preserves_sampling_and_result_paths(self):
        root = Path(__file__).resolve().parents[1]
        action = root / ".github/actions/run-numerical-experiment/action.yml"
        step, = yaml_load(action.read_text())["runs"]["steps"]
        with tempfile.TemporaryDirectory(prefix="ci numerical ") as directory:
            work = Path(directory)
            harness = work / "record arguments.py"
            harness.write_text("import json, pathlib, sys\n"
                               "p = pathlib.Path(sys.argv[sys.argv.index('--output') + 1])\n"
                               "p.mkdir()\n"
                               "(p / 'status.json').write_text(json.dumps(sys.argv[1:]))\n")
            for profile, sampling in [("smoke", ["--smoke", "--samples", "6", "--target-ms", "0.1"]),
                                      ("full", ["--samples", "12", "--target-ms", "5"]),
                                      ("unsupported", None)]:
                with self.subTest(profile=profile):
                    results = f"{profile} results"
                    env = dict(bootstrap.os.environ, HARNESS=str(harness), RUNNER_TEMP=directory,
                               RESULTS=results, PROFILE=profile)
                    launched = subprocess.run(["bash", "-eu", "-c", step["run"]], env=env,
                                              capture_output=True, text=True)
                    if sampling is None:
                        self.assertEqual(launched.returncode, 2)
                        self.assertFalse((work / results).exists())
                    else:
                        self.assertEqual(launched.returncode, 0, launched.stderr)
                        self.assertEqual(json.loads(launched.stdout),
                                         ["--prefix", str(work / "vastitas-openblas"),
                                          "--output", str(work / results), *sampling])

    def test_rust_installer_uses_the_channel_in_the_checked_out_manifest(self):
        root = Path(__file__).resolve().parents[1]
        steps = yaml_load((root / ".github/actions/setup-rust/action.yml").read_text())["runs"]["steps"]
        pin, install = steps
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            (work / "rust-toolchain.toml").write_text('[toolchain]\nchannel = "1.98.0"\n')
            output = work / "output"
            subprocess.run(["bash", "-eu", "-c", pin["run"]], cwd=work, check=True,
                           env=dict(bootstrap.os.environ, GITHUB_OUTPUT=str(output)))
            self.assertEqual(output.read_text(), "channel=1.98.0\n")
        self.assertEqual(install["with"]["toolchain"], "${{ steps." + pin["id"] + ".outputs.channel }}")

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

    def test_workflows_install_lean_only_through_the_pinned_bootstrap(self):
        # Third-party Lean actions fetch elan's unpinned master installer.
        workflows = Path(__file__).resolve().parents[1] / ".github" / "workflows"
        paths = sorted(workflows.glob("*.yml"))
        self.assertTrue(paths)
        for path in paths:
            with self.subTest(workflow=path.name):
                text = path.read_text(encoding="utf-8")
                self.assertNotIn("leanprover/lean-action", text)
                self.assertNotIn("elan-init.sh", text)
                for name, job in yaml_load(text)["jobs"].items():
                    installed = False
                    for step in job.get("steps", []):
                        if step.get("uses") == "./.github/actions/setup-elan":
                            installed = True
                        script = step.get("run", "")
                        self.assertNotIn("install_ci_elan.py", script)
                        if "lake " in script:
                            self.assertTrue(installed, f"{path.name}/{name} uses Lake before setup")
        steps = yaml_load((workflows.parent / "actions/setup-elan/action.yml").read_text())["runs"]["steps"]
        self.assertEqual([step["run"] for step in steps],
                         ['python3 scripts/install_ci_elan.py --destination "$RUNNER_TEMP/vastitas-elan"'])

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
