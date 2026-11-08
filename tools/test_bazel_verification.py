"""Offline integration tests: real queue and Git, fake Bazel/Lake executables."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

from agent_workspaces import AgentWorkspaceManager
from bazel_verification import PACKAGE_BUILD, bazel_target, ensure_bazel_coverage, verification_backend


FAKE_BUILDER = r'''
import json, os, pathlib, sys
args = sys.argv[1:]
with open(os.environ["BAZEL_TEST_LOG"], "a") as log:
    log.write(json.dumps([pathlib.Path(sys.argv[0]).name, *args]) + "\n")
if pathlib.Path(sys.argv[0]).name == "lake":
    assert args[:2] == ["env", "lean"], args
    paths = [pathlib.Path(args[2])]
else:
    assert args[:2] == ["build", "--config=buildbuddy"], args
    paths = []
    for arg in args:
        if arg.startswith("//") and arg != "//:RiemannResearch":
            package, name = arg[2:].split(":")
            source = pathlib.Path(package) / (name + ".lean")
            assert (source.parent / "BUILD.bazel").is_file(), source
            paths.append(source)
    if "//:RiemannResearch" in args:
        paths = list(pathlib.Path("RiemannResearch").rglob("*.lean"))
    assert paths, args
    for source in paths:
        assert source.is_file(), source
        assert (source.parent / "BUILD.bazel").is_file(), source
if any("FAIL_TEST" in source.read_text() for source in paths):
    print("error: deliberately failed test compilation", flush=True)
    sys.exit(1)
print("test compiler success", flush=True)
'''


def git(project, *args):
    return subprocess.run(["git", *args], cwd=project, check=True, capture_output=True, text=True).stdout.strip()


class BazelVerificationTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.source = self.root / "source"
        self.source.mkdir()
        for relative, content in {
            "BUILD.bazel": 'load("//bazel:lean_modules.bzl", "lean_project")\nlean_project()\n',
            "MODULE.bazel": 'module(name = "test")\n',
            "bazel/lean_modules.bzl": "# fake builder fixture\n",
            "RiemannResearch/Test/A.lean": "theorem sample : True := by trivial\n",
            "RiemannResearch.lean": "import RiemannResearch.Test.A\n",
            "lean-toolchain": "leanprover/lean4:v4.33.0-rc2\n",
            "lakefile.toml": 'name = "RiemannResearch"\n',
            "lake-manifest.json": '{"packages": []}\n',
            "AGENTS.md": "# Test\n", "README.md": "Test\n",
            ".gitignore": "/.lake/\n/bazel-*\n",
        }.items():
            path = self.source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        ensure_bazel_coverage(self.source)
        git(self.source, "init", "-b", "main")
        git(self.source, "config", "user.name", "Test")
        git(self.source, "config", "user.email", "test@example.com")
        git(self.source, "add", ".")
        git(self.source, "commit", "-m", "Initial fixture")
        self.remote = self.root / "remote.git"
        git(self.root, "clone", "--bare", str(self.source), str(self.remote))
        binary = self.root / "bin"
        binary.mkdir()
        for name in ("bazel", "lake"):
            path = binary / name
            path.write_text("#!" + sys.executable + "\n" + FAKE_BUILDER)
            path.chmod(0o755)
        self.log = self.root / "commands.jsonl"
        environment = patch.dict(os.environ, {
            "LEAN_VERIFICATION_BACKEND": "bazel", "LEAN_JOB_WORKERS": "1",
            "LEAN_REMOTE_CACHE_SERVICE": "", "LAKE_CACHE_DIR": "",
            "LEAN_AGENT_WORKSPACES_ROOT": str(self.root / "workspaces"),
            "LEAN_AGENT_WORKSPACES_STATE": str(self.root / "state"),
            "LEAN_SHARED_DEPS_ROOT": str(self.root / "deps"),
            "LEAN_SHARED_PROJECT_BUILDS_ROOT": str(self.root / "cache"),
            "BAZEL_TEST_LOG": str(self.log), "PATH": str(binary) + os.pathsep + os.environ["PATH"],
        })
        environment.start()
        self.addCleanup(environment.stop)
        self.manager = AgentWorkspaceManager(self.source, str(self.remote))
        self.addCleanup(self.manager._owner_lease.close)
        workspace = self.manager.open()
        self.token = workspace["workspace_token"]
        self.project = Path(workspace["project_root"])
        git(self.project, "config", "commit.gpgsign", "false")
        self.assertFalse(self.log.exists(), "Bazel workspace provisioning must not build with Lake")

    def commands(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def terminal(self, submission):
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            result = self.manager.job_status(submission["job_id"], include_logs=True)
            if result["terminal"]:
                return result
            time.sleep(0.01)
        self.fail("Queue did not finish")

    def test_default_and_rejected_backend(self):
        with patch.dict(os.environ):
            os.environ.pop("LEAN_VERIFICATION_BACKEND", None)
            self.assertEqual(verification_backend(), "bazel")
        with self.assertRaises(ValueError):
            self.manager.submit_build(self.token, "typo")

    def test_full_build_uses_buildbuddy_and_all_packages(self):
        result = self.terminal(self.manager.submit_build(self.token))
        self.assertEqual(result["state"], "succeeded")
        self.assertEqual(self.commands()[0][:3], ["bazel", "build", "--config=buildbuddy"])
        self.assertEqual(self.commands()[0][-1], "//:RiemannResearch")

    def test_new_directory_is_packaged_after_patch_and_checked(self):
        diff = "diff --git a/RiemannResearch/New/Deep/B.lean b/RiemannResearch/New/Deep/B.lean\nnew file mode 100644\n--- /dev/null\n+++ b/RiemannResearch/New/Deep/B.lean\n@@ -0,0 +1 @@\n+theorem b : True := by trivial\n"
        result = self.manager.apply_patch(self.token, diff)
        self.assertEqual(len(result["created_build_files"]), 2)
        for directory in ("New", "New/Deep"):
            self.assertEqual((self.project / "RiemannResearch" / directory / "BUILD.bazel").read_text(), PACKAGE_BUILD)
        checked = self.terminal(self.manager.submit_check_file(self.token, "RiemannResearch/New/Deep/B.lean"))
        self.assertTrue(checked["result"]["verified"])
        self.assertEqual(self.commands()[-1][-1], "//RiemannResearch/New/Deep:B")

    def test_snippet_success_failure_and_cleanup_no_fallback(self):
        for code, expected in (("example : True := by trivial\n", "succeeded"), ("-- FAIL_TEST\n", "failed")):
            result = self.terminal(self.manager.submit_run_code(self.token, code))
            self.assertEqual(result["state"], expected)
            self.assertEqual(result["result"]["backend"], "bazel")
            self.assertTrue(result["result"]["temporary_file_removed"])
        self.assertFalse(list((self.project / "RiemannResearch").glob("McpSnippet_*")))
        self.assertTrue(all(command[0] == "bazel" for command in self.commands()))

    def test_explicit_lake_override_and_frozen_request_identity(self):
        (self.project / ".lake/packages").mkdir(parents=True)
        request = self.manager.submit_run_code(self.token, "example : True := by trivial\n", backend="lake")
        result = self.terminal(request)
        self.assertEqual(result["state"], "succeeded")
        self.assertEqual(result["result"]["backend"], "lake")
        self.assertEqual(self.manager._read_job(request["job_id"])["arguments"]["backend"], "lake")
        self.assertEqual(self.commands()[0][:3], ["lake", "env", "lean"])

    def test_checkpoint_build_failure_blocks_publication(self):
        source = self.project / "RiemannResearch/Test/A.lean"
        before = git(self.remote, "rev-parse", "main")
        source.write_text("-- FAIL_TEST\n")
        result = self.terminal(self.manager.submit_checkpoint(self.token, "Failing checkpoint"))
        self.assertEqual(result["state"], "failed")
        self.assertEqual(git(self.remote, "rev-parse", "main"), before)

    def test_build_file_only_change_triggers_full_checkpoint(self):
        build = self.project / "RiemannResearch/Test/BUILD.bazel"
        build.write_text(build.read_text() + "# package change\n")
        result = self.terminal(self.manager.submit_checkpoint(self.token, "Package checkpoint"))
        self.assertEqual(result["state"], "succeeded", result)
        self.assertEqual(result["result"]["build"]["scope"], "full")
        self.assertEqual(self.commands()[-1][-1], "//:RiemannResearch")
        self.assertEqual(git(self.remote, "rev-parse", "main"), result["result"]["commit"])

    def test_coverage_check_is_read_only_then_fix_is_idempotent(self):
        source = self.project / "RiemannResearch/Fresh/Nested/C.lean"
        source.parent.mkdir(parents=True)
        source.write_text("example : True := by trivial\n")
        self.assertEqual(len(ensure_bazel_coverage(self.project, fix=False)), 2)
        self.assertFalse((source.parent / "BUILD.bazel").exists())
        self.assertEqual(len(ensure_bazel_coverage(self.project)), 2)
        self.assertEqual(ensure_bazel_coverage(self.project), [])
        self.assertEqual(bazel_target(self.project, source), "//RiemannResearch/Fresh/Nested:C")

    def test_coverage_preserves_custom_packages_and_rejects_symlinks(self):
        build = self.project / "RiemannResearch/Test/BUILD.bazel"
        custom = PACKAGE_BUILD + "# custom package\n"
        build.write_text(custom)
        ensure_bazel_coverage(self.project)
        self.assertEqual(build.read_text(), custom)
        build.write_text("# empty package loses coverage\n")
        with self.assertRaisesRegex(ValueError, "must call lean_modules"):
            ensure_bazel_coverage(self.project)
        build.unlink()
        build.symlink_to(self.source / "BUILD.bazel")
        with self.assertRaisesRegex(ValueError, "symlink"):
            ensure_bazel_coverage(self.project)


if __name__ == "__main__":
    unittest.main()
