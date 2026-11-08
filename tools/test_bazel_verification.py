"""Offline integration tests: real queue and Git, fake Bazel/Lake executables."""

import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

from agent_workspaces import AgentWorkspaceManager
from bazel_verification import (
    PACKAGE_BUILD, bazel_build_command, bazel_cache_options, bazel_output_base,
    bazel_target, ensure_bazel_coverage, verification_backend,
)


FAKE_BUILDER = r'''
import json, os, pathlib, shutil, sys
args = sys.argv[1:]
with open(os.environ["BAZEL_TEST_LOG"], "a") as log:
    log.write(json.dumps([pathlib.Path(sys.argv[0]).name, *args]) + "\n")
if pathlib.Path(sys.argv[0]).name == "lake":
    assert args[:2] == ["env", "lean"], args
    paths = [pathlib.Path(args[2])]
else:
    startup = []
    while args and args[0].startswith("--"):
        startup.append(args.pop(0))
    base = pathlib.Path(next(a.split("=", 1)[1] for a in startup if a.startswith("--output_base=")))
    assert "--output_user_root=" + str(base.parent) in startup, startup
    if args == ["clean", "--expunge_async"]:
        assert "--noblock_for_lock" in startup, startup
        if os.environ.get("BAZEL_TEST_BUSY") == "1":
            print("Another command holds the client lock", flush=True)
            sys.exit(9)
        shutil.rmtree(base)
        sys.exit(0)
    assert args[:2] == ["build", "--config=buildbuddy"], args
    base.mkdir(parents=True, exist_ok=True)
    (base / "generated-output").write_text("regenerable")
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
            "LEAN_BAZEL_STORAGE_ROOT": str(self.root / "global bazel cache"),
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

    def build_args(self, index=-1):
        command = self.commands()[index]
        return command[command.index("build"):]

    def expire(self):
        meta = self.manager._read_meta(self.token)
        meta["last_activity"] = 0
        self.manager._write_meta(meta)

    def prepare_outputs(self):
        base = bazel_output_base(self.project, self.manager.bazel_storage)
        base.mkdir(parents=True, exist_ok=True)
        (base / "generated-output").write_text("regenerable")
        for name in ("disk", "repository", "repo-contents"):
            shared = self.manager.bazel_storage / name
            shared.mkdir(exist_ok=True)
            (shared / "keep").write_text("shared")
        return base

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
        self.assertEqual(self.commands()[0][0], "bazel")
        self.assertEqual(self.build_args(0)[:2], ["build", "--config=buildbuddy"])
        self.assertEqual(self.commands()[0][-1], "//:RiemannResearch")

    def test_checkouts_share_caches_but_have_distinct_external_output_bases(self):
        second = self.manager.open()
        other = Path(second["project_root"])
        first_command = bazel_build_command(["//:RiemannResearch"], project=self.project,
                                            storage_root=self.manager.bazel_storage)
        second_command = bazel_build_command(["//:RiemannResearch"], project=other,
                                             storage_root=self.manager.bazel_storage)
        for prefix in ("--repository_cache=", "--repo_contents_cache=", "--disk_cache=", "--output_user_root="):
            first = next(a for a in first_command if a.startswith(prefix))
            self.assertIn(first, second_command)
            shared = Path(first.split("=", 1)[1])
            self.assertFalse(shared.is_relative_to(self.project))
            self.assertFalse(shared.is_relative_to(other))
        self.assertNotEqual(bazel_output_base(self.project, self.manager.bazel_storage),
                            bazel_output_base(other, self.manager.bazel_storage))
        for token in (self.token, second["workspace_token"]):
            self.assertEqual(self.terminal(self.manager.submit_build(token))["state"], "succeeded")
        self.assertEqual(len(self.commands()), 2)
        self.assertNotEqual(self.commands()[0][2], self.commands()[1][2])

    def test_bazelrc_and_managed_cache_flags_match(self):
        root = Path(__file__).resolve().parent.parent
        options = []
        for line in (root / ".bazelrc").read_text().splitlines():
            tokens = shlex.split(line, comments=True)
            if tokens and tokens[0] in {"build", "common"}:
                options.extend(tokens[1:])
        home = Path("~/.cache/riemann-bazel")
        for option in bazel_cache_options(home):
            self.assertIn(option, options)

    def test_storage_inside_source_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "outside"):
            bazel_output_base(self.project, self.project / "cache")

    def test_stale_dirty_source_kept_but_outputs_removed_and_shared_cache_kept(self):
        base = self.prepare_outputs()
        source = self.project / "RiemannResearch/Test/A.lean"
        source.write_text("-- unpublished edit\n")
        self.expire()
        result = self.manager.cleanup(retention_days=7, dry_run=False)
        self.assertFalse(base.exists())
        self.assertEqual(source.read_text(), "-- unpublished edit\n")
        self.assertTrue(result["preserved_unpublished"])
        self.assertEqual(len(result["bazel_outputs_removed"]), 1)
        for name in ("disk", "repository", "repo-contents"):
            self.assertEqual((self.manager.bazel_storage / name / "keep").read_text(), "shared")

    def test_busy_bazel_preserves_source_and_outputs(self):
        base = self.prepare_outputs()
        self.expire()
        with patch.dict(os.environ, {"BAZEL_TEST_BUSY": "1"}):
            result = self.manager.cleanup(retention_days=7, dry_run=False)
        self.assertTrue(self.project.is_dir())
        self.assertTrue(base.is_dir())
        self.assertFalse(result["archived_or_eligible"])
        self.assertIn("client lock", result["preserved_unpublished"][0]["reason"])

    def test_dry_run_and_active_editor_do_not_remove_outputs(self):
        base = self.prepare_outputs()
        self.expire()
        self.manager.cleanup(retention_days=7, dry_run=True)
        self.assertFalse(self.log.exists())
        self.assertTrue(base.is_dir())
        self.manager.can_archive = lambda project: False
        self.manager.cleanup(retention_days=7, dry_run=False)
        self.assertFalse(self.log.exists())
        self.assertTrue(base.is_dir())

    def test_output_parent_symlink_is_not_followed_for_cleanup(self):
        outside = self.root / "outside"
        outside.mkdir()
        outputs = self.manager.bazel_storage / "outputs"
        outputs.parent.mkdir(parents=True, exist_ok=True)
        outputs.symlink_to(outside, target_is_directory=True)
        result = self.manager._cleanup_bazel_outputs(self.project)
        self.assertFalse(result["removed"])
        self.assertIn("symlink", result["reason"])
        self.assertTrue(outside.is_dir())

    def test_integration_output_base_is_cleaned_after_publication(self):
        (self.source / "README.md").write_text("New upstream documentation\n")
        git(self.source, "add", "README.md")
        git(self.source, "commit", "-m", "Upstream update")
        git(self.source, "push", str(self.remote), "HEAD:main")
        (self.project / "RiemannResearch/Test/A.lean").write_text("theorem sample : True := by exact True.intro\n")
        result = self.terminal(self.manager.submit_checkpoint(self.token, "Update sample proof"))
        self.assertEqual(result["state"], "succeeded", result)
        self.assertTrue(result["result"]["integrated_with_newer_main"])
        cleanup = result["result"]["build"]["integration_output_cleanup"]
        self.assertTrue(cleanup["removed"])
        self.assertFalse(Path(cleanup["output_base"]).exists())
        self.assertEqual(list((self.manager.root / "_integration").iterdir()), [])
        self.assertTrue(bazel_output_base(self.project, self.manager.bazel_storage).is_dir())

    def test_failed_integration_does_not_leave_an_output_base(self):
        (self.source / "RiemannResearch/Test/A.lean").write_text("-- FAIL_TEST\n")
        git(self.source, "add", ".")
        git(self.source, "commit", "-m", "Upstream failing fixture")
        git(self.source, "push", str(self.remote), "HEAD:main")
        before = git(self.remote, "rev-parse", "main")
        aggregate = self.project / "RiemannResearch.lean"
        aggregate.write_text(aggregate.read_text() + "-- Independent workspace change\n")
        result = self.terminal(self.manager.submit_checkpoint(self.token, "Update aggregate comment"))
        self.assertEqual(result["state"], "failed", result)
        self.assertEqual(git(self.remote, "rev-parse", "main"), before)
        self.assertEqual(list((self.manager.root / "_integration").iterdir()), [])
        bases = list((self.manager.bazel_storage / "outputs").iterdir())
        self.assertEqual(bases, [bazel_output_base(self.project, self.manager.bazel_storage)])

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
