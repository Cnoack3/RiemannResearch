"""Offline integration checks for native Lake cache routing and disk cleanup."""

import json
import os
import select
import subprocess
import sys
import tempfile
import threading
import unittest
from pathlib import Path
from unittest.mock import patch

import agent_workspaces as workspaces


FAKE_LAKE = r'''
import json
import os
import sys
from pathlib import Path

args = sys.argv[1:]
state = Path(os.environ["CACHE_TEST_STATE"])
with (state / "commands.jsonl").open("a") as log:
    log.write(json.dumps({"args": args, "lease": os.environ.get("LEAN_NATIVE_CACHE_LOCK_HELD")}) + "\n")
mode = os.environ.get("CACHE_TEST_MODE", "")
if args[:2] == ["cache", "get"]:
    if mode == "auth":
        print("HTTP 403: denied")
        sys.exit(22)
    (state / "ready").touch()
elif args[:2] == ["cache", "put"]:
    if mode == "upload":
        print("HTTP 403: upload denied")
        sys.exit(22)
else:
    assert "build" in args or "lean" in args, args
    if mode == "compiler":
        print("error: unsolved goals")
        sys.exit(1)
    if "--no-build" in args and not (state / "ready").exists():
        print("imports are not available locally")
        sys.exit(3)
    build = Path.cwd() / ".lake" / "build" / "lib" / "lean"
    build.mkdir(parents=True, exist_ok=True)
    (build / "Sample.olean").write_text("restored output")
    if "-o" in args:
        Path(args[args.index("-o") + 1]).write_text("{}\n")
    print("fake checked successfully")
'''


class NativeCacheTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.cache = self.root / "cache"
        self.state = self.root / "fake-state"
        self.state.mkdir()
        self.project = self.root / "project"
        self.project.mkdir()
        (self.project / "Draft.lean").write_text("theorem draft : True := by trivial\n")
        self.fake_bin = self.root / "bin"
        self.fake_bin.mkdir()
        lake = self.fake_bin / "lake"
        lake.write_text("#!" + sys.executable + "\n" + FAKE_LAKE)
        lake.chmod(0o755)
        environment = patch.dict(os.environ, {
            "LEAN_VERIFICATION_BACKEND": "lake",
            "LAKE_CACHE_DIR": str(self.cache),
            "LEAN_REMOTE_CACHE_SERVICE": "gcs",
            "CACHE_TEST_STATE": str(self.state),
            "CACHE_TEST_MODE": "",
            "PATH": str(self.fake_bin) + os.pathsep + os.environ["PATH"],
        })
        environment.start()
        self.addCleanup(environment.stop)
        self.manager = self.manager_instance()

    @staticmethod
    def manager_instance():
        # Exercise real cache methods without starting unrelated queue workers.
        manager = workspaces.AgentWorkspaceManager.__new__(workspaces.AgentWorkspaceManager)
        manager.default_verification_backend = "lake"
        manager._cache_local = threading.local()
        manager._outputs_guard = threading.RLock()
        manager._job_local = threading.local()
        manager.lake_build_threads = manager.lean_num_threads = 2
        manager.can_archive = lambda project: True
        manager._record_metric = lambda *args, **kwargs: None
        manager._set_job_progress = lambda *args, **kwargs: None
        return manager

    def commands(self):
        path = self.state / "commands.jsonl"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def build(self):
        return self.manager._run_streaming(
            ["lake", "build", "RiemannResearch", "--quiet"],
            cwd=self.project, timeout=10, phase="building",
        )

    def seed_local(self):
        (self.state / "ready").touch()
        build = self.project / ".lake" / "build"
        build.mkdir(parents=True)
        (build / "existing.olean").write_text("existing output")
        return build

    def test_local_hit_skips_remote_get_and_sets_marker_only_in_children(self):
        self.seed_local()
        os.environ["LEAN_NATIVE_CACHE_LOCK_HELD"] = "untrusted inherited marker"
        self.assertEqual(self.build(), "fake checked successfully")
        commands = self.commands()
        self.assertIn("--no-build", commands[0]["args"])
        self.assertEqual(commands[1]["args"][:2], ["cache", "put"])
        self.assertEqual(len(commands), 2)
        self.assertTrue(all(command["lease"] == "1" for command in commands))
        self.assertEqual(os.environ["LEAN_NATIVE_CACHE_LOCK_HELD"], "untrusted inherited marker")
        self.assertNotIn("LEAN_NATIVE_CACHE_LOCK_HELD", self.manager._child_env(2))
        self.assertFalse((self.project / ".lake" / "build").exists())

    def test_only_exit_three_falls_back_to_remote_restoration(self):
        self.build()
        commands = [command["args"] for command in self.commands()]
        self.assertIn("--no-build", commands[0])
        self.assertEqual(commands[1][:3], ["cache", "get", "--mappings-only"])
        self.assertEqual(commands[2][0], "build")
        self.assertNotIn("--no-build", commands[2])
        self.assertEqual(commands[3][:2], ["cache", "put"])
        self.assertFalse((self.project / ".lake" / "build").exists())

    def test_compiler_and_auth_errors_do_not_continue_or_upload(self):
        for mode, expected_code, expected_commands in (("compiler", 1, 1), ("auth", 22, 2)):
            with self.subTest(mode=mode), patch.dict(os.environ, {
            "LEAN_VERIFICATION_BACKEND": "lake","CACHE_TEST_MODE": mode}):
                (self.state / "commands.jsonl").unlink(missing_ok=True)
                with self.assertRaises(workspaces.LakeCommandError) as error:
                    self.build()
                self.assertEqual(error.exception.returncode, expected_code)
                self.assertEqual(len(self.commands()), expected_commands)
                self.assertFalse(any(command["args"][:2] == ["cache", "put"] for command in self.commands()))

    def test_failed_upload_and_active_lsp_preserve_build_outputs(self):
        build = self.seed_local()
        with patch.dict(os.environ, {
            "LEAN_VERIFICATION_BACKEND": "lake","CACHE_TEST_MODE": "upload"}):
            with self.assertRaises(workspaces.LakeCommandError):
                self.build()
        self.assertTrue(build.exists())
        self.manager.can_archive = lambda project: False
        self.build()
        self.assertTrue(build.exists())

    def test_cleanup_preserves_sources_packages_records_and_cache_hardlinks(self):
        source = (self.project / "Draft.lean").read_bytes()
        (self.project / ".git").mkdir()
        (self.project / ".git" / "unpublished").write_text("unpublished history")
        records = self.root / "records"
        records.mkdir()
        (records / "verified.json").write_text('{"verified":true}')
        dependencies = self.root / "dependencies"
        dependencies.mkdir()
        (dependencies / "Mathlib.olean").write_text("shared Mathlib")
        build = self.seed_local()
        (self.project / ".lake" / "packages").symlink_to(dependencies, target_is_directory=True)
        artifact = self.cache / "artifacts" / "module.art"
        artifact.parent.mkdir(parents=True)
        artifact.write_text("remote-backed output")
        os.link(artifact, build / "linked.olean")
        self.manager._cleanup_workspace_outputs(self.project)
        self.assertFalse(build.exists())
        self.assertEqual(artifact.read_text(), "remote-backed output")
        self.assertEqual((self.project / "Draft.lean").read_bytes(), source)
        self.assertTrue((self.project / ".git" / "unpublished").exists())
        self.assertTrue((dependencies / "Mathlib.olean").exists())
        self.assertTrue((records / "verified.json").exists())
        build.symlink_to(dependencies, target_is_directory=True)
        self.manager._cleanup_workspace_outputs(self.project)
        self.assertTrue(build.is_symlink())
        self.assertTrue((dependencies / "Mathlib.olean").exists())

    def test_cache_limit_evicts_oldest_and_preserves_external_symlink(self):
        self.assertEqual(workspaces.NATIVE_CACHE_MAX_BYTES, 100 * 1024**3)
        artifacts = self.cache / "artifacts"
        artifacts.mkdir(parents=True)
        old, fresh = artifacts / "old.art", artifacts / "fresh.art"
        old.write_bytes(b"old-data")
        fresh.write_bytes(b"new-data")
        os.utime(old, ns=(1, 1))
        os.utime(fresh, ns=(2, 2))
        external = self.root / "external"
        external.write_bytes(b"keep this external file")
        (artifacts / "external.art").symlink_to(external)
        with patch.object(workspaces, "NATIVE_CACHE_MAX_BYTES", 8):
            self.manager._prune_native_cache()
        self.assertFalse(old.exists())
        self.assertTrue(fresh.exists())
        self.assertTrue(external.exists())

    def test_nested_lease_serializes_other_manager_and_pruning(self):
        artifact = self.cache / "artifacts" / "old.art"
        artifact.parent.mkdir(parents=True)
        artifact.write_bytes(b"held output")
        entered, release, pruned = threading.Event(), threading.Event(), threading.Event()
        errors = []

        def hold():
            try:
                with self.manager._native_cache_lock(), self.manager._native_cache_lock():
                    self.assertEqual(self.manager._child_env(2)["LEAN_NATIVE_CACHE_LOCK_HELD"], "1")
                    entered.set()
                    self.assertTrue(release.wait(3))
            except BaseException as error:
                errors.append(error)

        other = self.manager_instance()
        holder = threading.Thread(target=hold, daemon=True)
        holder.start()
        self.assertTrue(entered.wait(2), "nested native-cache lease deadlocked")
        with patch.object(workspaces, "NATIVE_CACHE_MAX_BYTES", 1):
            waiter = threading.Thread(target=lambda: (other._prune_native_cache(), pruned.set()), daemon=True)
            waiter.start()
            try:
                self.assertFalse(pruned.wait(0.15), "pruning crossed another manager's lease")
                self.assertTrue(artifact.exists())
            finally:
                release.set()
            holder.join(2)
            waiter.join(2)
        self.assertTrue(pruned.is_set())
        self.assertFalse(artifact.exists())
        self.assertEqual(errors, [])

    def test_native_lease_also_serializes_another_process(self):
        child_code = (
            "import threading,sys; from agent_workspaces import AgentWorkspaceManager; "
            "manager=AgentWorkspaceManager.__new__(AgentWorkspaceManager); "
            "manager._cache_local=threading.local(); "
            "lease=manager._native_cache_lock(); lease.__enter__(); "
            "print('entered',flush=True); sys.stdin.readline(); lease.__exit__(None,None,None)"
        )
        child = None
        try:
            with self.manager._native_cache_lock():
                child = subprocess.Popen(
                    [sys.executable, "-u", "-c", child_code],
                    cwd=Path(__file__).parent, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE, text=True,
                )
                readable, _, _ = select.select([child.stdout], [], [], 0.15)
                self.assertEqual(readable, [], "another process bypassed the native cache lease")
            readable, _, _ = select.select([child.stdout], [], [], 2)
            self.assertTrue(readable, "other process never acquired released lease")
            self.assertEqual(child.stdout.readline().strip(), "entered")
            _, stderr = child.communicate("release\n", timeout=2)
            self.assertEqual(child.returncode, 0, stderr)
        finally:
            if child is not None and child.poll() is None:
                child.kill()
                child.communicate()

    def test_verification_restores_imports_after_workspace_output_eviction(self):
        build = self.seed_local()
        self.manager._cleanup_workspace_outputs(self.project)
        (self.state / "ready").unlink()
        source = (self.project / "Draft.lean").read_bytes()
        result = self.manager._run_verification(self.project, self.project / "Draft.lean", 10)
        self.assertTrue(result["verified"], result)
        commands = [command["args"] for command in self.commands()]
        self.assertIn("--no-build", commands[0])
        self.assertIn("lean", commands[0])
        self.assertEqual(commands[1][:3], ["cache", "get", "--mappings-only"])
        self.assertEqual(commands[2][0], "lean")
        self.assertNotIn("--no-build", commands[2])
        self.assertEqual((self.project / "Draft.lean").read_bytes(), source)
        self.assertFalse(build.exists())


if __name__ == "__main__":
    unittest.main()

