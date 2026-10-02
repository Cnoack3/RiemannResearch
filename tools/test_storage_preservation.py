"""Storage-policy regression tests; no Lean or remote GitHub execution."""

from __future__ import annotations

import json
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import threading
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from agent_workspaces import (
    AgentWorkspaceManager, GIB, StorageAdmissionError, WorkspaceContinuationRequired,
)


def git(arguments, cwd):
    return subprocess.run(
        ["git", *arguments], cwd=cwd, check=True, capture_output=True, text=True
    ).stdout.strip()


def filesystem(available=100 * GIB, inodes=1_000_000, total_inodes=2_000_000):
    return SimpleNamespace(
        f_bavail=available // 4096, f_frsize=4096,
        f_files=total_inodes, f_favail=inodes,
    )


class GitOnlyManager(AgentWorkspaceManager):
    """Real tiny local Git repositories, without Lake or dependency downloads."""

    def _attach_dependencies(self, project):
        return "test-dependency-key"

    def _dependency_key(self, project):
        return "test-dependency-key"


class StoragePreservationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        self.source.mkdir()
        git(["init", "-b", "main"], self.source)
        git(["config", "user.name", "Storage Test"], self.source)
        git(["config", "user.email", "storage@example.invalid"], self.source)
        (self.source / "RiemannResearch" / "Test").mkdir(parents=True)
        (self.source / "RiemannResearch" / "Test" / "Base.lean").write_text(
            "theorem storage_base : True := by trivial\n"
        )
        (self.source / "RiemannResearch.lean").write_text("import RiemannResearch.Test.Base\n")
        (self.source / "README.md").write_text("# Test\n")
        (self.source / "AGENTS.md").write_text("# Test\n")
        (self.source / ".gitignore").write_text("/.lake\n/ignored-proof.lean\n")
        (self.source / "lean-toolchain").write_text("leanprover/lean4:v4.33.0-rc2\n")
        (self.source / "lakefile.toml").write_text('name = "RiemannResearch"\n')
        (self.source / "lake-manifest.json").write_text('{"packages": []}\n')
        git(["add", "."], self.source)
        git(["commit", "-m", "Test source"], self.source)
        self.remote = self.root / "remote.git"
        git(["clone", "--bare", str(self.source), str(self.remote)], self.root)
        self.environment = patch.dict(os.environ, {
            "LEAN_AGENT_WORKSPACES_ROOT": str(self.root / "workspaces"),
            "LEAN_AGENT_WORKSPACES_STATE": str(self.root / "state"),
            "LEAN_SHARED_DEPS_ROOT": str(self.root / "dependencies"),
            "LEAN_SHARED_PROJECT_BUILDS_ROOT": str(self.root / "project-cache"),
            "LEAN_NUM_THREADS": "8", "LEAN_LAKE_BUILD_THREADS": "8",
            "LEAN_JOB_WORKERS": "1",
        })
        self.environment.start()
        for name in (
            "LEAN_STORAGE_POLICY", "LEAN_STORAGE_RESERVE_BYTES",
            "LEAN_NEW_CLONE_BUDGET_BYTES", "LEAN_NEW_DEPS_BUDGET_BYTES",
            "LEAN_BUILD_GROWTH_BUDGET_BYTES",
        ):
            os.environ.pop(name, None)
        self.no_worker = patch("threading.Thread.start")
        self.no_worker.start()
        self.manager = GitOnlyManager(self.source, str(self.remote))
        self.space = patch("os.statvfs", return_value=filesystem())
        self.space.start()

    def tearDown(self):
        self.space.stop()
        self.manager._owner_lease.close()
        self.no_worker.stop()
        self.environment.stop()
        self.temporary.cleanup()

    def opened(self):
        result = self.manager.open()
        return result["workspace_token"], Path(result["project_root"])

    def sentinel(self, project):
        ignored = project / "ignored-proof.lean"
        ignored.write_bytes(b"unpublished ignored proof\x00\xff")
        build = project / ".lake" / "build" / "lib" / "lean" / "Keep.olean"
        build.parent.mkdir(parents=True, exist_ok=True)
        build.write_bytes(b"complete build bytes\x00\xfe")
        return {ignored: ignored.read_bytes(), build: build.read_bytes()}

    def assert_retained(self, files):
        for path, content in files.items():
            self.assertEqual(path.read_bytes(), content)

    def actual_dependency_key(self, project):
        return self.manager._dependency_key(project)

    def ready_dependencies(self, project):
        key = self.actual_dependency_key(project)
        directory = self.manager.shared / key
        packages = directory / "packages"
        packages.mkdir(parents=True)
        (packages / "sentinel.olean").write_bytes(b"shared dependency build")
        (directory / "READY.json").write_text('{"binary_cache_complete": true}\n')
        (project / ".lake").mkdir(exist_ok=True)
        return key, packages

    def test_default_policy_and_configuration_fail_closed(self):
        self.assertEqual(self.manager.storage_policy, "preserve")
        self.assertEqual(self.manager.storage_reserve_bytes, 10 * GIB)
        with patch.dict(os.environ, {"LEAN_STORAGE_POLICY": "preserv"}):
            with self.assertRaisesRegex(ValueError, "preserve or retention"):
                GitOnlyManager(self.source, str(self.remote))
        with patch.dict(os.environ, {"LEAN_STORAGE_RESERVE_BYTES": "0"}):
            with self.assertRaisesRegex(ValueError, "LEAN_STORAGE_RESERVE_BYTES"):
                GitOnlyManager(self.source, str(self.remote))

    def test_cleanup_preserves_clean_old_ignored_build_and_metadata(self):
        token, project = self.opened()
        files = self.sentinel(project)
        meta = self.manager._read_meta(token)
        meta["last_activity"] = time.time() - 30 * 86400
        self.manager._write_meta(meta)
        before = self.manager._meta_path(token).read_bytes()
        result = self.manager.cleanup(retention_days=14, dry_run=False)
        self.assertTrue(result["dry_run"])
        self.assertFalse(result["requested_dry_run"])
        self.assertEqual(len(result["archived_or_eligible"]), 1)
        self.assertEqual(self.manager._meta_path(token).read_bytes(), before)
        self.assert_retained(files)

    def test_open_never_invokes_automatic_cleanup_or_build_copy(self):
        with patch.object(self.manager, "cleanup", side_effect=AssertionError("cleanup")), \
             patch.object(self.manager, "_copy_build_tree", side_effect=AssertionError("copy")):
            result = self.manager.open()
        self.assertFalse(result["project_cache"]["restored"])

    def test_snapshot_restore_publish_and_prune_preserve_existing_content(self):
        token, project = self.opened()
        files = self.sentinel(project)
        commit = git(["rev-parse", "HEAD"], project)
        cache = self.manager._project_cache_dir("test-dependency-key", commit)
        (cache / "build").mkdir(parents=True)
        cached = cache / "build" / "Other.olean"
        cached.write_bytes(b"older cached proof build")
        (cache / "READY.json").write_text('{"created_at": 1}\n')
        with patch.object(self.manager, "_copy_build_tree", side_effect=AssertionError("copy")):
            self.assertFalse(self.manager._restore_project_cache(project, "test-dependency-key")["restored"])
            self.assertFalse(self.manager._publish_project_cache(project)["published"])
            self.manager._prune_project_cache("test-dependency-key")
        self.assertEqual(cached.read_bytes(), b"older cached proof build")
        self.assert_retained(files)

    def test_rehydration_and_reset_do_not_discard_existing_files(self):
        token, project = self.opened()
        files = self.sentinel(project)
        meta = self.manager._read_meta(token)
        before = self.manager._meta_path(token).read_bytes()
        with self.assertRaisesRegex(RuntimeError, "replace an existing workspace"):
            self.manager._rehydrate(meta)
        with self.assertRaisesRegex(RuntimeError, "destructive workspace reset"):
            self.manager.reset(token, "any-confirmation-token")
        self.assertEqual(self.manager._meta_path(token).read_bytes(), before)
        self.assert_retained(files)

    def test_stale_workspace_can_be_resumed_and_read_without_replacement(self):
        token, project = self.opened()
        files = self.sentinel(project)
        meta = self.manager._read_meta(token)
        meta.update(state="published", needs_rehydrate=True)
        self.manager._write_meta(meta)
        result = self.manager.open(token)
        self.assertTrue(result["needs_source_sync"])
        self.assertEqual(self.manager.read_file(token, "README.md")["content"], "# Test\n")
        self.assertEqual(self.manager._verification_project(token), project)
        self.assertEqual(self.manager._get(token)[1], project)
        self.assert_retained(files)

    def test_partial_clone_admission_error_returns_token_and_resumes_same_content(self):
        attach = AgentWorkspaceManager._attach_dependencies.__get__(self.manager)
        with patch.object(self.manager, "_attach_dependencies", new=attach), \
             patch("os.statvfs", return_value=filesystem(available=12 * GIB)):
            with self.assertRaises(StorageAdmissionError) as failure:
                self.manager.open()
        details = failure.exception.details
        self.assertEqual(details["operation"], "new dependency environment")
        self.assertEqual(details["required_bytes"], 42 * GIB)
        token, project = details["workspace_token"], Path(details["project_root"])
        self.assertEqual(self.manager._read_meta(token)["state"], "provisioning")
        head = git(["rev-parse", "HEAD"], project)
        retained = self.sentinel(project)
        self.ready_dependencies(project)
        with patch.object(self.manager, "_attach_dependencies", new=attach), \
             patch.object(self.manager, "_clone", side_effect=AssertionError("Do not clone again")):
            result = self.manager.open(token)
        self.assertEqual(result["state"], "active")
        self.assertEqual(result["base_commit"], head)
        self.assertEqual(result["project_root"], str(project))
        self.assert_retained(retained)

    def test_global_storage_lease_serializes_managers_and_rechecks_remaining_capacity(self):
        _, project = self.opened()
        second = GitOnlyManager(self.source, str(self.remote))
        entered, release = threading.Event(), threading.Event()
        available = [18 * GIB]
        errors = []
        commands = []

        def compile_command(*args, **kwargs):
            commands.append(args[0])
            entered.set()
            if not release.wait(5):
                raise AssertionError("test did not release build")
            available[0] = 10 * GIB
            return "built"

        def invoke(callback):
            try:
                callback()
            except Exception as exc:
                errors.append(exc)

        first_thread = threading.Thread(target=invoke, args=(lambda: self.manager._run_lake_build(project, ["lake", "build"]),))
        second_thread = threading.Thread(target=invoke, args=(lambda: second._run_lake_build(project, ["lake", "build"]),))
        clone_path = self.root / "blocked-clone" / "project"
        clone_thread = threading.Thread(target=invoke, args=(lambda: second._clone(clone_path),))
        self.no_worker.stop()
        try:
            with patch("os.statvfs", side_effect=lambda _: filesystem(available=available[0])), \
                 patch.object(self.manager, "_dependency_cache_preflight", return_value=("key", {"status": "complete"})), \
                 patch.object(second, "_dependency_cache_preflight", return_value=("key", {"status": "complete"})), \
                 patch.object(self.manager, "_run_streaming", side_effect=compile_command), \
                 patch.object(second, "_run_streaming", side_effect=AssertionError("second build must not run")), \
                 patch.object(second, "_run", side_effect=AssertionError("clone must not run")):
                first_thread.start()
                self.assertTrue(entered.wait(5))
                second_thread.start()
                clone_thread.start()
                # Their leases must remain blocked while the first operation owns its budget.
                second_thread.join(0.1)
                clone_thread.join(0.1)
                self.assertTrue(second_thread.is_alive())
                self.assertTrue(clone_thread.is_alive())
                self.assertEqual(commands, [["lake", "build"]])
                release.set()
                for thread in (first_thread, second_thread, clone_thread):
                    thread.join(5)
                    self.assertFalse(thread.is_alive())
            self.assertEqual(len(errors), 2)
            self.assertTrue(all(isinstance(error, StorageAdmissionError) for error in errors))
            self.assertFalse(clone_path.parent.exists())
        finally:
            release.set()
            self.no_worker.start()
            second._owner_lease.close()

    def test_cleanup_does_not_hold_registry_while_waiting_for_workspace(self):
        token, _ = self.opened()
        meta = self.manager._read_meta(token)
        meta["last_activity"] = time.time() - 30 * 86400
        self.manager._write_meta(meta)
        second = GitOnlyManager(self.source, str(self.remote))
        held, cleanup_waiting = threading.Event(), threading.Event()
        errors = []
        real_operation_lock = second._operation_lock

        def cleanup_operation(token):
            cleanup_waiting.set()
            return real_operation_lock(token)

        def register_while_holding_workspace():
            try:
                with self.manager._operation_lock(token):
                    held.set()
                    if not cleanup_waiting.wait(5):
                        raise AssertionError("cleanup did not attempt workspace lease")
                    with self.manager._storage_operation_lock():
                        self.manager._register_workspace()
            except Exception as exc:
                errors.append(exc)

        def clean():
            try:
                if not held.wait(5):
                    raise AssertionError("workspace lease was not acquired")
                second.cleanup(dry_run=True)
            except Exception as exc:
                errors.append(exc)

        parent = threading.Thread(target=register_while_holding_workspace, daemon=True)
        cleanup = threading.Thread(target=clean, daemon=True)
        self.no_worker.stop()
        try:
            with patch.object(second, "_operation_lock", side_effect=cleanup_operation):
                parent.start()
                cleanup.start()
                parent.join(5)
                cleanup.join(5)
                self.assertFalse(parent.is_alive(), "registration deadlocked with cleanup")
                self.assertFalse(cleanup.is_alive(), "cleanup deadlocked with registration")
            self.assertEqual(errors, [])
        finally:
            self.no_worker.start()
            second._owner_lease.close()

    def test_parent_handoff_does_not_wait_for_child_operation_under_storage_lease(self):
        token, project = self.opened()
        continuation = self.manager._register_workspace()
        self.manager._provision_workspace(continuation)
        continuation.update(state="continuation_validation")
        self.manager._write_meta(continuation)
        meta = self.manager._read_meta(token)
        meta.update(
            state="published", needs_rehydrate=True,
            published_commit=git(["rev-parse", "HEAD"], project),
            continuation_workspace_token=continuation["token"],
            continuation_project_root=continuation["path"],
        )
        self.manager._write_meta(meta)
        second = GitOnlyManager(self.source, str(self.remote))
        held, release = threading.Event(), threading.Event()
        errors = []

        def child():
            with second._operation_lock(continuation["token"]):
                held.set()
                release.wait(5)
                with second._storage_operation_lock():
                    pass

        def parent():
            try:
                self.manager.checkpoint(token, "Resume pending continuation", push=True)
            except Exception as exc:
                errors.append(exc)

        child_thread = threading.Thread(target=child, daemon=True)
        parent_thread = threading.Thread(target=parent, daemon=True)
        self.no_worker.stop()
        try:
            child_thread.start()
            self.assertTrue(held.wait(5))
            parent_thread.start()
            parent_thread.join(2)
            self.assertFalse(parent_thread.is_alive(), "parent waited for child while holding storage")
            self.assertEqual(len(errors), 1)
            self.assertIsInstance(errors[0], WorkspaceContinuationRequired)
            self.assertEqual(errors[0].details["continuation_workspace_token"], continuation["token"])
            release.set()
            child_thread.join(5)
            self.assertFalse(child_thread.is_alive())
        finally:
            release.set()
            self.no_worker.start()
            second._owner_lease.close()

    def test_successful_cache_preflight_persists_complete_marker_for_next_budget(self):
        _, project = self.opened()
        key, packages = self.ready_dependencies(project)
        ready = self.manager.shared / key / "READY.json"
        ready.write_text('{"binary_cache_complete": false, "key": "retained-key"}\n')
        with patch.object(self.manager, "_run_streaming", return_value="cache ready"):
            self.assertEqual(self.manager._dependency_cache_preflight(project)[1]["status"], "complete")
            marker = json.loads(ready.read_text())
            self.assertTrue(marker["binary_cache_complete"])
            self.assertEqual(marker["key"], "retained-key")
            with patch("os.statvfs", return_value=filesystem(available=18 * GIB)):
                self.manager._dependency_cache_preflight(project)
        self.assertEqual((packages / "sentinel.olean").read_bytes(), b"shared dependency build")

    def test_sync_and_dependency_refresh_preserve_metadata_before_refusal(self):
        token, project = self.opened()
        files = self.sentinel(project)
        before = self.manager._meta_path(token).read_bytes()
        with self.assertRaisesRegex(RuntimeError, "replacement-based synchronization"):
            self.manager.sync(token)
        with self.assertRaisesRegex(RuntimeError, "current dependency environment"):
            self.manager.update_dependencies(token)
        self.assertEqual(self.manager._meta_path(token).read_bytes(), before)
        self.assert_retained(files)

    def test_correct_shared_dependency_link_is_reused_without_mutation(self):
        _, project = self.opened()
        key, packages = self.ready_dependencies(project)
        link = project / ".lake" / "packages"
        link.symlink_to(packages, target_is_directory=True)
        before = os.readlink(link)
        with patch.object(self.manager, "_run", side_effect=AssertionError("Lake must not run")):
            actual = AgentWorkspaceManager._attach_dependencies(self.manager, project)
        self.assertEqual(actual, key)
        self.assertEqual(os.readlink(link), before)
        self.assertEqual((packages / "sentinel.olean").read_bytes(), b"shared dependency build")

    def test_existing_private_dependencies_are_protected_even_if_git_ignored(self):
        _, project = self.opened()
        packages = project / ".lake" / "packages"
        packages.mkdir(parents=True)
        sentinel = packages / "Unpublished.lean"
        sentinel.write_bytes(b"unpublished private dependency proof")
        with patch.object(self.manager, "_run", side_effect=AssertionError("Lake must not run")):
            with self.assertRaisesRegex(RuntimeError, "existing dependency files"):
                AgentWorkspaceManager._attach_dependencies(self.manager, project)
        self.assertEqual(sentinel.read_bytes(), b"unpublished private dependency proof")

    def test_mismatched_and_dangling_dependency_links_are_retained(self):
        for name, target_exists in (("wrong", True), ("dangling", False)):
            with self.subTest(link=name):
                _, project = self.opened()
                target = self.root / name
                if target_exists:
                    target.mkdir()
                    (target / "Proof.lean").write_bytes(b"other dependency proof")
                (project / ".lake").mkdir()
                link = project / ".lake" / "packages"
                link.symlink_to(target, target_is_directory=True)
                before = os.readlink(link)
                with self.assertRaisesRegex(RuntimeError, "existing dependency files"):
                    AgentWorkspaceManager._attach_dependencies(self.manager, project)
                self.assertEqual(os.readlink(link), before)
                if target_exists:
                    self.assertEqual((target / "Proof.lean").read_bytes(), b"other dependency proof")

    def test_incomplete_dependency_environment_is_retained(self):
        _, project = self.opened()
        key = self.actual_dependency_key(project)
        environment = self.manager.shared / key
        environment.mkdir()
        partial = environment / "Partial.olean"
        partial.write_bytes(b"retained partial environment")
        with self.assertRaisesRegex(RuntimeError, "incomplete dependency environment"):
            AgentWorkspaceManager._attach_dependencies(self.manager, project)
        self.assertEqual(partial.read_bytes(), b"retained partial environment")

    def test_low_space_open_denies_before_registry_or_clone(self):
        with patch("os.statvfs", return_value=filesystem(available=710 * 1024 ** 2)), \
             patch.object(self.manager, "_clone", side_effect=AssertionError("clone")):
            with self.assertRaises(StorageAdmissionError) as failure:
                self.manager.open()
        self.assertEqual(failure.exception.details["operation"], "new workspace clone")
        self.assertEqual(list(self.manager.state.glob("ws_*.json")), [])
        self.assertEqual(list(self.manager.root.iterdir()), [])

    def test_low_space_direct_clone_denies_before_git_and_directory_creation(self):
        destination = self.root / "new-parent" / "project"
        with patch("os.statvfs", return_value=filesystem(available=0)), \
             patch.object(self.manager, "_run", side_effect=AssertionError("Git must not run")):
            with self.assertRaises(StorageAdmissionError):
                self.manager._clone(destination)
        self.assertFalse(destination.parent.exists())

    def test_low_space_dependency_provision_denies_before_lake(self):
        _, project = self.opened()
        with patch("os.statvfs", return_value=filesystem(available=GIB)), \
             patch.object(self.manager, "_run", side_effect=AssertionError("Lake must not run")):
            with self.assertRaises(StorageAdmissionError):
                AgentWorkspaceManager._attach_dependencies(self.manager, project)
        self.assertFalse((project / ".lake" / "packages").exists())

    def test_low_space_cache_preflight_cannot_turn_into_fallback_build(self):
        _, project = self.opened()
        with patch("os.statvfs", return_value=filesystem(available=GIB)), \
             patch.object(self.manager, "_run_streaming", side_effect=AssertionError("no execution")):
            with self.assertRaises(StorageAdmissionError):
                self.manager._dependency_cache_preflight(project)
            with self.assertRaises(StorageAdmissionError):
                self.manager._run_lake_build(project, ["lake", "build", "RiemannResearch", "--quiet"])

    def test_space_is_rechecked_after_cache_download_before_compilation(self):
        _, project = self.opened()
        for status in ("complete", "incomplete"):
            with self.subTest(cache=status):
                with patch("os.statvfs", side_effect=[filesystem(), filesystem(available=GIB)]), \
                     patch.object(self.manager, "_dependency_cache_preflight", return_value=("key", {"status": status})), \
                     patch.object(self.manager, "_run_streaming", side_effect=AssertionError("build must not run")):
                    with self.assertRaises(StorageAdmissionError) as failure:
                        self.manager._run_lake_build(project, ["lake", "build", "RiemannResearch", "--quiet"])
                self.assertEqual(failure.exception.details["operation"], "Lean build after cache preparation")

    def test_storage_guard_checks_inodes_and_mounts_but_handles_unknown_inode_accounting(self):
        with patch("os.statvfs", return_value=filesystem(inodes=1)):
            with self.assertRaises(StorageAdmissionError):
                self.manager._require_storage_space("test", self.root)
        with patch("os.statvfs", return_value=filesystem(inodes=0, total_inodes=0)):
            self.manager._require_storage_space("test", self.root)
        shared_memory = Path("/dev/shm")
        if shared_memory.is_dir() and shared_memory.stat().st_dev != self.root.stat().st_dev:
            with patch("os.statvfs", side_effect=[filesystem(), filesystem(available=0)]):
                with self.assertRaises(StorageAdmissionError) as failure:
                    self.manager._require_storage_space("two mounts", self.root, shared_memory)
            self.assertEqual(failure.exception.details["path"], str(shared_memory))

    def test_inspection_error_fails_closed_with_bounded_error(self):
        with patch("os.statvfs", side_effect=OSError("cannot inspect")):
            with self.assertRaises(StorageAdmissionError) as failure:
                self.manager._require_storage_space("test", self.root)
        self.assertLess(len(str(failure.exception)), 1000)

    def test_build_copy_never_changes_existing_destination_in_preserve_mode(self):
        source, destination = self.root / "copy-source", self.root / "copy-destination"
        source.mkdir()
        destination.mkdir()
        sentinel = destination / "Keep.olean"
        sentinel.write_bytes(b"original destination")
        with patch("subprocess.run", side_effect=AssertionError("copy must not run")):
            with self.assertRaisesRegex(RuntimeError, "disables full build-tree copying"):
                self.manager._copy_build_tree(source, destination)
        self.assertEqual(sentinel.read_bytes(), b"original destination")

    def test_failed_copy_has_no_second_copy_and_retains_partial_staging(self):
        self.manager.storage_policy = "retention"
        source, destination = self.root / "copy-source", self.root / "copy-destination"
        source.mkdir()
        (source / "Proof.olean").write_bytes(b"source proof build")

        def failed_copy(*args, **kwargs):
            (destination / "partial.olean").write_bytes(b"partial output")
            return SimpleNamespace(returncode=1, stderr="No space left on device")

        with patch("subprocess.run", side_effect=failed_copy) as copy, \
             patch("shutil.copytree", side_effect=AssertionError("no fallback")):
            with self.assertRaisesRegex(RuntimeError, "partial staging was retained"):
                self.manager._copy_build_tree(source, destination)
        self.assertEqual(copy.call_count, 1)
        self.assertEqual((destination / "partial.olean").read_bytes(), b"partial output")
        self.assertEqual((source / "Proof.olean").read_bytes(), b"source proof build")

    def test_low_space_copy_denies_before_any_new_directory(self):
        self.manager.storage_policy = "retention"
        source, destination = self.root / "copy-source", self.root / "copy-destination"
        source.mkdir()
        (source / "Proof.olean").write_bytes(b"source proof build")
        with patch("os.statvfs", return_value=filesystem(available=0)), \
             patch("subprocess.run", side_effect=AssertionError("copy must not run")):
            with self.assertRaises(StorageAdmissionError):
                self.manager._copy_build_tree(source, destination)
        self.assertFalse(destination.exists())

    def test_build_still_uses_the_same_validation_command_and_does_not_claim_cache_verified(self):
        _, project = self.opened()
        with patch.object(self.manager, "_run_lake_build", return_value=("checked output", {"status": "complete"})) as build:
            result = self.manager._build(project)
        self.assertEqual(build.call_args.args[1], ["lake", "build", "RiemannResearch", "--quiet"])
        self.assertFalse(result["project_cache"]["published"])
        self.assertNotIn("verified", result["project_cache"])

    def advance_remote(self):
        clone = self.root / "remote-advance"
        git(["clone", str(self.remote), str(clone)], self.root)
        git(["config", "user.name", "Storage Test"], clone)
        git(["config", "user.email", "storage@example.invalid"], clone)
        (clone / "README.md").write_text("# New main\n")
        git(["add", "README.md"], clone)
        git(["commit", "-m", "Advance main"], clone)
        git(["push", "origin", "main"], clone)

    def local_report(self, project):
        report = project / "RiemannResearch" / "Test" / "Report.md"
        report.write_text("Preserved research note.\n")
        return report

    def test_successful_integration_retains_original_and_integration_worktrees(self):
        token, project = self.opened()
        original = self.sentinel(project)
        self.local_report(project)
        self.advance_remote()
        result = self.manager.checkpoint(token, "Preserve integration report", push=True)
        integration = Path(result["build"]["preserved_integration_project_root"])
        self.assertTrue(result["pushed"])
        self.assertTrue(integration.is_dir())
        self.assertTrue((integration / "RiemannResearch" / "Test" / "Report.md").is_file())
        self.assert_retained(original)
        resumed = self.manager.open(token)
        self.assertTrue(resumed["needs_source_sync"])
        self.assertIn("# Test", self.manager.read_file(token, "README.md")["content"])
        continuation_token = result["continuation_workspace_token"]
        self.assertEqual(resumed["continuation_workspace_token"], continuation_token)
        self.assertEqual(Path(resumed["continuation_project_root"]), integration)
        self.assertEqual(self.manager.open(continuation_token)["local_head"], result["commit"])
        self.assertEqual(self.manager._read_meta(token)["base_commit"], result["source_commit"])
        before_registry = set(self.manager.state.glob("ws_*.json"))
        with self.assertRaises(WorkspaceContinuationRequired) as failure:
            self.manager.checkpoint(token, "Repeat same checkpoint", push=True)
        self.assertEqual(failure.exception.details["continuation_workspace_token"], continuation_token)
        self.assertEqual(set(self.manager.state.glob("ws_*.json")), before_registry)
        retained_integration = self.sentinel(integration)
        extra = integration / "RiemannResearch" / "Test" / "Continued.md"
        extra.write_text("Continue the published research.\n")
        continued = self.manager.checkpoint(continuation_token, "Continue retained integration", push=True)
        self.assertFalse(continued["integrated_with_newer_main"])
        self.assertFalse(continued["rehydrate_on_next_workspace_call"])
        self.assertEqual(git(["rev-parse", "main"], self.remote), continued["commit"])
        self.assertIn("Continue", git(["show", "main:RiemannResearch/Test/Continued.md"], self.remote))
        self.assert_retained(original)
        self.assert_retained(retained_integration)

    def test_stale_source_patch_refuses_before_writing_and_kernel_check_keeps_local_provenance(self):
        token, project = self.opened()
        self.local_report(project)
        self.advance_remote()
        published = self.manager.checkpoint(token, "Publish divergent research", push=True)
        before = (project / "README.md").read_bytes()
        with self.assertRaises(WorkspaceContinuationRequired):
            self.manager.apply_patch(token, "not even parsed before handoff")
        self.assertEqual((project / "README.md").read_bytes(), before)
        relative = "RiemannResearch/Test/Base.lean"
        sha = hashlib.sha256((project / relative).read_bytes()).hexdigest()
        fake_lake = self.root / "fake-bin"
        fake_lake.mkdir()
        executable = fake_lake / "lake"
        executable.write_text('#!/bin/sh\nprintf "%s\\n" "$@" > "$FAKE_LEAN_ARGV"\nexit 0\n')
        executable.chmod(0o755)
        arguments = self.root / "fake-lean-argv"
        with patch.dict(os.environ, {"PATH": str(fake_lake) + os.pathsep + os.environ["PATH"], "FAKE_LEAN_ARGV": str(arguments)}):
            checked = self.manager._check_file(token, relative, 30, sha)
        self.assertTrue(checked["verified"])
        self.assertEqual(checked["local_head"], published["source_commit"])
        self.assertEqual(checked["published_commit"], published["commit"])
        self.assertNotEqual(checked["local_head"], checked["published_commit"])
        self.assertEqual(checked["checked_file_sha256"], sha)
        self.assertEqual(arguments.read_text().splitlines(), ["env", "lean", str(project / relative)])

    def test_failed_integration_retains_checkout_and_reports_its_location(self):
        token, project = self.opened()
        original = self.sentinel(project)
        self.local_report(project)
        self.advance_remote()
        real_validation = self.manager._checkpoint_validation

        def validation(path, *args, **kwargs):
            if path != project:
                (path / ".lake" / "build").mkdir(parents=True, exist_ok=True)
                (path / ".lake" / "build" / "Failed.olean").write_bytes(b"failed integration build")
                raise RuntimeError("simulated validation failure")
            return real_validation(path, *args, **kwargs)

        with patch.object(self.manager, "_checkpoint_validation", side_effect=validation):
            with self.assertRaisesRegex(RuntimeError, "Integration workspace preserved at"):
                self.manager.checkpoint(token, "Preserve failed report", push=True)
        integrations = [Path(json.loads(path.read_text())["path"]) for path in self.manager.state.glob("ws_*.json") if path != self.manager._meta_path(token)]
        self.assertEqual(len(integrations), 1)
        self.assertEqual((integrations[0] / ".lake" / "build" / "Failed.olean").read_bytes(), b"failed integration build")
        self.assert_retained(original)
        failed_token = integrations[0].parent.name
        self.assertTrue(self.manager._read_meta(failed_token)["integration_validation_pending"])
        remote_before = git(["rev-parse", "main"], self.remote)
        with patch.object(self.manager, "_run_lake_build", side_effect=RuntimeError("still fails full build")):
            with self.assertRaisesRegex(RuntimeError, "still fails full build"):
                self.manager.checkpoint(failed_token, "Retry failed integration", push=True)
        self.assertEqual(git(["rev-parse", "main"], self.remote), remote_before)
        with patch.object(self.manager, "_run_lake_build", return_value=("full kernel build", {"status": "complete"})) as full:
            retried = self.manager.checkpoint(failed_token, "Recover failed integration", push=True)
        self.assertEqual(full.call_args.args[1], ["lake", "build", "RiemannResearch", "--quiet"])
        self.assertTrue(retried["pushed"])
        self.assertFalse(self.manager._read_meta(failed_token)["integration_validation_pending"])
        self.assertEqual((integrations[0] / ".lake" / "build" / "Failed.olean").read_bytes(), b"failed integration build")

    def test_legacy_stale_publication_creates_one_fully_validated_continuation(self):
        token, project = self.opened()
        original = self.sentinel(project)
        self.advance_remote()
        published = git(["rev-parse", "main"], self.remote)
        meta = self.manager._read_meta(token)
        meta.update(state="published", needs_rehydrate=True, published_commit=published)
        self.manager._write_meta(meta)
        with patch.object(self.manager, "_run_lake_build", return_value=("full kernel build", {"status": "complete"})) as full:
            with self.assertRaises(WorkspaceContinuationRequired) as failure:
                self.manager.checkpoint(token, "Recover earlier publication", push=True)
        continuation = failure.exception.details["continuation_workspace_token"]
        self.assertEqual(full.call_args.args[1], ["lake", "build", "RiemannResearch", "--quiet"])
        self.assertEqual(self.manager.open(continuation)["local_head"], published)
        child = self.manager._read_meta(continuation)
        self.assertEqual(child["continuation_validated_commit"], published)
        with patch.object(self.manager, "_clone", side_effect=AssertionError("reuse continuation")), \
             patch.object(self.manager, "_run_lake_build", side_effect=AssertionError("already validated")):
            with self.assertRaises(WorkspaceContinuationRequired):
                self.manager.checkpoint(token, "Repeat earlier publication", push=True)
        self.assert_retained(original)

    def test_failed_legacy_continuation_is_readable_and_cannot_bypass_full_validation(self):
        token, project = self.opened()
        meta = self.manager._read_meta(token)
        head = git(["rev-parse", "HEAD"], project)
        meta.update(state="published", needs_rehydrate=True, published_commit=head)
        self.manager._write_meta(meta)
        with patch.object(self.manager, "_run_lake_build", side_effect=RuntimeError("kernel rejected continuation")):
            with self.assertRaises(WorkspaceContinuationRequired) as failed:
                self.manager.checkpoint(token, "Validate legacy continuation", push=True)
        child_token = failed.exception.details["continuation_workspace_token"]
        self.assertEqual(self.manager.open(child_token)["state"], "continuation_validation")
        self.assertEqual(self.manager.read_file(child_token, "README.md")["content"], "# Test\n")
        self.assertIn("status", self.manager.git_status(child_token))
        self.assertEqual(self.manager._verification_project(child_token), Path(failed.exception.details["continuation_project_root"]))
        with self.assertRaisesRegex(RuntimeError, "validation is pending"):
            self.manager.checkpoint(child_token, "Do not bypass validation", push=True)
        self.assertNotIn("continuation_validated_commit", self.manager._read_meta(child_token))
        with patch.object(self.manager, "_run_lake_build", return_value=("kernel accepted continuation", {"status": "complete"})) as full:
            with self.assertRaises(WorkspaceContinuationRequired):
                self.manager.checkpoint(token, "Finish legacy continuation", push=True)
        self.assertEqual(full.call_args.args[1], ["lake", "build", "RiemannResearch", "--quiet"])
        self.assertEqual(self.manager._read_meta(child_token)["continuation_validated_commit"], head)

    def test_low_space_integration_denies_before_creating_an_integration_checkout(self):
        token, project = self.opened()
        self.local_report(project)
        self.advance_remote()
        with patch("os.statvfs", return_value=filesystem(available=GIB)):
            with self.assertRaises(StorageAdmissionError):
                self.manager.checkpoint(token, "Capacity guard report", push=True)
        self.assertFalse((self.manager.root / "_integration").exists())
        self.assertTrue((project / "RiemannResearch" / "Test" / "Report.md").is_file())


if __name__ == "__main__":
    unittest.main()
