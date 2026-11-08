"""Offline tests for workspace-local indexed admission and retained job history.

Only fake job bodies run. Real admission, persisted records, leases and status
paths are exercised with event barriers rather than throughput thresholds.
"""

from contextlib import contextmanager
import json
import math
import os
from pathlib import Path
import secrets
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

import test_bazel_concurrency as scheduler_fixture


class JobAdmissionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        self.source.mkdir()
        self.barrier = scheduler_fixture.JobBarrier()
        self.managers = []
        self.submissions = []
        self.calls = []
        self.gates = []
        self.environment = patch.dict(os.environ, {
            "LEAN_AGENT_WORKSPACES_ROOT": str(self.root / "workspaces"),
            "LEAN_AGENT_WORKSPACES_STATE": str(self.root / "state"),
            "LEAN_SHARED_DEPS_ROOT": str(self.root / "dependencies"),
            "LEAN_SHARED_PROJECT_BUILDS_ROOT": str(self.root / "project-builds"),
            "LEAN_JOB_WORKERS": "1", "LEAN_BAZEL_JOB_WORKERS": "0",
            "LEAN_VERIFICATION_BACKEND": "bazel", "LEAN_NUM_THREADS": "2",
            "LEAN_LAKE_BUILD_THREADS": "2",
        })
        self.environment.start()
        self.manager = self.make_manager()

    def tearDown(self):
        try:
            for gate in self.gates:
                gate.set()
            self.barrier.release_all()
            for call in self.calls:
                call["thread"].join(timeout=5)
                self.assertFalse(call["thread"].is_alive(), "test call remained blocked")
            self.finish_jobs()
            for manager in self.managers:
                with manager._job_guard:
                    threads = list(manager._bazel_job_threads)
                for thread in threads:
                    thread.join(timeout=5)
                    self.assertFalse(thread.is_alive(), "fake Bazel worker did not stop")
                manager._job_queue.join()
                manager._owner_lease.close()
        finally:
            self.environment.stop()
            self.temporary.cleanup()

    def make_manager(self):
        manager = scheduler_fixture.BarrierManager(
            self.source, "offline-unused-remote", barrier=self.barrier,
        )
        self.managers.append(manager)
        return manager

    def workspace(self):
        token = "ws_" + secrets.token_hex(16)
        project = self.manager._workspace_dir(token)
        project.mkdir(parents=True)
        (project / "RiemannResearch").mkdir()
        (project / "RiemannResearch/Probe.lean").write_text("example : True := True.intro\n")
        self.manager._write_meta({
            "token": token, "path": str(project), "state": "active",
            "needs_rehydrate": False, "last_activity": time.time(),
        })
        self.barrier.register(token)
        return token

    @staticmethod
    def code(token):
        return f"-- workspace marker {token}\nexample : True := True.intro\n"

    def submit(self, manager, token, code=None):
        submission = manager.submit_run_code(token, code or self.code(token))
        self.submissions.append((manager, submission))
        return submission

    def spawn_call(self, function):
        call = {"done": threading.Event()}

        def run():
            try:
                call["result"] = function()
            except BaseException as exc:
                call["error"] = exc
            finally:
                call["done"].set()

        call["thread"] = threading.Thread(target=run, daemon=True)
        self.calls.append(call)
        call["thread"].start()
        return call

    def result(self, call):
        self.assertTrue(call["done"].wait(timeout=5), "independent call did not complete")
        if "error" in call:
            raise call["error"]
        return call["result"]

    def wait_entered(self, submission):
        job_id = submission["job_id"]
        self.barrier.wait_for(lambda: job_id in self.barrier.entered, "fake verification body")

    def finish_jobs(self):
        self.barrier.release_all()
        for manager, submission in self.submissions:
            job_id = submission["job_id"]
            self.barrier.wait_for(lambda job_id=job_id: job_id in self.barrier.finished,
                                  "persisted terminal result")
            status = manager.job_status(job_id)
            self.assertEqual(status["state"], "succeeded", status)
            self.assertEqual(status["result"]["request_sha256"], submission["request_sha256"])

    def assert_admission_metadata(self, submission):
        timing = submission["admission"]
        for field in ("lock_wait_seconds", "lookup_seconds", "persist_seconds",
                      "dispatch_seconds", "total_seconds"):
            self.assertIsInstance(timing[field], (int, float))
            self.assertTrue(math.isfinite(timing[field]))
            self.assertGreaterEqual(timing[field], 0)
            self.assertLessEqual(timing[field], timing["total_seconds"] + 1e-5)
        self.assertIsInstance(timing["records_examined"], int)
        self.assertGreaterEqual(timing["records_examined"], 0)

    def make_record(self, token, *, state="queued", owner=None, indexed=False):
        job_id = "job_" + secrets.token_hex(16)
        arguments = {"backend": "bazel", "code": self.code(token), "timeout_seconds": 300}
        record = {
            "job_id": job_id, "workspace_token": token, "kind": "run_code",
            "backend": "bazel", "arguments": arguments, "state": state,
            "submitted_at": time.time(),
            "request_sha256": self.manager._request_sha256(token, "run_code", arguments),
        }
        if owner is not None:
            record["owner_id"] = owner
        if indexed:
            self.manager._write_job(record)
        else:
            self.manager._job_path(job_id).write_text(json.dumps(record))
        return record

    def test_terminal_history_is_never_scanned_or_read_on_hot_paths(self):
        token = self.workspace()
        history_ids = set()
        for _ in range(1000):
            record = self.make_record(token, state="succeeded")
            history_ids.add(record["job_id"])
        original_glob = Path.glob
        original_read = self.manager._read_job

        def indexed_only(path, pattern):
            if path == self.manager.jobs:
                raise AssertionError("hot path scanned the historical job directory")
            return original_glob(path, pattern)

        def no_history_reads(job_id):
            if job_id in history_ids:
                raise AssertionError("hot path read a terminal history record")
            return original_read(job_id)

        with patch.object(Path, "glob", indexed_only), patch.object(
            self.manager, "_read_job", side_effect=no_history_reads,
        ):
            self.manager._ensure_workspace_idle(token, "inspect idle workspace")
            submission = self.submit(self.manager, token)
            self.wait_entered(submission)
            duplicate = self.submit(self.manager, token)
            self.assertTrue(duplicate["existing"])
            self.assertEqual(duplicate["job_id"], submission["job_id"])
            for response in (submission, duplicate):
                self.assert_admission_metadata(response)
                self.assertLess(response["admission"]["records_examined"], len(history_ids))
            status = self.manager.job_status(submission["job_id"])
            self.assertFalse(status["terminal"])
            self.assertLessEqual(status["admission_started_at"], status["submitted_at"])
            self.assertLessEqual(status["submitted_at"], status["started_at"])
            with self.assertRaisesRegex(RuntimeError, submission["job_id"]):
                self.manager._ensure_workspace_idle(token, "mutate busy workspace")
            self.finish_jobs()
            self.manager._ensure_workspace_idle(token, "inspect restored idle workspace")

    def exercise_blocked_workspace(self, *, index_read):
        token_a, token_b = self.workspace(), self.workspace()
        entered, release = threading.Event(), threading.Event()
        self.gates.append(release)
        if index_read:
            original_glob = Path.glob

            def blocked_index(path, pattern):
                if path == self.manager.pending_jobs / token_a:
                    entered.set()
                    if not release.wait(timeout=5):
                        raise RuntimeError("test did not release workspace A index")
                return original_glob(path, pattern)

            patched = patch.object(Path, "glob", blocked_index)
        else:
            original_lock = self.manager._admission_lock
            holder_entered = threading.Event()

            def hold_lock():
                with original_lock(token_a):
                    holder_entered.set()
                    if not release.wait(timeout=5):
                        raise RuntimeError("test did not release workspace A lock")

            self.spawn_call(hold_lock)
            self.assertTrue(holder_entered.wait(timeout=5))

            @contextmanager
            def observed_lock(token):
                if token == token_a:
                    entered.set()
                with original_lock(token):
                    yield

            patched = patch.object(self.manager, "_admission_lock", observed_lock)
        with patched:
            call_a = self.spawn_call(lambda: self.submit(self.manager, token_a))
            self.assertTrue(entered.wait(timeout=5), "A did not reach the blocked operation")
            call_b = self.spawn_call(lambda: self.submit(self.manager, token_b))
            submission_b = self.result(call_b)
            self.wait_entered(submission_b)
            status_call = self.spawn_call(lambda: self.manager.job_status(submission_b["job_id"]))
            status_b = self.result(status_call)
            self.assertEqual(status_b["workspace_token"], token_b)
            self.assertFalse(status_b["terminal"])
            self.assertFalse(call_a["done"].is_set(), "A unexpectedly passed its test barrier")
            release.set()
            submission_a = self.result(call_a)
            self.wait_entered(submission_a)
        self.finish_jobs()

    def test_blocked_workspace_admission_lock_does_not_block_another_workspace(self):
        self.exercise_blocked_workspace(index_read=False)

    def test_blocked_pending_index_read_does_not_block_another_workspace(self):
        self.exercise_blocked_workspace(index_read=True)

    def race_same_workspace(self, *, conflicting):
        second_manager = self.make_manager()
        token = self.workspace()
        start = threading.Barrier(3)

        def submit_together(manager, code):
            start.wait(timeout=5)
            return self.submit(manager, token, code)

        first = self.spawn_call(lambda: submit_together(self.manager, self.code(token)))
        second_code = self.code(token) + ("-- conflicting request\n" if conflicting else "")
        second = self.spawn_call(lambda: submit_together(second_manager, second_code))
        start.wait(timeout=5)
        self.assertTrue(first["done"].wait(timeout=5))
        self.assertTrue(second["done"].wait(timeout=5))
        results = [call["result"] for call in (first, second) if "result" in call]
        errors = [call["error"] for call in (first, second) if "error" in call]
        if conflicting:
            self.assertEqual(len(results), 1)
            self.assertEqual(len(errors), 1)
            self.assertIsInstance(errors[0], RuntimeError)
            self.assertIn(results[0]["job_id"], str(errors[0]))
        else:
            self.assertEqual(errors, [])
            self.assertEqual(len(results), 2)
            self.assertEqual(results[0]["job_id"], results[1]["job_id"])
            self.assertEqual(sum(response["accepted"] for response in results), 1)
        self.wait_entered(results[0])
        self.assertEqual(len(self.barrier.entered), 1)
        pending, _ = self.manager._indexed_pending_jobs(token)
        self.assertEqual([job["job_id"] for job in pending], [results[0]["job_id"]])
        for result in results:
            self.assert_admission_metadata(result)
        self.finish_jobs()
        self.assertEqual(self.manager._indexed_pending_jobs(token)[0], [])

    def test_cross_manager_simultaneous_duplicates_share_one_job(self):
        self.race_same_workspace(conflicting=False)

    def test_cross_manager_simultaneous_conflicts_admit_only_one_job(self):
        self.race_same_workspace(conflicting=True)

    def test_missing_record_and_terminal_record_markers_are_pruned(self):
        token = self.workspace()
        marker_dir = self.manager.pending_jobs / token
        marker_dir.mkdir()
        missing_id = "job_" + secrets.token_hex(16)
        missing = marker_dir / missing_id
        missing.touch()
        terminal = self.make_record(token, state="succeeded")
        stale = marker_dir / terminal["job_id"]
        stale.touch()
        pending, examined = self.manager._indexed_pending_jobs(token)
        self.assertEqual(pending, [])
        self.assertEqual(examined, len([missing, stale]))
        self.assertFalse(missing.exists())
        self.assertFalse(stale.exists())
        self.assertEqual(self.manager._read_job(terminal["job_id"])["state"], "succeeded")
        submission = self.submit(self.manager, token)
        self.wait_entered(submission)
        self.finish_jobs()

    def test_startup_recovers_legacy_pending_records_without_replaying_them(self):
        live_token, abandoned_token = self.workspace(), self.workspace()
        live = self.make_record(live_token, owner=self.manager._owner_id)
        abandoned = self.make_record(abandoned_token)
        restarted = self.make_manager()
        self.assertEqual(restarted._read_job(live["job_id"])["state"], "queued")
        self.assertTrue((restarted.pending_jobs / live_token / live["job_id"]).exists())
        with self.assertRaisesRegex(RuntimeError, live["job_id"]):
            restarted._ensure_workspace_idle(live_token, "mutate workspace")
        recovered = restarted.job_status(abandoned["job_id"])
        self.assertEqual(recovered["state"], "interrupted")
        self.assertTrue(recovered["terminal"])
        self.assertFalse((restarted.pending_jobs / abandoned_token / abandoned["job_id"]).exists())
        self.assertEqual(self.barrier.entered, {})
        submission = self.submit(restarted, abandoned_token)
        self.wait_entered(submission)
        self.finish_jobs()

    def test_corrupt_indexed_record_fails_closed_without_blocking_other_workspaces(self):
        corrupt_token, healthy_token = self.workspace(), self.workspace()
        record = self.make_record(corrupt_token, owner=self.manager._owner_id, indexed=True)
        path = self.manager._job_path(record["job_id"])
        path.write_text("{invalid JSON")
        with self.assertRaisesRegex(RuntimeError, path.name):
            self.make_manager()
        for operation in (
            lambda: self.manager._ensure_workspace_idle(corrupt_token, "mutate workspace"),
            lambda: self.manager.submit_run_code(corrupt_token, self.code(corrupt_token)),
        ):
            with self.assertRaises(json.JSONDecodeError):
                operation()
        self.assertEqual(path.read_text(), "{invalid JSON")
        self.assertTrue((self.manager.pending_jobs / corrupt_token / record["job_id"]).exists())
        submission = self.submit(self.manager, healthy_token)
        self.wait_entered(submission)
        self.finish_jobs()

    def test_valid_json_identity_and_state_corruption_fail_closed(self):
        for field, value, message in (
            ("job_id", "job_" + secrets.token_hex(16), "identity mismatch"),
            ("state", "unknown-job-state", "Invalid job record state"),
        ):
            with self.subTest(field=field):
                corrupt_token, healthy_token = self.workspace(), self.workspace()
                original = self.make_record(corrupt_token, owner=self.manager._owner_id, indexed=True)
                path = self.manager._job_path(original["job_id"])
                changed = {**original, field: value}
                serialized = json.dumps(changed)
                path.write_text(serialized)
                try:
                    for operation in (
                        lambda: self.manager._ensure_workspace_idle(corrupt_token, "mutate workspace"),
                        lambda: self.manager.submit_run_code(corrupt_token, self.code(corrupt_token)),
                        lambda: self.manager.job_status(original["job_id"]),
                    ):
                        with self.assertRaisesRegex(RuntimeError, message):
                            operation()
                    with self.assertRaisesRegex(RuntimeError, path.name):
                        self.make_manager()
                    self.assertEqual(path.read_text(), serialized)
                    self.assertTrue((self.manager.pending_jobs / corrupt_token / original["job_id"]).exists())
                    healthy = self.submit(self.manager, healthy_token)
                    self.wait_entered(healthy)
                    self.finish_jobs()
                finally:
                    path.write_text(json.dumps(original))


if __name__ == "__main__":
    unittest.main()
