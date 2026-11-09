"""Offline scheduler integration tests; no Lean, Bazel, or network process runs.

Real job records, admission, worker threads and flock leases are exercised.
Events hold fake job bodies until assertions are complete; observed failed
nonblocking flock attempts make capacity assertions independent of sleeps.
"""

from contextlib import contextmanager
import os
from pathlib import Path
import re
import secrets
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

import agent_workspaces
from agent_workspaces import AgentWorkspaceManager


class JobBarrier:
    def __init__(self):
        self.condition = threading.Condition()
        self.releases = {}
        self.entered = {}
        self.active = set()
        self.blocked = set()
        self.finished = set()
        self.maximum = {"bazel": 0, "lake": 0}

    def register(self, token):
        self.releases[token] = threading.Event()

    def wait_for(self, predicate, description):
        with self.condition:
            if not self.condition.wait_for(predicate, timeout=5):
                raise AssertionError(
                    f"Timed out waiting for {description}; entered={self.entered}, "
                    f"active={self.active}, blocked={self.blocked}, finished={self.finished}"
                )

    def release(self, token):
        self.releases[token].set()

    def release_all(self):
        for event in self.releases.values():
            event.set()


class BarrierManager(AgentWorkspaceManager):
    def __init__(self, *args, barrier, **kwargs):
        self.barrier = barrier
        self._test_local = threading.local()
        super().__init__(*args, **kwargs)

    @contextmanager
    def _heavy_worker_slot(self, backend="lake"):
        self._test_local.slot_job = self._job_local.job_id
        try:
            with super()._heavy_worker_slot(backend):
                yield
        finally:
            self._test_local.slot_job = None

    def _run_job(self, job_id):
        try:
            return super()._run_job(job_id)
        finally:
            with self.barrier.condition:
                self.barrier.finished.add(job_id)
                self.barrier.condition.notify_all()

    def _execute_job(self, job):
        job_id = job["job_id"]
        token = job["workspace_token"]
        backend = job["arguments"]["backend"]
        with self.barrier.condition:
            self.barrier.entered[job_id] = (token, backend)
            self.barrier.active.add(job_id)
            active_count = sum(
                self.barrier.entered[active][1] == backend
                for active in self.barrier.active
            )
            self.barrier.maximum[backend] = max(self.barrier.maximum[backend], active_count)
            self.barrier.condition.notify_all()
        try:
            if not self.barrier.releases[token].wait(timeout=10):
                raise RuntimeError("Test failed to release fake job")
            return {
                "verified": True,
                "backend": backend,
                "result_workspace": token,
                "result_code": job["arguments"]["code"],
            }
        finally:
            with self.barrier.condition:
                self.barrier.active.remove(job_id)
                self.barrier.condition.notify_all()


class BazelConcurrencyTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        self.source.mkdir()
        self.barrier = JobBarrier()
        self.managers = []
        self.submitted = []
        self.environment = patch.dict(os.environ, {
            "LEAN_AGENT_WORKSPACES_ROOT": str(self.root / "workspaces"),
            "LEAN_AGENT_WORKSPACES_STATE": str(self.root / "state"),
            "LEAN_SHARED_DEPS_ROOT": str(self.root / "dependencies"),
            "LEAN_SHARED_PROJECT_BUILDS_ROOT": str(self.root / "project-builds"),
            "LEAN_JOB_WORKERS": "1",
            "LEAN_NUM_THREADS": "2",
            "LEAN_LAKE_BUILD_THREADS": "2",
        })
        self.environment.start()
        os.environ.pop("LEAN_VERIFICATION_BACKEND", None)
        os.environ.pop("LEAN_BAZEL_JOB_WORKERS", None)
        original_flock = agent_workspaces.fcntl.flock

        def observe_flock(handle, operation):
            try:
                return original_flock(handle, operation)
            except BlockingIOError:
                for manager in self.managers:
                    job_id = getattr(manager._test_local, "slot_job", None)
                    if job_id is not None:
                        with self.barrier.condition:
                            self.barrier.blocked.add(job_id)
                            self.barrier.condition.notify_all()
                raise

        self.flock_patch = patch("agent_workspaces.fcntl.flock", side_effect=observe_flock)
        self.flock_patch.start()

    def tearDown(self):
        try:
            self.barrier.release_all()
            for _, submission, _, _ in self.submitted:
                job_id = submission["job_id"]
                self.barrier.wait_for(lambda job_id=job_id: job_id in self.barrier.finished,
                                      "all fake jobs to finish")
            for manager in self.managers:
                with manager._job_guard:
                    threads = list(manager._bazel_job_threads)
                for thread in threads:
                    thread.join(timeout=5)
                    self.assertFalse(thread.is_alive(), "Bazel test worker did not exit")
                manager._job_queue.join()
                manager._owner_lease.close()
        finally:
            self.flock_patch.stop()
            self.environment.stop()
            self.temporary.cleanup()

    def manager(self, *, bazel_cap=None, lake_cap=1):
        os.environ["LEAN_JOB_WORKERS"] = str(lake_cap)
        if bazel_cap is None:
            os.environ.pop("LEAN_BAZEL_JOB_WORKERS", None)
        else:
            os.environ["LEAN_BAZEL_JOB_WORKERS"] = str(bazel_cap)
        manager = BarrierManager(self.source, "offline-unused-remote", barrier=self.barrier)
        self.managers.append(manager)
        return manager

    def workspace(self, manager):
        token = "ws_" + secrets.token_hex(16)
        project = manager._workspace_dir(token)
        project.mkdir(parents=True)
        (project / "RiemannResearch").mkdir()
        (project / "RiemannResearch/Probe.lean").write_text("example : True := True.intro\n")
        manager._write_meta({
            "token": token, "path": str(project), "state": "active",
            "needs_rehydrate": False, "last_activity": time.time(),
        })
        self.barrier.register(token)
        return token

    def submit(self, manager, token=None, *, backend=""):
        token = token or self.workspace(manager)
        code = f"-- workspace marker {token}\nexample : True := True.intro\n"
        submission = manager.submit_run_code(token, code, backend=backend)
        selected_backend = backend or manager.default_verification_backend
        expected_workers = (manager.bazel_job_workers or None
                            if selected_backend == "bazel" else manager.job_workers)
        self.assertEqual(submission["worker_count"], expected_workers)
        self.assertEqual(submission["same_workspace_limit"], 1)
        self.submitted.append((manager, submission, token, code))
        return submission, token

    def wait_entered(self, *submissions):
        wanted = {submission["job_id"] for submission in submissions}
        self.barrier.wait_for(lambda: wanted.issubset(self.barrier.entered),
                              "requested fake job bodies to overlap")

    def finish_and_check(self):
        self.barrier.release_all()
        for manager, submission, token, code in self.submitted:
            job_id = submission["job_id"]
            self.barrier.wait_for(lambda job_id=job_id: job_id in self.barrier.finished,
                                  "terminal job record")
            result = manager.job_status(job_id)
            self.assertEqual(result["state"], "succeeded", result)
            self.assertEqual(result["workspace_token"], token)
            self.assertEqual(result["result"]["result_workspace"], token)
            self.assertEqual(result["result"]["result_code"], code)
            self.assertEqual(result["result"]["backend"], result["backend"])
            self.assertEqual(result["result"]["request_sha256"], submission["request_sha256"])
            self.assertEqual(result["worker_count"], submission["worker_count"])
            self.assertEqual(result["same_workspace_limit"], 1)

    def test_invalid_bazel_worker_limits_are_rejected(self):
        for value, message in ((-1, "must be nonnegative"), ("not-an-integer", "must be an integer")):
            with self.subTest(value=value):
                with self.assertRaisesRegex(ValueError, message):
                    self.manager(bazel_cap=value)
        self.assertEqual(self.managers, [])

    def test_failed_thread_start_is_terminal_and_allows_new_submission(self):
        manager = self.manager()
        token = self.workspace(manager)
        code = f"-- workspace marker {token}\nexample : True := True.intro\n"
        with patch("agent_workspaces.threading.Thread.start",
                   side_effect=RuntimeError("injected thread-start failure")):
            with self.assertRaisesRegex(RuntimeError, "injected thread-start failure"):
                manager.submit_run_code(token, code)
        jobs = manager.list_jobs(token)["jobs"]
        self.assertEqual(len(jobs), 1)
        failed_id = jobs[0]["job_id"]
        failed = manager.job_status(failed_id)
        self.assertEqual(failed["state"], "failed")
        self.assertTrue(failed["terminal"])
        self.assertIn("Bazel worker could not start", failed["error"])
        self.assertEqual(failed["worker_count"], 5)
        self.assertEqual(failed["same_workspace_limit"], 1)
        self.assertEqual(manager._bazel_job_threads, set())
        self.assertEqual(manager._active_jobs, set())
        self.assertIsNone(manager._pending_job_for_workspace(token))
        retry, _ = self.submit(manager, token)
        self.assertNotEqual(retry["job_id"], failed_id)
        self.wait_entered(retry)
        self.finish_and_check()
        self.assertEqual(manager.job_status(failed_id)["state"], "failed")

    def test_default_bazel_cap_is_five_across_manager_instances(self):
        manager = self.manager()
        other_manager = self.manager()
        self.assertEqual(manager.bazel_job_workers, 5)
        self.assertEqual(other_manager.bazel_job_workers, 5)
        self.assertEqual(manager.default_verification_backend, "bazel")
        submissions = [self.submit(manager)[0] for _ in range(5)]
        self.wait_entered(*submissions)
        sixth, _ = self.submit(other_manager)
        sixth_id = sixth["job_id"]
        self.barrier.wait_for(
            lambda: sixth_id in self.barrier.blocked or sixth_id in self.barrier.entered,
            "sixth job to attempt the shared capacity lease",
        )
        self.assertNotIn(sixth_id, self.barrier.entered)
        waiting = manager.job_status(sixth_id)
        self.assertEqual(waiting["state"], "queued")
        self.assertEqual(waiting["progress"]["phase"], "waiting_for_worker")
        self.assertNotIn("started_at", waiting)
        self.assertEqual(waiting["active_job_count"], 5)
        self.assertEqual(waiting["worker_count"], 5)
        self.assertIsNone(waiting["queue_position"])
        duplicate = other_manager.submit_run_code(
            self.submitted[-1][2], self.submitted[-1][3]
        )
        self.assertTrue(duplicate["existing"])
        self.assertEqual(duplicate["job_id"], sixth_id)
        self.assertEqual(duplicate["state"], "queued")
        with self.assertRaisesRegex(RuntimeError, re.escape(sixth_id)):
            other_manager.submit_run_code(self.submitted[-1][2], "example : True := trivial")
        with self.assertRaisesRegex(RuntimeError, re.escape(sixth_id)):
            other_manager.apply_patch(self.submitted[-1][2], "unreachable while queued")
        self.assertEqual(self.barrier.maximum["bazel"], 5)
        self.barrier.release(self.submitted[0][2])
        self.wait_entered(sixth)
        running = other_manager.job_status(sixth_id)
        self.assertEqual(running["state"], "running")
        self.assertGreaterEqual(running["started_at"], waiting["progress"]["updated_at"])
        self.assertEqual(self.barrier.maximum["bazel"], 5)
        with manager._job_queue.mutex:
            self.assertEqual(list(manager._job_queue.queue), [])
        self.finish_and_check()

    def test_worker_slot_failure_is_terminal_before_start(self):
        manager = self.manager()
        with patch.object(manager, "_heavy_worker_slot",
                          side_effect=RuntimeError("injected slot failure")):
            submission, token = self.submit(manager)
            job_id = submission["job_id"]
            self.barrier.wait_for(lambda: job_id in self.barrier.finished,
                                  "failed capacity acquisition")
        failed = manager.job_status(job_id)
        self.assertEqual(failed["state"], "failed")
        self.assertTrue(failed["terminal"])
        self.assertNotIn("started_at", failed)
        self.assertIn("injected slot failure", failed["error"])
        self.assertEqual(failed["active_job_count"], 0)
        self.assertIsNone(manager._pending_job_for_workspace(token))

    def test_explicit_zero_allows_more_than_five_bazel_jobs(self):
        manager = self.manager(bazel_cap=0)
        self.assertEqual(manager.bazel_job_workers, 0)
        submissions = [self.submit(manager)[0] for _ in range(6)]
        self.wait_entered(*submissions)
        self.assertEqual(self.barrier.maximum["bazel"], 6)
        self.finish_and_check()

    def test_bazel_cap_limits_bodies_after_waiter_reaches_shared_lease(self):
        manager = self.manager(bazel_cap=2)
        first, first_token = self.submit(manager)
        second, _ = self.submit(manager)
        self.wait_entered(first, second)
        third, _ = self.submit(manager)
        third_id = third["job_id"]
        self.barrier.wait_for(lambda: third_id in self.barrier.blocked or third_id in self.barrier.entered,
                              "third job to attempt its capacity lease")
        self.assertNotIn(third_id, self.barrier.entered)
        self.assertEqual(self.barrier.maximum["bazel"], 2)
        self.barrier.release(first_token)
        self.wait_entered(third)
        self.assertEqual(self.barrier.maximum["bazel"], 2)
        self.finish_and_check()

    def test_bazel_cap_is_shared_across_manager_instances(self):
        first_manager = self.manager(bazel_cap=1)
        second_manager = self.manager(bazel_cap=1)
        first, first_token = self.submit(first_manager)
        self.wait_entered(first)
        second, _ = self.submit(second_manager)
        second_id = second["job_id"]
        self.barrier.wait_for(lambda: second_id in self.barrier.blocked or second_id in self.barrier.entered,
                              "other manager to attempt the shared lease")
        self.assertNotIn(second_id, self.barrier.entered)
        self.barrier.release(first_token)
        self.wait_entered(second)
        self.assertEqual(self.barrier.maximum["bazel"], 1)
        self.finish_and_check()

    def test_lake_keeps_configured_worker_cap_and_queue(self):
        manager = self.manager(lake_cap=1)
        self.assertEqual(len(manager._job_worker_threads), 1)
        first, first_token = self.submit(manager, backend="lake")
        self.wait_entered(first)
        second, _ = self.submit(manager, backend="lake")
        with manager._job_queue.mutex:
            self.assertIn(second["job_id"], manager._job_queue.queue)
        self.assertEqual(manager.job_status(second["job_id"])["state"], "queued")
        self.barrier.release(first_token)
        self.wait_entered(second)
        self.assertEqual(self.barrier.maximum["lake"], 1)
        self.finish_and_check()

    def test_bazel_does_not_wait_behind_a_lake_job(self):
        manager = self.manager(lake_cap=1)
        lake, _ = self.submit(manager, backend="lake")
        self.wait_entered(lake)
        first, _ = self.submit(manager)
        second, _ = self.submit(manager)
        self.wait_entered(lake, first, second)
        self.assertEqual(len(self.barrier.active), 3)
        self.finish_and_check()

    def test_same_workspace_duplicate_and_mutation_exclusion_remain(self):
        manager = self.manager()
        first, token = self.submit(manager)
        self.wait_entered(first)
        code = self.submitted[0][3]
        duplicate = manager.submit_run_code(token, code)
        self.assertTrue(duplicate["existing"])
        self.assertEqual(duplicate["job_id"], first["job_id"])
        with self.assertRaisesRegex(RuntimeError, re.escape(first["job_id"])):
            manager.submit_run_code(token, code + "-- different\n")
        with self.assertRaisesRegex(RuntimeError, re.escape(first["job_id"])):
            manager.submit_check_file(token, "RiemannResearch/Probe.lean")
        with self.assertRaisesRegex(RuntimeError, re.escape(first["job_id"])):
            manager.apply_patch(token, "not reached because workspace is busy")
        other, _ = self.submit(manager)
        self.wait_entered(first, other)
        self.assertEqual(self.barrier.maximum["bazel"], 2)
        self.finish_and_check()


if __name__ == "__main__":
    unittest.main()
