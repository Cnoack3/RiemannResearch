"""Offline queue/verification regression tests; all Lean execution is faked.

Run with: python tools/test_verification_jobs.py
No real proof, canonical repository, network, or publication is touched.
"""

import hashlib
import errno
import json
import os
import re
import secrets
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest.mock import patch

from agent_workspaces import AgentWorkspaceManager, MAX_PATCH_BYTES, MAX_READ_BYTES


FAKE_LAKE = r'''
import os
import subprocess
import sys
import time
from pathlib import Path

assert sys.argv[1:3] == ["env", "lean"], sys.argv
code = Path(sys.argv[3]).read_text()
if "TIMEOUT" in code:
    child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
    print("before-timeout CHILD_PID=" + str(child.pid), flush=True)
    time.sleep(60)
if "SIGNAL" in code:
    os.kill(os.getpid(), 9)
if "FLOOD" in code:
    print("x" * 100000 + "\nlast-diagnostic", file=sys.stderr, flush=True)
if "HEARTBEAT" in code:
    print("error: maximum number of heartbeats exceeded (maxHeartbeats)", flush=True)
    sys.exit(1)
if "RECURSION" in code:
    print("error: maximum recursion depth has been reached", flush=True)
    sys.exit(1)
if "FAIL" in code:
    print("simulated-error: unsolved goals", file=sys.stderr, flush=True)
    sys.exit(1)
print("simulated-verified", flush=True)
'''


class HoldingManager(AgentWorkspaceManager):
    def __init__(self, *args, **kwargs):
        self.worker_entered = threading.Event()
        self.worker_release = threading.Event()
        self.executions = []
        super().__init__(*args, **kwargs)

    def _execute_job(self, job):
        self.executions.append(job["kind"])
        if job["kind"] == "build":
            self.worker_entered.set()
            if not self.worker_release.wait(10):
                raise RuntimeError("Test failed to release its held worker")
            return {"output": "fake-build"}
        return super()._execute_job(job)


class VerificationJobsTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        self.source.mkdir()
        self.fake_bin = self.root / "bin"
        self.fake_bin.mkdir()
        fake_lake = self.fake_bin / "lake"
        fake_lake.write_text("#!" + sys.executable + "\n" + FAKE_LAKE)
        fake_lake.chmod(0o755)
        self.environment = patch.dict(os.environ, {
            "LEAN_AGENT_WORKSPACES_ROOT": str(self.root / "workspaces"),
            "LEAN_AGENT_WORKSPACES_STATE": str(self.root / "state"),
            "LEAN_SHARED_DEPS_ROOT": str(self.root / "shared"),
            "LEAN_SHARED_PROJECT_BUILDS_ROOT": str(self.root / "project-builds"),
            "LEAN_NUM_THREADS": "2",
            "LEAN_LAKE_BUILD_THREADS": "2",
            "LEAN_STORAGE_POLICY": "preserve",
            "PATH": str(self.fake_bin) + os.pathsep + os.environ["PATH"],
        })
        self.environment.start()
        self.previous_workers = os.environ.pop("LEAN_JOB_WORKERS", None)
        self.managers = []
        self.manager = self.new_manager()
        self.token, self.project = self.workspace()

    def tearDown(self):
        for manager in self.managers:
            manager.worker_release.set()
        for manager in self.managers:
            manager._job_queue.join()
            # No queued work remains; release test leases before temp cleanup.
            manager._owner_lease.close()
        if self.previous_workers is not None:
            os.environ["LEAN_JOB_WORKERS"] = self.previous_workers
        self.environment.stop()
        self.temporary.cleanup()

    def new_manager(self):
        manager = HoldingManager(self.source, "unused-offline-test-remote")
        self.managers.append(manager)
        return manager

    def workspace(self):
        token = "ws_" + secrets.token_hex(16)
        project = self.manager._workspace_dir(token)
        project.mkdir(parents=True)
        subprocess.run(["git", "init", "-q", str(project)], check=True, capture_output=True)
        module = project / "RiemannResearch"
        module.mkdir()
        (module / "Basic.lean").write_text("theorem sample : True := by trivial\n")
        (module / "Other.lean").write_text("theorem other : True := by trivial\n")
        (project / "RiemannResearch.lean").write_text("import RiemannResearch.Basic\n")
        (project / "README.md").write_text("test\n")
        # Managed clones have a real source revision; verification reports its
        # provenance even when all Lean execution in this suite is simulated.
        subprocess.run(["git", "add", "--all"], cwd=project, check=True, capture_output=True)
        subprocess.run([
            "git", "-c", "user.name=Offline Fixture", "-c", "user.email=fixture@example.invalid",
            "commit", "-q", "-m", "Create verification fixture",
        ], cwd=project, check=True, capture_output=True)
        self.manager._write_meta({
            "token": token, "path": str(project), "state": "active",
            "needs_rehydrate": False, "last_activity": time.time(),
        })
        return token, project

    def terminal(self, submission, manager=None):
        manager = manager or self.manager
        deadline = time.monotonic() + 8
        while time.monotonic() < deadline:
            status = manager.job_status(submission["job_id"], include_logs=True)
            if status["terminal"]:
                return status
            time.sleep(0.01)
        self.fail("Job did not become terminal: " + json.dumps(status))

    def hold_worker(self):
        token, _ = self.workspace()
        submission = self.manager.submit_build(token)
        self.assertTrue(self.manager.worker_entered.wait(2))
        return submission

    def test_startup_metadata_error_does_not_kill_worker_or_execute_job(self):
        held = self.hold_worker()
        queued = self.manager.submit_run_code(self.token, "-- must not execute")
        original = self.manager._write_job

        def fail_start(job):
            if job["job_id"] == queued["job_id"] and job["state"] == "running":
                raise OSError(errno.ENOSPC, "simulated full state mount")
            return original(job)

        with patch.object(self.manager, "_write_job", side_effect=fail_start):
            self.manager.worker_release.set()
            self.terminal(held)
            status = self.terminal(queued)
        self.manager._job_queue.join()
        self.assertEqual(status["state"], "failed")
        self.assertIn("Errno 28", status["error"])
        self.assertEqual(self.manager.executions, ["build"])
        self.assertTrue(self.manager._job_worker_threads[0].is_alive())
        self.assertNotIn(queued["job_id"], self.manager._active_jobs)

    def test_terminal_metadata_error_is_nondurable_and_worker_continues(self):
        held = self.hold_worker()
        queued = self.manager.submit_run_code(self.token, "-- success but state disk full")
        original = self.manager._write_job

        def fail_finish(job):
            if job["job_id"] == queued["job_id"] and job["state"] == "succeeded":
                raise OSError(errno.ENOSPC, "simulated full state mount")
            return original(job)

        with patch.object(self.manager, "_write_job", side_effect=fail_finish):
            self.manager.worker_release.set()
            self.terminal(held)
            status = self.terminal(queued)
            self.manager._job_queue.join()
            self.assertTrue(status["result"]["verified"])
            self.assertFalse(status["metadata_durable"])
            self.assertIn("Errno 28", status["metadata_persistence_error"])
            self.assertIsNone(self.manager._pending_job_for_workspace(self.token))
            next_job = self.manager.submit_run_code(self.token, "-- next simulated proof")
            self.assertEqual(self.terminal(next_job)["state"], "succeeded")
        recovered = self.manager.job_status(queued["job_id"])
        self.assertTrue(recovered["metadata_durable"])
        self.assertNotIn("metadata_persistence_error", recovered)
        self.assertTrue(self.manager._job_worker_threads[0].is_alive())

    def test_partial_metadata_temporary_file_is_removed(self):
        job = {
            "job_id": "job_" + secrets.token_hex(16), "state": "queued",
            "submitted_at": time.time(),
        }
        self.manager._write_job(job)
        original = Path.write_text

        def partial_write(path, data, **kwargs):
            if ".tmp." in path.name:
                original(path, "partial", **kwargs)
                raise OSError(errno.ENOSPC, "simulated partial write")
            return original(path, data, **kwargs)

        with patch.object(Path, "write_text", partial_write):
            with self.assertRaises(OSError):
                self.manager._write_job({**job, "state": "running"})
        self.assertEqual(self.manager._read_job(job["job_id"])["state"], "queued")
        self.assertEqual(list(self.manager.jobs.glob("*.tmp.*")), [])

    def assert_process_exited(self, pid):
        deadline = time.monotonic() + 2
        while time.monotonic() < deadline:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                return
            identity = self.manager._process_identity(pid)
            if identity is not None and identity["state"] == "Z":
                return
            time.sleep(0.01)
        self.fail(f"Disposable child {pid} did not exit")

    def test_streaming_timeout_kills_child_session(self):
        code = (
            "import subprocess,sys,time; "
            "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)']); "
            "print('CHILD_PID='+str(p.pid),flush=True); time.sleep(60)"
        )
        with self.assertRaises(subprocess.TimeoutExpired) as caught:
            self.manager._run_streaming(
                [sys.executable, "-c", code], cwd=self.project, timeout=1, phase="building",
            )
        pid = int(re.search(r"CHILD_PID=(\d+)", caught.exception.output).group(1))
        self.assert_process_exited(pid)

    def test_progress_metadata_failure_kills_live_child_session(self):
        pid_file = self.root / "child.pid"
        code = (
            "import subprocess,sys,time; from pathlib import Path; "
            "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)']); "
            "Path(sys.argv[1]).write_text(str(p.pid)); "
            "print('[1/2] Active',flush=True); time.sleep(60)"
        )
        original = self.manager._set_job_progress

        def progress(phase, **kwargs):
            if kwargs.get("detail") == "Active":
                raise OSError(errno.ENOSPC, "simulated progress metadata error")
            return original(phase, **kwargs)

        with patch.object(self.manager, "_set_job_progress", side_effect=progress):
            with self.assertRaises(OSError):
                self.manager._run_streaming(
                    [sys.executable, "-c", code, str(pid_file)],
                    cwd=self.project, timeout=3, phase="building",
                )
        self.assert_process_exited(int(pid_file.read_text()))

    def test_orphaned_live_process_blocks_replay_until_process_exits(self):
        process = subprocess.Popen(
            [sys.executable, "-c", "import time; time.sleep(60)"], start_new_session=True,
        )
        try:
            job = {
                "job_id": "job_" + secrets.token_hex(16), "workspace_token": self.token,
                "kind": "build", "arguments": {}, "state": "running",
                "submitted_at": time.time(), "owner_id": secrets.token_hex(16),
                # Some isolated test runtimes expose host /proc with namespace
                # PIDs. An unidentifiable child must also block unsafe replay.
                "process": self.manager._process_identity(process.pid) or {"pid": process.pid},
            }
            self.manager._write_job(job)
            status = self.manager.job_status(job["job_id"])
            self.assertFalse(status["liveness"]["owner_alive"])
            self.assertIsNot(status["liveness"]["process_alive"], False)
            self.assertFalse(status["terminal"])
            with self.assertRaises(RuntimeError):
                self.manager.submit_run_code(self.token, "-- forbidden replay")
        finally:
            self.manager._kill_verification_group(process)
        self.assertEqual(self.manager.job_status(job["job_id"])["state"], "interrupted")

    def test_silent_live_job_heartbeat_is_not_a_progress_or_failure_claim(self):
        held = self.hold_worker()
        process = subprocess.Popen(
            [sys.executable, "-c", "import time; time.sleep(60)"], start_new_session=True,
        )
        try:
            self.manager._job_local.job_id = held["job_id"]
            before = self.manager._read_job(held["job_id"])["progress"]
            self.manager._job_command_heartbeat(process, force=True)
            status = self.manager.job_status(held["job_id"])
            self.assertTrue(status["liveness"]["process_alive"])
            self.assertLess(status["liveness"]["heartbeat_age_seconds"], 1)
            self.assertEqual(status["progress"]["updated_at"], before["updated_at"])
            self.assertEqual(status["state"], "running")
        finally:
            self.manager._kill_verification_group(process)
            self.manager._clear_job_command()
            self.manager._job_local.job_id = None
            self.manager.worker_release.set()
        self.terminal(held)

    def test_diagnostics_is_read_only_and_reports_server_mounts(self):
        with patch.object(self.manager, "_get", side_effect=AssertionError("must not restore")):
            result = self.manager.diagnostics(self.token)
        self.assertIn("temporary_files", result["filesystems"])
        self.assertEqual(result["filesystems"]["workspace"]["path"], str(self.project))
        self.assertGreaterEqual(result["filesystems"]["job_state"]["available_bytes"], 0)
        self.assertGreaterEqual(result["filesystems"]["job_state"]["available_inodes"], 0)
        self.assertEqual(result["worker_threads_alive"], self.manager.job_workers)

    def test_legacy_running_record_cannot_certify_children_stopped(self):
        job = {
            "job_id": "job_" + secrets.token_hex(16), "workspace_token": self.token,
            "kind": "build", "arguments": {}, "state": "running",
            "submitted_at": time.time(), "owner_id": secrets.token_hex(16),
        }
        self.manager._write_job(job)
        status = self.manager.job_status(job["job_id"])
        self.assertFalse(status["liveness"]["owner_alive"])
        self.assertIsNone(status["liveness"]["process_alive"])
        self.assertFalse(status["terminal"])
        with self.assertRaises(RuntimeError):
            self.manager.submit_run_code(self.token, "-- unsafe legacy replay")

    def test_launch_marker_is_durable_before_popen_and_start_failure_clears_it(self):
        held = self.hold_worker()
        queued = self.manager.submit_run_code(self.token, "-- simulated launch failure")
        observed = []
        real_popen = subprocess.Popen

        def before_launch(*args, **kwargs):
            if args[0][0] != "lake":
                return real_popen(*args, **kwargs)
            job = self.manager._read_job(queued["job_id"])
            observed.append(job["process"])
            raise FileNotFoundError("simulated unavailable executable")

        with patch("agent_workspaces.subprocess.Popen", side_effect=before_launch):
            self.manager.worker_release.set()
            self.terminal(held)
            status = self.terminal(queued)
        self.assertEqual(observed, [{"launch_in_progress": True}])
        self.assertIsNone(status["process"])
        self.assertEqual(status["result"]["classification"], "process_error")

    def test_launch_window_orphan_blocks_other_workspace_and_queued_execution(self):
        held = self.hold_worker()
        queued = self.manager.submit_run_code(self.token, "-- wait behind orphan")
        orphan_token, _ = self.workspace()
        orphan = {
            "job_id": "job_" + secrets.token_hex(16), "workspace_token": orphan_token,
            "kind": "build", "arguments": {}, "state": "running",
            "submitted_at": time.time(), "owner_id": secrets.token_hex(16),
            "process_tracking_version": 1, "process": {"launch_in_progress": True},
        }
        self.manager._write_job(orphan)
        try:
            status = self.manager.job_status(orphan["job_id"])
            self.assertIsNone(status["liveness"]["process_alive"])
            third_token, _ = self.workspace()
            with self.assertRaisesRegex(RuntimeError, "shared caches"):
                self.manager.submit_run_code(third_token, "-- unsafe second build")
            self.manager.worker_release.set()
            self.terminal(held)
            deadline = time.monotonic() + 2
            while time.monotonic() < deadline:
                waiting = self.manager.job_status(queued["job_id"])
                if waiting["progress"]["phase"] == "waiting_for_orphan":
                    break
                time.sleep(0.01)
            self.assertEqual(waiting["progress"]["phase"], "waiting_for_orphan")
            self.assertEqual(self.manager.executions, ["build"])
        finally:
            # Simulate an administrator's confirmed termination; no child exists
            # in this fixture. Never infer this from old progress in production.
            self.manager._write_job({**orphan, "state": "interrupted", "finished_at": time.time()})
            self.manager.worker_release.set()
        self.assertEqual(self.terminal(queued)["state"], "succeeded")

    def test_recorded_pid_reuse_does_not_identify_new_process_as_old_job(self):
        job = {"job_id": "job_" + secrets.token_hex(16), "state": "running", "process": {
            "pid": 123, "start_ticks": "100", "boot_id": "old-boot",
        }}
        current = {"pid": 123, "start_ticks": "200", "boot_id": "new-boot", "state": "R"}
        with patch.object(self.manager, "_process_identity", return_value=current):
            with patch.object(self.manager, "_process_group_alive", return_value=False):
                self.assertIs(self.manager._job_process_alive(job), False)
            with patch.object(self.manager, "_process_group_alive", return_value=True):
                self.assertIsNone(self.manager._job_process_alive(job))

    def test_heavy_slot_rechecks_orphan_after_lock_acquisition(self):
        orphan = {"job_id": "job_" + secrets.token_hex(16)}
        # Owner exits between first scan and flock acquisition. Work must wait
        # through the second scan and another orphan scan before it can enter.
        scans = [None, orphan, orphan, None, None]
        delays = []
        with patch.object(self.manager, "_orphaned_running_job", side_effect=scans) as probe:
            with patch("agent_workspaces.time.sleep", side_effect=delays.append):
                with self.manager._heavy_worker_slot():
                    self.assertEqual(probe.call_count, 5)
        self.assertEqual(delays, [0.05, 0.05])

    def test_synchronous_command_timeout_also_closes_child_session(self):
        pid_file = self.root / "ordinary-child.pid"
        code = (
            "import subprocess,sys,time; from pathlib import Path; "
            "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(60)']); "
            "Path(sys.argv[1]).write_text(str(p.pid)); time.sleep(60)"
        )
        with self.assertRaises(subprocess.TimeoutExpired):
            self.manager._run(
                [sys.executable, "-c", code, str(pid_file)], cwd=self.project, timeout=1,
            )
        self.assert_process_exited(int(pid_file.read_text()))

    def test_prompt_enqueue_poll_and_exact_code_identity(self):
        self.assertEqual(self.manager.job_workers, 1)
        held = self.hold_worker()
        code = "-- exact Unicode bytes: α\ntheorem sample : True := by trivial\n"
        started = time.monotonic()
        with patch.object(self.manager, "_get", side_effect=AssertionError("admission must not restore")):
            queued = self.manager.submit_run_code(self.token, code, 17)
            duplicate = self.manager.submit_run_code(self.token, code, 17)
            for _ in range(5):
                status = self.manager.job_status(queued["job_id"])
                self.assertEqual(status["state"], "queued")
            for changed_code, timeout in ((code + "\n", 17), (code, 18)):
                with self.assertRaisesRegex(RuntimeError, queued["job_id"]):
                    self.manager.submit_run_code(self.token, changed_code, timeout)
            with self.assertRaisesRegex(RuntimeError, queued["job_id"]):
                self.manager.submit_check_file(self.token, "RiemannResearch/Basic.lean")
        self.assertLess(time.monotonic() - started, 1.0)
        self.assertEqual(self.manager.executions, ["build"])
        self.assertTrue(queued["accepted"])
        self.assertTrue(duplicate["existing"])
        self.assertEqual(queued["job_id"], duplicate["job_id"])
        expected = hashlib.sha256(json.dumps({
            "workspace_token": self.token, "kind": "run_code",
            "arguments": {"code": code, "timeout_seconds": 17},
        }, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()).hexdigest()
        self.assertEqual(queued["request_sha256"], expected)
        self.assertEqual(status["code_sha256"], hashlib.sha256(code.encode()).hexdigest())
        self.manager.worker_release.set()
        self.terminal(held)
        finished = self.terminal(queued)
        self.assertEqual(finished["result"]["request_sha256"], expected)
        self.assertEqual(finished["result"]["code_sha256"], status["code_sha256"])

    def test_success_error_limits_and_cleanup(self):
        for code, classification in (
            ("-- fine", "success"), ("-- FAIL", "compiler_error"),
            ("-- HEARTBEAT", "compiler_error"), ("-- RECURSION", "compiler_error"),
            ("-- FLOOD", "success"), ("-- FLOOD FAIL", "compiler_error"),
        ):
            with self.subTest(code=code):
                queued = self.manager.submit_run_code(self.token, code)
                status = self.terminal(queued)
                result = status["result"]
                success = classification == "success"
                self.assertEqual(status["state"], "succeeded" if success else "failed")
                self.assertEqual(result["classification"], classification)
                self.assertEqual(result["exit_code"], 0 if success else 1)
                self.assertEqual(result["verified"], success)
                self.assertTrue(result["temporary_file_removed"])
                self.assertGreaterEqual(result["elapsed_seconds"], 0)
                self.assertLessEqual(len(result["output"]), 4000 if success else 8000)
                self.assertEqual(result["output_truncated"], "FLOOD" in code)
                if "FLOOD" in code:
                    self.assertIn("last-diagnostic", result["output"])
                self.assertNotIn("output", self.manager.job_status(queued["job_id"])["result"])
                self.assertFalse(list((self.project / ".lake" / "agent-scratch").glob("*.lean")))

    def test_timeout_preserves_diagnostics_kills_group_and_reaps_parent(self):
        children = []
        real_popen = subprocess.Popen

        def tracked_popen(*args, **kwargs):
            child = real_popen(*args, **kwargs)
            if args[0][0] == "lake":
                children.append(child)
            return child

        with patch("agent_workspaces.subprocess.Popen", side_effect=tracked_popen):
            queued = self.manager.submit_run_code(self.token, "-- TIMEOUT", 1)
            result = self.terminal(queued)["result"]
        self.assertEqual(result["classification"], "wall_timeout")
        self.assertFalse(result["verified"])
        self.assertIn("before-timeout", result["output"])
        self.assertTrue(result["temporary_file_removed"])
        self.assertGreaterEqual(result["elapsed_seconds"], 1)
        self.assertLess(result["elapsed_seconds"], 3)
        self.assertEqual(len(children), 1)
        self.assertEqual(children[0].returncode, -9)
        with self.assertRaises(ChildProcessError):
            os.waitpid(children[0].pid, os.WNOHANG)
        descendant = int(re.search(r"CHILD_PID=(\d+)", result["output"])[1])
        self.assert_process_exited(descendant)
        self.assertFalse(list((self.project / ".lake" / "agent-scratch").glob("*.lean")))

    def test_cleanup_failure_is_not_reported_as_removed(self):
        unlink = Path.unlink

        def deny_scratch(path, *args, **kwargs):
            if path.name.startswith("Run_"):
                raise PermissionError("simulated cleanup denial")
            return unlink(path, *args, **kwargs)

        with patch.object(Path, "unlink", deny_scratch):
            result = self.terminal(self.manager.submit_run_code(self.token, "-- fine"))["result"]
        self.assertFalse(result["temporary_file_removed"])
        self.assertIn("cleanup denial", result["cleanup_error"])
        for path in (self.project / ".lake" / "agent-scratch").glob("*.lean"):
            path.unlink()

    def test_process_signal_and_startup_failures_are_not_lean_diagnostics(self):
        result = self.terminal(self.manager.submit_run_code(self.token, "-- SIGNAL"))["result"]
        self.assertEqual(result["classification"], "process_error")
        self.assertEqual(result["exit_code"], -9)
        real_popen = subprocess.Popen

        def missing_lake(*args, **kwargs):
            if args[0][0] == "lake":
                raise FileNotFoundError("missing lake")
            return real_popen(*args, **kwargs)

        with patch("agent_workspaces.subprocess.Popen", side_effect=missing_lake):
            result = self.terminal(self.manager.submit_run_code(self.token, "-- cannot start"))["result"]
        self.assertEqual(result["classification"], "process_error")
        self.assertIsNone(result["exit_code"])
        self.assertIn("missing lake", result["error"])
        self.assertTrue(result["temporary_file_removed"])

    def test_published_workspace_accepts_verification_before_and_after_resume(self):
        meta = self.manager._read_meta(self.token)
        meta["state"] = "published"
        self.manager._write_meta(meta)
        self.assertEqual(self.terminal(self.manager.submit_run_code(self.token, "-- published"))["state"],
                         "succeeded")
        with patch.object(self.manager, "_dependency_key", return_value="offline-test"), \
             patch.object(self.manager, "_rehydrate", side_effect=AssertionError("must not restore")):
            self.assertEqual(self.manager.open(self.token)["state"], "published")
        self.assertEqual(self.terminal(self.manager.submit_check_file(
            self.token, "RiemannResearch/Basic.lean"))["state"], "succeeded")

    def test_invalid_code_timeout_and_workspace_rejected_before_enqueue(self):
        for code in (None, "", " \n", "\x00", "x" * (MAX_PATCH_BYTES + 1)):
            with self.subTest(code_size=len(code) if code is not None else None):
                with self.assertRaises(ValueError):
                    self.manager.submit_run_code(self.token, code)
        for timeout in (0, -1, 1801, 1.5, "1", True, None):
            for method, arg in ((self.manager.submit_run_code, "-- fine"),
                                (self.manager.submit_check_file, "RiemannResearch/Basic.lean")):
                with self.assertRaises(ValueError):
                    method(self.token, arg, timeout)
        for token in ("bad-token", "ws_" + "z" * 24):
            with self.assertRaises(ValueError):
                self.manager.submit_run_code(token, "-- fine")
        meta = self.manager._read_meta(self.token)
        meta["needs_rehydrate"] = True
        self.manager._write_meta(meta)
        # Opt-in retention still requires replacement-based restoration;
        # preserve mode instead verifies the retained local source revision.
        with patch.object(self.manager, "storage_policy", "retention"):
            with self.assertRaisesRegex(ValueError, "Resume"):
                self.manager.submit_run_code(self.token, "-- fine")
        self.assertEqual(list(self.manager.jobs.glob("job_*.json")), [])

    def test_invalid_file_paths_and_size_rejected_before_enqueue(self):
        (self.project / "tools").mkdir()
        (self.project / "tools" / "private.lean").write_text("-- private")
        outside = self.root / "outside.lean"
        outside.write_text("-- outside")
        (self.project / "RiemannResearch" / "Escape.lean").symlink_to(outside)
        large = self.project / "RiemannResearch" / "Large.lean"
        large.write_bytes(b"x" * (MAX_READ_BYTES + 1))
        for path in ("", None, "\x00", "README.md", "../outside.lean", "tools/private.lean",
                     ".lake/hidden.lean", "RiemannResearch/Missing.lean", "RiemannResearch",
                     "RiemannResearch/Escape.lean", "RiemannResearch/Large.lean",
                     str(self.project / "RiemannResearch/Basic.lean"), "x" * 4097):
            with self.subTest(path=path):
                with self.assertRaises(ValueError):
                    self.manager.submit_check_file(self.token, path)
        self.assertEqual(list(self.manager.jobs.glob("job_*.json")), [])

    def test_file_queue_exact_identity_and_persistent_results(self):
        self.hold_worker()
        path = "RiemannResearch/Basic.lean"
        contents = (self.project / path).read_bytes()
        queued = self.manager.submit_check_file(self.token, path, 11)
        duplicate = self.manager.submit_check_file(self.token, path, 11)
        self.assertTrue(duplicate["existing"])
        self.assertEqual(queued["job_id"], duplicate["job_id"])
        for changed_path, timeout in (("RiemannResearch/Other.lean", 11), (path, 12),
                                      ("RiemannResearch/./Basic.lean", 11)):
            with self.assertRaisesRegex(RuntimeError, queued["job_id"]):
                self.manager.submit_check_file(self.token, changed_path, timeout)
        self.manager.worker_release.set()
        completed = self.terminal(queued)
        self.assertEqual(completed["state"], "succeeded")
        self.assertEqual(completed["file_sha256"], hashlib.sha256(contents).hexdigest())
        self.assertEqual(completed["result"]["checked_file_sha256"], completed["file_sha256"])
        self.assertIsNone(completed["result"]["temporary_file_removed"])
        self.assertEqual((self.project / path).read_bytes(), contents)
        self.assertFalse((self.project / ".lake" / "agent-scratch").exists())
        second = self.new_manager()
        reloaded = second.job_status(queued["job_id"], include_logs=True)
        self.assertEqual(reloaded["result"], completed["result"])
        self.assertEqual(reloaded["request_sha256"], queued["request_sha256"])
        root_check = self.manager.submit_check_file(self.token, "RiemannResearch.lean")
        self.assertEqual(self.terminal(root_check)["result"]["classification"], "success")

    def test_changed_file_before_execution_fails_without_verification(self):
        self.hold_worker()
        path = "RiemannResearch/Basic.lean"
        queued = self.manager.submit_check_file(self.token, path)
        original_hash = self.manager.job_status(queued["job_id"])["file_sha256"]
        (self.project / path).write_text("-- changed after admission")
        with self.assertRaisesRegex(RuntimeError, queued["job_id"]):
            self.manager.submit_check_file(self.token, path)
        with patch.object(self.manager, "_run_verification", side_effect=AssertionError("must not run")):
            self.manager.worker_release.set()
            status = self.terminal(queued)
        self.assertEqual(status["state"], "failed")
        self.assertIn("changed after submission", status["error"])
        self.assertEqual(status["file_sha256"], original_hash)
        self.assertNotIn("result", status)

    def test_changed_file_during_execution_invalidates_result(self):
        path = "RiemannResearch/Basic.lean"
        real_run = self.manager._run_verification

        def change_during(project, resolved, timeout):
            result = real_run(project, resolved, timeout)
            resolved.write_text("-- changed during verification")
            return result

        with patch.object(self.manager, "_run_verification", side_effect=change_during):
            status = self.terminal(self.manager.submit_check_file(self.token, path))
        self.assertEqual(status["state"], "failed")
        self.assertEqual(status["result"]["classification"], "source_changed")
        self.assertFalse(status["result"]["verified"])

    def test_new_manager_preserves_live_owner_and_deduplicates_across_managers(self):
        held = self.hold_worker()
        queued = self.manager.submit_run_code(self.token, "-- queued")
        second = self.new_manager()
        self.assertEqual(second.job_status(held["job_id"])["state"], "running")
        self.assertEqual(second.job_status(queued["job_id"])["state"], "queued")
        duplicate = second.submit_run_code(self.token, "-- queued")
        self.assertEqual(duplicate["job_id"], queued["job_id"])
        with self.assertRaisesRegex(RuntimeError, queued["job_id"]):
            second.submit_run_code(self.token, "-- different")
        self.manager.worker_release.set()
        self.assertEqual(self.terminal(queued, second)["state"], "succeeded")

    def test_abandoned_jobs_interrupted_not_replayed_and_completed_preserved(self):
        completed = self.terminal(self.manager.submit_run_code(self.token, "-- done"))
        abandoned = []
        for state in ("queued", "running"):
            job = {
                "job_id": "job_" + secrets.token_hex(16), "workspace_token": self.token,
                "kind": "checkpoint", "arguments": {"message": "Never publish", "push": True},
                "state": state, "submitted_at": time.time(), "owner_id": secrets.token_hex(16),
                "process_tracking_version": 1,
            }
            self.manager._write_job(job)
            abandoned.append(job["job_id"])
        second = self.new_manager()
        for job_id in abandoned:
            status = second.job_status(job_id)
            self.assertEqual(status["state"], "interrupted")
            self.assertIn("not replayed", status["error"])
        self.assertEqual(second.executions, [])
        self.assertEqual(second.job_status(completed["job_id"], include_logs=True)["result"],
                         completed["result"])

    def test_owner_exit_recovered_by_already_running_manager_status_and_admission(self):
        owner = secrets.token_hex(16)
        script = (
            "import fcntl, sys; "
            "f = open(sys.argv[1], 'a+'); fcntl.flock(f, fcntl.LOCK_EX); "
            "print('leased', flush=True); sys.stdin.read()"
        )
        process = subprocess.Popen(
            [sys.executable, "-c", script, str(self.manager._owner_directory / owner)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
        )
        jobs = []
        try:
            self.assertEqual(process.stdout.readline().strip(), "leased")
            second_token, _ = self.workspace()
            for token in (self.token, second_token):
                job = {
                    "job_id": "job_" + secrets.token_hex(16), "workspace_token": token,
                    "kind": "checkpoint", "arguments": {"message": "Never publish", "push": True},
                    "state": "running", "submitted_at": time.time(), "owner_id": owner,
                    "process_tracking_version": 1,
                }
                self.manager._write_job(job)
                jobs.append(job)
                self.assertEqual(self.manager.job_status(job["job_id"])["state"], "running")
        finally:
            process.communicate(timeout=2)
        self.assertEqual(self.manager.job_status(jobs[0]["job_id"])["state"], "interrupted")
        submitted = self.manager.submit_run_code(second_token, "-- after owner exit")
        self.assertEqual(self.manager._read_job(jobs[1]["job_id"])["state"], "interrupted")
        self.assertEqual(self.terminal(submitted)["state"], "succeeded")

    def test_list_jobs_recovers_terminal_and_active_ids_without_request_contents(self):
        first = self.manager.submit_run_code(self.token, "-- private proof contents")
        self.terminal(first)
        second = self.manager.submit_check_file(self.token, "RiemannResearch/Basic.lean")
        self.terminal(second)
        self.hold_worker()
        third = self.manager.submit_run_code(self.token, "-- another private proof")
        listing = self.manager.list_jobs(self.token, limit=2)
        self.assertEqual(listing["total_matches"], 3)
        self.assertTrue(listing["truncated"])
        self.assertEqual([job["job_id"] for job in listing["jobs"]],
                         [third["job_id"], second["job_id"]])
        self.assertFalse(listing["jobs"][0]["terminal"])
        self.assertTrue(listing["jobs"][1]["terminal"])
        for job in listing["jobs"]:
            self.assertEqual(set(job), {"job_id", "kind", "state", "request_sha256", "submitted_at", "terminal"})
        self.assertNotIn("private proof", json.dumps(listing))
        for limit in (0, 101, 1.5, True):
            with self.assertRaises(ValueError):
                self.manager.list_jobs(self.token, limit)
        self.manager.worker_release.set()
        self.terminal(third)
        reloaded = self.new_manager().list_jobs(self.token)
        self.assertEqual(reloaded["jobs"][0]["job_id"], third["job_id"])
        self.assertTrue(all(job["terminal"] for job in reloaded["jobs"]))

    def test_inflight_patch_blocks_verification_but_not_admission_poll_or_reads(self):
        patch_entered = threading.Event()
        patch_release = threading.Event()
        errors = []
        original_run = self.manager._run
        source = self.project / "RiemannResearch/Basic.lean"

        def blocked_patch(args, **kwargs):
            if args[:2] == ["git", "apply"]:
                if "--check" in args:
                    patch_entered.set()
                    if not patch_release.wait(3):
                        raise RuntimeError("test did not release mutation")
                else:
                    source.write_text("-- changed by managed patch")
                return ""
            return original_run(args, **kwargs)

        def mutate():
            try:
                self.manager.apply_patch(self.token, "+++ b/RiemannResearch/Basic.lean\n")
            except Exception as exc:
                errors.append(exc)

        with patch.object(self.manager, "_run", side_effect=blocked_patch), \
             patch.object(self.manager, "_architecture_audit", return_value=[]), \
             patch.object(self.manager, "_run_verification", side_effect=AssertionError("must not check changed source")):
            thread = threading.Thread(target=mutate)
            thread.start()
            try:
                self.assertTrue(patch_entered.wait(1))
                started = time.monotonic()
                queued = self.manager.submit_check_file(self.token, "RiemannResearch/Basic.lean")
                deadline = time.monotonic() + 1
                while time.monotonic() < deadline:
                    status = self.manager.job_status(queued["job_id"])
                    if status["progress"]["phase"] == "waiting_for_workspace":
                        break
                    time.sleep(0.01)
                self.assertEqual(status["progress"]["phase"], "waiting_for_workspace")
                self.assertIn("theorem sample", self.manager.read_file(
                    self.token, "RiemannResearch/Basic.lean")["content"])
                self.assertLess(time.monotonic() - started, 1)
            finally:
                patch_release.set()
                thread.join(3)
            status = self.terminal(queued)
        self.assertFalse(thread.is_alive())
        self.assertEqual(errors, [])
        self.assertEqual(status["state"], "failed")
        self.assertIn("changed after submission", status["error"])

    def test_read_file_and_status_remain_responsive_during_compiler_execution(self):
        entered = threading.Event()
        release = threading.Event()
        original_run = self.manager._run_verification

        def blocked_run(*args):
            entered.set()
            if not release.wait(3):
                raise RuntimeError("test did not release compiler")
            return original_run(*args)

        with patch.object(self.manager, "_run_verification", side_effect=blocked_run):
            queued = self.manager.submit_run_code(self.token, "-- held compiler")
            try:
                self.assertTrue(entered.wait(1))
                metadata_before = self.manager._read_meta(self.token)
                started = time.monotonic()
                self.assertIn("theorem sample", self.manager.read_file(
                    self.token, "RiemannResearch/Basic.lean")["content"])
                self.assertEqual(self.manager.job_status(queued["job_id"])["state"], "running")
                self.assertLess(time.monotonic() - started, 0.5)
                self.assertEqual(self.manager._read_meta(self.token), metadata_before)
            finally:
                release.set()
            self.assertEqual(self.terminal(queued)["state"], "succeeded")

    def test_two_managed_mutations_do_not_overlap(self):
        entered = threading.Event()
        release = threading.Event()
        second_attempted = threading.Event()
        errors = []
        active = 0
        maximum = 0
        checks = 0
        guard = threading.Lock()

        def simulated_patch(args, **kwargs):
            nonlocal active, maximum, checks
            self.assertEqual(args[:2], ["git", "apply"])
            if "--check" in args:
                with guard:
                    active += 1
                    checks += 1
                    maximum = max(maximum, active)
                entered.set()
                if not release.wait(3):
                    raise RuntimeError("test did not release patch")
            else:
                with guard:
                    active -= 1
            return ""

        def mutate(second=False):
            if second:
                second_attempted.set()
            try:
                self.manager.apply_patch(self.token, "+++ b/RiemannResearch/Basic.lean\n")
            except Exception as exc:
                errors.append(exc)

        with patch.object(self.manager, "_run", side_effect=simulated_patch), \
             patch.object(self.manager, "_architecture_audit", return_value=[]):
            first = threading.Thread(target=mutate)
            second = threading.Thread(target=mutate, args=(True,))
            first.start()
            try:
                self.assertTrue(entered.wait(1))
                second.start()
                self.assertTrue(second_attempted.wait(1))
                self.assertEqual(checks, 1)
            finally:
                release.set()
                first.join(3)
                second.join(3)
        self.assertEqual(errors, [])
        self.assertEqual(checks, 2)
        self.assertEqual(maximum, 1)

    def test_external_process_worker_lock_keeps_submission_and_poll_responsive(self):
        script = (
            "import fcntl, sys; "
            "f = open(sys.argv[1], 'a+'); fcntl.flock(f, fcntl.LOCK_EX); "
            "print('locked', flush=True); sys.stdin.read()"
        )
        process = subprocess.Popen(
            [sys.executable, "-c", script, str(self.manager.state / ".heavy-worker-0.lock")],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
        )
        try:
            self.assertEqual(process.stdout.readline().strip(), "locked")
            started = time.monotonic()
            queued = self.manager.submit_run_code(self.token, "-- waiting for external slot")
            deadline = time.monotonic() + 1
            while time.monotonic() < deadline:
                status = self.manager.job_status(queued["job_id"])
                if status["progress"]["phase"] == "waiting_for_worker":
                    break
                time.sleep(0.01)
            self.assertLess(time.monotonic() - started, 1)
            self.assertEqual(status["progress"]["phase"], "waiting_for_worker")
            self.assertEqual(self.manager.executions, [])
        finally:
            process.communicate(timeout=2)
        self.assertEqual(self.terminal(queued)["state"], "succeeded")

    def test_changed_checkpoint_arguments_do_not_reuse_existing_job(self):
        self.hold_worker()
        queued = self.manager.submit_checkpoint(self.token, "Test checkpoint", push=False)
        duplicate = self.manager.submit_checkpoint(self.token, "Test checkpoint", push=False)
        self.assertEqual(duplicate["job_id"], queued["job_id"])
        for message, push in (("Other checkpoint", False), ("Test checkpoint", True)):
            with self.assertRaisesRegex(RuntimeError, queued["job_id"]):
                self.manager.submit_checkpoint(self.token, message, push=push)
        # Never run a checkpoint, even against the offline temporary repository.
        with patch.object(self.manager, "checkpoint", return_value={"test_only": True}):
            self.manager.worker_release.set()
            self.terminal(queued)


if __name__ == "__main__":
    unittest.main(verbosity=2)
