"""Offline subprocess and lifecycle checks for editor cache coordination."""

import ast
import asyncio
from contextlib import contextmanager
import fcntl
import json
import os
from pathlib import Path
import re
import select
import subprocess
import sys
import tempfile
import threading
from types import SimpleNamespace
import unittest
from unittest.mock import patch


WRAPPER = Path(__file__).with_name("lean_cache_lake.py")
MCP_SOURCE = Path(__file__).with_name("lean_workspace_mcp.py")
HEADER = '{"imports":[{"module":"RiemannResearch.Sample"}]}\n'
FAKE_LAKE = r'''
import json
import os
from pathlib import Path
import sys

args = sys.argv[1:]
state = Path(os.environ["EDITOR_CACHE_TEST_STATE"])
header = sys.stdin.buffer.readline().decode() if "-" in args else None
with (state / "commands.jsonl").open("a") as log:
    log.write(json.dumps({"args":args,"header":header,"lease":os.environ.get("LEAN_NATIVE_CACHE_LOCK_HELD")}) + "\n")
mode = os.environ.get("EDITOR_CACHE_TEST_MODE", "")
if args[:1] == ["env"]:
    # Native Lake augments child environments with its own executable as LAKE.
    environment = {**os.environ, "LAKE": sys.argv[0]}
    os.execvpe(args[1], args[1:], environment)
elif args[:2] == ["cache", "get"]:
    print("metadata fetched")
    print("cache diagnostic", file=sys.stderr)
    if mode == "auth":
        print("HTTP 403: denied", file=sys.stderr)
        sys.exit(22)
    (state / "ready").touch()
elif "setup-file" in args:
    if mode == "compiler":
        print("compiler diagnostic", file=sys.stderr)
        sys.exit(1)
    if not (state / "ready").exists():
        print("discarded probe output")
        print("probe diagnostic", file=sys.stderr)
        sys.exit(3)
    print(json.dumps({"name":"Sample","header":header}))
    print("setup diagnostic", file=sys.stderr)
else:
    print("passed through")
'''


class EditorLakeTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.state = self.root / "state"
        self.state.mkdir()
        self.lake = self.root / "lake"
        self.lake.write_text("#!" + sys.executable + "\n" + FAKE_LAKE)
        self.lake.chmod(0o755)
        self.cache = self.root / "cache"
        environment = patch.dict(os.environ, {
            "LEAN_CACHE_LAKE_BINARY": str(self.lake),
            "LEAN_REMOTE_CACHE_SERVICE": "gcs",
            "LAKE_CACHE_DIR": str(self.cache),
            "LEAN_NATIVE_CACHE_LOCK_HELD": "",
            "EDITOR_CACHE_TEST_STATE": str(self.state),
            "EDITOR_CACHE_TEST_MODE": "",
        })
        environment.start()
        self.addCleanup(environment.stop)

    def commands(self):
        return [json.loads(line) for line in (self.state / "commands.jsonl").read_text().splitlines()]

    def invoke(self, *args, marker=None):
        environment = dict(os.environ)
        if marker is not None:
            environment["LEAN_NATIVE_CACHE_LOCK_HELD"] = marker
        return subprocess.run(
            [sys.executable, str(WRAPPER), *args], input=HEADER,
            capture_output=True, text=True, timeout=3, env=environment,
        )

    def test_setup_replays_one_header_keeps_no_build_and_returns_only_final_json(self):
        result = self.invoke("setup-file", "Sample.lean", "-", "--no-build", "--no-cache")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["header"], HEADER)
        self.assertNotIn("discarded probe output", result.stdout)
        self.assertNotIn("metadata fetched", result.stdout)
        self.assertIn("metadata fetched", result.stderr)
        self.assertIn("setup diagnostic", result.stderr)
        commands = self.commands()
        self.assertEqual(commands[1]["args"][:3], ["cache", "get", "--mappings-only"])
        for command in (commands[0], commands[2]):
            self.assertEqual(command["header"], HEADER)
            self.assertIn("--no-build", command["args"])
            self.assertNotIn("--no-cache", command["args"])
        self.assertTrue(all(command["lease"] == "1" for command in commands))

    def test_compiler_and_authentication_failures_do_not_retry_setup(self):
        for mode, returncode, count in (("compiler", 1, 1), ("auth", 22, 2)):
            with self.subTest(mode=mode), patch.dict(os.environ, {"EDITOR_CACHE_TEST_MODE": mode}):
                (self.state / "commands.jsonl").unlink(missing_ok=True)
                result = self.invoke("setup-file", "Sample.lean", "-", "--no-build", "--no-cache")
                self.assertEqual(result.returncode, returncode, result.stderr)
                self.assertEqual(len(self.commands()), count)
                self.assertEqual(result.stdout, "")

    def test_stdin_need_not_reach_eof_before_setup_finishes(self):
        (self.state / "ready").touch()
        process = subprocess.Popen(
            [sys.executable, str(WRAPPER), "setup-file", "Sample.lean", "-", "--no-build"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        )
        try:
            process.stdin.write(HEADER)
            process.stdin.flush()
            readable, _, _ = select.select([process.stdout], [], [], 2)
            self.assertTrue(readable, "wrapper waited for EOF instead of one header line")
            self.assertEqual(json.loads(process.stdout.readline())["header"], HEADER)
            process.communicate(timeout=2)
            self.assertEqual(process.returncode, 0)
        finally:
            if process.poll() is None:
                process.kill()
                process.communicate()

    def test_setup_uses_same_exclusive_cross_process_lock_and_honors_parent_marker(self):
        (self.state / "ready").touch()
        lock_path = self.cache.parent / f".{self.cache.name}.lock"
        with lock_path.open("a+") as lock:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
            process = subprocess.Popen(
                [sys.executable, str(WRAPPER), "setup-file", "Sample.lean", "-"],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            )
            try:
                process.stdin.write(HEADER)
                process.stdin.flush()
                readable, _, _ = select.select([process.stdout], [], [], 0.15)
                self.assertEqual(readable, [], "editor setup bypassed another process's lease")
                nested = self.invoke("setup-file", "Sample.lean", "-", marker="1")
                self.assertEqual(nested.returncode, 0, nested.stderr)
            finally:
                fcntl.flock(lock.fileno(), fcntl.LOCK_UN)
                if process.poll() is None:
                    stdout, stderr = process.communicate(timeout=2)
                    self.assertEqual(process.returncode, 0, stderr)
                    self.assertEqual(json.loads(stdout)["header"], HEADER)

    def test_serve_passes_through_without_a_lifetime_cache_lease(self):
        lock_path = self.cache.parent / f".{self.cache.name}.lock"
        with lock_path.open("a+") as lock:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
            result = self.invoke("serve", "--")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "passed through")
        self.assertEqual(self.commands()[0]["args"], ["serve", "--"])


class RecordingGuard:
    def __init__(self):
        self.lock = threading.RLock()
        self.exits = []
        self.on_exit = lambda: None

    def __enter__(self):
        self.lock.acquire()

    def __exit__(self, *args):
        self.exits.append(self.on_exit())
        self.lock.release()


class LifecycleManager:
    def __init__(self, root):
        self.default_verification_backend = "lake"
        self.root = root
        self._outputs_guard = RecordingGuard()
        self.calls = []
        self.pending = False
        self.become_pending_inside_lock = False

    def _ensure_workspace_idle(self, token, operation):
        self.calls.append("idle")
        if self.pending:
            raise RuntimeError("job is running")

    @contextmanager
    def _operation_lock(self, token):
        self.calls.append("workspace lease")
        if self.become_pending_inside_lock:
            self.pending = True
        yield

    @contextmanager
    def _native_cache_lock(self):
        self.calls.append("cache lease")
        yield

    def _cleanup_workspace_outputs(self, project):
        self.calls.append("cleanup")

    def _prune_native_cache(self):
        self.calls.append("prune")


class FakeClient:
    def __init__(self, project, **kwargs):
        self.project = project
        self.kwargs = kwargs
        self.alive = False
        self._transport = SimpleNamespace(_proc=SimpleNamespace(returncode=None))
        self.started = asyncio.Event()
        self.release = None
        self.fail_start = False
        self.close_called = False

    async def start(self):
        self.started.set()
        if self.release is not None:
            await self.release.wait()
        if self.fail_start:
            raise RuntimeError("startup failed after subprocess spawn")
        self.alive = True

    async def close(self):
        self.close_called = True
        # A failed transport close may leave the subprocess alive.


def lifecycle_hooks(manager, client_utils, start, evict):
    names = {
        "_client_process_running", "_workspace_can_archive", "_start_cached_client",
        "_cleanup_closed_client_outputs", "_evict_cached_client",
    }
    parsed = ast.parse(MCP_SOURCE.read_text())
    nodes = [node for node in parsed.body if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name in names]
    namespace = {
        "os": os, "Path": Path, "asyncio": asyncio, "__file__": str(MCP_SOURCE),
        "shutil": SimpleNamespace(which=lambda command: "/usr/bin/lake"),
        "AGENT_WORKSPACES": manager, "lean_client_utils": client_utils,
        "_cache_clients": {}, "_original_start_client": start, "_original_evict_client": evict,
        "TOKEN_RE": re.compile(r"^ws_[A-Za-z0-9_-]{20,80}$"),
    }
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(MCP_SOURCE), "exec"), namespace)
    return namespace


class EditorLifecycleTests(unittest.IsolatedAsyncioTestCase):
    async def asyncSetUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        root = Path(self.temporary.name) / "workspaces"
        self.project = root / ("ws_" + "a" * 24) / "RiemannResearch"
        self.manager = LifecycleManager(root)
        self.clients = []
        self.factory_release = None
        self.fail_start = False

        def factory(project, **kwargs):
            client = FakeClient(project, **kwargs)
            client.release = self.factory_release
            client.fail_start = self.fail_start
            self.clients.append(client)
            return client

        self.client_utils = SimpleNamespace(
            AsyncLeanLSPClient=factory, _max_opened_files=lambda: 2,
            _shared_clients={}, _builds_in_progress=set(),
            logger=SimpleNamespace(exception=lambda *args: None),
        )

        async def start(project):
            return "uncached client"

        async def evict():
            project = next(iter(self.client_utils._shared_clients))
            client = self.client_utils._shared_clients.pop(project)
            client.alive = False
            client._transport._proc.returncode = 0

        self.hooks = lifecycle_hooks(self.manager, self.client_utils, start, evict)
        environment = patch.dict(os.environ, {"LEAN_REMOTE_CACHE_SERVICE": "gcs", "LAKE": "original lake", "LEAN_NATIVE_CACHE_LOCK_HELD": "inherited"})
        environment.start()
        self.addCleanup(environment.stop)

    async def test_start_claim_and_scoped_server_environment(self):
        self.factory_release = asyncio.Event()
        self.manager._outputs_guard.on_exit = lambda: dict(self.hooks["_cache_clients"])
        task = asyncio.create_task(self.hooks["_start_cached_client"](self.project))
        await asyncio.sleep(0)
        self.assertFalse(self.hooks["_workspace_can_archive"](self.project))
        self.assertIsNone(self.manager._outputs_guard.exits[0][self.project])
        self.factory_release.set()
        client = await task
        command = client.kwargs["server_command"]
        self.assertEqual(command[:5], ["/usr/bin/lake", "env", "env", "-u", "LEAN_NATIVE_CACHE_LOCK_HELD"])
        self.assertIn(f"LAKE={WRAPPER}", command)
        self.assertIn("LAKE_RESTORE_ARTIFACTS=true", command)
        self.assertIn("--server", command)
        self.assertNotIn("flock", command)
        self.assertEqual(os.environ["LAKE"], "original lake")
        self.assertNotIn("cache lease", self.manager.calls)

    async def test_bazel_workspace_provisions_editor_dependencies_only_on_demand(self):
        self.manager.default_verification_backend = "bazel"
        calls = []
        self.manager._attach_dependencies = lambda project: calls.append(project)
        await self.hooks["_start_cached_client"](self.project)
        self.assertEqual(calls, [self.project])

    async def test_retired_client_remains_protected_until_process_exits(self):
        client = FakeClient(str(self.project))
        self.hooks["_cache_clients"][self.project] = client
        self.assertFalse(client.alive)
        self.assertFalse(self.hooks["_workspace_can_archive"](self.project))
        client._transport._proc.returncode = 0
        self.assertTrue(self.hooks["_workspace_can_archive"](self.project))
        self.assertNotIn(self.project, self.hooks["_cache_clients"])

    async def test_previous_live_process_blocks_replacement_start(self):
        previous = FakeClient(str(self.project))
        self.hooks["_cache_clients"][self.project] = previous
        with self.assertRaisesRegex(ValueError, "previous Lean server is still closing"):
            await self.hooks["_start_cached_client"](self.project)
        self.assertIs(self.hooks["_cache_clients"][self.project], previous)
        self.assertEqual(self.clients, [])
        previous._transport._proc.returncode = 0
        replacement = await self.hooks["_start_cached_client"](self.project)
        self.assertIs(self.hooks["_cache_clients"][self.project], replacement)

    async def test_native_lake_environment_rewrite_still_reaches_setup_wrapper(self):
        root = Path(self.temporary.name)
        state = root / "state"
        state.mkdir()
        binary_dir = root / "bin"
        binary_dir.mkdir()
        lake = binary_dir / "lake"
        lake.write_text("#!" + sys.executable + "\n" + FAKE_LAKE)
        lake.chmod(0o755)
        lean = binary_dir / "lean"
        lean.write_text("#!" + sys.executable + "\n" + (
            "import json,os,subprocess,sys\n"
            "assert '--server' in sys.argv\n"
            "result=subprocess.run([os.environ['LAKE'],'setup-file','Sample.lean','-',"
            "'--no-build','--no-cache'],input=" + repr(HEADER) + ",text=True,capture_output=True)\n"
            "print(json.dumps({'lake':os.environ['LAKE'],'lease':os.environ.get('LEAN_NATIVE_CACHE_LOCK_HELD'),"
            "'returncode':result.returncode,'setup':result.stdout,'stderr':result.stderr}))\n"
        ))
        lean.chmod(0o755)
        self.hooks["shutil"] = SimpleNamespace(which=lambda command: str(lake))
        client = await self.hooks["_start_cached_client"](self.project)
        with patch.dict(os.environ, {
            "PATH": str(binary_dir) + os.pathsep + os.environ["PATH"],
            "LAKE_CACHE_DIR": str(root / "cache"),
            "EDITOR_CACHE_TEST_STATE": str(state), "EDITOR_CACHE_TEST_MODE": "",
        }):
            result = await asyncio.to_thread(
                subprocess.run, client.kwargs["server_command"], capture_output=True, text=True, timeout=3,
            )
        self.assertEqual(result.returncode, 0, result.stderr)
        server = json.loads(result.stdout)
        self.assertEqual(server["lake"], str(WRAPPER))
        self.assertIsNone(server["lease"])
        self.assertEqual(server["returncode"], 0, server["stderr"])
        self.assertEqual(json.loads(server["setup"])["header"], HEADER)
        commands = [json.loads(line) for line in (state / "commands.jsonl").read_text().splitlines()]
        self.assertEqual(commands[0]["args"][0], "env")
        self.assertEqual(commands[2]["args"][:3], ["cache", "get", "--mappings-only"])
        self.assertTrue(all(command["lease"] == "1" for command in commands[1:]))

    async def test_failed_start_keeps_live_process_claim(self):
        self.fail_start = True
        with self.assertRaisesRegex(RuntimeError, "startup failed"):
            await self.hooks["_start_cached_client"](self.project)
        self.assertFalse(self.hooks["_workspace_can_archive"](self.project))
        self.assertTrue(self.clients[0].close_called)

    async def test_dead_eviction_cleans_under_workspace_and_cache_leases(self):
        client = FakeClient(str(self.project))
        client.alive = True
        self.client_utils._shared_clients[self.project] = client
        self.hooks["_cache_clients"][self.project] = client
        await self.hooks["_evict_cached_client"]()
        self.assertEqual(self.manager.calls, ["idle", "workspace lease", "cache lease", "idle", "cleanup", "prune"])

    async def test_pending_jobs_defer_cleanup_before_and_after_operation_lease(self):
        for initial_pending in (True, False):
            with self.subTest(initial_pending=initial_pending):
                self.manager.calls.clear()
                self.manager.pending = initial_pending
                self.manager.become_pending_inside_lock = not initial_pending
                self.hooks["_cleanup_closed_client_outputs"](self.project)
                self.assertNotIn("cleanup", self.manager.calls)
                self.assertNotIn("prune", self.manager.calls)


if __name__ == "__main__":
    unittest.main()

