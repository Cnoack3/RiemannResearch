"""Dependency-free regression tests of the wrapper's actual handler bodies.

AST extraction deliberately avoids starting a real MCP server or importing
Lean. These tests do not replace the pinned-MCP integration smoke test on host.
"""

from __future__ import annotations

import ast
import asyncio
from pathlib import Path
import threading
import unittest


SOURCE = Path(__file__).with_name("lean_workspace_mcp.py")


def load_handlers(manager):
    tree = ast.parse(SOURCE.read_text())
    selected = []
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and (
            node.name.startswith("agent_workspace_") or node.name == "queued_lean_build"
        ):
            if not isinstance(node, ast.AsyncFunctionDef):
                raise AssertionError(f"Blocking synchronous handler: {node.name}")
            node.decorator_list = []
            selected.append(node)
    namespace = {"asyncio": asyncio, "AGENT_WORKSPACES": manager}
    exec(compile(ast.Module(body=selected, type_ignores=[]), str(SOURCE), "exec"), namespace)
    return namespace


class RecordingManager:
    def __init__(self):
        self.calls = []

    def __getattr__(self, method):
        def call(*arguments):
            self.calls.append((method, arguments, threading.get_ident()))
            return {"method": method, "arguments": arguments}
        return call


class AsyncHandlerTests(unittest.IsolatedAsyncioTestCase):
    async def test_all_workspace_handlers_offload_correct_arguments(self):
        manager = RecordingManager()
        handlers = load_handlers(manager)
        cases = [
            ("agent_workspace_open", (), "open", ("",)),
            ("agent_workspace_list_files", ("ws",), "list_files", ("ws", "", 200)),
            ("agent_workspace_search_files", ("ws", "term"), "search_files",
             ("ws", "term", "*.lean", 20, False, 500)),
            ("agent_workspace_read_file", ("ws", "RiemannResearch/A.lean"), "read_file",
             ("ws", "RiemannResearch/A.lean", 1, 0, 20000)),
            ("agent_workspace_apply_patch", ("ws", "patch"), "apply_patch", ("ws", "patch")),
            ("agent_workspace_git_status", ("ws",), "git_status", ("ws",)),
            ("agent_workspace_git_diff", ("ws",), "git_diff", ("ws",)),
            ("agent_workspace_sync", ("ws",), "sync", ("ws",)),
            ("agent_workspace_update_deps", ("ws",), "submit_update_dependencies", ("ws", "")),
            ("queued_lean_build", ("/approved/project",), "submit_build_for_project", ("/approved/project", "")),
            ("agent_workspace_checkpoint", ("ws", "checkpoint"), "submit_checkpoint",
             ("ws", "checkpoint", True, "")),
            ("agent_workspace_job_status", ("job",), "job_status", ("job", False)),
            ("agent_workspace_list_jobs", ("ws",), "list_jobs", ("ws", 20)),
            ("agent_workspace_reset", ("ws",), "reset", ("ws", "")),
            ("agent_workspace_run_code", ("ws", "example : True := True.intro"), "submit_run_code",
             ("ws", "example : True := True.intro", 300, "")),
            ("agent_workspace_check_file", ("ws", "RiemannResearch/A.lean"), "submit_check_file",
             ("ws", "RiemannResearch/A.lean", 300, "")),
        ]
        for name, arguments, expected_method, expected_arguments in cases:
            with self.subTest(handler=name):
                result = await handlers[name](*arguments)
                method, args, thread = manager.calls[-1]
                self.assertEqual((method, args), (expected_method, expected_arguments))
                self.assertNotEqual(thread, threading.get_ident())
                self.assertEqual(result["method"], expected_method)
        self.assertEqual(len(cases), len([name for name in handlers if name.startswith("agent_workspace_") or name == "queued_lean_build"]))

    async def test_status_responds_while_clone_is_blocked(self):
        entered, release = threading.Event(), threading.Event()

        class Manager(RecordingManager):
            def open(self, token):
                entered.set()
                if not release.wait(3):
                    raise AssertionError("clone was not released")
                return {"workspace_token": token}

        handlers = load_handlers(Manager())
        opening = asyncio.create_task(handlers["agent_workspace_open"]("ws"))
        try:
            self.assertTrue(await asyncio.to_thread(entered.wait, 1))
            status = await asyncio.wait_for(handlers["agent_workspace_job_status"]("job"), 1)
            self.assertEqual(status["method"], "job_status")
            self.assertFalse(opening.done())
        finally:
            release.set()
            await opening

    async def test_run_code_returns_acceptance_without_compiling(self):
        class Manager:
            def submit_run_code(self, *args):
                return {"accepted": True, "job_id": "job_test", "state": "queued"}

            def run_code(self, *args):
                raise AssertionError("A request must not compile synchronously")

        handlers = load_handlers(Manager())
        result = await handlers["agent_workspace_run_code"]("ws", "code")
        self.assertEqual(result["job_id"], "job_test")
        self.assertNotIn("verified", result)

    async def test_build_requires_project_before_dispatch(self):
        manager = RecordingManager()
        handlers = load_handlers(manager)
        with self.assertRaisesRegex(ValueError, "lean_project_path is required"):
            await handlers["queued_lean_build"]("")
        self.assertEqual(manager.calls, [])

    async def test_worker_errors_propagate_not_success(self):
        class Manager:
            def submit_check_file(self, *args):
                raise ValueError("Path is protected")

        handlers = load_handlers(Manager())
        with self.assertRaisesRegex(ValueError, "Path is protected"):
            await handlers["agent_workspace_check_file"]("ws", "tools/server.lean")

    async def test_backend_override_reaches_all_acceptance_jobs(self):
        manager = RecordingManager()
        handlers = load_handlers(manager)
        for name, args, method in (
            ("queued_lean_build", ("/project", "lake"), "submit_build_for_project"),
            ("agent_workspace_checkpoint", ("ws", "checkpoint", False, "lake"), "submit_checkpoint"),
            ("agent_workspace_run_code", ("ws", "example : True := True.intro", 30, "lake"), "submit_run_code"),
            ("agent_workspace_check_file", ("ws", "RiemannResearch/A.lean", 30, "lake"), "submit_check_file"),
        ):
            await handlers[name](*args)
            self.assertEqual(manager.calls[-1][:2], (method, args))

    async def test_explicit_options_are_not_lost(self):
        manager = RecordingManager()
        handlers = load_handlers(manager)
        await handlers["agent_workspace_job_status"]("job", True)
        self.assertEqual(manager.calls[-1][:2], ("job_status", ("job", True)))
        await handlers["agent_workspace_checkpoint"]("ws", "message", False)
        self.assertEqual(manager.calls[-1][:2], ("submit_checkpoint", ("ws", "message", False, "")))
        await handlers["agent_workspace_run_code"]("ws", "code", 900)
        self.assertEqual(manager.calls[-1][:2], ("submit_run_code", ("ws", "code", 900, "")))


if __name__ == "__main__":
    unittest.main()

