"""Offline publication gates using local Git repositories and simulated Lean."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from agent_workspaces import AgentWorkspaceManager


def git(project, *args):
    return subprocess.run(
        ["git", *args], cwd=project, check=True, capture_output=True, text=True,
    ).stdout.strip()


class GateManager(AgentWorkspaceManager):
    def _run_lake_build(self, project, args, *, timeout=3600):
        self.build_calls.append((project, args))
        if self.during_build is not None:
            self.during_build(project)
        if any("FAIL_BUILD" in path.read_text() for path in project.rglob("*.lean")):
            raise RuntimeError("simulated Lean compilation failed")
        return "simulated Lean compilation passed", {"status": "complete"}


class CheckpointGateTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.source = self.root / "source"
        self.source.mkdir()
        git(self.source, "init", "-b", "main")
        git(self.source, "config", "user.name", "Test")
        git(self.source, "config", "user.email", "test@example.com")
        git(self.source, "config", "commit.gpgsign", "false")
        self.child_relative = Path("RiemannResearch/Test/Child.lean")
        self.other_relative = Path("RiemannResearch/Test/Other.lean")
        (self.source / self.child_relative).parent.mkdir(parents=True)
        (self.source / self.child_relative).write_text("theorem child : True := by trivial\n")
        (self.source / self.other_relative).write_text("theorem other : True := by trivial\n")
        (self.source / "RiemannResearch.lean").write_text(
            "import RiemannResearch.Test.Child\nimport RiemannResearch.Test.Other\n"
        )
        for name, contents in {
            "README.md": "# Test\n", "AGENTS.md": "# Test\n", ".gitignore": "/.lake\n",
            "lean-toolchain": "leanprover/lean4:v4.33.0-rc2\n",
            "lakefile.toml": 'name = "RiemannResearch"\n',
            "lake-manifest.json": '{"version":"1.1.0","packagesDir":".lake/packages","packages":[]}\n',
        }.items():
            (self.source / name).write_text(contents)
        git(self.source, "add", ".")
        git(self.source, "commit", "-m", "Initial source")
        self.initial = git(self.source, "rev-parse", "HEAD")
        self.remote = self.root / "remote.git"
        git(self.root, "clone", "--bare", str(self.source), str(self.remote))
        git(self.source, "remote", "add", "origin", str(self.remote))
        environment = patch.dict(os.environ, {
            "LEAN_AGENT_WORKSPACES_ROOT": str(self.root / "workspaces"),
            "LEAN_AGENT_WORKSPACES_STATE": str(self.root / "state"),
            "LEAN_SHARED_DEPS_ROOT": str(self.root / "shared"),
            "LEAN_SHARED_PROJECT_BUILDS_ROOT": str(self.root / "project-cache"),
            "LEAN_REMOTE_CACHE_SERVICE": "", "LAKE_CACHE_DIR": "",
            "LEAN_NUM_THREADS": "2", "LEAN_LAKE_BUILD_THREADS": "2", "LEAN_JOB_WORKERS": "1",
            "LEAN_PROJECT_CACHE_KEEP": "8",
        })
        environment.start()
        self.addCleanup(environment.stop)
        self.manager = GateManager(self.source, str(self.remote))
        self.addCleanup(self.manager._owner_lease.close)
        self.manager.build_calls = []
        self.manager.during_build = None
        # Preseed the empty dependency environment so setup cannot invoke Lake.
        dependency = self.manager.shared / self.manager._dependency_key(self.source)
        (dependency / "packages").mkdir(parents=True)
        (dependency / "READY.json").write_text(json.dumps({"binary_cache_complete": True}))
        workspace = self.manager.open()
        self.token = workspace["workspace_token"]
        self.project = Path(workspace["project_root"])
        git(self.project, "config", "commit.gpgsign", "false")
        self.child = self.project / self.child_relative

    def remote_head(self):
        return git(self.remote, "rev-parse", "main")

    def checkpoint(self):
        return self.manager.checkpoint(self.token, "Validated checkpoint", push=True)

    def change_child(self, contents="theorem child : True := by exact True.intro\n"):
        self.child.write_text(contents)

    def upstream_change(self, relative, contents):
        (self.source / relative).write_text(contents)
        git(self.source, "add", ".")
        git(self.source, "commit", "-m", "Concurrent upstream source")
        git(self.source, "push", "origin", "HEAD:main")
        return self.remote_head()

    def test_invalid_current_lean_blocks_commit_and_push(self):
        self.change_child("def invalid : Nat := FAIL_BUILD\n")
        with self.assertRaisesRegex(RuntimeError, "Lean compilation failed"):
            self.checkpoint()
        self.assertEqual(git(self.project, "rev-parse", "HEAD"), self.initial)
        self.assertEqual(self.remote_head(), self.initial)
        self.assertIn("FAIL_BUILD", self.child.read_text())

    def test_invalid_unpublished_commit_is_checked_against_workspace_base(self):
        self.change_child("def invalid : Nat := FAIL_BUILD\n")
        git(self.project, "add", ".")
        git(self.project, "commit", "-m", "Unpublished invalid proof")
        unpublished = git(self.project, "rev-parse", "HEAD")
        self.assertEqual(git(self.project, "status", "--porcelain"), "")
        with self.assertRaisesRegex(RuntimeError, "Lean compilation failed"):
            self.checkpoint()
        self.assertEqual(self.remote_head(), self.initial)
        self.assertEqual(git(self.project, "rev-parse", "HEAD"), unpublished)
        self.assertEqual(len(self.manager.build_calls), 1)

    def test_changed_child_always_validates_aggregate_and_explicit_child(self):
        self.change_child()
        with patch.object(self.manager, "_run", wraps=self.manager._run) as commands:
            result = self.checkpoint()
        self.assertEqual(result["build"]["scope"], "project_and_changed_modules")
        self.assertEqual(self.manager.build_calls[0][1], [
            "lake", "build", "+RiemannResearch", "+RiemannResearch.Test.Child", "--quiet",
        ])
        self.assertEqual(self.remote_head(), result["commit"])
        pushes = [
            call.args[0] for call in commands.call_args_list
            if call.args[0][:2] == ["git", "push"]
        ]
        self.assertEqual(pushes, [["git", "push", "origin", f"{result['commit']}:main"]])

    def test_aggregate_placeholder_is_audited_before_compilation(self):
        aggregate = self.project / "RiemannResearch.lean"
        aggregate.write_text(aggregate.read_text() + "theorem invalid : False := by sorry\n")
        with self.assertRaisesRegex(ValueError, r"RiemannResearch\.lean.*placeholder"):
            self.checkpoint()
        self.assertEqual(self.manager.build_calls, [])
        self.assertEqual(git(self.project, "rev-parse", "HEAD"), self.initial)
        self.assertEqual(self.remote_head(), self.initial)

    def test_integrated_source_audit_failure_does_not_push(self):
        upstream = self.upstream_change(
            "RiemannResearch.lean",
            (self.source / "RiemannResearch.lean").read_text() + "theorem invalid : False := by sorry\n",
        )
        self.change_child()
        with self.assertRaisesRegex(ValueError, "Integrated Lean source audit failed"):
            self.checkpoint()
        self.assertEqual(self.remote_head(), upstream)
        self.assertEqual(len(self.manager.build_calls), 1)
        self.assertNotEqual(git(self.project, "rev-parse", "HEAD"), self.initial)
        self.assertIn("True.intro", self.child.read_text())

    def test_integrated_source_compilation_failure_does_not_push(self):
        upstream = self.upstream_change(self.other_relative, "def upstreamInvalid : Nat := FAIL_BUILD\n")
        self.change_child()
        with self.assertRaisesRegex(RuntimeError, "Lean compilation failed"):
            self.checkpoint()
        self.assertEqual(self.remote_head(), upstream)
        self.assertEqual(len(self.manager.build_calls), 2)
        self.assertIn("_integration", self.manager.build_calls[1][0].parts)
        self.assertIn("+RiemannResearch", self.manager.build_calls[1][1])

    def test_source_mutation_during_validation_blocks_commit_and_preserves_work(self):
        self.change_child()
        self.manager.during_build = lambda project: (project / self.child_relative).write_text(
            "theorem changedDuringBuild : True := by trivial\n"
        )
        with self.assertRaisesRegex(RuntimeError, "Source changed during checkpoint validation"):
            self.checkpoint()
        self.assertEqual(git(self.project, "rev-parse", "HEAD"), self.initial)
        self.assertEqual(self.remote_head(), self.initial)
        self.assertIn("changedDuringBuild", self.child.read_text())

    def test_documentation_only_checkpoint_skips_lean_and_publishes(self):
        (self.project / "README.md").write_text("# Updated documentation\n")
        result = self.checkpoint()
        self.assertEqual(result["build"]["scope"], "skipped")
        self.assertEqual(self.manager.build_calls, [])
        self.assertEqual(self.remote_head(), result["commit"])
        self.assertNotEqual(self.remote_head(), self.initial)

    def test_dependency_aggregate_and_deleted_child_deltas_use_full_scope(self):
        for relative in ("lakefile.toml", "RiemannResearch.lean", str(self.child_relative)):
            with self.subTest(relative=relative):
                path = self.project / relative
                original = path.read_text()
                if relative == str(self.child_relative):
                    path.unlink()
                else:
                    path.write_text(original + "\n-- changed configuration or aggregate\n")
                try:
                    result = self.manager._checkpoint_validation(self.project)
                    self.assertEqual(result["scope"], "full")
                    self.assertIn("+RiemannResearch", self.manager.build_calls[-1][1])
                finally:
                    path.write_text(original)

    def test_unpublished_unsupported_lean_scope_cannot_skip_validation(self):
        (self.project / "Main.lean").write_text("def unsupported : Nat := FAIL_BUILD\n")
        git(self.project, "add", "Main.lean")
        git(self.project, "commit", "-m", "Unsupported top level Lean")
        with self.assertRaisesRegex(ValueError, "Unsupported Lean source scope"):
            self.checkpoint()
        self.assertEqual(self.remote_head(), self.initial)
        self.assertEqual(self.manager.build_calls, [])


if __name__ == "__main__":
    unittest.main()
