import os
import subprocess
import tempfile
from pathlib import Path

from agent_workspaces import AgentWorkspaceManager


def run(args, cwd):
    subprocess.run(args, cwd=cwd, check=True, capture_output=True, text=True)


class TestManager(AgentWorkspaceManager):
    def _attach_dependencies(self, project):
        return "test-deps"

    def _dependency_key(self, project):
        return "test-deps"

    def _build(self, project):
        return {"command": "test-build", "elapsed_seconds": 0}


with tempfile.TemporaryDirectory() as raw:
    temp = Path(raw)
    source = temp / "source"
    remote = temp / "remote.git"
    source.mkdir()
    run(["git", "init", "-b", "main"], source)
    run(["git", "config", "user.name", "Test"], source)
    run(["git", "config", "user.email", "test@example.com"], source)
    (source / "RiemannResearch").mkdir()
    (source / "RiemannResearch" / "Basic.lean").write_text("theorem base : True := by trivial\n")
    (source / "RiemannResearch.lean").write_text("import RiemannResearch.Basic\n")
    (source / "README.md").write_text("# Test\n")
    (source / "AGENTS.md").write_text("# Test\n")
    (source / ".gitignore").write_text("/.lake\n")
    (source / "lean-toolchain").write_text("leanprover/lean4:v4.19.0\n")
    (source / "lakefile.toml").write_text('name = "RiemannResearch"\n')
    (source / "lake-manifest.json").write_text('{"version": "1.1.0", "packagesDir": ".lake/packages", "packages": []}\n')
    run(["git", "add", "."], source)
    run(["git", "commit", "-m", "Initial"], source)
    run(["git", "clone", "--bare", str(source), str(remote)], temp)

    os.environ["LEAN_AGENT_WORKSPACES_ROOT"] = str(temp / "workspaces")
    os.environ["LEAN_AGENT_WORKSPACES_STATE"] = str(temp / "state")
    os.environ["LEAN_SHARED_DEPS_ROOT"] = str(temp / "shared")
    fake_bin = temp / "bin"
    fake_bin.mkdir()
    fake_lake = fake_bin / "lake"
    fake_lake.write_text(
        "#!/bin/sh\n"
        "if grep -q FAIL \"$3\"; then echo simulated-error; exit 1; fi\n"
        "echo simulated-verified\n"
    )
    fake_lake.chmod(0o755)
    os.environ["PATH"] = str(fake_bin) + os.pathsep + os.environ["PATH"]
    closed_projects = []
    manager = TestManager(
        source, str(remote), before_replace=lambda path: closed_projects.append(str(path))
    )

    first = manager.open()
    second = manager.open()
    assert first["project_root"] != second["project_root"]
    first_token = first["workspace_token"]
    second_token = second["workspace_token"]
    run_ok = manager.run_code(first_token, "theorem scratch : True := by trivial\n")
    assert run_ok["verified"] and "simulated-verified" in run_ok["output"]
    run_bad = manager.run_code(first_token, "FAIL\n")
    assert not run_bad["verified"] and "simulated-error" in run_bad["output"]
    assert not list((Path(first["project_root"]) / ".lake" / "agent-scratch").glob("*.lean"))

    patch_one = """diff --git a/RiemannResearch/One.lean b/RiemannResearch/One.lean
new file mode 100644
--- /dev/null
+++ b/RiemannResearch/One.lean
@@ -0,0 +1 @@
+theorem one : True := by trivial
"""
    manager.apply_patch(first_token, patch_one)
    assert not (Path(second["project_root"]) / "RiemannResearch" / "One.lean").exists()
    first_publish = manager.checkpoint(first_token, "Publish first")
    assert first_publish["pushed"]

    patch_two = """diff --git a/RiemannResearch/Two.lean b/RiemannResearch/Two.lean
new file mode 100644
--- /dev/null
+++ b/RiemannResearch/Two.lean
@@ -0,0 +1 @@
+theorem two : True := by trivial
"""
    manager.apply_patch(second_token, patch_two)
    second_publish = manager.checkpoint(second_token, "Publish second")
    assert second_publish["integrated_with_newer_main"]
    resumed = manager.open(second_token)
    resumed_root = Path(resumed["project_root"])
    assert (resumed_root / "RiemannResearch" / "One.lean").is_file()
    assert (resumed_root / "RiemannResearch" / "Two.lean").is_file()

    published_meta = manager._read_meta(first_token)
    published_meta["last_activity"] = 0
    manager._write_meta(published_meta)
    published_root = Path(first["project_root"])
    archived = manager.cleanup(retention_days=30, dry_run=False)
    assert not published_root.exists()
    assert archived["archived_or_eligible"]
    assert str(published_root) in closed_projects
    assert Path(manager.open(first_token)["project_root"]).is_dir()

    dirty = manager.open()
    dirty_root = Path(dirty["project_root"])
    (dirty_root / "RiemannResearch" / "Dirty.lean").write_text("theorem dirty : True := by trivial\n")
    preview = manager.reset(dirty["workspace_token"])
    (dirty_root / "RiemannResearch" / "Dirty.lean").write_text(
        "theorem dirty : True := by\n  trivial\n"
    )
    try:
        manager.reset(dirty["workspace_token"], preview["confirmation_token"])
        raise AssertionError("stale reset token was accepted")
    except ValueError:
        pass
    assert (dirty_root / "RiemannResearch" / "Dirty.lean").is_file()
    meta = manager._read_meta(dirty["workspace_token"])
    meta["last_activity"] = 0
    manager._write_meta(meta)
    cleanup = manager.cleanup(retention_days=30, dry_run=False)
    assert dirty_root.is_dir()
    assert cleanup["preserved_unpublished"]

print("isolated workspace lifecycle ok")
