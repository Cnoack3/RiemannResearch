import os
import subprocess
import tempfile
import threading
import time
from pathlib import Path

from agent_workspaces import AgentWorkspaceManager


def run(args, cwd):
    subprocess.run(args, cwd=cwd, check=True, capture_output=True, text=True)


class TestManager(AgentWorkspaceManager):
    def __init__(self, *args, **kwargs):
        self.test_build_guard = threading.Lock()
        self.active_test_builds = 0
        self.max_active_test_builds = 0
        super().__init__(*args, **kwargs)

    def _attach_dependencies(self, project):
        return "test-deps"

    def _dependency_key(self, project):
        return "test-deps"

    def _build(self, project):
        with self.test_build_guard:
            self.active_test_builds += 1
            self.max_active_test_builds = max(
                self.max_active_test_builds,
                self.active_test_builds,
            )
        try:
            time.sleep(0.2)
            return {
                "command": "test-build",
                "elapsed_seconds": 0,
                "output": "simulated-build-log",
            }
        finally:
            with self.test_build_guard:
                self.active_test_builds -= 1


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
    (source / "RiemannResearch.lean").write_text(
        "import RiemannResearch.Basic\n"
        "import RiemannResearch.Test.One\n"
        "import RiemannResearch.Test.Two\n"
    )
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
    os.environ["LEAN_SHARED_PROJECT_BUILDS_ROOT"] = str(temp / "shared-project-builds")
    os.environ["LEAN_NUM_THREADS"] = "8"
    os.environ["LEAN_LAKE_BUILD_THREADS"] = "4"
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
    active_projects = set()
    manager = TestManager(
        source,
        str(remote),
        before_replace=lambda path: closed_projects.append(str(path)),
        can_archive=lambda path: str(path) not in active_projects,
    )
    assert manager.lean_num_threads == 8
    assert manager.lake_build_threads == 4
    assert manager._run(
        ["sh", "-c", 'printf %s "$LEAN_NUM_THREADS"'],
        cwd=source,
        lean_num_threads=manager.lake_build_threads,
    ) == "4"

    first = manager.open()
    first_root = Path(first["project_root"])
    mathlib_sentinel = (
        first_root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
    )
    original_run = manager._run

    def repairing_run(args, **kwargs):
        if args == ["lake", "exe", "cache", "get"]:
            mathlib_sentinel.parent.mkdir(parents=True, exist_ok=True)
            mathlib_sentinel.write_text("cached-mathlib\n")
            return "cache restored"
        return original_run(args, **kwargs)

    manager._run = repairing_run
    repaired_cache = manager._ensure_mathlib_cache(first_root)
    manager._run = original_run
    assert repaired_cache["ready"] and repaired_cache["repaired"]
    assert not manager._ensure_mathlib_cache(first_root)["repaired"]
    mathlib_sentinel.unlink()

    def unavailable_cache_run(args, **kwargs):
        if args == ["lake", "exe", "cache", "get"]:
            raise RuntimeError("binary cache unavailable")
        return original_run(args, **kwargs)

    manager._run = unavailable_cache_run
    source_fallback = manager._ensure_mathlib_cache(first_root)
    manager._run = original_run
    assert source_fallback["source_build_required"]
    assert "binary cache unavailable" in source_fallback["binary_cache_error"]
    mathlib_sentinel.parent.mkdir(parents=True, exist_ok=True)
    mathlib_sentinel.write_text("cached-mathlib\n")
    seeded_artifact = first_root / ".lake" / "build" / "lib" / "Seeded.olean"
    seeded_artifact.parent.mkdir(parents=True)
    seeded_artifact.write_text("cached-project-artifact\n")
    cache_result = manager._publish_project_cache(first_root)
    assert cache_result["published"]
    second = manager.open()
    assert second["project_cache"]["restored"]
    restored_artifact = Path(second["project_root"]) / ".lake" / "build" / "lib" / "Seeded.olean"
    assert restored_artifact.read_text() == "cached-project-artifact\n"
    assert first["project_root"] != second["project_root"]
    first_token = first["workspace_token"]
    second_token = second["workspace_token"]
    listed = manager.list_files(first_token, pattern="Basic", limit=1)
    assert listed["files"] == ["RiemannResearch/Basic.lean"]
    assert not listed["truncated"]
    searched = manager.search_files(first_token, "theorem", limit=1)
    assert searched["matches"][0]["path"] == "RiemannResearch/Basic.lean"
    assert searched["matches"][0]["line"] == 1
    assert searched["total_matches"] == 1
    assert not searched["truncated"]
    assert manager.search_files(first_token, "THEOREM", case_sensitive=True)["matches"] == []
    ranged = manager.read_file(
        first_token, "RiemannResearch/Basic.lean", start_line=1, max_chars=12
    )
    assert ranged["content"] == "theorem base"
    assert ranged["truncated"]
    assert ranged["total_lines"] == 1
    first_job = manager.submit_build_for_project(first["project_root"])
    duplicate_job = manager.submit_build(first_token)
    second_job = manager.submit_build(second_token)
    assert duplicate_job["existing"]
    assert duplicate_job["job_id"] == first_job["job_id"]
    assert duplicate_job["retry_after_seconds"] >= 20
    assert second_job["queue_position"] is not None
    queued_status = manager.job_status(second_job["job_id"])
    assert queued_status["retry_after_seconds"] >= 45
    if queued_status["state"] == "queued":
        assert queued_status["retry_after_seconds"] >= 60
    try:
        manager.submit_checkpoint(first_token, "Blocked checkpoint")
        raise AssertionError("a second job kind was queued for the same workspace")
    except RuntimeError as exc:
        assert first_job["job_id"] in str(exc)
    try:
        manager.run_code(first_token, "theorem blocked : True := by trivial\n")
        raise AssertionError("workspace mutation was allowed while a build was queued")
    except RuntimeError as exc:
        assert first_job["job_id"] in str(exc)
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline:
        first_status = manager.job_status(first_job["job_id"])
        second_status = manager.job_status(second_job["job_id"])
        if first_status["terminal"] and second_status["terminal"]:
            break
        time.sleep(0.01)
    assert first_status["state"] == "succeeded"
    assert second_status["state"] == "succeeded"
    assert first_status["retry_after_seconds"] == 0
    assert "output" not in first_status["result"]
    first_status_with_logs = manager.job_status(
        first_job["job_id"], include_logs=True
    )
    assert first_status_with_logs["result"]["output"] == "simulated-build-log"
    assert manager.max_active_test_builds == 1
    run_ok = manager.run_code(first_token, "theorem scratch : True := by trivial\n")
    assert run_ok["verified"] and "simulated-verified" in run_ok["output"]
    run_bad = manager.run_code(first_token, "FAIL\n")
    assert not run_bad["verified"] and "simulated-error" in run_bad["output"]
    assert not list((Path(first["project_root"]) / ".lake" / "agent-scratch").glob("*.lean"))

    bad_module = first_root / "RiemannResearch" / "Test" / "Bad.lean"
    bad_module.parent.mkdir(parents=True, exist_ok=True)
    bad_module.write_text("import Mathlib\n\ntheorem bad : True := by trivial\n")
    assert any("umbrella `import Mathlib`" in item for item in manager._architecture_audit(first_root))
    bad_module.unlink()

    patch_one = """diff --git a/RiemannResearch/Test/One.lean b/RiemannResearch/Test/One.lean
new file mode 100644
--- /dev/null
+++ b/RiemannResearch/Test/One.lean
@@ -0,0 +1 @@
+theorem one : True := by trivial
"""
    applied_one = manager.apply_patch(first_token, patch_one)
    assert applied_one["checkpoint_ready"]
    assert not (
        Path(second["project_root"]) / "RiemannResearch" / "Test" / "One.lean"
    ).exists()
    first_publish = manager.checkpoint(first_token, "Publish first")
    assert first_publish["pushed"]

    patch_two = """diff --git a/RiemannResearch/Test/Two.lean b/RiemannResearch/Test/Two.lean
new file mode 100644
--- /dev/null
+++ b/RiemannResearch/Test/Two.lean
@@ -0,0 +1 @@
+theorem two : True := by trivial
"""
    manager.apply_patch(second_token, patch_two)
    second_publish = manager.checkpoint(second_token, "Publish second")
    assert second_publish["integrated_with_newer_main"]
    resumed = manager.open(second_token)
    resumed_root = Path(resumed["project_root"])
    assert (resumed_root / "RiemannResearch" / "Test" / "One.lean").is_file()
    assert (resumed_root / "RiemannResearch" / "Test" / "Two.lean").is_file()

    published_meta = manager._read_meta(first_token)
    published_meta["last_activity"] = 0
    manager._write_meta(published_meta)
    published_root = Path(first["project_root"])
    active_projects.add(str(published_root))
    active_cleanup = manager.cleanup(retention_days=14, dry_run=False)
    assert published_root.is_dir()
    assert any(
        item["reason"] == "active Lean client or build"
        for item in active_cleanup["preserved_unpublished"]
    )
    active_projects.remove(str(published_root))
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
    metrics = manager.metrics_path.read_text()
    assert '"event":"read_file"' in metrics
    assert '"event":"job_status"' in metrics
    assert first_token not in metrics

print("isolated workspace lifecycle ok")
