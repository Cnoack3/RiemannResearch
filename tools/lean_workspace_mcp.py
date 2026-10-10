"""Restricted persistent-workspace tools layered onto lean-lsp-mcp.

The server deliberately exposes no arbitrary shell command and confines every
filesystem operation to one configured Lean project.
"""

from __future__ import annotations

import asyncio
import hashlib
import os
import re
import subprocess
import time
from pathlib import Path
from typing import Literal

from lean_lsp_mcp import main as lean_lsp_main
from lean_lsp_mcp import client_utils as lean_client_utils
from lean_lsp_mcp.server import mcp
from mcp.server.fastmcp import Context
from pydantic import BaseModel, ConfigDict

from agent_workspaces import AgentWorkspaceManager


WORKFLOW_INSTRUCTIONS = """For local Lean verification or persistence, call agent_workspace_open once and retain its token and absolute project_root; reopen that token to resume an older clone. Discover declarations with bounded lean_local_search first, then focused declaration lookup, Loogle, or LeanSearch; batch #check for shortlisted signatures. Never read the whole theorem catalog for discovery. Use bounded agent_workspace_search_files only when declaration search and filename filtering are insufficient. Test a coherent proof with agent_workspace_run_code. After failure, use compact diagnostics; request full details only if evidence was omitted. When several local tactic repairs are plausible in an existing file, batch 2-5 snippets with lean_multi_attempt instead of one call per tactic. Before persistent edits, read AGENTS.md, inspect the matching subject directory, and use cohesive, sensibly named modules with focused imports; checkpoint rejects umbrella `import Mathlib` and unexported root-level modules. A long cohesive theorem may remain in one file; split by mathematical responsibility, not an arbitrary line count. Checkpoints skip Lean for documentation-only changes and otherwise build changed modules plus local reverse dependents; lean_build remains an explicit queued full-project validation and should not run immediately before checkpoint. If lakefile.toml changes, queue agent_workspace_update_deps once before further validation. Exact dependency configurations and binary artifacts are shared by content key; cache preparation is protected and project builds are clone-local. Poll queued work no sooner than retry_after_seconds and never resubmit it; running status includes phase and Lake task progress. Successful material proofs are checkpointed with push enabled unless the user requests exploration only. Never use sorry, admit, project-local axioms, unsafe declarations, force pushes, rebases, stashes, merge commits, or discarded work. Reset requires preview and explicit permission. Distinguish informal reasoning from kernel verification. If Lean decisively invalidates user logic, lead with '## Lean found a problem' and exact evidence."""

WORKFLOW_INSTRUCTIONS += (
    " agent_workspace_run_code and agent_workspace_check_file are asynchronous "
    "verification jobs: acceptance is NOT verification. Retain the job_id, poll "
    "agent_workspace_job_status at retry_after_seconds, and inspect the terminal "
    "result. Do not resubmit a timed-out HTTP request blindly: recover the "
    "job ID using agent_workspace_list_jobs, including completed jobs. Exact "
    "duplicate submission reuses only a queued/running job, not a terminal one. "
    "A Lean error, heartbeat limit, "
    "or recursion limit is a proof/compiler result, not evidence that the MCP "
    "transport is down. wall_timeout is a per-job execution deadline. HTTP 504 "
    "and Session terminated are transport/session failures; neither proves the "
    "underlying job failed. Interrupted jobs are not automatically replayed, "
    "especially publication jobs. Only one heavy queue worker runs by default; "
    "keep direct upstream LSP proof operations sequential as well."
)

_existing_instructions = getattr(mcp._mcp_server, "instructions", "") or ""
mcp._mcp_server.instructions = (
    WORKFLOW_INSTRUCTIONS + ("\n\n" + _existing_instructions if _existing_instructions else "")
)


PROJECT_ROOT = Path(os.environ["LEAN_WORKSPACE_ROOT"]).expanduser().resolve()
EXPECTED_REMOTE = os.environ.get(
    "LEAN_WORKSPACE_REMOTE", "https://github.com/Cnoack3/RiemannResearch.git"
)


def _bounded_env_int(name: str, default: int, minimum: int, maximum: int) -> int:
    raw = os.environ.get(name, str(default))
    try:
        value = int(raw)
    except ValueError as exc:
        raise ValueError(f"{name} must be an integer") from exc
    if not minimum <= value <= maximum:
        raise ValueError(f"{name} must be between {minimum} and {maximum}")
    return value


MAX_SHARED_LEAN_CLIENTS = _bounded_env_int(
    "LEAN_MAX_SHARED_CLIENTS", 16, 1, 64
)
WORKSPACE_RETENTION_DAYS = _bounded_env_int(
    "LEAN_WORKSPACE_RETENTION_DAYS", 14, 7, 3650
)
LEAN_WORKSPACE_THREADS = _bounded_env_int(
    "LEAN_WORKSPACE_THREADS", 8, 1, 8
)
LEAN_LAKE_BUILD_THREADS = min(
    _bounded_env_int("LEAN_LAKE_BUILD_THREADS", 8, 1, 8),
    LEAN_WORKSPACE_THREADS,
)
LEAN_JOB_WORKERS = _bounded_env_int("LEAN_JOB_WORKERS", 1, 1, 4)
# Cap the Lean runtime task pool inherited by LSP clients and every Lake/Lean
# child process. Queue one heavy job by default; explicit higher concurrency
# remains available to host operators. This does not limit upstream LSP tools.
os.environ["LEAN_NUM_THREADS"] = str(LEAN_WORKSPACE_THREADS)
os.environ["LEAN_LAKE_BUILD_THREADS"] = str(LEAN_LAKE_BUILD_THREADS)
os.environ["LEAN_JOB_WORKERS"] = str(LEAN_JOB_WORKERS)
# lean-lsp-mcp 0.29.0 hard-codes this private cap at eight. Pinning that
# package version in the service makes this narrow override deterministic.
lean_client_utils._MAX_SHARED_CLIENTS = MAX_SHARED_LEAN_CLIENTS
MAX_READ_BYTES = 1_000_000
MAX_PATCH_BYTES = 2_000_000


def _workspace_can_archive(project: Path) -> bool:
    key = project.resolve(strict=False)
    return (
        key not in lean_client_utils._shared_clients
        and key not in lean_client_utils._builds_in_progress
    )

AGENT_WORKSPACES = AgentWorkspaceManager(
    PROJECT_ROOT,
    EXPECTED_REMOTE,
    before_replace=lean_client_utils.close_shared_client,
    can_archive=_workspace_can_archive,
    retention_days=WORKSPACE_RETENTION_DAYS,
)

DENIED_PARTS = {".git", ".lake", ".elan", ".ssh", "tools", "__pycache__"}
ROOT_WRITABLE = {
    ".gitignore",
    "AGENTS.md",
    "README.md",
    "RiemannResearch.lean",
    "lakefile.toml",
}
ROOT_READABLE = ROOT_WRITABLE | {
    "lake-manifest.json", "lakefile.toml", "lean-toolchain"
}
WRITABLE_PREFIXES = {"RiemannResearch"}
WRITABLE_SUFFIXES = {".lean", ".md", ".toml", ".yml", ".yaml", ".json"}
RESETTABLE_UNTRACKED_ROOT_SUFFIXES = WRITABLE_SUFFIXES | {".txt"}


def _run(args: list[str], *, input_text: str | None = None, timeout: int = 60) -> str:
    if args[:2] == ["lake", "build"] and os.environ.get("LEAN_REMOTE_CACHE_SERVICE"):
        if input_text is not None:
            raise ValueError("Cached Lake builds do not accept stdin")
        output, _ = AGENT_WORKSPACES._run_lake_build(PROJECT_ROOT, args, timeout=timeout)
        return output
    completed = subprocess.run(
        args,
        cwd=PROJECT_ROOT,
        input=input_text,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
        env={**os.environ, "GIT_TERMINAL_PROMPT": "0"},
    )
    output = (completed.stdout + completed.stderr).strip()
    if completed.returncode != 0:
        raise RuntimeError(
            f"Command failed ({completed.returncode}): {' '.join(args)}\n{output[-12000:]}"
        )
    return output


def _relative_path(raw: str, *, writable: bool = False) -> tuple[str, Path]:
    if not raw or "\x00" in raw:
        raise ValueError("Path is empty or invalid")
    candidate = Path(raw)
    if candidate.is_absolute():
        raise ValueError("Use a project-relative path")
    resolved = (PROJECT_ROOT / candidate).resolve(strict=False)
    try:
        relative = resolved.relative_to(PROJECT_ROOT)
    except ValueError as exc:
        raise ValueError("Path escapes the Lean project") from exc
    if not relative.parts or any(part in DENIED_PARTS for part in relative.parts):
        raise ValueError("Path is protected")
    normalized = relative.as_posix()
    if writable:
        root_ok = normalized in ROOT_WRITABLE
        nested_ok = (
            relative.parts[0] in WRITABLE_PREFIXES
            and resolved.suffix.lower() in WRITABLE_SUFFIXES
        )
        if not (root_ok or nested_ok):
            raise ValueError(f"Writes are not allowed for {normalized}")
    else:
        root_ok = normalized in ROOT_READABLE
        nested_ok = (
            relative.parts[0] in WRITABLE_PREFIXES
            and resolved.suffix.lower() in WRITABLE_SUFFIXES
        )
        if not (root_ok or nested_ok):
            raise ValueError(f"Reads are not allowed for {normalized}")
    return normalized, resolved


def _project_files() -> list[str]:
    output = _run(["rg", "--files", "-g", "!.git/**", "-g", "!.lake/**"], timeout=30)
    files: list[str] = []
    for raw in output.splitlines():
        try:
            normalized, _ = _relative_path(raw)
        except ValueError:
            continue
        files.append(normalized)
    return sorted(files)


def _patch_paths(patch: str) -> list[str]:
    if len(patch.encode("utf-8")) > MAX_PATCH_BYTES:
        raise ValueError("Patch is too large")
    forbidden_markers = (
        "GIT binary patch",
        "Binary files ",
        "deleted file mode",
        "rename from ",
        "rename to ",
        "copy from ",
        "copy to ",
        "old mode ",
        "new mode ",
    )
    if any(marker in patch for marker in forbidden_markers):
        raise ValueError("Binary, deletion, rename, copy, and mode-changing patches are denied")

    paths: list[str] = []
    saw_header = False
    for line in patch.splitlines():
        if line.startswith("new file mode ") and line != "new file mode 100644":
            raise ValueError("Only regular non-executable new files (mode 100644) are allowed")
        if line.startswith("+++ "):
            saw_header = True
            raw = line[4:].split("\t", 1)[0]
            if raw == "/dev/null":
                raise ValueError("File deletion is denied")
            if raw.startswith("b/"):
                raw = raw[2:]
            normalized, _ = _relative_path(raw, writable=True)
            paths.append(normalized)
    if not saw_header or not paths:
        raise ValueError("Expected a unified Git patch with +++ file headers")
    return sorted(set(paths))


def _tail(text: str, lines: int = 200) -> str:
    return "\n".join(text.splitlines()[-lines:])


def _project_olean_snapshot() -> dict[str, int]:
    """Record project artifact mtimes without scanning dependency build trees."""
    artifact_root = PROJECT_ROOT / ".lake" / "build" / "lib" / "lean" / "RiemannResearch"
    if not artifact_root.is_dir():
        return {}
    snapshot: dict[str, int] = {}
    for path in artifact_root.rglob("*.olean"):
        try:
            snapshot[path.relative_to(artifact_root).as_posix()] = path.stat().st_mtime_ns
        except FileNotFoundError:
            continue
    return snapshot


def _validate_origin() -> str:
    remote = _run(["git", "remote", "get-url", "origin"])
    accepted = {
        EXPECTED_REMOTE,
        "git@github.com:Cnoack3/RiemannResearch.git",
    }
    if remote not in accepted:
        raise ValueError(f"Refusing unexpected origin remote: {remote}")
    branch = _run(["git", "branch", "--show-current"])
    if branch != "main":
        raise ValueError(f"Refusing Git operation from unexpected branch: {branch}")
    return remote


def _sync_clean_tree() -> dict:
    remote = _validate_origin()
    status = _run(["git", "status", "--porcelain"])
    if status:
        raise ValueError("Refusing to synchronize a non-clean working tree:\n" + status)
    before = _run(["git", "rev-parse", "HEAD"])
    _run(["git", "fetch", "--prune", "origin", "main"], timeout=300)
    merge_output = _run(["git", "merge", "--ff-only", "origin/main"], timeout=120)
    after = _run(["git", "rev-parse", "HEAD"])
    return {
        "remote": remote,
        "before": before,
        "after": after,
        "changed": before != after,
        "output": merge_output,
    }


def _scan_project_lean() -> list[str]:
    warnings: list[str] = []
    patterns = {
        "placeholder": re.compile(r"\b(?:sorry|admit)\b"),
        "axiom declaration": re.compile(r"^\s*axiom\b", re.MULTILINE),
        "unsafe declaration": re.compile(r"^\s*unsafe\b", re.MULTILINE),
    }
    for relative in _project_files():
        if not relative.endswith(".lean"):
            continue
        _, path = _relative_path(relative)
        text = path.read_text(encoding="utf-8")
        for label, pattern in patterns.items():
            for match in pattern.finditer(text):
                line = text.count("\n", 0, match.start()) + 1
                warnings.append(f"{relative}:{line}: {label}")
    return warnings


def _resettable_path(raw: str, *, untracked: bool = False) -> tuple[str, Path]:
    """Resolve a path that the fail-safe may restore or remove."""
    try:
        return _relative_path(raw, writable=True)
    except ValueError as original_error:
        if not raw or "\x00" in raw:
            raise original_error
        candidate = Path(raw)
        if candidate.is_absolute():
            raise original_error
        resolved = (PROJECT_ROOT / candidate).resolve(strict=False)
        try:
            relative = resolved.relative_to(PROJECT_ROOT)
        except ValueError:
            raise original_error
        if not relative.parts or any(part in DENIED_PARTS for part in relative.parts):
            raise original_error

        normalized = relative.as_posix()
        if normalized == "lake-manifest.json":
            return normalized, resolved

        safe_root_file = (
            untracked
            and len(relative.parts) == 1
            and not relative.name.startswith(".")
            and resolved.suffix.lower() in RESETTABLE_UNTRACKED_ROOT_SUFFIXES
        )
        if safe_root_file:
            return normalized, resolved
        raise original_error


def _workspace_reset_plan() -> dict:
    """Describe uncommitted changes and bind them to an exact confirmation token."""
    remote = _validate_origin()
    status = _run(["git", "status", "--porcelain"])
    head = _run(["git", "rev-parse", "HEAD"])

    tracked_raw = _run(["git", "diff", "--name-only", "-z", "HEAD", "--"])
    untracked_raw = _run(
        ["git", "ls-files", "--others", "--exclude-standard", "-z", "--"]
    )
    tracked_candidates = sorted(path for path in tracked_raw.split("\0") if path)
    untracked_candidates = sorted(path for path in untracked_raw.split("\0") if path)

    tracked: list[str] = []
    untracked: list[str] = []
    protected: list[str] = []
    resolved_untracked: dict[str, Path] = {}

    for raw in tracked_candidates:
        try:
            normalized, _ = _resettable_path(raw)
            tracked.append(normalized)
        except ValueError:
            protected.append(raw)

    for raw in untracked_candidates:
        try:
            normalized, resolved = _resettable_path(raw, untracked=True)
            if (
                resolved.is_symlink()
                or not resolved.is_file()
                or resolved.stat().st_size > MAX_PATCH_BYTES
            ):
                raise ValueError("Untracked path is not a resettable regular file")
            untracked.append(normalized)
            resolved_untracked[normalized] = resolved
        except (OSError, ValueError):
            protected.append(raw)

    digest = hashlib.sha256()
    digest.update(head.encode("utf-8"))
    digest.update(b"\0")
    digest.update(status.encode("utf-8"))
    digest.update(b"\0")
    digest.update(_run(["git", "diff", "--binary", "HEAD", "--"]).encode("utf-8"))
    for normalized in untracked:
        digest.update(b"\0")
        digest.update(normalized.encode("utf-8"))
        digest.update(b"\0")
        digest.update(resolved_untracked[normalized].read_bytes())

    return {
        "remote": remote,
        "head": head,
        "status": status.splitlines(),
        "tracked_paths": tracked,
        "untracked_paths": untracked,
        "protected_paths": sorted(set(protected)),
        "confirmation_token": digest.hexdigest(),
    }


@mcp.tool(
    name="workspace_list_files",
    description="List persistent files in the RiemannResearch project, excluding build and Git internals.",
)
def workspace_list_files() -> dict:
    return {"project_root": str(PROJECT_ROOT), "files": _project_files()}


@mcp.tool(
    name="workspace_read_file",
    description="Read a UTF-8 text file from the persistent RiemannResearch project.",
)
def workspace_read_file(path: str) -> dict:
    normalized, resolved = _relative_path(path)
    if not resolved.is_file():
        raise FileNotFoundError(normalized)
    if resolved.stat().st_size > MAX_READ_BYTES:
        raise ValueError("File is too large to read through this tool")
    return {"path": normalized, "content": resolved.read_text(encoding="utf-8")}


@mcp.tool(
    name="workspace_apply_patch",
    description=(
        "Apply a unified Git patch inside approved theorem/documentation paths. "
        "Deletions, binaries, renames, build caches, Git internals, and connector code are denied."
    ),
)
def workspace_apply_patch(patch: str) -> dict:
    sync = None
    if not _run(["git", "status", "--porcelain"]):
        sync = _sync_clean_tree()
    paths = _patch_paths(patch)
    _run(["git", "apply", "--check", "--whitespace=error-all", "-"], input_text=patch)
    _run(["git", "apply", "--whitespace=error-all", "-"], input_text=patch)
    return {
        "applied": True,
        "paths": paths,
        "synced_before_edit": sync,
        "status": _run(["git", "status", "--short"]),
    }


@mcp.tool(
    name="workspace_git_status",
    description="Show the branch, working-tree status, remotes, and recent local commits.",
)
def workspace_git_status() -> dict:
    return {
        "status": _run(["git", "status", "--short", "--branch"]),
        "remotes": _run(["git", "remote", "-v"]),
        "recent_commits": _run(["git", "log", "-n", "8", "--oneline", "--decorate"]),
    }


@mcp.tool(
    name="workspace_git_diff",
    description="Show unstaged and staged changes in the persistent Lean project.",
)
def workspace_git_diff() -> dict:
    return {
        "unstaged": _run(["git", "diff", "--no-ext-diff", "--"]),
        "staged": _run(["git", "diff", "--cached", "--no-ext-diff", "--"]),
    }


@mcp.tool(
    name="workspace_sync",
    description=(
        "Safely synchronize the clean local main branch from the configured private "
        "GitHub origin using fetch plus fast-forward-only merge. Never creates merge "
        "commits, rebases, stashes, force-pushes, or discards local work."
    ),
)
def workspace_sync() -> dict:
    return _sync_clean_tree()


@mcp.tool(
    name="workspace_reset",
    description=(
        "Destructive fail-safe that discards only uncommitted changes in approved "
        "RiemannResearch paths while preserving every commit and the current branch. "
        "First call with an empty confirmation_token to preview. Show that preview to "
        "the user and obtain explicit permission; only then call again with the returned "
        "token. The token is rejected if another agent changes the workspace."
    ),
    annotations={
        "title": "Reset uncommitted Lean workspace",
        "readOnlyHint": False,
        "destructiveHint": True,
        "idempotentHint": False,
        "openWorldHint": False,
    },
)
def workspace_reset(confirmation_token: str = "") -> dict:
    plan = _workspace_reset_plan()
    if not plan["status"]:
        return {
            "reset": False,
            "clean": True,
            "message": "Workspace is already clean; nothing was discarded.",
            "head": plan["head"],
        }

    if plan["protected_paths"]:
        return {
            "reset": False,
            "clean": False,
            "reset_allowed": False,
            "message": "Reset refused because protected paths have uncommitted changes.",
            **plan,
        }

    if not confirmation_token:
        return {
            "reset": False,
            "clean": False,
            "reset_allowed": True,
            "requires_explicit_user_permission": True,
            "message": (
                "Preview only. Show these paths to the user and obtain explicit permission "
                "before calling workspace_reset again with confirmation_token."
            ),
            **plan,
        }

    if confirmation_token != plan["confirmation_token"]:
        raise ValueError(
            "Confirmation token is stale or invalid; preview the reset again and ask the user."
        )

    if plan["tracked_paths"]:
        _run(
            [
                "git",
                "restore",
                "--source=HEAD",
                "--staged",
                "--worktree",
                "--",
                *plan["tracked_paths"],
            ]
        )
    for relative in plan["untracked_paths"]:
        _, resolved = _resettable_path(relative, untracked=True)
        resolved.unlink()

    remaining = _run(["git", "status", "--porcelain"])
    if remaining:
        raise RuntimeError(
            "Reset did not produce a clean workspace; no further cleanup was attempted:\n"
            + remaining
        )

    return {
        "reset": True,
        "clean": True,
        "discarded_tracked_paths": plan["tracked_paths"],
        "discarded_untracked_paths": plan["untracked_paths"],
        "head": plan["head"],
        "message": "Uncommitted approved workspace changes were discarded.",
    }


@mcp.tool(
    name="workspace_update_dependencies",
    description=(
        "Run Lake's dependency resolver after an approved lakefile.toml patch. "
        "An optional package name limits the update to that dependency."
    ),
)
def workspace_update_dependencies(package: str = "") -> dict:
    if package and not re.fullmatch(r"[A-Za-z][A-Za-z0-9_.-]*", package):
        raise ValueError("Invalid Lake package name")
    args = ["lake", "update"] + ([package] if package else [])
    output = _run(args, timeout=1800)
    return {"updated": package or "all", "output": _tail(output)}


@mcp.tool(
    name="workspace_checkpoint",
    description=(
        "Scan project Lean files, run lake build, create a local Git commit, and optionally "
        "push that exact commit to the configured private GitHub main branch."
    ),
)
def workspace_checkpoint(message: str, push: bool = True) -> dict:
    message = message.strip()
    if not 5 <= len(message) <= 120 or "\n" in message:
        raise ValueError("Commit message must be one line containing 5-120 characters")

    deleted = _run(["git", "status", "--porcelain"]).splitlines()
    deleted = [line for line in deleted if line[:2].strip() == "D" or "D" in line[:2]]
    if deleted:
        raise ValueError("Checkpoint refuses file deletions: " + "; ".join(deleted))

    warnings = _scan_project_lean()
    if warnings:
        raise ValueError("Lean source audit failed:\n" + "\n".join(warnings[:100]))

    if push:
        _validate_origin()
        _run(["git", "fetch", "origin", "main"], timeout=300)
        _run(["git", "merge-base", "--is-ancestor", "origin/main", "HEAD"])

    build_before = _project_olean_snapshot()
    build_started = time.monotonic()
    build_output = _run(
        ["lake", "build", "RiemannResearch", "--quiet"], timeout=3600
    )
    build_seconds = round(time.monotonic() - build_started, 3)
    build_after = _project_olean_snapshot()
    rebuilt_modules = sorted(
        name for name, mtime in build_after.items() if build_before.get(name) != mtime
    )
    build_metrics = {
        "command": "lake build RiemannResearch --quiet",
        "elapsed_seconds": build_seconds,
        "project_olean_count": len(build_after),
        "rebuilt_project_olean_count": len(rebuilt_modules),
        "rebuilt_project_oleans": rebuilt_modules,
        "incremental_note": (
            "Lake traverses the transitive task graph but reuses unchanged artifacts "
            "from .lake; only changed project .olean mtimes are listed here."
        ),
    }
    _run(
        [
            "git",
            "add",
            "--",
            "RiemannResearch",
            "RiemannResearch.lean",
            "README.md",
            "lakefile.toml",
            "lake-manifest.json",
            "lean-toolchain",
            ".gitignore",
            "AGENTS.md",
        ]
    )
    staged = _run(["git", "diff", "--cached", "--name-only"])
    if not staged:
        pushed = False
        if push:
            _run(["git", "push", "origin", "HEAD:main"], timeout=300)
            pushed = True
        return {
            "committed": False,
            "pushed": pushed,
            "commit": _run(["git", "rev-parse", "HEAD"]),
            "message": "No checkpointable changes",
            "build": _tail(build_output),
            "build_metrics": build_metrics,
        }

    _run(["git", "commit", "-m", message], timeout=120)
    commit = _run(["git", "rev-parse", "HEAD"])
    pushed = False
    if push:
        _run(["git", "push", "origin", "HEAD:main"], timeout=300)
        pushed = True

    return {
        "committed": True,
        "pushed": pushed,
        "commit": commit,
        "files": staged.splitlines(),
        "build": _tail(build_output),
        "build_metrics": build_metrics,
    }


# FastMCP 1.28.1 invokes synchronous tool functions on its event loop. Project
# I/O, Git, cache locks and clone creation must therefore run in threads. Do not
# wrap mutations in wait_for: cancelling an await does not stop the thread and
# must not be reported as rollback. Long compilations have durable jobs below.
@mcp.tool(
    name="agent_workspace_open",
    description="Open a fresh isolated Lean clone, or resume one by token.",
)
async def agent_workspace_open(resume_token: str = "") -> dict:
    return await asyncio.to_thread(AGENT_WORKSPACES.open, resume_token)


@mcp.tool(
    name="agent_workspace_list_files",
    description="List matching project files with a bounded result count.",
)
async def agent_workspace_list_files(
    workspace_token: str, pattern: str = "", limit: int = 200
) -> dict:
    return await asyncio.to_thread(AGENT_WORKSPACES.list_files, workspace_token, pattern, limit)


@mcp.tool(
    name="agent_workspace_search_files",
    description=(
        "Bounded literal search in approved project text files. Use only when "
        "declaration search and filename filtering are insufficient."
    ),
)
async def agent_workspace_search_files(
    workspace_token: str,
    query: str,
    file_glob: str = "*.lean",
    limit: int = 20,
    case_sensitive: bool = False,
    max_match_chars: int = 500,
) -> dict:
    return await asyncio.to_thread(
        AGENT_WORKSPACES.search_files,
        workspace_token,
        query,
        file_glob,
        limit,
        case_sensitive,
        max_match_chars,
    )


@mcp.tool(
    name="agent_workspace_read_file",
    description="Read a bounded line range from an approved project file.",
)
async def agent_workspace_read_file(
    workspace_token: str,
    path: str,
    start_line: int = 1,
    end_line: int = 0,
    max_chars: int = 20_000,
) -> dict:
    return await asyncio.to_thread(
        AGENT_WORKSPACES.read_file,
        workspace_token, path, start_line, end_line, max_chars
    )


@mcp.tool(
    name="agent_workspace_apply_patch",
    description="Apply a non-destructive patch and report publication architecture blockers.",
)
async def agent_workspace_apply_patch(workspace_token: str, patch: str) -> dict:
    return await asyncio.to_thread(AGENT_WORKSPACES.apply_patch, workspace_token, patch)


@mcp.tool(
    name="agent_workspace_git_status",
    description="Show concise Git and publication status for an isolated clone.",
)
async def agent_workspace_git_status(workspace_token: str) -> dict:
    return await asyncio.to_thread(AGENT_WORKSPACES.git_status, workspace_token)


@mcp.tool(
    name="agent_workspace_git_diff",
    description="Show staged and unstaged clone changes.",
)
async def agent_workspace_git_diff(workspace_token: str) -> dict:
    return await asyncio.to_thread(AGENT_WORKSPACES.git_diff, workspace_token)


@mcp.tool(
    name="agent_workspace_sync",
    description="Safely refresh a clean clone from published main.",
)
async def agent_workspace_sync(workspace_token: str) -> dict:
    return await asyncio.to_thread(AGENT_WORKSPACES.sync, workspace_token)


@mcp.tool(
    name="agent_workspace_update_deps",
    description=(
        "Queue a dependency update after an intentional lakefile.toml change; "
        "the resulting exact dependency environment is shared by content key."
    ),
)
async def agent_workspace_update_deps(
    workspace_token: str, package: str = ""
) -> dict:
    return await asyncio.to_thread(
        AGENT_WORKSPACES.submit_update_dependencies, workspace_token, package
    )


mcp.remove_tool("lean_build")


@mcp.tool(
    name="lean_build",
    description=(
        "Queue incremental project validation using shared Mathlib binaries; "
        "do not call immediately before checkpoint."
    ),
)
async def queued_lean_build(lean_project_path: str) -> dict:
    if not lean_project_path:
        raise ValueError(
            "lean_project_path is required and must equal project_root from "
            "agent_workspace_open"
        )
    return await asyncio.to_thread(AGENT_WORKSPACES.submit_build_for_project, lean_project_path)


@mcp.tool(
    name="agent_workspace_checkpoint",
    description="Queue audit, affected-module validation, commit, and publication.",
)
async def agent_workspace_checkpoint(
    workspace_token: str, message: str, push: bool = True
) -> dict:
    return await asyncio.to_thread(
        AGENT_WORKSPACES.submit_checkpoint, workspace_token, message, push
    )


@mcp.tool(
    name="agent_workspace_job_status",
    description=(
        "Check queued/running work, including phase, percent, and estimated remaining time; "
        "obey retry_after_seconds and request logs only if needed."
    ),
)
async def agent_workspace_job_status(job_id: str, include_logs: bool = False) -> dict:
    return await asyncio.to_thread(AGENT_WORKSPACES.job_status, job_id, include_logs)


@mcp.tool(
    name="agent_workspace_list_jobs",
    description=(
        "List bounded recent job summaries for a workspace without starting Lean; "
        "recover a lost job ID after an HTTP timeout before submitting again."
    ),
)
async def agent_workspace_list_jobs(workspace_token: str, limit: int = 20) -> dict:
    return await asyncio.to_thread(AGENT_WORKSPACES.list_jobs, workspace_token, limit)


@mcp.tool(
    name="agent_workspace_reset",
    description=(
        "Permission-gated fail-safe for one isolated clone. First call without a token "
        "to preview, obtain explicit user permission, then submit the exact token."
    ),
    annotations={
        "title": "Reset isolated Lean workspace",
        "readOnlyHint": False,
        "destructiveHint": True,
        "idempotentHint": False,
        "openWorldHint": False,
    },
)
async def agent_workspace_reset(
    workspace_token: str, confirmation_token: str = ""
) -> dict:
    return await asyncio.to_thread(AGENT_WORKSPACES.reset, workspace_token, confirmation_token)


@mcp.tool(
    name="agent_workspace_run_code",
    description=(
        "Queue one ephemeral Lean snippet and return its job ID immediately; "
        "poll agent_workspace_job_status for bounded diagnostics and verification. "
        "An accepted job is not a verified theorem."
    ),
)
async def agent_workspace_run_code(
    workspace_token: str, code: str, timeout_seconds: int = 300
) -> dict:
    return await asyncio.to_thread(
        AGENT_WORKSPACES.submit_run_code, workspace_token, code, timeout_seconds
    )


@mcp.tool(
    name="agent_workspace_check_file",
    description=(
        "Queue compilation of an existing approved project-relative .lean file; "
        "return a job ID, then poll agent_workspace_job_status. "
        "Use this for full-file verification instead of a long LSP diagnostic request."
    ),
)
async def agent_workspace_check_file(
    workspace_token: str, path: str, timeout_seconds: int = 300
) -> dict:
    return await asyncio.to_thread(
        AGENT_WORKSPACES.submit_check_file, workspace_token, path, timeout_seconds
    )


# Replace the two highest-volume discovery tools with bounded defaults while
# retaining explicit full-detail modes. Calls still use lean-lsp-mcp's original
# implementations and validation.
_original_diagnostics_tool = mcp._tool_manager.get_tool("lean_diagnostic_messages")
_original_local_search_tool = mcp._tool_manager.get_tool("lean_local_search")
if _original_diagnostics_tool is None or _original_local_search_tool is None:
    raise RuntimeError("Pinned lean-lsp-mcp tools are missing")
_original_diagnostics = _original_diagnostics_tool.fn
_original_local_search = _original_local_search_tool.fn
mcp.remove_tool("lean_diagnostic_messages")
mcp.remove_tool("lean_local_search")


class _OpenToolResult(BaseModel):
    """Preserve structured MCP results while allowing compact/full variants."""

    model_config = ConfigDict(extra="allow")


@mcp.tool(
    name="lean_diagnostic_messages",
    description="Get bounded Lean diagnostics; set full_details only when compact output is insufficient.",
    annotations=_original_diagnostics_tool.annotations,
)
async def bounded_diagnostic_messages(
    ctx: Context,
    file_path: str,
    start_line: int | None = None,
    end_line: int | None = None,
    declaration_name: str | None = None,
    severity: Literal["error", "warning", "info", "hint"] | None = None,
    timeout_s: float | None = None,
    interactive: bool = False,
    max_items: int = 20,
    max_message_chars: int = 2000,
    full_details: bool = False,
) -> _OpenToolResult:
    if not 1 <= max_items <= 100:
        raise ValueError("max_items must be between 1 and 100")
    if not 200 <= max_message_chars <= 8000:
        raise ValueError("max_message_chars must be between 200 and 8000")
    result = await _original_diagnostics(
        ctx,
        file_path,
        start_line,
        end_line,
        declaration_name,
        interactive,
        timeout_s,
        severity,
    )
    data = result.model_dump() if hasattr(result, "model_dump") else result
    if interactive or full_details:
        return _OpenToolResult.model_validate(data)
    if not isinstance(data, dict) or "items" not in data:
        return _OpenToolResult.model_validate(data)
    items = data.get("items") or []
    compact_items = []
    for item in items[:max_items]:
        compact = dict(item)
        message = str(compact.get("message", ""))
        compact["message"] = message[:max_message_chars]
        compact["message_truncated"] = len(message) > max_message_chars
        compact_items.append(compact)
    return _OpenToolResult.model_validate({
        "success": data.get("success", True),
        "partial": data.get("partial", False),
        "timed_out": data.get("timed_out", False),
        "still_elaborating_lines": data.get("still_elaborating_lines"),
        "failed_dependencies": data.get("failed_dependencies", []),
        "items": compact_items,
        "total_items": len(items),
        "truncated": len(items) > len(compact_items),
    })


@mcp.tool(
    name="lean_local_search",
    description="Fast bounded declaration-name search. Batch #check shortlisted names for signatures.",
    annotations=_original_local_search_tool.annotations,
)
async def bounded_local_search(
    ctx: Context,
    query: str,
    limit: int = 8,
    project_root: str | None = None,
) -> _OpenToolResult:
    if not 1 <= limit <= 25:
        raise ValueError("limit must be between 1 and 25")
    result = await _original_local_search(ctx, query, limit, project_root)
    data = result.model_dump() if hasattr(result, "model_dump") else result
    return _OpenToolResult.model_validate(data)


# Keep the model-facing catalog focused. Retired endpoint names and overlapping
# editor/search helpers are intentionally not advertised.
for _retired_tool in (
    "workspace_list_files",
    "workspace_read_file",
    "workspace_apply_patch",
    "workspace_git_status",
    "workspace_git_diff",
    "workspace_sync",
    "workspace_reset",
    "workspace_update_dependencies",
    "workspace_checkpoint",
    "lean_run_code",
    "lean_get_widget_source",
    "lean_code_actions",
    "lean_completions",
    "lean_get_widgets",
    "lean_hammer_premise",
    "lean_hover_info",
    "lean_leanfinder",
    "lean_profile_proof",
    "lean_references",
    "lean_state_search",
    "lean_term_goal",
):
    mcp.remove_tool(_retired_tool)


# FastMCP derives large response schemas from lean-lsp-mcp's Pydantic models.
# Advertise only their common top-level object shape. Keeping a non-null schema
# preserves FastMCP's structured-output conversion and the original output-model
# validation, while avoiding thousands of repeated catalog characters.
for _tool in mcp._tool_manager.list_tools():
    if _tool.fn_metadata.output_schema is not None:
        _tool.fn_metadata.output_schema = {"type": "object"}
    _tool.__dict__.pop("output_schema", None)


if __name__ == "__main__":
    raise SystemExit(lean_lsp_main())
