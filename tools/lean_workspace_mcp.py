"""Restricted persistent-workspace tools layered onto lean-lsp-mcp.

The server deliberately exposes no arbitrary shell command and confines every
filesystem operation to one configured Lean project.
"""

from __future__ import annotations

import hashlib
import os
import re
import subprocess
import time
from pathlib import Path

from lean_lsp_mcp import main as lean_lsp_main
from lean_lsp_mcp.server import mcp

from agent_workspaces import AgentWorkspaceManager


WORKFLOW_INSTRUCTIONS = """For every new or concurrent Lean task, first call agent_workspace_open without a token and retain its workspace_token and project_root for the life of the chat. Resume an earlier task by calling agent_workspace_open with its saved token. Use only agent_workspace_* persistence tools for that clone. Pass absolute paths beneath project_root to Lean file, diagnostic, search, and build tools; use agent_workspace_run_code for ephemeral snippets and never use relative paths. Search existing project and Mathlib declarations before constructing a proof. Verify Lean code, save every successful material proof unless the user explicitly requests exploration only, then call agent_workspace_checkpoint with push enabled and report its published commit SHA. Never use sorry, admit, project-local axioms, unsafe declarations, force pushes, rebases, stashes, merge commits, or discarded local work. Treat agent_workspace_reset as a destructive fail-safe: preview it without a confirmation token, show the exact plan, obtain explicit user permission, and only then submit the returned token. The shared canonical workspace_* persistence tools are retired; use agent_workspace_* exclusively. Before substantive work, read and follow the clone's repository-root AGENTS.md. Distinguish informal mathematical arguments from kernel-verified Lean proofs. If Lean decisively invalidates user-supplied logic, lead the response with '## Lean found a problem' and the exact evidence."""

_existing_instructions = getattr(mcp._mcp_server, "instructions", "") or ""
mcp._mcp_server.instructions = (
    WORKFLOW_INSTRUCTIONS + ("\n\n" + _existing_instructions if _existing_instructions else "")
)


PROJECT_ROOT = Path(os.environ["LEAN_WORKSPACE_ROOT"]).expanduser().resolve()
EXPECTED_REMOTE = os.environ.get(
    "LEAN_WORKSPACE_REMOTE", "https://github.com/Cnoack3/RiemannResearch.git"
)
MAX_READ_BYTES = 1_000_000
MAX_PATCH_BYTES = 2_000_000

AGENT_WORKSPACES = AgentWorkspaceManager(PROJECT_ROOT, EXPECTED_REMOTE)

DENIED_PARTS = {".git", ".lake", ".elan", ".ssh", "tools", "__pycache__"}
ROOT_WRITABLE = {
    ".gitignore",
    "AGENTS.md",
    "README.md",
    "RiemannResearch.lean",
    "lakefile.toml",
}
ROOT_READABLE = ROOT_WRITABLE | {"lake-manifest.json", "lean-toolchain"}
WRITABLE_PREFIXES = {"RiemannResearch"}
WRITABLE_SUFFIXES = {".lean", ".md", ".toml", ".yml", ".yaml", ".json"}
RESETTABLE_UNTRACKED_ROOT_SUFFIXES = WRITABLE_SUFFIXES | {".txt"}


def _run(args: list[str], *, input_text: str | None = None, timeout: int = 60) -> str:
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


@mcp.tool(
    name="agent_workspace_open",
    description=(
        "Create a fresh independent Git clone for this agent, or resume/recreate the "
        "clone identified by resume_token. Call this before new Lean research and "
        "retain the returned workspace_token in the chat."
    ),
)
def agent_workspace_open(resume_token: str = "") -> dict:
    return AGENT_WORKSPACES.open(resume_token)


@mcp.tool(
    name="agent_workspace_list_files",
    description="List persistent files in one isolated Lean agent clone.",
)
def agent_workspace_list_files(workspace_token: str) -> dict:
    return AGENT_WORKSPACES.list_files(workspace_token)


@mcp.tool(
    name="agent_workspace_read_file",
    description=(
        "Read an approved UTF-8 file in one isolated clone. Returns the absolute path "
        "to use with Lean diagnostic and proof tools."
    ),
)
def agent_workspace_read_file(workspace_token: str, path: str) -> dict:
    return AGENT_WORKSPACES.read_file(workspace_token, path)


@mcp.tool(
    name="agent_workspace_apply_patch",
    description=(
        "Apply a non-destructive unified patch to approved theorem or documentation "
        "paths in one isolated clone."
    ),
)
def agent_workspace_apply_patch(workspace_token: str, patch: str) -> dict:
    return AGENT_WORKSPACES.apply_patch(workspace_token, patch)


@mcp.tool(
    name="agent_workspace_git_status",
    description="Show status and publication state for one isolated clone.",
)
def agent_workspace_git_status(workspace_token: str) -> dict:
    return AGENT_WORKSPACES.git_status(workspace_token)


@mcp.tool(
    name="agent_workspace_git_diff",
    description="Show staged and unstaged changes in one isolated clone.",
)
def agent_workspace_git_diff(workspace_token: str) -> dict:
    return AGENT_WORKSPACES.git_diff(workspace_token)


@mcp.tool(
    name="agent_workspace_sync",
    description=(
        "Synchronize a clean isolated clone by safely rehydrating it from published "
        "main. Dirty files and unpublished commits are never discarded."
    ),
)
def agent_workspace_sync(workspace_token: str) -> dict:
    return AGENT_WORKSPACES.sync(workspace_token)


@mcp.tool(
    name="agent_workspace_update_dependencies",
    description=(
        "Update Lake dependencies in one isolated clone, then attach the matching "
        "content-addressed shared dependency environment."
    ),
)
def agent_workspace_update_dependencies(
    workspace_token: str, package: str = ""
) -> dict:
    return AGENT_WORKSPACES.update_dependencies(workspace_token, package)


@mcp.tool(
    name="agent_workspace_checkpoint",
    description=(
        "Audit and incrementally build one isolated clone, commit its work locally, "
        "then publish transactionally under a global lock. If main advanced, validate "
        "a clean integration clone before pushing."
    ),
)
def agent_workspace_checkpoint(
    workspace_token: str, message: str, push: bool = True
) -> dict:
    return AGENT_WORKSPACES.checkpoint(workspace_token, message, push)


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
def agent_workspace_reset(
    workspace_token: str, confirmation_token: str = ""
) -> dict:
    return AGENT_WORKSPACES.reset(workspace_token, confirmation_token)


@mcp.tool(
    name="agent_workspace_run_code",
    description=(
        "Compile an ephemeral Lean snippet inside one isolated clone and return its "
        "diagnostics. The temporary file lives under .lake and is always removed."
    ),
)
def agent_workspace_run_code(
    workspace_token: str, code: str, timeout_seconds: int = 300
) -> dict:
    return AGENT_WORKSPACES.run_code(workspace_token, code, timeout_seconds)


# The ChatGPT connector currently exposes at most 32 tools. Retire the shared
# canonical persistence surface after migration, plus pathless/niche upstream
# tools that cannot be routed safely to an isolated clone.
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
):
    mcp.remove_tool(_retired_tool)


if __name__ == "__main__":
    raise SystemExit(lean_lsp_main())
