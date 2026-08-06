"""Restricted persistent-workspace tools layered onto lean-lsp-mcp.

The server deliberately exposes no arbitrary shell command and confines every
filesystem operation to one configured Lean project.
"""

from __future__ import annotations

import os
import re
import subprocess
from pathlib import Path

from lean_lsp_mcp import main as lean_lsp_main
from lean_lsp_mcp.server import mcp


WORKFLOW_INSTRUCTIONS = """For persistent Lean research, first call workspace_sync when the working tree is clean. Search existing project and Mathlib declarations before constructing a proof. Verify Lean code with the Lean tools, save every successful material proof in the RiemannResearch project unless the user explicitly requests an exploratory-only result, then call workspace_checkpoint with push enabled and report the commit SHA. Never use sorry, admit, project-local axioms, unsafe declarations, force pushes, rebases, stashes, merge commits, or discarded local work. If the tree is dirty or diverged, stop and explain the conflict. Distinguish informal mathematical arguments from kernel-verified Lean proofs."""

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

    build_output = _run(["lake", "build"], timeout=3600)
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
    }


if __name__ == "__main__":
    raise SystemExit(lean_lsp_main())
