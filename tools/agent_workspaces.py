"""Resumable, isolated Git workspaces for Lean MCP agents.

This module intentionally exposes no arbitrary shell execution.  Every path is
confined to a registered clone and every publication is serialized.
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import re
import secrets
import shutil
import subprocess
import tempfile
import time
from contextlib import contextmanager
from pathlib import Path
from typing import Callable, Iterator


TOKEN_RE = re.compile(r"^ws_[A-Za-z0-9_-]{20,80}$")
PACKAGE_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_.-]*$")
MAX_READ_BYTES = 1_000_000
MAX_PATCH_BYTES = 2_000_000
DENIED_PARTS = {".git", ".lake", ".elan", ".ssh", "tools", "__pycache__"}
ROOT_WRITABLE = {
    ".gitignore", "AGENTS.md", "README.md", "RiemannResearch.lean", "lakefile.toml"
}
ROOT_READABLE = ROOT_WRITABLE | {"lake-manifest.json", "lean-toolchain"}
WRITABLE_SUFFIXES = {".lean", ".md", ".toml", ".yml", ".yaml", ".json"}


class AgentWorkspaceManager:
    def __init__(
        self,
        canonical_root: Path,
        remote: str,
        before_replace: Callable[[Path], None] | None = None,
        can_archive: Callable[[Path], bool] | None = None,
        retention_days: int = 14,
    ) -> None:
        if not 7 <= retention_days <= 3650:
            raise ValueError("Retention must be between 7 and 3650 days")
        self.canonical_root = canonical_root.resolve()
        self.remote = remote
        self.before_replace = before_replace
        self.can_archive = can_archive
        self.retention_days = retention_days
        home = Path(os.environ.get("HOME", "/home/cri_2025")).resolve()
        self.root = Path(
            os.environ.get("LEAN_AGENT_WORKSPACES_ROOT", home / "lean-agent-workspaces")
        ).resolve()
        self.state = Path(
            os.environ.get("LEAN_AGENT_WORKSPACES_STATE", home / ".local/state/lean-agent-workspaces")
        ).resolve()
        self.shared = Path(
            os.environ.get("LEAN_SHARED_DEPS_ROOT", home / ".cache/lean-agent-dependencies")
        ).resolve()
        for path in (self.root, self.state, self.shared):
            path.mkdir(parents=True, exist_ok=True)

    def _run(
        self,
        args: list[str],
        *,
        cwd: Path,
        input_text: str | None = None,
        timeout: int = 300,
    ) -> str:
        result = subprocess.run(
            args,
            cwd=cwd,
            input=input_text,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
            env={**os.environ, "GIT_TERMINAL_PROMPT": "0"},
        )
        output = (result.stdout + result.stderr).strip()
        if result.returncode:
            raise RuntimeError(
                f"Command failed ({result.returncode}): {' '.join(args)}\n{output[-12000:]}"
            )
        return output

    @contextmanager
    def _lock(self, path: Path) -> Iterator[None]:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a+", encoding="utf-8") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)

    def _meta_path(self, token: str) -> Path:
        if not TOKEN_RE.fullmatch(token):
            raise ValueError("Invalid workspace token; call agent_workspace_open without a token")
        return self.state / f"{token}.json"

    def _read_meta(self, token: str) -> dict:
        path = self._meta_path(token)
        if not path.is_file():
            raise ValueError("Unknown workspace token; call agent_workspace_open without a token")
        return json.loads(path.read_text(encoding="utf-8"))

    def _write_meta(self, meta: dict) -> None:
        path = self._meta_path(meta["token"])
        temp = path.with_suffix(f".tmp.{os.getpid()}")
        temp.write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        os.replace(temp, path)

    def _workspace_dir(self, token: str) -> Path:
        return self.root / token / "RiemannResearch"

    def _validate_workspace_path(self, token: str, path: Path) -> None:
        expected = self._workspace_dir(token)
        if path.resolve(strict=False) != expected.resolve(strict=False):
            raise RuntimeError("Workspace registry path is inconsistent")
        if expected.parent.parent != self.root:
            raise RuntimeError("Workspace path escapes the managed root")

    def _clone(self, destination: Path, commit: str | None = None) -> None:
        destination.parent.mkdir(parents=True, exist_ok=True)
        if destination.exists():
            raise RuntimeError(f"Clone destination already exists: {destination}")
        self._run(
            ["git", "clone", "--single-branch", "--branch", "main", self.remote, str(destination)],
            cwd=destination.parent,
            timeout=900,
        )
        self._run(["git", "config", "user.name", "Lean Research Agent"], cwd=destination)
        self._run(["git", "config", "user.email", "lean-agent@localhost"], cwd=destination)
        if commit:
            self._run(["git", "checkout", "--detach", commit], cwd=destination)
        self._attach_dependencies(destination)

    def _dependency_key(self, project: Path) -> str:
        digest = hashlib.sha256()
        for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
            digest.update(name.encode())
            digest.update(b"\0")
            digest.update((project / name).read_bytes())
            digest.update(b"\0")
        return digest.hexdigest()[:24]

    def _attach_dependencies(self, project: Path) -> str:
        key = self._dependency_key(project)
        env_root = self.shared / key
        packages = env_root / "packages"
        ready = env_root / "READY.json"
        local_packages = project / ".lake" / "packages"
        with self._lock(self.shared / ".provision.lock"):
            if not ready.is_file():
                if local_packages.is_symlink():
                    local_packages.unlink()
                elif local_packages.exists():
                    shutil.rmtree(local_packages)
                manifest = (project / "lake-manifest.json").read_bytes()
                self._run(["lake", "update"], cwd=project, timeout=1800)
                (project / "lake-manifest.json").write_bytes(manifest)
                self._run(["lake", "exe", "cache", "get"], cwd=project, timeout=3600)
                temp = self.shared / f".{key}.tmp.{os.getpid()}"
                if temp.exists():
                    shutil.rmtree(temp)
                temp.mkdir(parents=True)
                if not local_packages.is_dir():
                    raise RuntimeError("Lake did not materialize dependency packages")
                shutil.move(str(local_packages), str(temp / "packages"))
                (temp / "READY.json").write_text(
                    json.dumps({"key": key, "created_at": time.time()}) + "\n",
                    encoding="utf-8",
                )
                if env_root.exists():
                    shutil.rmtree(env_root)
                os.replace(temp, env_root)
            if local_packages.is_symlink():
                if local_packages.resolve() != packages.resolve():
                    local_packages.unlink()
            elif local_packages.exists():
                shutil.rmtree(local_packages)
            local_packages.parent.mkdir(parents=True, exist_ok=True)
            if not local_packages.exists():
                local_packages.symlink_to(packages, target_is_directory=True)
        return key

    def _rehydrate(self, meta: dict) -> Path:
        token = meta["token"]
        project = Path(meta["path"])
        self._validate_workspace_path(token, project)
        if project.exists():
            status = self._run(["git", "status", "--porcelain"], cwd=project)
            head = self._run(["git", "rev-parse", "HEAD"], cwd=project)
            safe = not status and head in {
                meta.get("published_commit"),
                meta.get("base_commit"),
                meta.get("archive_commit"),
                meta.get("source_commit"),
            }
            if not safe:
                raise RuntimeError(
                    "Workspace needs rehydration but contains unpublished work; it was preserved. "
                    "Inspect agent_workspace_git_status."
                )
            if self.before_replace is not None:
                self.before_replace(project)
            shutil.rmtree(project)
        commit = meta.get("published_commit") or meta.get("archive_commit")
        self._clone(project, commit=commit)
        if commit:
            self._run(["git", "switch", "-C", "main", commit], cwd=project)
        else:
            commit = self._run(["git", "rev-parse", "HEAD"], cwd=project)
        meta.update(
            state="active",
            base_commit=commit,
            needs_rehydrate=False,
            rehydrated_at=time.time(),
        )
        self._write_meta(meta)
        return project

    def open(self, resume_token: str = "") -> dict:
        self.cleanup(retention_days=self.retention_days, dry_run=False)
        if resume_token:
            self._meta_path(resume_token)
            with self._lock(self.state / f"{resume_token}.lock"):
                meta = self._read_meta(resume_token)
                project = Path(meta["path"])
                if not project.is_dir() or meta.get("needs_rehydrate"):
                    project = self._rehydrate(meta)
                resumed = True
                meta["last_activity"] = time.time()
                self._write_meta(meta)
        else:
            with self._lock(self.state / ".registry.lock"):
                token = "ws_" + secrets.token_urlsafe(24)
                project = self._workspace_dir(token)
                meta = {
                    "token": token,
                    "path": str(project),
                    "created_at": time.time(),
                    "last_activity": time.time(),
                    "base_commit": None,
                    "published_commit": None,
                    "state": "provisioning",
                    "needs_rehydrate": False,
                }
                self._write_meta(meta)
            with self._lock(self.state / f"{token}.lock"):
                self._clone(project)
                head = self._run(["git", "rev-parse", "HEAD"], cwd=project)
                meta.update(base_commit=head, state="active")
                self._write_meta(meta)
                resumed = False
        return self.describe(meta, resumed=resumed)

    def _get(self, token: str, *, rehydrate: bool = True) -> tuple[dict, Path]:
        self._meta_path(token)
        with self._lock(self.state / f"{token}.lock"):
            meta = self._read_meta(token)
            project = Path(meta["path"])
            self._validate_workspace_path(token, project)
            if rehydrate and (not project.is_dir() or meta.get("needs_rehydrate")):
                project = self._rehydrate(meta)
            if not project.is_dir():
                raise RuntimeError(
                    "Workspace clone is archived. Resume it with agent_workspace_open and this token."
                )
            meta["last_activity"] = time.time()
            self._write_meta(meta)
            return meta, project

    def describe(self, meta: dict, *, resumed: bool) -> dict:
        project = Path(meta["path"])
        return {
            "workspace_token": meta["token"],
            "project_root": str(project),
            "resumed": resumed,
            "state": meta["state"],
            "base_commit": meta.get("base_commit"),
            "shared_dependency_key": self._dependency_key(project),
            "retention_days": self.retention_days,
            "usage": (
                "Pass workspace_token to every agent_workspace_* tool. Pass absolute paths "
                "under project_root to Lean file tools. Do not use relative paths or lean_run_code."
            ),
        }

    def _relative(self, project: Path, raw: str, *, writable: bool = False) -> tuple[str, Path]:
        if not raw or "\x00" in raw or Path(raw).is_absolute():
            raise ValueError("Use a nonempty project-relative path")
        resolved = (project / raw).resolve(strict=False)
        try:
            relative = resolved.relative_to(project)
        except ValueError as exc:
            raise ValueError("Path escapes the managed clone") from exc
        if not relative.parts or any(part in DENIED_PARTS for part in relative.parts):
            raise ValueError("Path is protected")
        normalized = relative.as_posix()
        allowed = normalized in (ROOT_WRITABLE if writable else ROOT_READABLE) or (
            relative.parts[0] == "RiemannResearch" and resolved.suffix.lower() in WRITABLE_SUFFIXES
        )
        if not allowed:
            raise ValueError(f"Access is not allowed for {normalized}")
        return normalized, resolved

    def list_files(self, token: str) -> dict:
        _, project = self._get(token)
        output = self._run(["rg", "--files", "-g", "!.git/**", "-g", "!.lake/**"], cwd=project)
        files = []
        for raw in output.splitlines():
            try:
                files.append(self._relative(project, raw)[0])
            except ValueError:
                pass
        return {"workspace_token": token, "project_root": str(project), "files": sorted(files)}

    def read_file(self, token: str, path: str) -> dict:
        _, project = self._get(token)
        normalized, resolved = self._relative(project, path)
        if not resolved.is_file() or resolved.stat().st_size > MAX_READ_BYTES:
            raise ValueError("File is missing or too large")
        return {
            "workspace_token": token,
            "path": normalized,
            "absolute_path": str(resolved),
            "content": resolved.read_text(encoding="utf-8"),
        }

    def _patch_paths(self, project: Path, patch: str) -> list[str]:
        if len(patch.encode()) > MAX_PATCH_BYTES:
            raise ValueError("Patch is too large")
        forbidden = (
            "GIT binary patch", "Binary files ", "deleted file mode", "rename from ",
            "rename to ", "copy from ", "copy to ", "old mode ", "new mode ",
        )
        if any(marker in patch for marker in forbidden):
            raise ValueError("Binary, deletion, rename, copy, and mode-changing patches are denied")
        paths = []
        for line in patch.splitlines():
            if line.startswith("+++ "):
                raw = line[4:].split("\t", 1)[0]
                if raw.startswith("b/"):
                    raw = raw[2:]
                paths.append(self._relative(project, raw, writable=True)[0])
        if not paths:
            raise ValueError("Expected a unified Git patch")
        return sorted(set(paths))

    def apply_patch(self, token: str, patch: str) -> dict:
        _, project = self._get(token)
        paths = self._patch_paths(project, patch)
        self._run(["git", "apply", "--check", "--whitespace=error-all", "-"], cwd=project, input_text=patch)
        self._run(["git", "apply", "--whitespace=error-all", "-"], cwd=project, input_text=patch)
        return {"applied": True, "paths": paths, "project_root": str(project)}

    def git_status(self, token: str) -> dict:
        meta, project = self._get(token, rehydrate=False)
        return {
            "workspace_token": token,
            "state": meta["state"],
            "status": self._run(["git", "status", "--short", "--branch"], cwd=project),
            "recent_commits": self._run(["git", "log", "-n", "8", "--oneline", "--decorate"], cwd=project),
            "published_commit": meta.get("published_commit"),
            "needs_rehydrate": meta.get("needs_rehydrate", False),
        }

    def git_diff(self, token: str) -> dict:
        _, project = self._get(token, rehydrate=False)
        return {
            "unstaged": self._run(["git", "diff", "--no-ext-diff", "--"], cwd=project),
            "staged": self._run(["git", "diff", "--cached", "--no-ext-diff", "--"], cwd=project),
        }

    def sync(self, token: str) -> dict:
        meta, project = self._get(token, rehydrate=False)
        status = self._run(["git", "status", "--porcelain"], cwd=project)
        if status:
            raise ValueError("Refusing to synchronize a dirty isolated workspace; its work was preserved")
        head = self._run(["git", "rev-parse", "HEAD"], cwd=project)
        if head != meta.get("published_commit") and head != meta.get("base_commit"):
            raise ValueError("Workspace has unpublished local commits; checkpoint them before synchronization")
        meta["needs_rehydrate"] = True
        self._write_meta(meta)
        project = self._rehydrate(meta)
        after = self._run(["git", "rev-parse", "HEAD"], cwd=project)
        return {"before": head, "after": after, "changed": head != after, "project_root": str(project)}

    def update_dependencies(self, token: str, package: str = "") -> dict:
        if package and not PACKAGE_RE.fullmatch(package):
            raise ValueError("Invalid Lake package name")
        _, project = self._get(token)
        local_packages = project / ".lake" / "packages"
        if local_packages.is_symlink():
            local_packages.unlink()
        args = ["lake", "update"] + ([package] if package else [])
        output = self._run(args, cwd=project, timeout=1800)
        key = self._attach_dependencies(project)
        return {"updated": package or "all", "shared_dependency_key": key, "output": output[-12000:]}

    def run_code(self, token: str, code: str, timeout_seconds: int = 300) -> dict:
        if not code.strip():
            raise ValueError("Lean code is empty")
        if len(code.encode("utf-8")) > MAX_PATCH_BYTES:
            raise ValueError("Lean code is too large")
        if not 1 <= timeout_seconds <= 1800:
            raise ValueError("timeout_seconds must be between 1 and 1800")
        _, project = self._get(token)
        scratch = project / ".lake" / "agent-scratch"
        scratch.mkdir(parents=True, exist_ok=True)
        path = scratch / f"Run_{secrets.token_hex(12)}.lean"
        path.write_text(code, encoding="utf-8")
        try:
            result = subprocess.run(
                ["lake", "env", "lean", str(path)],
                cwd=project,
                text=True,
                capture_output=True,
                timeout=timeout_seconds,
                check=False,
                env={**os.environ, "GIT_TERMINAL_PROMPT": "0"},
            )
            output = (result.stdout + result.stderr).strip()
            return {
                "workspace_token": token,
                "verified": result.returncode == 0,
                "exit_code": result.returncode,
                "output": output[-12000:],
                "temporary_file_removed": True,
                "project_root": str(project),
            }
        finally:
            path.unlink(missing_ok=True)

    def _scan(self, project: Path) -> list[str]:
        warnings = []
        patterns = {
            "placeholder": re.compile(r"\b(?:sorry|admit)\b"),
            "axiom declaration": re.compile(r"^\s*axiom\b", re.MULTILINE),
            "unsafe declaration": re.compile(r"^\s*unsafe\b", re.MULTILINE),
        }
        for path in (project / "RiemannResearch").rglob("*.lean"):
            text = path.read_text(encoding="utf-8")
            for label, pattern in patterns.items():
                for match in pattern.finditer(text):
                    line = text.count("\n", 0, match.start()) + 1
                    warnings.append(f"{path.relative_to(project)}:{line}: {label}")
        return warnings

    def _build(self, project: Path) -> dict:
        started = time.monotonic()
        output = self._run(["lake", "build", "RiemannResearch", "--quiet"], cwd=project, timeout=3600)
        return {
            "command": "lake build RiemannResearch --quiet",
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "output": "\n".join(output.splitlines()[-200:]),
            "cache": "shared dependency artifacts; private per-clone .lake/build",
        }

    def checkpoint(self, token: str, message: str, push: bool = True) -> dict:
        message = message.strip()
        if not 5 <= len(message) <= 120 or "\n" in message:
            raise ValueError("Commit message must be one line containing 5-120 characters")
        meta, project = self._get(token)
        warnings = self._scan(project)
        if warnings:
            raise ValueError("Lean source audit failed:\n" + "\n".join(warnings[:100]))
        build = self._build(project)
        self._run([
            "git", "add", "--", "RiemannResearch", "RiemannResearch.lean", "README.md",
            "lakefile.toml", "lake-manifest.json", "lean-toolchain", ".gitignore", "AGENTS.md",
        ], cwd=project)
        staged = self._run(["git", "diff", "--cached", "--name-only"], cwd=project)
        if staged:
            self._run(["git", "commit", "-m", message], cwd=project)
        local_head = self._run(["git", "rev-parse", "HEAD"], cwd=project)
        if not push:
            return {"committed": bool(staged), "pushed": False, "commit": local_head, "build": build}

        with self._lock(self.state / ".publish.lock"):
            self._run(["git", "fetch", "origin", "main"], cwd=project)
            origin = self._run(["git", "rev-parse", "origin/main"], cwd=project)
            base = meta["base_commit"]
            if origin == base:
                self._run(["git", "merge-base", "--is-ancestor", origin, local_head], cwd=project)
                self._run(["git", "push", "origin", "HEAD:main"], cwd=project, timeout=600)
                published = local_head
                integrated = False
            else:
                commits = self._run(
                    ["git", "rev-list", "--reverse", f"{base}..{local_head}"], cwd=project
                ).splitlines()
                if not commits:
                    meta["needs_rehydrate"] = True
                    self._write_meta(meta)
                    published = origin
                    integrated = True
                else:
                    integration_parent = self.root / "_integration"
                    integration_parent.mkdir(parents=True, exist_ok=True)
                    integration = Path(tempfile.mkdtemp(prefix="publish-", dir=integration_parent))
                    try:
                        integration.rmdir()
                        self._clone(integration)
                        self._run(["git", "fetch", str(project), local_head], cwd=integration)
                        for commit in commits:
                            self._run(["git", "cherry-pick", commit], cwd=integration)
                        self._attach_dependencies(integration)
                        integrated_build = self._build(integration)
                        self._run(["git", "push", "origin", "HEAD:main"], cwd=integration, timeout=600)
                        published = self._run(["git", "rev-parse", "HEAD"], cwd=integration)
                        build["integrated_build"] = integrated_build
                        integrated = True
                    finally:
                        shutil.rmtree(integration, ignore_errors=True)

            meta.update(
                published_commit=published,
                base_commit=published,
                source_commit=local_head,
                state="published",
                needs_rehydrate=(published != local_head),
                last_activity=time.time(),
            )
            self._write_meta(meta)
        return {
            "committed": bool(staged),
            "pushed": True,
            "source_commit": local_head,
            "commit": published,
            "integrated_with_newer_main": integrated,
            "rehydrate_on_next_workspace_call": meta["needs_rehydrate"],
            "files": staged.splitlines(),
            "build": build,
        }

    def reset(self, token: str, confirmation_token: str = "") -> dict:
        meta, project = self._get(token, rehydrate=False)
        status = self._run(["git", "status", "--porcelain"], cwd=project)
        head = self._run(["git", "rev-parse", "HEAD"], cwd=project)
        tracked_diff = self._run(["git", "diff", "--binary", "HEAD", "--"], cwd=project)
        untracked = self._run(
            ["git", "ls-files", "--others", "--exclude-standard"], cwd=project
        ).splitlines()
        resolved_untracked = []
        for raw in untracked:
            _, path = self._relative(project, raw, writable=True)
            if (
                not path.is_file()
                or path.is_symlink()
                or path.stat().st_size > MAX_PATCH_BYTES
            ):
                raise RuntimeError(f"Reset refused protected untracked path: {raw}")
            resolved_untracked.append((raw, path))
        digest_builder = hashlib.sha256((head + "\0" + status + "\0" + tracked_diff).encode())
        for raw, path in resolved_untracked:
            digest_builder.update(b"\0")
            digest_builder.update(raw.encode())
            digest_builder.update(b"\0")
            digest_builder.update(path.read_bytes())
        digest = digest_builder.hexdigest()
        if not status:
            return {"reset": False, "clean": True, "message": "Workspace is already clean"}
        if not confirmation_token:
            return {
                "reset": False,
                "clean": False,
                "requires_explicit_user_permission": True,
                "status": status.splitlines(),
                "confirmation_token": digest,
            }
        if confirmation_token != digest:
            raise ValueError("Confirmation token is stale; preview again")
        self._run(["git", "restore", "--source=HEAD", "--staged", "--worktree", "--", "."], cwd=project)
        for _, path in resolved_untracked:
            path.unlink()
        meta["last_activity"] = time.time()
        self._write_meta(meta)
        return {"reset": True, "clean": True, "head": head}

    def cleanup(self, retention_days: int = 14, dry_run: bool = True, _already_locked: bool = False) -> dict:
        if not 7 <= retention_days <= 3650:
            raise ValueError("Retention must be between 7 and 3650 days")
        cutoff = time.time() - retention_days * 86400
        archived, preserved = [], []

        def perform() -> None:
            for path in self.state.glob("ws_*.json"):
                meta = json.loads(path.read_text(encoding="utf-8"))
                token = meta["token"]
                project = Path(meta["path"])
                if meta.get("last_activity", 0) >= cutoff or not project.is_dir():
                    continue
                self._validate_workspace_path(token, project)
                if self.can_archive is not None and not self.can_archive(project):
                    preserved.append({
                        "workspace_token": token,
                        "reason": "active Lean client or build",
                    })
                    continue
                status = self._run(["git", "status", "--porcelain"], cwd=project)
                head = self._run(["git", "rev-parse", "HEAD"], cwd=project)
                safe_heads = {meta.get("published_commit"), meta.get("base_commit")}
                if status or head not in safe_heads:
                    preserved.append({"workspace_token": token, "reason": "unpublished work"})
                    continue
                archived.append({"workspace_token": token, "commit": head})
                if not dry_run:
                    if self.before_replace is not None:
                        self.before_replace(project)
                    shutil.rmtree(project)
                    meta.update(
                        state="archived", archive_commit=head, needs_rehydrate=True,
                        archived_at=time.time(),
                    )
                    self._write_meta(meta)

        if _already_locked:
            perform()
        else:
            with self._lock(self.state / ".registry.lock"):
                perform()
        return {
            "dry_run": dry_run,
            "retention_days": retention_days,
            "archived_or_eligible": archived,
            "preserved_unpublished": preserved,
            "policy": "Dirty or unpublished workspaces are never automatically deleted.",
        }
