"""Resumable, isolated Git workspaces for Lean MCP agents.

This module intentionally exposes no arbitrary shell execution.  Every path is
confined to a registered clone and every publication is serialized.
"""

from __future__ import annotations

import fcntl
import fnmatch
import hashlib
import json
import os
import queue
import re
import secrets
import shutil
import subprocess
import tempfile
import threading
import time
from contextlib import contextmanager
from pathlib import Path
from typing import Callable, Iterator


TOKEN_RE = re.compile(r"^ws_[A-Za-z0-9_-]{20,80}$")
JOB_RE = re.compile(r"^job_[A-Za-z0-9_-]{20,80}$")
PACKAGE_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_.-]*$")
MAX_READ_BYTES = 1_000_000
MAX_PATCH_BYTES = 2_000_000
DEFAULT_READ_CHARS = 20_000
MAX_METRICS_BYTES = 5_000_000
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
        try:
            self.lean_num_threads = int(os.environ.get("LEAN_NUM_THREADS", "8"))
        except ValueError as exc:
            raise ValueError("LEAN_NUM_THREADS must be an integer") from exc
        if not 1 <= self.lean_num_threads <= 8:
            raise ValueError("LEAN_NUM_THREADS must be between 1 and 8")
        try:
            requested_build_threads = int(os.environ.get("LEAN_LAKE_BUILD_THREADS", "4"))
        except ValueError as exc:
            raise ValueError("LEAN_LAKE_BUILD_THREADS must be an integer") from exc
        if not 1 <= requested_build_threads <= 4:
            raise ValueError("LEAN_LAKE_BUILD_THREADS must be between 1 and 4")
        self.lake_build_threads = min(requested_build_threads, self.lean_num_threads)
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
        self.project_cache = Path(
            os.environ.get(
                "LEAN_SHARED_PROJECT_BUILDS_ROOT",
                home / ".cache/lean-agent-project-builds",
            )
        ).resolve()
        self.jobs = self.state / "jobs"
        self.metrics_path = self.state / "metrics.jsonl"
        try:
            self.project_cache_keep = int(os.environ.get("LEAN_PROJECT_CACHE_KEEP", "8"))
        except ValueError as exc:
            raise ValueError("LEAN_PROJECT_CACHE_KEEP must be an integer") from exc
        if not 1 <= self.project_cache_keep <= 128:
            raise ValueError("LEAN_PROJECT_CACHE_KEEP must be between 1 and 128")
        for path in (self.root, self.state, self.shared, self.project_cache, self.jobs):
            path.mkdir(parents=True, exist_ok=True)
        self._job_queue: queue.Queue[str] = queue.Queue()
        self._job_guard = threading.Lock()
        self._metrics_guard = threading.Lock()
        self._job_local = threading.local()
        self._active_job: str | None = None
        self._recover_interrupted_jobs()
        self._job_worker_thread = threading.Thread(
            target=self._job_worker,
            name="lean-workspace-jobs",
            daemon=True,
        )
        self._job_worker_thread.start()

    def _record_metric(self, event: str, **fields: object) -> None:
        record = {"time": time.time(), "event": event, **fields}
        line = json.dumps(record, separators=(",", ":"), sort_keys=True) + "\n"
        try:
            with self._metrics_guard:
                if (
                    self.metrics_path.is_file()
                    and self.metrics_path.stat().st_size > MAX_METRICS_BYTES
                ):
                    rotated = self.metrics_path.with_suffix(".jsonl.1")
                    rotated.unlink(missing_ok=True)
                    os.replace(self.metrics_path, rotated)
                with self.metrics_path.open("a", encoding="utf-8") as handle:
                    handle.write(line)
        except OSError:
            # Observability must never interrupt proof or publication work.
            pass

    @staticmethod
    def _workspace_label(token: str) -> str:
        return hashlib.sha256(token.encode("utf-8")).hexdigest()[:12]

    def _run(
        self,
        args: list[str],
        *,
        cwd: Path,
        input_text: str | None = None,
        timeout: int = 300,
        lean_num_threads: int | None = None,
    ) -> str:
        started = time.monotonic()
        result = subprocess.run(
            args,
            cwd=cwd,
            input=input_text,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
            env={
                **os.environ,
                "GIT_TERMINAL_PROMPT": "0",
                "LEAN_NUM_THREADS": str(lean_num_threads or self.lean_num_threads),
            },
        )
        output = (result.stdout + result.stderr).strip()
        self._record_metric(
            "command",
            program=args[0],
            action=args[1] if len(args) > 1 else "",
            elapsed_seconds=round(time.monotonic() - started, 3),
            exit_code=result.returncode,
            output_chars=len(output),
        )
        if result.returncode:
            raise RuntimeError(
                f"Command failed ({result.returncode}): {' '.join(args)}\n{output[-8000:]}"
            )
        return output

    @contextmanager
    def _lock(self, path: Path, *, shared: bool = False) -> Iterator[None]:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a+", encoding="utf-8") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_SH if shared else fcntl.LOCK_EX)
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

    def _clone(self, destination: Path, commit: str | None = None) -> dict:
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
        dependency_key = self._attach_dependencies(destination)
        return self._restore_project_cache(destination, dependency_key)

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

    def _project_cache_dir(self, dependency_key: str, commit: str) -> Path:
        if not re.fullmatch(r"[0-9a-f]{40}", commit):
            raise ValueError("Project cache requires a full Git commit SHA")
        return self.project_cache / dependency_key / commit

    def _copy_build_tree(self, source: Path, destination: Path) -> None:
        if destination.exists():
            shutil.rmtree(destination)
        destination.mkdir(parents=True)
        result = subprocess.run(
            ["cp", "--archive", "--reflink=auto", f"{source}/.", str(destination)],
            text=True,
            capture_output=True,
            check=False,
        )
        if result.returncode:
            shutil.rmtree(destination, ignore_errors=True)
            shutil.copytree(source, destination)

    def _restore_project_cache(self, project: Path, dependency_key: str) -> dict:
        commit = self._run(["git", "rev-parse", "HEAD"], cwd=project)
        cache = self._project_cache_dir(dependency_key, commit)
        source = cache / "build"
        ready = cache / "READY.json"
        with self._lock(self.project_cache / ".cache.lock", shared=True):
            if not ready.is_file() or not source.is_dir():
                return {"restored": False, "commit": commit, "dependency_key": dependency_key}
            destination = project / ".lake" / "build"
            temporary = (
                destination.parent / f".build.restore.{os.getpid()}.{secrets.token_hex(4)}"
            )
            try:
                self._copy_build_tree(source, temporary)
                if destination.exists():
                    shutil.rmtree(destination)
                os.replace(temporary, destination)
            finally:
                shutil.rmtree(temporary, ignore_errors=True)
        return {
            "restored": True,
            "commit": commit,
            "dependency_key": dependency_key,
            "cache_path": str(cache),
        }

    def _publish_project_cache(self, project: Path) -> dict:
        status = self._run(["git", "status", "--porcelain"], cwd=project)
        if status:
            return {"published": False, "reason": "workspace source is dirty"}
        source = project / ".lake" / "build"
        if not source.is_dir():
            return {"published": False, "reason": "project build directory is missing"}
        dependency_key = self._dependency_key(project)
        commit = self._run(["git", "rev-parse", "HEAD"], cwd=project)
        cache = self._project_cache_dir(dependency_key, commit)
        ready = cache / "READY.json"
        lock = self.project_cache / dependency_key / f".{commit}.lock"
        with self._lock(lock):
            if ready.is_file() and (cache / "build").is_dir():
                return {
                    "published": False,
                    "already_present": True,
                    "commit": commit,
                    "dependency_key": dependency_key,
                }
            temporary = cache.parent / f".{commit}.tmp.{os.getpid()}.{secrets.token_hex(4)}"
            shutil.rmtree(temporary, ignore_errors=True)
            temporary.mkdir(parents=True)
            try:
                self._copy_build_tree(source, temporary / "build")
                (temporary / "READY.json").write_text(
                    json.dumps(
                        {
                            "commit": commit,
                            "dependency_key": dependency_key,
                            "created_at": time.time(),
                        },
                        sort_keys=True,
                    )
                    + "\n",
                    encoding="utf-8",
                )
                if cache.exists():
                    shutil.rmtree(cache)
                os.replace(temporary, cache)
            finally:
                shutil.rmtree(temporary, ignore_errors=True)
        self._prune_project_cache(dependency_key)
        return {
            "published": True,
            "commit": commit,
            "dependency_key": dependency_key,
            "cache_path": str(cache),
        }

    def _prune_project_cache(self, dependency_key: str) -> None:
        with self._lock(self.project_cache / ".cache.lock"):
            root = self.project_cache / dependency_key
            entries = []
            if not root.is_dir():
                return
            for path in root.iterdir():
                ready = path / "READY.json"
                if not path.is_dir() or not ready.is_file():
                    continue
                try:
                    created_at = json.loads(ready.read_text(encoding="utf-8"))["created_at"]
                except (OSError, KeyError, ValueError, TypeError, json.JSONDecodeError):
                    continue
                entries.append((float(created_at), path))
            for _, path in sorted(entries, reverse=True)[self.project_cache_keep :]:
                shutil.rmtree(path, ignore_errors=True)

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
        project_cache = self._clone(project, commit=commit)
        if commit:
            self._run(["git", "switch", "-C", "main", commit], cwd=project)
        else:
            commit = self._run(["git", "rev-parse", "HEAD"], cwd=project)
        meta.update(
            state="active",
            base_commit=commit,
            needs_rehydrate=False,
            rehydrated_at=time.time(),
            project_cache=project_cache,
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
                project_cache = self._clone(project)
                head = self._run(["git", "rev-parse", "HEAD"], cwd=project)
                meta.update(base_commit=head, state="active", project_cache=project_cache)
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
            "project_cache": meta.get("project_cache", {"restored": False}),
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

    def list_files(self, token: str, pattern: str = "", limit: int = 200) -> dict:
        if len(pattern) > 200:
            raise ValueError("pattern is too long")
        if not 1 <= limit <= 1000:
            raise ValueError("limit must be between 1 and 1000")
        _, project = self._get(token)
        output = self._run(["rg", "--files", "-g", "!.git/**", "-g", "!.lake/**"], cwd=project)
        files = []
        for raw in output.splitlines():
            try:
                files.append(self._relative(project, raw)[0])
            except ValueError:
                pass
        files = sorted(files)
        if pattern:
            lowered = pattern.lower()
            files = [
                path for path in files
                if lowered in path.lower() or fnmatch.fnmatch(path, pattern)
            ]
        total = len(files)
        result = {
            "workspace_token": token,
            "project_root": str(project),
            "pattern": pattern,
            "files": files[:limit],
            "total_matches": total,
            "truncated": total > limit,
        }
        self._record_metric(
            "list_files",
            workspace=self._workspace_label(token),
            total_matches=total,
            returned=min(total, limit),
        )
        return result

    def search_files(
        self,
        token: str,
        query: str,
        file_glob: str = "*.lean",
        limit: int = 20,
        case_sensitive: bool = False,
        max_match_chars: int = 500,
    ) -> dict:
        """Search approved project text files without exposing unrestricted rg."""
        if not query.strip() or len(query) > 200 or "\n" in query or "\r" in query:
            raise ValueError("query must be one non-empty line of at most 200 characters")
        if not file_glob or len(file_glob) > 200:
            raise ValueError("file_glob must contain 1-200 characters")
        if not 1 <= limit <= 100:
            raise ValueError("limit must be between 1 and 100")
        if not 80 <= max_match_chars <= 1000:
            raise ValueError("max_match_chars must be between 80 and 1000")

        _, project = self._get(token)
        listed = self.list_files(token, limit=1000)
        paths = [path for path in listed["files"] if fnmatch.fnmatch(path, file_glob)]
        needle = query if case_sensitive else query.casefold()
        matches: list[dict[str, object]] = []
        total_matches = 0
        for relative in paths:
            normalized, resolved = self._relative(project, relative)
            if not resolved.is_file() or resolved.stat().st_size > MAX_READ_BYTES:
                continue
            try:
                lines = resolved.read_text(encoding="utf-8").splitlines()
            except UnicodeDecodeError:
                continue
            for line_number, line in enumerate(lines, start=1):
                haystack = line if case_sensitive else line.casefold()
                column = haystack.find(needle)
                if column < 0:
                    continue
                total_matches += 1
                if len(matches) >= limit:
                    continue
                start = max(0, column - max_match_chars // 3)
                end = min(len(line), start + max_match_chars)
                if end - start < max_match_chars:
                    start = max(0, end - max_match_chars)
                excerpt = line[start:end]
                matches.append({
                    "path": normalized,
                    "line": line_number,
                    "column": column + 1,
                    "text": ("…" if start else "") + excerpt + ("…" if end < len(line) else ""),
                    "text_start_column": start + 1,
                })

        result = {
            "workspace_token": token,
            "query": query,
            "file_glob": file_glob,
            "case_sensitive": case_sensitive,
            "matches": matches,
            "total_matches": total_matches,
            "truncated": total_matches > len(matches),
        }
        self._record_metric(
            "search_files",
            workspace=self._workspace_label(token),
            searched_files=len(paths),
            total_matches=total_matches,
            returned=len(matches),
        )
        return result

    def read_file(
        self,
        token: str,
        path: str,
        start_line: int = 1,
        end_line: int = 0,
        max_chars: int = DEFAULT_READ_CHARS,
    ) -> dict:
        if start_line < 1 or end_line < 0 or (end_line and end_line < start_line):
            raise ValueError("Use a valid 1-based line range")
        if not 1 <= max_chars <= 100_000:
            raise ValueError("max_chars must be between 1 and 100000")
        _, project = self._get(token)
        normalized, resolved = self._relative(project, path)
        if not resolved.is_file() or resolved.stat().st_size > MAX_READ_BYTES:
            raise ValueError("File is missing or too large")
        text = resolved.read_text(encoding="utf-8")
        lines = text.splitlines(keepends=True)
        selected = "".join(lines[start_line - 1 : end_line or None])
        truncated = len(selected) > max_chars
        content = selected[:max_chars]
        returned_lines = content.count("\n") + (1 if content and not content.endswith("\n") else 0)
        result = {
            "workspace_token": token,
            "path": normalized,
            "absolute_path": str(resolved),
            "content": content,
            "start_line": start_line,
            "end_line": start_line + max(returned_lines - 1, 0),
            "total_lines": len(lines),
            "truncated": truncated or bool(end_line and end_line < len(lines)),
        }
        self._record_metric(
            "read_file",
            workspace=self._workspace_label(token),
            path=normalized,
            returned_chars=len(content),
            truncated=result["truncated"],
        )
        return result

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
        self._ensure_workspace_idle(token, "apply a patch")
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
            "recent_commits": self._run(["git", "log", "-n", "3", "--oneline", "--decorate"], cwd=project),
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
        self._ensure_workspace_idle(token, "synchronize")
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
        self._ensure_workspace_idle(token, "update dependencies")
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
        self._ensure_workspace_idle(token, "run Lean code")
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
        started = time.monotonic()
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
            verified = result.returncode == 0
            output_limit = 4000 if verified else 8000
            response = {
                "workspace_token": token,
                "verified": verified,
                "exit_code": result.returncode,
                "output": output[-output_limit:],
                "output_truncated": len(output) > output_limit,
                "temporary_file_removed": True,
                "project_root": str(project),
            }
            self._record_metric(
                "run_code",
                workspace=self._workspace_label(token),
                elapsed_seconds=round(time.monotonic() - started, 3),
                verified=verified,
                request_chars=len(code),
                output_chars=len(response["output"]),
            )
            return response
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
        output = self._run(
            ["lake", "build", "RiemannResearch", "--quiet"],
            cwd=project,
            timeout=3600,
            lean_num_threads=self.lake_build_threads,
        )
        result = {
            "command": "lake build RiemannResearch --quiet",
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "lean_num_threads": self.lake_build_threads,
            "output": "\n".join(output.splitlines()[-20:]),
            "cache": "shared dependencies and commit-keyed seed; private per-clone .lake/build",
        }
        result["project_cache"] = self._publish_project_cache(project)
        self._record_metric(
            "build",
            elapsed_seconds=result["elapsed_seconds"],
            output_chars=len(result["output"]),
            cache_published=result["project_cache"].get("published", False),
        )
        return result

    def build(self, token: str) -> dict:
        self._ensure_workspace_idle(token, "build")
        _, project = self._get(token)
        return self._build(project)

    def checkpoint(self, token: str, message: str, push: bool = True) -> dict:
        self._ensure_workspace_idle(token, "checkpoint")
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
            project_cache = self._publish_project_cache(project)
            return {
                "committed": bool(staged),
                "pushed": False,
                "commit": local_head,
                "build": build,
                "project_cache": project_cache,
            }

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
        if not meta["needs_rehydrate"]:
            project_cache = self._publish_project_cache(project)
        else:
            project_cache = {
                "published": False,
                "reason": "integrated commit cache was produced by the clean integration build",
            }
        return {
            "committed": bool(staged),
            "pushed": True,
            "source_commit": local_head,
            "commit": published,
            "integrated_with_newer_main": integrated,
            "rehydrate_on_next_workspace_call": meta["needs_rehydrate"],
            "files": staged.splitlines(),
            "build": build,
            "project_cache": project_cache,
        }

    def _job_path(self, job_id: str) -> Path:
        if not JOB_RE.fullmatch(job_id):
            raise ValueError("Invalid job ID")
        return self.jobs / f"{job_id}.json"

    def _read_job(self, job_id: str) -> dict:
        path = self._job_path(job_id)
        if not path.is_file():
            raise ValueError("Unknown job ID")
        return json.loads(path.read_text(encoding="utf-8"))

    def _write_job(self, job: dict) -> None:
        path = self._job_path(job["job_id"])
        temporary = path.with_suffix(f".tmp.{os.getpid()}.{secrets.token_hex(4)}")
        temporary.write_text(
            json.dumps(job, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        os.replace(temporary, path)

    def _recover_interrupted_jobs(self) -> None:
        for path in self.jobs.glob("job_*.json"):
            try:
                job = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, ValueError, json.JSONDecodeError):
                continue
            if job.get("state") not in {"queued", "running"}:
                continue
            job.update(
                state="interrupted",
                finished_at=time.time(),
                error=(
                    "The MCP service restarted while this job was pending. Inspect workspace "
                    "and Git status before submitting it again."
                ),
            )
            self._write_job(job)

    def _queue_position(self, job_id: str) -> int | None:
        with self._job_guard:
            if self._active_job == job_id:
                return 0
            with self._job_queue.mutex:
                pending = list(self._job_queue.queue)
            try:
                return pending.index(job_id) + (1 if self._active_job else 0) + 1
            except ValueError:
                job = self._read_job(job_id)
                return 1 if job.get("state") == "queued" else None

    def _existing_job(self, token: str, kind: str) -> dict | None:
        for path in self.jobs.glob("job_*.json"):
            try:
                job = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, ValueError, json.JSONDecodeError):
                continue
            if (
                job.get("workspace_token") == token
                and job.get("kind") == kind
                and job.get("state") in {"queued", "running"}
            ):
                return job
        return None

    def _pending_job_for_workspace(self, token: str) -> dict | None:
        for path in self.jobs.glob("job_*.json"):
            try:
                job = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, ValueError, json.JSONDecodeError):
                continue
            if (
                job.get("workspace_token") == token
                and job.get("state") in {"queued", "running"}
            ):
                return job
        return None

    def _ensure_workspace_idle(self, token: str, operation: str) -> None:
        if getattr(self._job_local, "workspace_token", None) == token:
            return
        job = self._pending_job_for_workspace(token)
        if job is not None:
            raise RuntimeError(
                f"Cannot {operation} while job {job['job_id']} is {job['state']}; "
                "poll agent_workspace_job_status until it is terminal."
            )

    def _submit_job(self, token: str, kind: str, arguments: dict) -> dict:
        self._meta_path(token)
        if not self._meta_path(token).is_file():
            raise ValueError("Unknown workspace token")
        with self._job_guard:
            existing = self._existing_job(token, kind)
            if existing is not None:
                job_id = existing["job_id"]
                position = self._queue_position_unlocked(job_id)
                retry_after = (
                    45
                    if existing["state"] == "running"
                    else min(180, 60 + 30 * max((position or 1) - 1, 0))
                )
                return {
                    "accepted": False,
                    "existing": True,
                    "job_id": job_id,
                    "state": existing["state"],
                    "queue_position": position,
                    "retry_after_seconds": retry_after,
                    "instruction": "Poll after retry_after_seconds; do not resubmit.",
                }
            pending = self._pending_job_for_workspace(token)
            if pending is not None:
                raise RuntimeError(
                    f"Workspace already has {pending['kind']} job {pending['job_id']} "
                    f"{pending['state']}; poll it until terminal before submitting {kind}."
                )
            job_id = "job_" + secrets.token_urlsafe(24)
            job = {
                "job_id": job_id,
                "workspace_token": token,
                "kind": kind,
                "arguments": arguments,
                "state": "queued",
                "submitted_at": time.time(),
            }
            self._write_job(job)
            self._job_queue.put(job_id)
            position = self._queue_position_unlocked(job_id)
        self._record_metric(
            "job_submitted",
            job_id=job_id,
            workspace=self._workspace_label(token),
            kind=kind,
            queue_position=position,
        )
        return {
            "accepted": True,
            "job_id": job_id,
            "state": "queued",
            "queue_position": position,
            "retry_after_seconds": min(
                180, 60 + 30 * max((position or 1) - 1, 0)
            ),
            "instruction": (
                "Poll after retry_after_seconds until terminal. Do not resubmit."
            ),
        }

    def _queue_position_unlocked(self, job_id: str) -> int | None:
        if self._active_job == job_id:
            return 0
        with self._job_queue.mutex:
            pending = list(self._job_queue.queue)
        try:
            return pending.index(job_id) + (1 if self._active_job else 0) + 1
        except ValueError:
            job = self._read_job(job_id)
            return 1 if job.get("state") == "queued" else None

    def submit_build(self, token: str) -> dict:
        return self._submit_job(token, "build", {})

    def submit_build_for_project(self, project_path: str) -> dict:
        project = Path(project_path).expanduser().resolve()
        for path in self.state.glob("ws_*.json"):
            try:
                meta = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, ValueError, json.JSONDecodeError):
                continue
            registered = Path(meta.get("path", "")).resolve(strict=False)
            if registered == project:
                self._validate_workspace_path(meta["token"], registered)
                return self.submit_build(meta["token"])
        raise ValueError(
            "lean_project_path must be the exact project_root returned by "
            "agent_workspace_open"
        )

    def submit_checkpoint(self, token: str, message: str, push: bool = True) -> dict:
        message = message.strip()
        if not 5 <= len(message) <= 120 or "\n" in message:
            raise ValueError("Commit message must be one line containing 5-120 characters")
        return self._submit_job(token, "checkpoint", {"message": message, "push": push})

    def submit_update_dependencies(self, token: str, package: str = "") -> dict:
        if package and not PACKAGE_RE.fullmatch(package):
            raise ValueError("Invalid Lake package name")
        return self._submit_job(token, "update_dependencies", {"package": package})

    def _execute_job(self, job: dict) -> dict:
        token = job["workspace_token"]
        arguments = job["arguments"]
        self._job_local.workspace_token = token
        try:
            if job["kind"] == "build":
                return self.build(token)
            if job["kind"] == "checkpoint":
                return self.checkpoint(token, arguments["message"], arguments["push"])
            if job["kind"] == "update_dependencies":
                return self.update_dependencies(token, arguments.get("package", ""))
            raise RuntimeError(f"Unsupported job kind: {job['kind']}")
        finally:
            self._job_local.workspace_token = None

    def _job_worker(self) -> None:
        while True:
            job_id = self._job_queue.get()
            with self._job_guard:
                self._active_job = job_id
                job = self._read_job(job_id)
                job.update(state="running", started_at=time.time())
                self._write_job(job)
            try:
                result = self._execute_job(job)
            except Exception as exc:
                job.update(
                    state="failed",
                    finished_at=time.time(),
                    error=f"{type(exc).__name__}: {exc}",
                )
            else:
                job.update(state="succeeded", finished_at=time.time(), result=result)
            finally:
                self._write_job(job)
                self._record_metric(
                    "job_finished",
                    job_id=job_id,
                    kind=job.get("kind"),
                    state=job.get("state"),
                    elapsed_seconds=round(
                        job.get("finished_at", time.time())
                        - job.get("started_at", job.get("submitted_at", time.time())),
                        3,
                    ),
                )
                with self._job_guard:
                    self._active_job = None
                self._job_queue.task_done()

    @staticmethod
    def _compact_result(value: object, *, include_logs: bool) -> object:
        if isinstance(value, dict):
            return {
                key: AgentWorkspaceManager._compact_result(item, include_logs=include_logs)
                for key, item in value.items()
                if include_logs or key != "output"
            }
        if isinstance(value, list):
            return [
                AgentWorkspaceManager._compact_result(item, include_logs=include_logs)
                for item in value
            ]
        return value

    def job_status(self, job_id: str, include_logs: bool = False) -> dict:
        job = self._read_job(job_id)
        now = time.time()
        response = {
            key: value
            for key, value in job.items()
            if key not in {"arguments"}
        }
        response["queue_position"] = self._queue_position(job_id)
        response["elapsed_seconds"] = round(
            (job.get("finished_at", now) - job.get("started_at", job["submitted_at"])),
            3,
        )
        response["terminal"] = job["state"] in {
            "succeeded",
            "failed",
            "interrupted",
        }
        if response["terminal"]:
            retry_after = 0
        elif job["state"] == "running":
            retry_after = 45
        else:
            # Poll less frequently as the job sits farther back in the FIFO.
            retry_after = min(
                180,
                60 + 30 * max((response["queue_position"] or 1) - 1, 0),
            )
        response["retry_after_seconds"] = retry_after
        if "result" in response:
            response["result"] = self._compact_result(
                response["result"], include_logs=include_logs
            )
        self._record_metric(
            "job_status",
            job_id=job_id,
            state=job["state"],
            terminal=response["terminal"],
            include_logs=include_logs,
            response_chars=len(json.dumps(response, separators=(",", ":"))),
        )
        return response

    def reset(self, token: str, confirmation_token: str = "") -> dict:
        self._ensure_workspace_idle(token, "reset")
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
                pending_job = self._pending_job_for_workspace(token)
                if pending_job is not None:
                    preserved.append({
                        "workspace_token": token,
                        "reason": f"queued or running job {pending_job['job_id']}",
                    })
                    continue
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
