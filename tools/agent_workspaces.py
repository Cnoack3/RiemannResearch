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
import selectors
import secrets
import shutil
import signal
import subprocess
import tempfile
import threading
import time
from contextlib import contextmanager
from functools import wraps
from pathlib import Path
from typing import Callable, Iterator


TOKEN_RE = re.compile(r"^ws_[A-Za-z0-9_-]{20,80}$")
JOB_RE = re.compile(r"^job_[A-Za-z0-9_-]{20,80}$")
PACKAGE_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_.-]*$")
MAX_READ_BYTES = 1_000_000
MAX_PATCH_BYTES = 2_000_000
DEFAULT_READ_CHARS = 20_000
MAX_METRICS_BYTES = 5_000_000
PROGRESS_UPDATE_SECONDS = 60
MAX_VERIFICATION_OUTPUT_BYTES = 32_000
DENIED_PARTS = {".git", ".lake", ".elan", ".ssh", "tools", "__pycache__"}
ROOT_WRITABLE = {
    ".gitignore", "AGENTS.md", "README.md", "RiemannResearch.lean", "lakefile.toml"
}
ROOT_READABLE = ROOT_WRITABLE | {
    "lake-manifest.json", "lakefile.toml", "lean-toolchain"
}
WRITABLE_SUFFIXES = {".lean", ".md", ".toml", ".yml", ".yaml", ".json"}


def _workspace_operation(method):
    """Serialize full managed mutations, not merely their initial idle check."""
    @wraps(method)
    def locked(self, token, *args, **kwargs):
        if method.__name__ != "_get":
            # Fail fast when already busy, then repeat the authoritative check
            # inside the decorated mutation after its full operation lock.
            self._ensure_workspace_idle(token, method.__name__)
        with self._operation_lock(token):
            return method(self, token, *args, **kwargs)
    return locked


def _lake_cache_operation(method):
    @wraps(method)
    def locked(self, args, **kwargs):
        cache = os.environ.get("LAKE_CACHE_DIR")
        if not os.environ.get("LEAN_REMOTE_CACHE_SERVICE") or not cache or args[0] != "lake":
            return method(self, args, **kwargs)
        root = Path(cache).expanduser().resolve()
        try:
            with self._lock(root.parent / f".{root.name}.lock", shared=True):
                return method(self, args, **kwargs)
        finally:
            if args[:2] == ["lake", "build"] and "-o" not in args:
                self._prune_native_cache()
    return locked


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
            requested_build_threads = int(os.environ.get("LEAN_LAKE_BUILD_THREADS", "8"))
        except ValueError as exc:
            raise ValueError("LEAN_LAKE_BUILD_THREADS must be an integer") from exc
        if not 1 <= requested_build_threads <= 8:
            raise ValueError("LEAN_LAKE_BUILD_THREADS must be between 1 and 8")
        self.lake_build_threads = min(requested_build_threads, self.lean_num_threads)
        try:
            self.job_workers = int(os.environ.get("LEAN_JOB_WORKERS", "1"))
        except ValueError as exc:
            raise ValueError("LEAN_JOB_WORKERS must be an integer") from exc
        if not 1 <= self.job_workers <= 4:
            raise ValueError("LEAN_JOB_WORKERS must be between 1 and 4")
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
        self._operation_local = threading.local()
        self._active_jobs: set[str] = set()
        # A lifetime lease distinguishes another live manager from an actual
        # restart. The OS releases it on process exit, including SIGKILL.
        self._owner_id = secrets.token_hex(16)
        self._owner_directory = self.state / "job-owners"
        self._owner_directory.mkdir(exist_ok=True)
        self._owner_lease = (self._owner_directory / self._owner_id).open("a+")
        fcntl.flock(self._owner_lease.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        self._recover_interrupted_jobs()
        self._job_worker_threads = [
            threading.Thread(
                target=self._job_worker,
                name=f"lean-workspace-job-{index + 1}",
                daemon=True,
            )
            for index in range(self.job_workers)
        ]
        for worker in self._job_worker_threads:
            worker.start()

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

    @_lake_cache_operation
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

    def _set_job_progress(
        self,
        phase: str,
        *,
        detail: str = "",
        current: int | None = None,
        total: int | None = None,
        force: bool = False,
    ) -> None:
        job_id = getattr(self._job_local, "job_id", None)
        if not job_id:
            return
        now = time.time()
        last_write = getattr(self._job_local, "last_progress_write", 0.0)
        if not force and current != total and now - last_write < PROGRESS_UPDATE_SECONDS:
            return
        previous = getattr(self._job_local, "progress", {})
        phase_started_at = (
            previous.get("phase_started_at", now)
            if previous.get("phase") == phase
            else now
        )
        percent = None
        if current is not None and total:
            percent = round(min(100.0, 100.0 * current / total), 1)
        progress = {
            "phase": phase,
            "detail": detail[-240:],
            "current": current,
            "total": total,
            "percent": percent,
            "phase_started_at": phase_started_at,
            "updated_at": now,
        }
        with self._job_guard:
            job = self._read_job(job_id)
            if job.get("state") != "running":
                return
            job["progress"] = progress
            self._write_job(job)
        self._job_local.progress = progress
        self._job_local.last_progress_write = now

    @staticmethod
    def _parse_lake_progress(record: str) -> tuple[int, int, str] | None:
        clean = re.sub(r"\x1b\[[0-9;?]*[ -/]*[@-~]", "", record)
        match = re.search(r"\[(\d+)/(\d+)\]\s+(.+)", clean)
        if match is None:
            return None
        return int(match.group(1)), int(match.group(2)), match.group(3).strip()

    @_lake_cache_operation
    def _run_streaming(
        self,
        args: list[str],
        *,
        cwd: Path,
        timeout: int,
        phase: str,
    ) -> str:
        """Run a long command while publishing bounded Lake-style progress."""
        service = os.environ.get("LEAN_REMOTE_CACHE_SERVICE")
        if service and args[:2] == ["lake", "build"] and "-o" not in args:
            options = [f"--service={service}", "--repo=Cnoack3/RiemannResearch"]
            with tempfile.TemporaryDirectory(prefix="lake-cache-") as tmp:
                mappings = str(Path(tmp) / "outputs.jsonl")
                try:
                    self._run_streaming(
                        ["lake", "cache", "get", "--mappings-only", *options],
                        cwd=cwd, timeout=timeout, phase="remote_cache_restore",
                    )
                except RuntimeError as exc:
                    if "no outputs found" not in str(exc):
                        raise
                output = self._run_streaming(
                    [*args, "-o", mappings], cwd=cwd, timeout=timeout, phase=phase,
                )
                self._run_streaming(
                    ["lake", "cache", "put", mappings, *options],
                    cwd=cwd, timeout=timeout, phase="remote_cache_upload",
                )
                if self.can_archive is None or self.can_archive(cwd):
                    self._remove_setup_files(cwd)
                return output
        started = time.monotonic()
        self._set_job_progress(phase, detail="Starting " + " ".join(args), force=True)
        process = subprocess.Popen(
            args,
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            bufsize=0,
            start_new_session=True,
            env={
                **os.environ,
                "GIT_TERMINAL_PROMPT": "0",
                "LEAN_NUM_THREADS": str(self.lake_build_threads),
            },
        )
        if process.stdout is None:
            raise RuntimeError("Failed to capture command output")
        selector = selectors.DefaultSelector()
        selector.register(process.stdout, selectors.EVENT_READ)
        output = ""
        pending = ""
        deadline = started + timeout
        try:
            while True:
                if time.monotonic() > deadline:
                    self._kill_verification_group(process)
                    raise subprocess.TimeoutExpired(args, timeout, output=output[-8000:])
                events = selector.select(timeout=1.0)
                for key, _ in events:
                    chunk = os.read(key.fileobj.fileno(), 65536)
                    if not chunk:
                        selector.unregister(key.fileobj)
                        continue
                    text = chunk.decode("utf-8", errors="replace")
                    output = (output + text)[-100_000:]
                    pending += text
                    records = re.split(r"[\r\n]+", pending)
                    pending = records.pop()
                    for record in records:
                        parsed = self._parse_lake_progress(record)
                        if parsed is not None:
                            current, total, detail = parsed
                            self._set_job_progress(
                                phase,
                                detail=detail,
                                current=current,
                                total=total,
                                force=current == total,
                            )
                if process.poll() is not None and not selector.get_map():
                    break
            if pending:
                parsed = self._parse_lake_progress(pending)
                if parsed is not None:
                    current, total, detail = parsed
                    self._set_job_progress(
                        phase,
                        detail=detail,
                        current=current,
                        total=total,
                        force=True,
                    )
        finally:
            selector.close()
            process.stdout.close()
        elapsed = round(time.monotonic() - started, 3)
        output = output.strip()
        self._record_metric(
            "command",
            program=args[0],
            action=args[1] if len(args) > 1 else "",
            elapsed_seconds=elapsed,
            exit_code=process.returncode,
            output_chars=len(output),
        )
        if process.returncode:
            raise RuntimeError(
                f"Command failed ({process.returncode}): {' '.join(args)}\n{output[-8000:]}"
            )
        return output

    def _dependency_cache_preflight(self, project: Path) -> tuple[str, dict]:
        """Populate exact dependency binaries before a build.

        Cache downloads are globally serialized. A failed preflight is not a
        build failure, but it causes the build itself to take an exclusive
        per-dependency lock so Lake can safely fill missing artifacts.
        """
        key = self._attach_dependencies(project)
        started = time.monotonic()
        output = ""
        error = None
        self._set_job_progress(
            "dependency_cache",
            detail="Waiting for protected binary-cache preparation",
            force=True,
        )
        with self._lock(self.shared / ".cache-get.lock"):
            try:
                output = self._run_streaming(
                    ["lake", "exe", "cache", "get"],
                    cwd=project,
                    timeout=1800,
                    phase="dependency_cache",
                )
            except (RuntimeError, subprocess.TimeoutExpired) as exc:
                error = str(exc)[-2000:]
        result = {
            "command": "lake exe cache get",
            "status": "complete" if error is None else "incomplete",
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "output": "\n".join(output.splitlines()[-20:]),
        }
        if error is not None:
            result["warning"] = error
        return key, result

    def _run_lake_build(
        self, project: Path, args: list[str], *, timeout: int = 3600
    ) -> tuple[str, dict]:
        key, cache = self._dependency_cache_preflight(project)
        if cache["status"] == "complete":
            output = self._run_streaming(
                args, cwd=project, timeout=timeout, phase="building"
            )
        else:
            with self._lock(self.shared / key / ".fallback-build.lock"):
                output = self._run_streaming(
                    args, cwd=project, timeout=timeout, phase="building"
                )
        return output, cache

    @staticmethod
    def _remove_setup_files(project: Path) -> None:
        for path in (project / ".lake" / "build" / "ir").rglob("*.setup.json"):
            path.unlink(missing_ok=True)

    def _prune_native_cache(self) -> None:
        cache = os.environ.get("LAKE_CACHE_DIR")
        if not os.environ.get("LEAN_REMOTE_CACHE_SERVICE") or not cache:
            return
        root = Path(cache).expanduser().resolve()
        with self._lock(root.parent / f".{root.name}.lock"):
            files = []
            for name in ("artifacts", "outputs", "revisions"):
                for path in (root / name).rglob("*"):
                    if path.is_file() and not path.is_symlink():
                        stat = path.stat()
                        files.append((stat.st_mtime_ns, str(path), stat.st_size))
            size = sum(item[2] for item in files)
            for _, path, length in sorted(files):
                if size <= 20 * 1024**3:
                    break
                Path(path).unlink()
                size -= length
                parent = Path(path).parent
                while parent != root:
                    try:
                        parent.rmdir()
                    except OSError:
                        break
                    parent = parent.parent

    @contextmanager
    def _lock(self, path: Path, *, shared: bool = False) -> Iterator[None]:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a+", encoding="utf-8") as handle:
            fcntl.flock(handle.fileno(), fcntl.LOCK_SH if shared else fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)

    @contextmanager
    def _operation_lock(self, token: str) -> Iterator[None]:
        """Cross-process, same-thread-reentrant lease for managed workspace operations.

        Admission/status never take this potentially long-held lock. External
        writers and raw Lean/LSP clients do not participate in this protocol.
        """
        self._meta_path(token)
        held = getattr(self._operation_local, "held", None)
        if held is None:
            held = self._operation_local.held = set()
        if token in held:
            yield
            return
        with self._lock(self.state / f"{token}.operation.lock"):
            held.add(token)
            try:
                yield
            finally:
                held.remove(token)

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
                cache_error = None
                try:
                    self._run(
                        ["lake", "exe", "cache", "get"],
                        cwd=project,
                        timeout=1200,
                        lean_num_threads=self.lake_build_threads,
                    )
                except (RuntimeError, subprocess.TimeoutExpired) as exc:
                    # Some exact dependency revisions do not have complete
                    # binary releases. Lake will fill missing artifacts during
                    # a per-dependency serialized fallback build.
                    cache_error = str(exc)[-2000:]
                temp = self.shared / f".{key}.tmp.{os.getpid()}"
                if temp.exists():
                    shutil.rmtree(temp)
                temp.mkdir(parents=True)
                if not local_packages.is_dir():
                    raise RuntimeError("Lake did not materialize dependency packages")
                shutil.move(str(local_packages), str(temp / "packages"))
                (temp / "READY.json").write_text(
                    json.dumps(
                        {
                            "key": key,
                            "created_at": time.time(),
                            "binary_cache_complete": cache_error is None,
                            "binary_cache_error": cache_error,
                        }
                    )
                    + "\n",
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
        if os.environ.get("LEAN_REMOTE_CACHE_SERVICE"):
            self._remove_setup_files(project)
        return {
            "restored": True,
            "commit": commit,
            "dependency_key": dependency_key,
            "cache_path": str(cache),
        }

    def _publish_project_cache(self, project: Path) -> dict:
        if os.environ.get("LEAN_REMOTE_CACHE_SERVICE"):
            return {"published": False, "reason": "native remote cache replaces commit snapshots"}
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
            with self._operation_lock(resume_token), self._lock(self.state / f"{resume_token}.lock"):
                meta = self._read_meta(resume_token)
                project = Path(meta["path"])
                if not project.is_dir() or meta.get("needs_rehydrate"):
                    self._ensure_workspace_idle(resume_token, "restore workspace")
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
            with self._operation_lock(token), self._lock(self.state / f"{token}.lock"):
                project_cache = self._clone(project)
                head = self._run(["git", "rev-parse", "HEAD"], cwd=project)
                meta.update(base_commit=head, state="active", project_cache=project_cache)
                self._write_meta(meta)
                resumed = False
        return self.describe(meta, resumed=resumed)

    @_workspace_operation
    def _get(self, token: str, *, rehydrate: bool = True) -> tuple[dict, Path]:
        self._meta_path(token)
        with self._lock(self.state / f"{token}.lock"):
            meta = self._read_meta(token)
            project = Path(meta["path"])
            self._validate_workspace_path(token, project)
            if rehydrate and (not project.is_dir() or meta.get("needs_rehydrate")):
                self._ensure_workspace_idle(token, "restore workspace")
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
        _, project = self._read_project(token)
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

        _, project = self._read_project(token)
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
        _, project = self._read_project(token)
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

    @_workspace_operation
    def apply_patch(self, token: str, patch: str) -> dict:
        self._ensure_workspace_idle(token, "apply a patch")
        _, project = self._get(token)
        paths = self._patch_paths(project, patch)
        self._run(["git", "apply", "--check", "--whitespace=error-all", "-"], cwd=project, input_text=patch)
        self._run(["git", "apply", "--whitespace=error-all", "-"], cwd=project, input_text=patch)
        architecture_issues = self._architecture_audit(project)
        return {
            "applied": True,
            "paths": paths,
            "project_root": str(project),
            "checkpoint_ready": not architecture_issues,
            "architecture_issues": architecture_issues,
        }

    def git_status(self, token: str) -> dict:
        meta, project = self._read_project(token)
        return {
            "workspace_token": token,
            "state": meta["state"],
            "status": self._run(["git", "status", "--short", "--branch"], cwd=project),
            "recent_commits": self._run(["git", "log", "-n", "3", "--oneline", "--decorate"], cwd=project),
            "published_commit": meta.get("published_commit"),
            "needs_rehydrate": meta.get("needs_rehydrate", False),
        }

    def git_diff(self, token: str) -> dict:
        _, project = self._read_project(token)
        return {
            "unstaged": self._run(["git", "diff", "--no-ext-diff", "--"], cwd=project),
            "staged": self._run(["git", "diff", "--cached", "--no-ext-diff", "--"], cwd=project),
        }

    @_workspace_operation
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

    @_workspace_operation
    def update_dependencies(self, token: str, package: str = "") -> dict:
        self._ensure_workspace_idle(token, "update dependencies")
        if package and not PACKAGE_RE.fullmatch(package):
            raise ValueError("Invalid Lake package name")
        _, project = self._get(token)
        self._set_job_progress(
            "updating_dependencies",
            detail=f"Updating {package or 'all exact dependencies'}",
            force=True,
        )
        local_packages = project / ".lake" / "packages"
        if local_packages.is_symlink():
            local_packages.unlink()
        args = ["lake", "update"] + ([package] if package else [])
        output = self._run(args, cwd=project, timeout=1800)
        key = self._attach_dependencies(project)
        return {"updated": package or "all", "shared_dependency_key": key, "output": output[-12000:]}

    @staticmethod
    def _validate_verification_timeout(timeout_seconds: int) -> None:
        if type(timeout_seconds) is not int or not 1 <= timeout_seconds <= 1800:
            raise ValueError("timeout_seconds must be an integer between 1 and 1800")

    @classmethod
    def _validate_code(cls, code: str, timeout_seconds: int) -> None:
        if not isinstance(code, str) or not code.strip():
            raise ValueError("Lean code is empty")
        if len(code.encode("utf-8")) > MAX_PATCH_BYTES:
            raise ValueError("Lean code is too large")
        if "\x00" in code:
            raise ValueError("Lean code contains a NUL character")
        cls._validate_verification_timeout(timeout_seconds)

    def _read_project(self, token: str) -> tuple[dict, Path]:
        """Read-only snapshot; no restore, writer lock, or metadata overwrite.

        Reads are not transactional against managed or external source changes.
        Explicitly reopen archived/stale clones before reading or admission.
        """
        meta = self._read_meta(token)
        project = Path(meta["path"])
        self._validate_workspace_path(token, project)
        if (
            meta.get("state") not in {"active", "published"} or not project.is_dir()
        ):
            raise ValueError("Resume this workspace with agent_workspace_open before reading or verification")
        return meta, project

    def _verification_project(self, token: str) -> Path:
        meta, project = self._read_project(token)
        if meta.get("needs_rehydrate"):
            raise ValueError("Resume this workspace with agent_workspace_open before verification")
        return project

    def _verification_file(self, project: Path, raw: str) -> tuple[str, Path, str]:
        if not isinstance(raw, str) or not raw or len(raw) > 4096 or "\x00" in raw:
            raise ValueError("Use an approved Lean file path of at most 4096 characters")
        normalized, path = self._relative(project, raw)
        if path.suffix != ".lean" or not path.is_file():
            raise ValueError("Verification requires an existing approved .lean file")
        if path.stat().st_size > MAX_READ_BYTES:
            raise ValueError("Lean file is too large")
        with path.open("rb") as handle:
            content = handle.read(MAX_READ_BYTES + 1)
        if len(content) > MAX_READ_BYTES:
            raise ValueError("Lean file is too large")
        return normalized, path, hashlib.sha256(content).hexdigest()

    @staticmethod
    def _request_sha256(token: str, kind: str, arguments: dict) -> str:
        request = {"workspace_token": token, "kind": kind, "arguments": arguments}
        encoded = json.dumps(
            request, sort_keys=True, separators=(",", ":"), ensure_ascii=False
        ).encode("utf-8")
        return hashlib.sha256(encoded).hexdigest()

    @staticmethod
    def _kill_verification_group(process: subprocess.Popen) -> None:
        # Kill descendants even if the Lake parent has exited but they still
        # hold its diagnostic pipe. Reap our direct child; orphan descendants
        # are reaped by the host's init, not by this (non-subreaper) service.
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()

    def _run_verification(self, project: Path, path: Path, timeout_seconds: int) -> dict:
        """Bound memory and wall time independently of Lean's logical limits."""
        started = time.monotonic()
        self._set_job_progress("verifying", detail="Checking Lean source", force=True)
        try:
            process = subprocess.Popen(
                ["lake", "env", "lean", str(path)],
                cwd=project,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                bufsize=0,
                start_new_session=True,
                env={
                    **os.environ,
                    "GIT_TERMINAL_PROMPT": "0",
                    "LEAN_NUM_THREADS": str(self.lean_num_threads),
                },
            )
        except OSError as exc:
            return {
                "verified": False, "classification": "process_error", "exit_code": None,
                "error": f"{type(exc).__name__}: {exc}"[-1000:],
                "timeout_seconds": timeout_seconds,
                "elapsed_seconds": round(time.monotonic() - started, 3),
                "output": "", "output_truncated": False, "output_bytes": 0,
            }
        selector = selectors.DefaultSelector()
        tail = b""
        output_bytes = 0
        timed_out = False
        deadline = started + timeout_seconds
        try:
            assert process.stdout is not None
            selector.register(process.stdout, selectors.EVENT_READ)
            while selector.get_map() or process.poll() is None:
                now = time.monotonic()
                if now >= deadline:
                    if timed_out:
                        break  # An escaped descendant must not hold us indefinitely.
                    timed_out = True
                    self._kill_verification_group(process)
                    deadline = time.monotonic() + 1.0  # Bounded post-kill pipe drain.
                for key, _ in selector.select(timeout=min(0.1, max(0.0, deadline - now))):
                    chunk = os.read(key.fileobj.fileno(), 65536)
                    if not chunk:
                        selector.unregister(key.fileobj)
                    else:
                        output_bytes += len(chunk)
                        tail = (tail + chunk)[-MAX_VERIFICATION_OUTPUT_BYTES:]
            process.wait()
        finally:
            if process.poll() is None:
                self._kill_verification_group(process)
            selector.close()
            if process.stdout is not None:
                process.stdout.close()
        verified = not timed_out and process.returncode == 0
        output = tail.decode("utf-8", errors="replace").strip()
        output_limit = 4000 if verified else 8000
        return {
            "verified": verified,
            "classification": (
                "wall_timeout" if timed_out else "success" if verified
                else "process_error" if process.returncode < 0 else "compiler_error"
            ),
            "exit_code": process.returncode,
            "timeout_seconds": timeout_seconds,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "output": output[-output_limit:],
            "output_truncated": output_bytes > len(tail) or len(output) > output_limit,
            "output_bytes": output_bytes,
        }

    @_workspace_operation
    def run_code(self, token: str, code: str, timeout_seconds: int = 300) -> dict:
        """Synchronous execution primitive; MCP callers should submit_run_code."""
        self._ensure_workspace_idle(token, "run Lean code")
        self._validate_code(code, timeout_seconds)
        _, project = self._get(token)
        scratch = project / ".lake" / "agent-scratch"
        scratch.mkdir(parents=True, exist_ok=True)
        path = scratch / f"Run_{secrets.token_hex(12)}.lean"
        response = {
            "workspace_token": token,
            "project_root": str(project),
            "request_sha256": self._request_sha256(
                token, "run_code", {"code": code, "timeout_seconds": timeout_seconds}
            ),
            "code_sha256": hashlib.sha256(code.encode("utf-8")).hexdigest(),
            "temporary_file_removed": False,
        }
        try:
            path.write_text(code, encoding="utf-8")
            response.update(self._run_verification(project, path, timeout_seconds))
        finally:
            try:
                path.unlink(missing_ok=True)
            except OSError as exc:
                response["cleanup_error"] = str(exc)[-1000:]
            response["temporary_file_removed"] = not path.exists()
        self._record_metric(
            "run_code",
            workspace=self._workspace_label(token),
            elapsed_seconds=response["elapsed_seconds"],
            verified=response["verified"],
            request_chars=len(code),
            output_chars=len(response["output"]),
        )
        return response

    @_workspace_operation
    def _check_file(self, token: str, path: str, timeout_seconds: int, file_sha256: str) -> dict:
        self._ensure_workspace_idle(token, "check Lean file")
        self._validate_verification_timeout(timeout_seconds)
        _, project = self._get(token)
        normalized, resolved, checked_sha256 = self._verification_file(project, path)
        if checked_sha256 != file_sha256:
            raise RuntimeError("Lean file changed after submission; submit its current contents again")
        result = {
            "workspace_token": token,
            "project_root": str(project),
            "path": normalized,
            "file_sha256": file_sha256,
            "checked_file_sha256": checked_sha256,
            # No temporary file is created or removed for an existing-file check.
            "temporary_file_removed": None,
            **self._run_verification(project, resolved, timeout_seconds),
        }
        try:
            unchanged = self._verification_file(project, path)[2] == file_sha256
        except (OSError, ValueError):
            unchanged = False
        if not unchanged:
            result.update(
                verified=False,
                classification="source_changed",
                error="Lean file changed during verification; this result is not a certificate",
            )
        return result

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

    @staticmethod
    def _head_text(project: Path, relative: str) -> str | None:
        result = subprocess.run(
            ["git", "show", f"HEAD:{relative}"],
            cwd=project,
            text=True,
            capture_output=True,
            check=False,
        )
        return result.stdout if result.returncode == 0 else None

    def _architecture_audit(self, project: Path) -> list[str]:
        changed = self._run(
            [
                "git", "diff", "--name-only", "--diff-filter=ACMR", "HEAD", "--",
                "RiemannResearch", "RiemannResearch.lean",
            ],
            cwd=project,
        ).splitlines()
        untracked = self._run(
            [
                "git", "ls-files", "--others", "--exclude-standard", "--",
                "RiemannResearch", "RiemannResearch.lean",
            ],
            cwd=project,
        ).splitlines()
        relative_files = sorted(
            {path for path in changed + untracked if path.endswith(".lean")}
        )
        export_text = (project / "RiemannResearch.lean").read_text(encoding="utf-8")
        umbrella = re.compile(r"^\s*import\s+Mathlib\s*(?:--.*)?$", re.MULTILINE)
        problems: list[str] = []
        for relative in relative_files:
            path = project / relative
            text = path.read_text(encoding="utf-8")
            baseline = self._head_text(project, relative)
            is_new = baseline is None
            match = umbrella.search(text)
            if match is not None:
                line = text.count("\n", 0, match.start()) + 1
                problems.append(
                    f"{relative}:{line}: umbrella `import Mathlib` is forbidden in "
                    "new or modified modules; use focused Mathlib/project imports"
                )

            parts = Path(relative).parts
            if is_new and len(parts) < 3:
                problems.append(
                    f"{relative}: new modules must live in a named subject directory "
                    "under RiemannResearch/"
                )

            if is_new and relative != "RiemannResearch.lean":
                module = relative.removesuffix(".lean").replace("/", ".")
                if not re.search(
                    rf"^\s*import\s+{re.escape(module)}\s*$",
                    export_text,
                    re.MULTILINE,
                ):
                    problems.append(
                        f"{relative}: new module is not exported by RiemannResearch.lean"
                    )
        return problems

    def _build(self, project: Path) -> dict:
        started = time.monotonic()
        output, dependency_cache = self._run_lake_build(
            project,
            ["lake", "build", "RiemannResearch", "--quiet"],
            timeout=3600,
        )
        result = {
            "command": "lake build RiemannResearch --quiet",
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "lean_num_threads": self.lake_build_threads,
            "output": "\n".join(output.splitlines()[-20:]),
            "cache": "shared dependencies and commit-keyed seed; private per-clone .lake/build",
            "dependency_cache": dependency_cache,
        }
        result["project_cache"] = self._publish_project_cache(project)
        self._record_metric(
            "build",
            elapsed_seconds=result["elapsed_seconds"],
            output_chars=len(result["output"]),
            cache_published=result["project_cache"].get("published", False),
        )
        return result

    def _checkpoint_changed_paths(
        self,
        project: Path,
        base_ref: str = "HEAD",
        include_untracked: bool = True,
    ) -> list[str]:
        changed = self._run(
            ["git", "diff", "--name-only", "--diff-filter=ACDMRTUXB", base_ref, "--"],
            cwd=project,
        ).splitlines()
        if include_untracked:
            changed.extend(
                self._run(
                    ["git", "ls-files", "--others", "--exclude-standard"],
                    cwd=project,
                ).splitlines()
            )
        return sorted(set(changed))

    @staticmethod
    def _lean_module(relative: str) -> str | None:
        if not relative.startswith("RiemannResearch/") or not relative.endswith(".lean"):
            return None
        return relative.removesuffix(".lean").replace("/", ".")

    def _affected_lean_targets(self, project: Path, changed_modules: set[str]) -> list[str]:
        reverse_imports: dict[str, set[str]] = {}
        import_pattern = re.compile(
            r"^\s*import\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*(?:--.*)?$",
            re.MULTILINE,
        )
        for path in (project / "RiemannResearch").rglob("*.lean"):
            module = self._lean_module(str(path.relative_to(project)))
            if module is None:
                continue
            text = path.read_text(encoding="utf-8")
            for imported in import_pattern.findall(text):
                if imported.startswith("RiemannResearch."):
                    reverse_imports.setdefault(imported, set()).add(module)

        affected = set(changed_modules)
        pending = list(changed_modules)
        while pending:
            imported = pending.pop()
            for dependent in reverse_imports.get(imported, set()):
                if dependent not in affected:
                    affected.add(dependent)
                    pending.append(dependent)
        return sorted(affected)

    def _checkpoint_validation(
        self,
        project: Path,
        base_ref: str = "HEAD",
        include_untracked: bool = True,
    ) -> dict:
        changed_paths = self._checkpoint_changed_paths(
            project, base_ref=base_ref, include_untracked=include_untracked
        )
        dependency_files = {"lakefile.toml", "lake-manifest.json", "lean-toolchain"}
        changed_project_lean = {
            path for path in changed_paths if self._lean_module(path) is not None
        }
        deleted_project_lean = {
            path for path in changed_project_lean if not (project / path).is_file()
        }

        if dependency_files.intersection(changed_paths) or deleted_project_lean:
            result = self._build(project)
            result.update(
                scope="full",
                reason=(
                    "dependency configuration changed"
                    if dependency_files.intersection(changed_paths)
                    else "a project Lean module was deleted or moved"
                ),
                changed_paths=changed_paths,
            )
            return result

        changed_modules = {
            module
            for path in changed_project_lean
            if (module := self._lean_module(path)) is not None
        }
        if not changed_modules:
            if "RiemannResearch.lean" in changed_paths:
                result = self._build(project)
                result.update(
                    scope="full",
                    reason="the aggregate project module changed without a changed child module",
                    changed_paths=changed_paths,
                )
                return result
            result = {
                "command": None,
                "scope": "skipped",
                "reason": "no project Lean or dependency files changed",
                "changed_paths": changed_paths,
                "elapsed_seconds": 0,
                "output": "",
            }
            self._record_metric(
                "checkpoint_validation",
                scope="skipped",
                changed_path_count=len(changed_paths),
                elapsed_seconds=0,
            )
            return result

        targets = self._affected_lean_targets(project, changed_modules)
        lake_targets = [f"+{module}" for module in targets]
        started = time.monotonic()
        output, dependency_cache = self._run_lake_build(
            project,
            ["lake", "build", *lake_targets, "--quiet"],
            timeout=3600,
        )
        result = {
            "command": f"lake build <{len(targets)} affected module(s)> --quiet",
            "scope": "affected_modules",
            "changed_paths": changed_paths,
            "changed_modules": sorted(changed_modules),
            "target_count": len(targets),
            "targets": targets[:100],
            "targets_truncated": len(targets) > 100,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "lean_num_threads": self.lake_build_threads,
            "output": "\n".join(output.splitlines()[-20:]),
            "cache": "shared dependencies; private per-clone affected-module build",
            "dependency_cache": dependency_cache,
        }
        self._record_metric(
            "checkpoint_validation",
            scope="affected_modules",
            changed_path_count=len(changed_paths),
            changed_module_count=len(changed_modules),
            target_count=len(targets),
            elapsed_seconds=result["elapsed_seconds"],
            output_chars=len(result["output"]),
        )
        return result

    @_workspace_operation
    def build(self, token: str) -> dict:
        self._ensure_workspace_idle(token, "build")
        _, project = self._get(token)
        return self._build(project)

    @_workspace_operation
    def checkpoint(self, token: str, message: str, push: bool = True) -> dict:
        self._ensure_workspace_idle(token, "checkpoint")
        message = message.strip()
        if not 5 <= len(message) <= 120 or "\n" in message:
            raise ValueError("Commit message must be one line containing 5-120 characters")
        meta, project = self._get(token)
        self._set_job_progress("auditing", detail="Auditing changed source", force=True)
        warnings = self._scan(project)
        warnings.extend(self._architecture_audit(project))
        if warnings:
            raise ValueError("Lean source audit failed:\n" + "\n".join(warnings[:100]))
        build = self._checkpoint_validation(project)
        self._set_job_progress("committing", detail="Creating local checkpoint", force=True)
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

        self._set_job_progress("publishing", detail="Waiting for publication lock", force=True)
        with self._lock(self.state / ".publish.lock"):
            self._set_job_progress("publishing", detail="Synchronizing with origin/main", force=True)
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
                    self._set_job_progress(
                        "integrating",
                        detail="Validating changes against newer origin/main",
                        force=True,
                    )
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
                        integrated_build = self._checkpoint_validation(
                            integration, base_ref="origin/main", include_untracked=False
                        )
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

    def _job_owner_alive(self, job: dict) -> bool:
        owner = job.get("owner_id", "")
        if not isinstance(owner, str) or not re.fullmatch(r"[0-9a-f]{32}", owner):
            return False  # Legacy records have no liveness lease.
        with (self._owner_directory / owner).open("a+") as handle:
            try:
                fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                return True
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
        return False

    def _recover_interrupted_jobs(self) -> None:
        # Serialize recovery with admission, never with long-running execution.
        # Pending jobs are never replayed: a checkpoint may have published just
        # before the owner died, and retrying it automatically would be unsafe.
        with self._lock(self.state / ".jobs-admission.lock"):
            for path in self.jobs.glob("job_*.json"):
                try:
                    job = json.loads(path.read_text(encoding="utf-8"))
                except (OSError, ValueError, json.JSONDecodeError):
                    continue
                self._interrupt_abandoned_job(job)

    def _interrupt_abandoned_job(self, job: dict) -> dict:
        """Caller holds admission lock and has read a fresh job record."""
        if job.get("state") in {"queued", "running"} and not self._job_owner_alive(job):
            job.update(
                state="interrupted",
                finished_at=time.time(),
                error=(
                    "The job owner exited while this job was pending. Inspect workspace "
                    "and Git status before submitting it again; it was not replayed."
                ),
            )
            self._write_job(job)
        return job

    def _read_live_job(self, job_id: str) -> dict:
        job = self._read_job(job_id)
        if job.get("state") in {"queued", "running"} and not self._job_owner_alive(job):
            with self._lock(self.state / ".jobs-admission.lock"):
                job = self._interrupt_abandoned_job(self._read_job(job_id))
        return job

    @contextmanager
    def _heavy_worker_slot(self) -> Iterator[None]:
        """Admission for queued work across cooperating managers on this state root.

        Explicit LEAN_JOB_WORKERS overrides select the slot count. All managers
        should use the same setting. This does NOT limit raw LSP/external Lean,
        synchronous internal helpers, or unrelated tools outside this queue.
        """
        self._set_job_progress(
            "waiting_for_worker", detail="Waiting for a shared heavy-worker slot", force=True
        )
        while True:
            for index in range(self.job_workers):
                handle = (self.state / f".heavy-worker-{index}.lock").open("a+")
                try:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    handle.close()
                    continue
                try:
                    yield
                finally:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
                    handle.close()
                return
            time.sleep(0.05)

    def _queue_position(self, job_id: str) -> int | None:
        with self._job_guard:
            if job_id in self._active_jobs:
                return 0
            with self._job_queue.mutex:
                pending = list(self._job_queue.queue)
            try:
                return pending.index(job_id) + 1
            except ValueError:
                job = self._read_job(job_id)
                return 1 if job.get("state") == "queued" else None

    def _existing_job(self, token: str, kind: str, arguments: dict) -> dict | None:
        for path in self.jobs.glob("job_*.json"):
            try:
                job = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, ValueError, json.JSONDecodeError):
                continue
            if (
                job.get("workspace_token") == token
                and job.get("kind") == kind
                and job.get("arguments") == arguments
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
            job = self._read_live_job(job["job_id"])
            if job.get("state") not in {"queued", "running"}:
                job = None
        if job is not None:
            raise RuntimeError(
                f"Cannot {operation} while job {job['job_id']} is {job['state']}; "
                "poll agent_workspace_job_status until it is terminal."
            )

    def _submit_job(self, token: str, kind: str, arguments: dict) -> dict:
        self._meta_path(token)
        if not self._meta_path(token).is_file():
            raise ValueError("Unknown workspace token")
        with self._job_guard, self._lock(self.state / ".jobs-admission.lock"):
            pending = self._pending_job_for_workspace(token)
            if pending is not None:
                self._interrupt_abandoned_job(pending)
            existing = self._existing_job(token, kind, arguments)
            if existing is not None:
                job_id = existing["job_id"]
                position = self._queue_position_unlocked(job_id)
                retry_after = (
                    60
                    if existing["state"] == "running"
                    else min(120, 30 + 15 * max((position or 1) - 1, 0))
                )
                return {
                    "accepted": False,
                    "existing": True,
                    "job_id": job_id,
                    "state": existing["state"],
                    "request_sha256": existing.get("request_sha256"),
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
                "request_sha256": self._request_sha256(token, kind, arguments),
                "owner_id": self._owner_id,
                "state": "queued",
                "submitted_at": time.time(),
                "progress": {
                    "phase": "queued",
                    "detail": "Waiting for an available workspace worker",
                    "current": None,
                    "total": None,
                    "percent": None,
                    "phase_started_at": time.time(),
                    "updated_at": time.time(),
                },
            }
            if kind == "run_code":
                job["code_sha256"] = hashlib.sha256(arguments["code"].encode("utf-8")).hexdigest()
            elif kind == "check_file":
                job["file_sha256"] = arguments["file_sha256"]
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
            "request_sha256": job["request_sha256"],
            "queue_position": position,
            "worker_count": self.job_workers,
            "retry_after_seconds": min(120, 30 + 15 * max((position or 1) - 1, 0)),
            "instruction": (
                "Poll after retry_after_seconds until terminal. Do not resubmit."
            ),
        }

    def _queue_position_unlocked(self, job_id: str) -> int | None:
        if job_id in self._active_jobs:
            return 0
        with self._job_queue.mutex:
            pending = list(self._job_queue.queue)
        try:
            return pending.index(job_id) + 1
        except ValueError:
            job = self._read_job(job_id)
            return 1 if job.get("state") == "queued" else None

    def submit_build(self, token: str) -> dict:
        return self._submit_job(token, "build", {})

    def submit_run_code(self, token: str, code: str, timeout_seconds: int = 300) -> dict:
        self._validate_code(code, timeout_seconds)
        self._verification_project(token)
        return self._submit_job(
            token, "run_code", {"code": code, "timeout_seconds": timeout_seconds}
        )

    def submit_check_file(self, token: str, path: str, timeout_seconds: int = 300) -> dict:
        self._validate_verification_timeout(timeout_seconds)
        project = self._verification_project(token)
        _, _, file_sha256 = self._verification_file(project, path)
        return self._submit_job(
            token, "check_file",
            {"path": path, "timeout_seconds": timeout_seconds, "file_sha256": file_sha256},
        )

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
            if job["kind"] == "run_code":
                return self.run_code(token, arguments["code"], arguments["timeout_seconds"])
            if job["kind"] == "check_file":
                return self._check_file(
                    token, arguments["path"], arguments["timeout_seconds"], arguments["file_sha256"]
                )
            raise RuntimeError(f"Unsupported job kind: {job['kind']}")
        finally:
            self._job_local.workspace_token = None

    def _job_worker(self) -> None:
        while True:
            job_id = self._job_queue.get()
            with self._job_guard:
                self._active_jobs.add(job_id)
                job = self._read_job(job_id)
                job.update(state="running", started_at=time.time())
                self._write_job(job)
            self._job_local.job_id = job_id
            self._job_local.last_progress_write = 0.0
            self._job_local.progress = {}
            try:
                with self._heavy_worker_slot():
                    self._set_job_progress(
                        "waiting_for_workspace", detail="Waiting for the workspace operation lock",
                        force=True,
                    )
                    with self._operation_lock(job["workspace_token"]):
                        result = self._execute_job(job)
                result["request_sha256"] = job["request_sha256"]
            except Exception as exc:
                job.update(
                    state="failed",
                    finished_at=time.time(),
                    error=f"{type(exc).__name__}: {exc}"[-8000:],
                )
            else:
                verification_failed = (
                    job["kind"] in {"run_code", "check_file"} and not result.get("verified")
                )
                job.update(
                    state="failed" if verification_failed else "succeeded",
                    finished_at=time.time(), result=result,
                )
            finally:
                with self._job_guard:
                    current = self._read_job(job_id)
                    current.update(
                        {key: value for key, value in job.items() if key != "progress"}
                    )
                    progress = current.get("progress", {})
                    progress.update(
                        phase="complete" if job.get("state") == "succeeded" else "failed",
                        percent=100.0 if job.get("state") == "succeeded" else progress.get("percent"),
                        updated_at=time.time(),
                    )
                    current["progress"] = progress
                    self._write_job(current)
                    self._active_jobs.discard(job_id)
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
                self._job_local.job_id = None
                self._job_local.progress = {}
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

    def list_jobs(self, token: str, limit: int = 20) -> dict:
        """Recover job IDs after a lost response; never include code, arguments, or logs."""
        self._read_meta(token)
        if type(limit) is not int or not 1 <= limit <= 100:
            raise ValueError("limit must be an integer between 1 and 100")
        jobs = []
        for path in self.jobs.glob("job_*.json"):
            try:
                job = json.loads(path.read_text(encoding="utf-8"))
                if job.get("workspace_token") != token:
                    continue
                job = self._read_live_job(job["job_id"])
            except (OSError, ValueError, KeyError, json.JSONDecodeError):
                continue
            jobs.append({
                key: job.get(key)
                for key in ("job_id", "kind", "state", "request_sha256", "submitted_at")
            })
            jobs[-1]["terminal"] = job.get("state") in {"succeeded", "failed", "interrupted"}
        jobs.sort(key=lambda job: (job["submitted_at"], job["job_id"]), reverse=True)
        return {
            "workspace_token": token, "jobs": jobs[:limit],
            "total_matches": len(jobs), "truncated": len(jobs) > limit,
        }

    def job_status(self, job_id: str, include_logs: bool = False) -> dict:
        job = self._read_live_job(job_id)
        now = time.time()
        response = {
            key: value
            for key, value in job.items()
            if key not in {"arguments"}
        }
        response["queue_position"] = self._queue_position(job_id)
        response["worker_count"] = self.job_workers
        response["active_job_count"] = len(self._active_jobs)
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
            retry_after = 60
        else:
            retry_after = min(120, 30 + 15 * max((response["queue_position"] or 1) - 1, 0))
        response["retry_after_seconds"] = retry_after
        progress = response.get("progress")
        if job["state"] == "running" and isinstance(progress, dict):
            current = progress.get("current")
            total = progress.get("total")
            phase_started = progress.get("phase_started_at")
            if current and total and phase_started and current < total:
                phase_elapsed = max(0.0, now - float(phase_started))
                estimated_total = phase_elapsed * total / current
                progress["estimated_remaining_seconds"] = round(
                    max(0.0, estimated_total - phase_elapsed), 1
                )
                progress["estimate_note"] = "Task-count estimate; Lean tasks vary in cost."
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

    @_workspace_operation
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

        def inspect_workspace(path: Path) -> None:
            # Re-read after acquiring the operation lease: an in-flight change
            # may have refreshed metadata or dirtied the clone while we waited.
            meta = json.loads(path.read_text(encoding="utf-8"))
            token = meta["token"]
            project = Path(meta["path"])
            if meta.get("last_activity", 0) >= cutoff or not project.is_dir():
                return
            self._validate_workspace_path(token, project)
            pending_job = self._pending_job_for_workspace(token)
            if pending_job is not None:
                preserved.append({
                    "workspace_token": token,
                    "reason": f"queued or running job {pending_job['job_id']}",
                })
                return
            if self.can_archive is not None and not self.can_archive(project):
                preserved.append({
                    "workspace_token": token,
                    "reason": "active Lean client or build",
                })
                return
            status = self._run(["git", "status", "--porcelain"], cwd=project)
            head = self._run(["git", "rev-parse", "HEAD"], cwd=project)
            safe_heads = {meta.get("published_commit"), meta.get("base_commit")}
            if status or head not in safe_heads:
                preserved.append({"workspace_token": token, "reason": "unpublished work"})
                return
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

        def perform() -> None:
            for path in self.state.glob("ws_*.json"):
                meta = json.loads(path.read_text(encoding="utf-8"))
                if meta.get("last_activity", 0) >= cutoff:
                    continue
                with self._operation_lock(meta["token"]):
                    inspect_workspace(path)

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

