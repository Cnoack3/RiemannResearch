"""Native Lake content-addressed caching through an authenticated loopback bridge.

Designed for the RiemannResearch verifier's managed build entry point. This
module never commits/pushes, never changes dependency sources and never cleans
build trees. Lake remains responsible for checking source/import/build traces.
Pinned protocol reference: leanprover/lean4 v4.33.0-rc2, Lake/CLI/Main.lean.
"""
from __future__ import annotations

import hashlib
import json
import os
import platform
import re
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

SERVICE = "lean-gcs"
NAME_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_.-]*$")
MAX_MAP_BYTES = 128 * 1024 * 1024


def validate_mapping(data: bytes) -> None:
    """Reject malformed maps before Lake's permissive JSONL parser sees them."""
    lines = data.decode("utf-8").splitlines()
    if not lines or not isinstance(json.loads(lines[0]), str):
        raise ValueError("Missing Lake mappings schema header")
    for line in lines[1:]:
        if not line.strip():
            continue
        row = json.loads(line)
        if not isinstance(row, list) or len(row) != 2:
            raise ValueError("Invalid Lake input-to-output mapping")


class RemoteArtifactCache:
    def __init__(self, manager, project: Path, dependency_key: str):
        self.manager, self.project = manager, project
        self.url = os.environ.get("LEAN_REMOTE_CACHE_URL", "").rstrip("/")
        self.enabled = bool(self.url)
        self.required = os.environ.get("LEAN_REMOTE_CACHE_REQUIRED", "1") != "0"
        self.result = {"enabled": self.enabled, "restored": [], "misses": [], "uploaded": [], "already_uploaded": []}
        if not self.enabled:
            return
        parsed = urllib.parse.urlsplit(self.url)
        if (parsed.scheme != "http" or parsed.hostname != "127.0.0.1"
                or parsed.query or parsed.fragment or parsed.username
                or parsed.path not in ("", "/")):
            raise ValueError("LEAN_REMOTE_CACHE_URL must be an HTTP loopback origin")
        if os.environ.get("LAKE_ARTIFACT_CACHE", "").lower() not in {"1", "true", "yes", "on"}:
            raise ValueError("Remote caching requires LAKE_ARTIFACT_CACHE=true")
        if not os.environ.get("LAKE_CONFIG") or not os.environ.get("LAKE_CACHE_DIR"):
            raise ValueError("Remote caching requires LAKE_CONFIG and LAKE_CACHE_DIR")
        namespace = os.environ.get("LEAN_REMOTE_CACHE_NAMESPACE", "Cnoack3/RiemannResearch")
        if not namespace or any(not re.fullmatch(r"[A-Za-z0-9_.-]+", p) or p in {".", ".."}
                                for p in namespace.split("/")):
            raise ValueError("Invalid remote cache namespace")
        toolchain = (project / "lean-toolchain").read_bytes()
        system = (platform.system() + "/" + platform.machine()).encode()
        identity = hashlib.sha256(toolchain + b"\0" + system).hexdigest()[:24]
        # Dependency configuration, Lean version and platform isolate native hash
        # spaces. Source/import options remain part of Lake's own input hash.
        self.base = f"{namespace}/v1/{identity}/{dependency_key}"
        self.receipts = Path(os.environ.get("LEAN_REMOTE_CACHE_RECEIPTS",
                                           manager.shared / "remote-artifact-receipts"))
        self.receipts.mkdir(parents=True, exist_ok=True, mode=0o700)
        manifest = json.loads((project / "lake-manifest.json").read_text())
        self.packages = []
        for pkg in manifest.get("packages", []):
            name = pkg.get("name", "")
            if not NAME_RE.fullmatch(name):
                raise ValueError("Invalid package name in Lake manifest")
            if pkg.get("type") not in {None, "git"}:
                raise ValueError("Remote dependency export currently requires Git dependencies")
            self.packages.append(name)
        if len(set(self.packages)) != len(self.packages) or len(self.packages) > 64:
            raise ValueError("Invalid dependency package list")

    def scope(self, package: str | None = None) -> str:
        return self.base + (f"/dependencies/{package}" if package else "/project")

    def command(self, args, phase="remote_cache"):
        return self.manager._run_streaming(args, cwd=self.project, timeout=1800, phase=phase)

    def restore(self) -> None:
        for package in [None, *self.packages]:
            scope = self.scope(package)
            url = self.url + "/r0/" + urllib.parse.quote(scope, safe="/") + "/latest.jsonl"
            try:
                with urllib.request.urlopen(url, timeout=60) as response:
                    data = response.read(MAX_MAP_BYTES + 1)
            except urllib.error.HTTPError as exc:
                if exc.code == 404:
                    self.result["misses"].append(package or "project")
                    continue
                raise RuntimeError(f"Remote cache mapping read failed: HTTP {exc.code}") from None
            if len(data) > MAX_MAP_BYTES:
                raise ValueError("Remote mappings exceed the configured size limit")
            validate_mapping(data)
            # A local file is needed for Lake's native cache add command.
            with tempfile.TemporaryDirectory(prefix="lean-cache-map-", dir=self.project / ".lake") as temp:
                path = Path(temp) / "outputs.jsonl"
                path.write_bytes(data)
                args = ["lake", "cache", "add", str(path)]
                if package:
                    # v4.33's cache add takes the package as a positional argument.
                    args.append(package)
                args += [f"--service={SERVICE}", f"--scope={scope}", "--no-overwrite"]
                self.command(args)
            self.result["restored"].append(package or "project")

    def publish(self, mappings: Path, package: str | None = None) -> bool:
        data = mappings.read_bytes()
        validate_mapping(data)
        fingerprint = hashlib.sha256(data).hexdigest()
        receipt_key = hashlib.sha256((self.url + "/" + self.scope(package)).encode()).hexdigest()
        receipt_file = self.receipts / (receipt_key + ".json")
        try:
            receipt = json.loads(receipt_file.read_text())
            # Refresh daily so externally expired/deleted objects can be filled.
            if receipt["sha256"] == fingerprint and 0 <= time.time() - receipt["uploaded_at"] < 86400:
                self.result["already_uploaded"].append(package or "project")
                return False
        except (OSError, ValueError, KeyError, TypeError):
            pass
        # Unlike cache get, cache put does not resolve --rev through Git. A
        # merged latest map collects *successful* partial and dirty-tree builds
        # under distinct native input hashes, without claiming to verify HEAD.
        self.command(["lake", "cache", "put", str(mappings), f"--service={SERVICE}",
                      f"--scope={self.scope(package)}", "--rev=latest"])
        # Write a receipt only after the gateway confirms artifacts and mappings.
        fd, temp = tempfile.mkstemp(prefix=".receipt-", dir=self.receipts)
        try:
            with os.fdopen(fd, "w") as handle:
                json.dump({"sha256": fingerprint, "uploaded_at": time.time()}, handle)
            os.replace(temp, receipt_file)
        finally:
            Path(temp).unlink(missing_ok=True)
        self.result["uploaded"].append(package or "project")
        return True

    def invalidate_root_receipt(self) -> None:
        key = hashlib.sha256((self.url + "/" + self.scope()).encode()).hexdigest()
        (self.receipts / (key + ".json")).unlink(missing_ok=True)

    def record_failure(self, error: Exception, operation: str) -> None:
        message = f"Remote cache {operation} failed ({type(error).__name__})"
        self.result.setdefault("warnings", []).append(message)
        self.manager._record_metric("remote_cache_failure", operation=operation,
                                    error_type=type(error).__name__, required=self.required)
        if self.required:
            raise RuntimeError(message + "; verification/publication stopped") from error


def run_cached_build(manager, project: Path, args: list[str], *, timeout: int = 3600):
    """Replace only _run_lake_build; retain its dependency preparation/lock."""
    key, cache = manager._dependency_cache_preflight(project)
    remote = RemoteArtifactCache(manager, project, key)
    if not remote.enabled:
        if cache["status"] == "complete":
            output = manager._run_streaming(args, cwd=project, timeout=timeout, phase="building")
        else:
            with manager._lock(manager.shared / key / ".fallback-build.lock"):
                output = manager._run_streaming(args, cwd=project, timeout=timeout, phase="building")
        return output, cache
    try:
        remote.restore()
    except Exception as exc:
        remote.record_failure(exc, "restore")
    (project / ".lake").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="lean-cache-build-", dir=project / ".lake") as temp:
        mappings = Path(temp) / "project.jsonl"
        def build_and_export():
            output = manager._run_streaming([*args, "-o", str(mappings)],
                                           cwd=project, timeout=timeout, phase="building")
            # A failed Lean build exits above and never enters the upload path.
            try:
                uploaded = remote.publish(mappings)
                # -o records one package per traversal. Replaying the identical
                # successful request with --package merely gathers dependency
                # mappings from already checked artifacts, preserving signed
                # proof/axiom audits and the final server publication gate.
                for package in remote.packages if uploaded else []:
                    dep_map = Path(temp) / f"{package}.jsonl"
                    remote.command([*args, f"--package={package}", "-o", str(dep_map)],
                                   phase="remote_dependency_export")
                    remote.publish(dep_map, package)
            except Exception as exc:
                # A root upload alone does not complete a cache cycle: retry
                # dependency export on the next build if any later step fails.
                remote.invalidate_root_receipt()
                remote.record_failure(exc, "upload")
            return output
        if cache["status"] == "complete":
            output = build_and_export()
        else:
            with manager._lock(manager.shared / key / ".fallback-build.lock"):
                output = build_and_export()
    cache["remote_artifacts"] = remote.result
    manager._record_metric("remote_cache", restored=len(remote.result["restored"]),
                           misses=len(remote.result["misses"]), uploaded=len(remote.result["uploaded"]))
    return output, cache
