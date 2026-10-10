#!/usr/bin/env python3
"""Coordinate the editor's short Lake calls with the plugin's native cache."""

from __future__ import annotations

import fcntl
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def run_lake(args: list[str]) -> int:
    lake = os.environ.get("LEAN_CACHE_LAKE_BINARY") or shutil.which("lake")
    if not lake:
        raise RuntimeError("Lake executable was not found")
    service = os.environ.get("LEAN_REMOTE_CACHE_SERVICE")
    cache = os.environ.get("LAKE_CACHE_DIR")
    if not service or not cache or "setup-file" not in args:
        return subprocess.call([lake, *args])

    # Lean writes one header line, without closing stdin. Replay it on retry.
    header = sys.stdin.buffer.readline() if "-" in args else None
    args = [arg for arg in args if arg != "--no-cache"]
    env = {**os.environ, "LEAN_NATIVE_CACHE_LOCK_HELD": "1"}
    root = Path(cache).expanduser().resolve()
    lock_path = root.parent / f".{root.name}.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a+") as lock:
        if os.environ.get("LEAN_NATIVE_CACHE_LOCK_HELD") != "1":
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        # Only the final setup JSON may reach stdout; diagnostics use stderr.
        with tempfile.TemporaryFile() as output, tempfile.TemporaryFile() as errors:
            result = subprocess.run(
                [lake, *args], input=header, stdout=output, stderr=errors, env=env
            )
            if result.returncode == 3:
                restored = subprocess.run(
                    [lake, "cache", "get", "--mappings-only", f"--service={service}",
                     "--repo=Cnoack3/RiemannResearch"],
                    stdin=subprocess.DEVNULL, stdout=sys.stderr,
                    stderr=subprocess.PIPE, env=env,
                )
                sys.stderr.buffer.write(restored.stderr)
                if restored.returncode and b"no outputs found" not in restored.stderr:
                    return restored.returncode
                output.seek(0)
                output.truncate()
                errors.seek(0)
                errors.truncate()
                result = subprocess.run(
                    [lake, *args], input=header, stdout=output, stderr=errors, env=env
                )
            output.seek(0)
            shutil.copyfileobj(output, sys.stdout.buffer)
            errors.seek(0)
            shutil.copyfileobj(errors, sys.stderr.buffer)
            return result.returncode


if __name__ == "__main__":
    sys.exit(run_lake(sys.argv[1:]))
