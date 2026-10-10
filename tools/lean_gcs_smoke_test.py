"""Actual Lean/Lake/GCS acceptance: cold, warm, fresh cache, changed import.

Run on the user's Lean server after starting the bridge, before activating the
verifier integration. No research source files are changed. The tiny remote
objects live under a unique smoke namespace. Full transcript is printed as JSON.
"""
from __future__ import annotations

import argparse
import contextlib
import json
import os
import secrets
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_remote_cache import run_cached_build


class ProbeManager:
    def __init__(self, state):
        self.shared, self.commands = state, []
    def _dependency_cache_preflight(self, project):
        return "smoke-environment", {"status": "complete"}
    @contextlib.contextmanager
    def _lock(self, path):
        yield
    def _record_metric(self, event, **fields):
        pass
    def _run_streaming(self, args, *, cwd, timeout, phase):
        started = time.monotonic()
        result = subprocess.run(args, cwd=cwd, env=os.environ.copy(), capture_output=True,
                                text=True, timeout=timeout)
        output = result.stdout + result.stderr
        self.commands.append({"phase": phase, "command": args[:3],
                              "seconds": round(time.monotonic() - started, 3),
                              "exit_code": result.returncode, "output": output[-10000:]})
        if result.returncode:
            raise RuntimeError(output)
        return output


def make_project(path, toolchain):
    path.mkdir()
    (path / "lean-toolchain").write_text(toolchain)
    (path / "lakefile.toml").write_text('name = "CacheSmoke"\ndefaultTargets = ["CacheSmoke"]\n'
                                      '[[lean_lib]]\nname = "CacheSmoke"\n')
    subprocess.run(["git", "init", "--quiet", str(path)], check=True)
    subprocess.run(["lake", "update"], cwd=path, check=True, capture_output=True, text=True)
    (path / "CacheSmoke").mkdir()
    (path / "CacheSmoke" / "Leaf.lean").write_text('def cacheLeaf : Nat := 41\n')
    (path / "CacheSmoke" / "Unrelated.lean").write_text('theorem cacheUnrelated : 2 = 2 := rfl\n')
    (path / "CacheSmoke.lean").write_text('import CacheSmoke.Leaf\nimport CacheSmoke.Unrelated\n'
                                        'example : cacheLeaf + 1 = 42 := rfl\n')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--url", default="http://127.0.0.1:8765")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    toolchain = (args.repo / "lean-toolchain").read_text()
    if toolchain.strip() != "leanprover/lean4:v4.33.0-rc2":
        raise RuntimeError("This cache integration was inspected for v4.33.0-rc2; re-audit a new toolchain first")
    real_lean = subprocess.check_output(["elan", "which", "lean"], cwd=args.repo, text=True).strip()
    with tempfile.TemporaryDirectory(prefix="lean-gcs-probe-", dir=Path.home()) as tmp:
        root = Path(tmp)
        first, fresh = root / "first", root / "fresh"
        make_project(first, toolchain)
        make_project(fresh, toolchain)
        log = root / "lean-invocations.jsonl"
        shim = root / "lean-probe"
        shim.write_text('#!' + sys.executable + '\nimport json, os, sys\n'
                        'with open(os.environ["LEAN_CACHE_PROBE_LOG"], "a") as h:\n'
                        '    h.write(json.dumps(sys.argv[1:]) + "\\n")\n'
                        'os.execv(' + repr(real_lean) + ', [' + repr(real_lean) + '] + sys.argv[1:])\n')
        shim.chmod(0o700)
        os.environ.update({"LEAN_REMOTE_CACHE_URL": args.url, "LEAN_REMOTE_CACHE_REQUIRED": "1",
            "LEAN_REMOTE_CACHE_NAMESPACE": "smoke/" + secrets.token_hex(12),
            "LAKE_CONFIG": str(args.config.resolve()), "LAKE_ARTIFACT_CACHE": "true",
            "LAKE_RESTORE_ARTIFACTS": "true", "LAKE_CACHE_KEY": "loopback:unused",
            "LEAN": str(shim), "LEAN_CACHE_PROBE_LOG": str(log)})
        manager = ProbeManager(root)
        report = {"toolchain": toolchain.strip(), "phases": []}
        def build(label, project, cache_dir):
            os.environ["LAKE_CACHE_DIR"] = str(cache_dir)
            log.write_text("")
            start = time.monotonic()
            _, result = run_cached_build(manager, project, ["lake", "build", "CacheSmoke"])
            compiled = set()
            for line in log.read_text().splitlines():
                for arg in json.loads(line):
                    if isinstance(arg, str) and arg.endswith(".lean"):
                        path = Path(arg)
                        if not path.is_absolute():
                            path = project / path
                        try:
                            compiled.add(str(path.relative_to(project)))
                        except ValueError:
                            pass
            phase = {"name": label, "seconds": round(time.monotonic() - start, 3),
                     "compiled_sources": sorted(compiled), "remote": result["remote_artifacts"]}
            report["phases"].append(phase)
            print(json.dumps(phase), flush=True)
            return compiled
        cold = build("cold", first, root / "cache-first")
        if not {"CacheSmoke.lean", "CacheSmoke/Leaf.lean", "CacheSmoke/Unrelated.lean"} <= cold:
            raise AssertionError("Cold acceptance did not observe actual Lean compilation")
        if build("unchanged-warm", first, root / "cache-first"):
            raise AssertionError("Unchanged warm build compiled Lean source")
        if build("fresh-workspace-empty-local-cache", fresh, root / "cache-fresh"):
            raise AssertionError("Remote cache failed to eliminate source compilation in a fresh workspace")
        # Change the leaf while leaving the consumer statement true. A changed
        # imported source must rebuild both modules and preserve the unrelated one.
        (first / "CacheSmoke" / "Leaf.lean").write_text('def cacheLeaf : Nat := 40 + 1\n')
        changed = build("changed-import", first, root / "cache-first")
        if changed != {"CacheSmoke.lean", "CacheSmoke/Leaf.lean"}:
            raise AssertionError(f"Unexpected invalidation: {sorted(changed)}")
        report.update(passed=True, commands=manager.commands)
        if args.output:
            args.output.write_text(json.dumps(report, indent=2) + "\n")
        print("Actual Lean/Lake/GCS remote-cache acceptance passed.")


if __name__ == "__main__":
    main()
