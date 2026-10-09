"""Conservative CI classification and provenance; never runs Lean or edits sources."""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path, PurePosixPath


def git(*arguments: str) -> str:
    return subprocess.check_output(["git", *arguments], text=True).strip()


def documentation_only(paths: list[str]) -> bool:
    """Only prose extensions qualify; unknown/build/tool paths require Lean."""
    return bool(paths) and all(
        PurePosixPath(path).suffix.lower() in {".md", ".rst"}
        and PurePosixPath(path).name.lower() != "agents.md"
        and not path.startswith((".github/", "tools/"))
        for path in paths
    )


def classify(event: str, base: str) -> tuple[bool, str, list[str]]:
    # Main and manual base audits always retain the full integration build.
    if event != "pull_request":
        return True, "full integration build", []
    if not re.fullmatch(r"[0-9a-fA-F]{40}", base):
        return True, "missing or invalid comparison base", []
    try:
        raw = subprocess.check_output(
            ["git", "diff", "--name-only", "--no-renames", "-z", base, "HEAD"]
        )
        paths = [path.decode("utf-8", errors="strict") for path in raw.split(b"\0") if path]
    except (subprocess.CalledProcessError, UnicodeDecodeError):
        return True, "comparison unavailable", []
    prose = documentation_only(paths)
    return not prose, "documentation-only PR" if prose else "Lean or other inputs changed", paths


def resources(path: Path) -> dict:
    stats = os.statvfs(path)
    return {
        "available_bytes": stats.f_bavail * stats.f_frsize,
        "available_inodes": stats.f_favail,
    }


def hash_file(path: str) -> str | None:
    candidate = Path(path)
    return hashlib.sha256(candidate.read_bytes()).hexdigest() if candidate.is_file() else None


def source_digest() -> str:
    """Hash paths and contents of every tracked Lean source, including root files."""
    raw = subprocess.check_output(["git", "ls-files", "-z", "--", "*.lean"])
    digest = hashlib.sha256()
    for path in sorted(item for item in raw.split(b"\0") if item):
        content = Path(os.fsdecode(path)).read_bytes()
        digest.update(len(path).to_bytes(8, "big"))
        digest.update(path)
        digest.update(len(content).to_bytes(8, "big"))
        digest.update(content)
    return digest.hexdigest()


def output_directory() -> Path:
    return Path(os.environ["RUNNER_TEMP"])


def classify_step() -> None:
    required, reason, paths = classify(os.environ.get("CI_EVENT", ""), os.environ.get("CI_BASE_SHA", ""))
    initial = {
        "lean_required": required,
        "reason": reason,
        "changed_file_count": len(paths),
        "lean_source_sha256": source_digest(),
        "resources": resources(Path.cwd()),
        "timestamp": time.time(),
    }
    (output_directory() / "lean-ci-initial.json").write_text(json.dumps(initial, indent=2) + "\n")
    with Path(os.environ["GITHUB_OUTPUT"]).open("a") as handle:
        handle.write(f"lean_required={str(required).lower()}\n")
        handle.write(f"lean_source_sha256={initial['lean_source_sha256']}\n")
    print(json.dumps(initial, sort_keys=True))


def receipt_step() -> None:
    initial_path = output_directory() / "lean-ci-initial.json"
    initial = json.loads(initial_path.read_text()) if initial_path.is_file() else None
    outcome = os.environ.get("CI_LEAN_OUTCOME", "")
    required_raw = os.environ.get("CI_LEAN_REQUIRED", "")
    required = {"true": True, "false": False}.get(required_raw)
    prose = required is False and os.environ.get("CI_CLASSIFICATION_OUTCOME") == "success"
    record = {
        "schema_version": 1,
        "commit": git("rev-parse", "HEAD"),
        "tree": git("rev-parse", "HEAD^{tree}"),
        "lean_source_sha256": initial.get("lean_source_sha256") if initial else None,
        "event": os.environ.get("GITHUB_EVENT_NAME"),
        "run_id": os.environ.get("GITHUB_RUN_ID"),
        "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
        "input_sha256": {name: hash_file(name) for name in ("lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json")},
        "toolchain": Path("lean-toolchain").read_text().strip(),
        "target": ["RiemannResearch"],
        "command": ["lake", "build", "RiemannResearch", "--quiet"],
        "validation": "not run: documentation-only PR" if prose else "incremental full-library build required",
        "lean_required": required,
        "lean_build_outcome": outcome,
        "lean_verified": required is True and outcome == "success",
        "classification_outcome": os.environ.get("CI_CLASSIFICATION_OUTCOME"),
        "tooling_outcome": os.environ.get("CI_TOOLING_OUTCOME"),
        "dependency_cache_restored": os.environ.get("CI_DEPENDENCY_CACHE"),
        "project_cache_restored": os.environ.get("CI_PROJECT_CACHE"),
        "initial": initial,
        "final_resources": resources(Path.cwd()),
        "timestamp": time.time(),
    }
    (output_directory() / "lean-ci-receipt.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    with Path(os.environ["GITHUB_STEP_SUMMARY"]).open("a") as handle:
        handle.write("\nCI receipt: commit `" + record["commit"] + "`, Lean outcome `" + outcome + "`.\n")
        if prose:
            handle.write("Documentation-only PR: no Lean verification claimed.\n")
        handle.write("Available bytes/inodes: " + json.dumps(record["final_resources"]) + ".\n")
    print(json.dumps(record, sort_keys=True))


if __name__ == "__main__":
    if sys.argv[1:] == ["classify"]:
        classify_step()
    elif sys.argv[1:] == ["receipt"]:
        receipt_step()
    else:
        raise SystemExit("usage: ci_lean.py classify|receipt")
