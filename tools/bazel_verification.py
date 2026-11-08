"""Bazel verification policy shared by the MCP server and the coverage CLI."""

from __future__ import annotations

import argparse
import os
import re
from pathlib import Path


PACKAGE_BUILD = 'load("//bazel:lean_modules.bzl", "lean_modules")\n\nlean_modules()\n'
BACKENDS = {"bazel", "lake"}


def verification_backend(value: str | None = None) -> str:
    backend = value or os.environ.get("LEAN_VERIFICATION_BACKEND", "bazel")
    if backend not in BACKENDS:
        raise ValueError("LEAN_VERIFICATION_BACKEND/backend must be 'bazel' or 'lake'")
    return backend


def project_sources(project: Path) -> list[Path]:
    """List owned source files without following symlinks or vendored workspaces."""
    project = project.resolve()
    sources = []
    aggregate = project / "RiemannResearch.lean"
    if aggregate.is_file() and not aggregate.is_symlink():
        sources.append(aggregate)
    root = project / "RiemannResearch"
    if root.is_symlink():
        raise ValueError("RiemannResearch must not be a symlink")
    for directory, dirs, files in os.walk(root, followlinks=False):
        parent = Path(directory)
        dirs[:] = sorted(d for d in dirs if not d.startswith(".")
                         and not d.startswith("bazel-")
                         and not (parent / d).is_symlink())
        for name in sorted(files):
            source = parent / name
            if name.endswith(".lean"):
                if source.is_symlink():
                    raise ValueError(f"Lean source must not be a symlink: {source}")
                sources.append(source)
    return sorted(sources)


def ensure_bazel_coverage(project: Path, *, fix: bool = True) -> list[str]:
    """Give every source directory and its ancestors a Bazel package.

    Only create absent files. Preserve existing package definitions, and never
    silently replace a BUILD file or follow a symlink. The root aggregate must
    be defined by the repository's existing lean_project() macro.
    """
    project = project.resolve()
    for name in ("BUILD.bazel", "MODULE.bazel", "bazel/lean_modules.bzl"):
        if not (project / name).is_file():
            raise ValueError(f"Bazel setup missing {name}; select backend='lake' explicitly for legacy verification")
    directories = set()
    for source in project_sources(project):
        parent = source.parent
        while parent != project:
            directories.add(parent)
            parent = parent.parent
    missing = []
    for directory in sorted(directories):
        build = directory / "BUILD.bazel"
        if build.is_symlink() or (directory / "BUILD").is_symlink():
            raise ValueError(f"Bazel package file must not be a symlink: {directory}")
        if build.exists():
            if not build.is_file():
                raise ValueError(f"Not a regular BUILD.bazel file: {build}")
            if not re.search(r"(?m)^\s*lean_modules\(\)\s*(?:#.*)?$", build.read_text(encoding="utf-8")):
                raise ValueError(f"{build} must call lean_modules() to cover its Lean sources; existing contents were preserved")
            continue
        if (directory / "BUILD").exists():
            raise ValueError(f"Migrate {directory / 'BUILD'} to BUILD.bazel before verification")
        missing.append(build.relative_to(project).as_posix())
        if fix:
            with build.open("x", encoding="utf-8") as handle:
                handle.write(PACKAGE_BUILD)
    return missing


def bazel_target(project: Path, source: Path) -> str:
    relative = source.resolve().relative_to(project.resolve())
    if relative == Path("RiemannResearch.lean"):
        return "//:RiemannResearch_module"
    if relative.parts[0] != "RiemannResearch" or relative.suffix != ".lean":
        raise ValueError("Bazel verification requires an owned Lean source")
    return f"//{relative.parent.as_posix()}:{relative.stem}"


def bazel_build_command(targets: list[str]) -> list[str]:
    return ["bazel", "build", "--config=buildbuddy", "--color=no", "--curses=no", *targets]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="Fail if a Lean directory lacks BUILD.bazel")
    mode.add_argument("--fix", action="store_true", help="Create missing lean_modules() packages")
    args = parser.parse_args()
    missing = ensure_bazel_coverage(args.root, fix=args.fix)
    for path in missing:
        print(("created " if args.fix else "missing ") + path)
    return int(bool(missing) and not args.fix)


if __name__ == "__main__":
    raise SystemExit(main())
