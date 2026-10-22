#!/usr/bin/env python3
"""Inventory the SDK runtime file globs used by this repository's Lean rules.

Read file metadata only. This is a logical input inventory, not a measurement of
cache downloads, wire bytes, or billing. Accept a benchmark report or output base.
"""

import argparse
from collections import Counter
import fnmatch
import os
from pathlib import Path
import stat
import sys

MAX_ENTRIES = 100_000
MAX_DIRS = 30_000
MAX_EXTERNAL = 4_096
GIB = 1024 ** 3


def output_base(path):
    run = path / "run.txt"
    if not run.is_file():
        return path
    with run.open(encoding="utf-8") as stream:
        text = stream.read(65_537)
    if len(text) > 65_536:
        raise ValueError("benchmark metadata exceeds size limit")
    bases = [line[12:] for line in text.splitlines() if line.startswith("output_base=")]
    if len(bases) != 1 or not Path(bases[0]).is_absolute():
        raise ValueError("benchmark metadata needs one absolute output_base")
    return Path(bases[0])


def sdk_root(base):
    roots = set()
    with os.scandir(base / "external") as entries:
        for count, entry in enumerate(entries, 1):
            if count > MAX_EXTERNAL:
                raise ValueError("external repository count exceeds limit")
            root = Path(entry.path)
            if (root / "bin/lean").is_file() and (root / "lib/lean/Init.olean").is_file():
                roots.add(root.resolve(strict=True))
    if len(roots) != 1:
        raise ValueError(f"expected one Lean SDK repository; found {len(roots)}")
    return roots.pop()


def kind(name, shared_library=False):
    if shared_library and (fnmatch.fnmatchcase(name, "*.so*") or name.endswith(".dylib")):
        return "shared libraries"
    for suffix in (".olean.private", ".olean.server", ".olean", ".ir.sig", ".ir"):
        if name.endswith(suffix):
            return suffix
    if fnmatch.fnmatchcase(name, "*.olean*"):
        return "other .olean*"
    return None


def inventory(root):
    namespaces, kinds = Counter(), Counter()
    files = 0
    visited = 0
    directories = 0

    def add(path, artifact_kind, namespace):
        nonlocal files
        info = path.stat()
        if not stat.S_ISREG(info.st_mode):
            raise ValueError("selected SDK input is not a regular file")
        files += 1
        if files > MAX_ENTRIES:
            raise ValueError("SDK input count exceeds limit")
        namespaces[namespace] += info.st_size
        kinds[artifact_kind] += info.st_size

    def fail(error):
        raise error

    lib = root / "lib"
    stdlib = lib / "lean"
    for directory, subdirs, names in os.walk(stdlib, onerror=fail, followlinks=False):
        directories += 1
        visited += len(names) + len(subdirs)
        if directories > MAX_DIRS or visited > MAX_ENTRIES:
            raise ValueError("SDK directory inventory exceeds limit")
        if any((Path(directory) / name).is_symlink() for name in subdirs):
            raise ValueError("SDK directory symlink prevents a complete inventory")
        relative = Path(directory).relative_to(stdlib)
        for name in names:
            artifact_kind = kind(name, shared_library=relative == Path("."))
            if artifact_kind is None:
                continue
            namespace = relative.parts[0] if relative.parts else name.split(".", 1)[0]
            if artifact_kind == "shared libraries":
                namespace = "runtime libraries"
            elif namespace not in ("Init", "Lean", "Std", "Lake"):
                namespace = "other modules"
            add(Path(directory) / name, artifact_kind, namespace)
    with os.scandir(lib) as entries:
        for count, entry in enumerate(entries, 1):
            if count > MAX_ENTRIES:
                raise ValueError("SDK lib directory exceeds limit")
            if kind(entry.name, shared_library=True) == "shared libraries" and not entry.is_dir():
                add(Path(entry.path), "shared libraries", "runtime libraries")
    return files, namespaces, kinds


def breakdown(values):
    return "; ".join(f"{name} {size / GIB:.3f}" for name, size in sorted(values.items(), key=lambda x: (-x[1], x[0])))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path, help="benchmark report directory or Bazel output base")
    args = parser.parse_args()
    try:
        files, namespaces, kinds = inventory(sdk_root(output_base(args.path)))
    except (OSError, ValueError) as error:
        print(f"SDK inventory unavailable: {error}", file=sys.stderr)
        return 1
    print(f"Lean SDK runtime input inventory: {sum(kinds.values()) / GIB:.3f} GiB ({files:,} files; declared sizes)")
    print(f"SDK namespaces (GiB): {breakdown(namespaces)}")
    print(f"SDK artifact kinds (GiB): {breakdown(kinds)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
