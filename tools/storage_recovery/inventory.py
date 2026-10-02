#!/usr/bin/env python3
"""Bounded, read-only Linux storage/Git/process inventory. No Lean jobs."""
import argparse
import datetime as dt
import heapq
import json
import os
from pathlib import Path
import selectors
import stat
import subprocess
import time


def mount_unescape(value):
    for old, new in ((r"\040", " "), (r"\011", "\t"),
                     (r"\012", "\n"), (r"\134", "\\")):
        value = value.replace(old, new)
    return value


def mount_for(path):
    matches = []
    try:
        for line in Path("/proc/self/mountinfo").read_text().splitlines():
            before, after = line.split(" - ", 1)
            fields, extra = before.split(), after.split()
            mount = mount_unescape(fields[4])
            if path == mount or path.startswith(mount.rstrip("/") + "/"):
                matches.append({"mountpoint": mount, "device": fields[2],
                                "filesystem": extra[0],
                                "mount_options": fields[5],
                                "source": mount_unescape(extra[1])})
    except (OSError, ValueError, IndexError) as exc:
        return {"error": str(exc)}
    return max(matches, key=lambda value: len(value["mountpoint"])) if matches else None


def filesystem_info(path):
    v = os.statvfs(path)
    return {"path": path, "device_id": os.stat(path).st_dev,
            "mount": mount_for(path), "total_bytes": v.f_blocks * v.f_frsize,
            "free_bytes_including_reserved": v.f_bfree * v.f_frsize,
            "available_bytes_to_current_user": v.f_bavail * v.f_frsize,
            "total_inodes": v.f_files, "free_inodes": v.f_ffree,
            "available_inodes_to_current_user": v.f_favail,
            "quota": "not measured; available blocks can reflect mount/quota constraints"}


def disk_inventory(root, max_entries=150000, max_seconds=30, max_depth=2,
                   top_count=20):
    """Sum allocated bytes once per inode, without following links/mounts."""
    root = Path(root).absolute()
    start = time.monotonic()
    root_device = root.lstat().st_dev
    pending = [root]
    seen = set()
    buckets = {}
    largest = []
    errors, skipped_mounts, repositories = [], [], []
    entries = files = symlinks = directories = duplicates = logical = allocated = 0
    reason = None
    while pending:
        if entries >= max_entries:
            reason = "entry budget reached"
            break
        if time.monotonic() - start >= max_seconds:
            reason = "time budget reached"
            break
        path = pending.pop()
        try:
            value = path.lstat()
        except OSError as exc:
            if len(errors) < 100:
                errors.append({"path": str(path), "error": str(exc)})
            continue
        if value.st_dev != root_device:
            if len(skipped_mounts) < 100:
                skipped_mounts.append(str(path))
            continue
        entries += 1
        relative = path.relative_to(root)
        is_directory = stat.S_ISDIR(value.st_mode)
        if path.name == ".git" and len(repositories) < 100:
            repositories.append(str(path.parent))
        if is_directory:
            directories += 1
            try:
                # Consume one entry at a time rather than materializing a huge directory.
                with os.scandir(path) as iterator:
                    for child in iterator:
                        if len(pending) + entries >= max_entries:
                            reason = "entry budget reached while enumerating directory"
                            break
                        pending.append(Path(child.path))
            except OSError as exc:
                if len(errors) < 100:
                    errors.append({"path": str(path), "error": str(exc)})
        elif stat.S_ISREG(value.st_mode):
            files += 1
        elif stat.S_ISLNK(value.st_mode):
            symlinks += 1
        key = (value.st_dev, value.st_ino)
        if key in seen:
            duplicates += 1
            continue
        seen.add(key)
        size = value.st_blocks * 512
        allocated += size
        logical += value.st_size
        # Each inode belongs to exactly one deepest reported ancestor bucket.
        parts = relative.parts
        if is_directory:
            bucket = Path(*parts[:max_depth]) if parts else Path(".")
        else:
            bucket = Path(*parts[:-1][:max_depth]) if len(parts) > 1 else Path(".")
        bucket_name = str(bucket)
        buckets[bucket_name] = buckets.get(bucket_name, 0) + size
        if not is_directory:
            item = (size, str(path), value.st_size)
            if len(largest) < top_count:
                heapq.heappush(largest, item)
            elif item > largest[0]:
                heapq.heapreplace(largest, item)
    return {"root": str(root), "elapsed_seconds": round(time.monotonic() - start, 3),
            "complete": reason is None and not errors and not skipped_mounts,
            "incomplete_reason": reason, "entries_observed": entries,
            "files_observed": files, "directories_observed": directories,
            "symlinks_not_followed": symlinks,
            "hardlink_duplicate_entries_not_counted_twice": duplicates,
            "allocated_bytes_observed": allocated, "logical_bytes_observed": logical,
            "byte_count_note": "Lower bounds for incomplete scans. Blocks counted once per inode within this root; roots may overlap. Sparse/shared CoW extents are not physical exclusive-space estimates.",
            "largest_buckets": [{"relative_directory": key, "allocated_bytes_observed": val}
                                for key, val in sorted(buckets.items(), key=lambda x: (-x[1], x[0]))[:top_count]],
            "largest_entries": [{"path": path, "allocated_bytes": size, "logical_bytes": apparent}
                                for size, path, apparent in sorted(largest, reverse=True)],
            "errors": errors, "other_mounts_not_scanned": skipped_mounts,
            "git_candidates": sorted(set(repositories))}


def git_read(root, arguments, timeout=30, max_bytes=2 * 1024 * 1024):
    """Bound capture of a read-only child. Only this child may be terminated."""
    command = ["git", "-c", "core.fsmonitor=false", "-C", str(root)] + arguments
    environment = dict(os.environ, GIT_OPTIONAL_LOCKS="0")
    try:
        process = subprocess.Popen(command, env=environment, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT)
    except OSError as exc:
        return {"error": str(exc), "complete": False}
    output = bytearray()
    cutoff = None
    end = time.monotonic() + timeout
    with selectors.DefaultSelector() as selector:
        selector.register(process.stdout, selectors.EVENT_READ)
        while selector.get_map():
            remaining = end - time.monotonic()
            if remaining <= 0:
                cutoff = "git child timeout"
                break
            for key, _ in selector.select(min(remaining, 0.2)):
                chunk = os.read(key.fd, 65536)
                if not chunk:
                    selector.unregister(key.fileobj)
                    break
                if len(output) + len(chunk) > max_bytes:
                    output.extend(chunk[:max_bytes - len(output)])
                    cutoff = "git child output limit"
                    break
                output.extend(chunk)
            if cutoff:
                break
    if cutoff:
        process.kill()  # This own read-only Git subprocess only; never a job PID.
    code = process.wait()
    process.stdout.close()
    return {"complete": cutoff is None and code == 0, "exit_code": code,
            "cutoff": cutoff, "output": bytes(output).decode("utf-8", "surrogateescape")}


def git_inventory(root):
    result = {"requested_root": str(root)}
    for label, command in (
        ("repository_root", ["rev-parse", "--show-toplevel"]),
        ("head", ["rev-parse", "HEAD"]),
        ("status_porcelain_nul_records", ["status", "--porcelain=v1", "-z", "--untracked-files=all"]),
        ("untracked_lean_files", ["ls-files", "--others", "--exclude-standard", "-z", "--", "*.lean"]),
        ("ignored_lean_files", ["ls-files", "--others", "--ignored", "--exclude-standard", "-z", "--", "*.lean"]),
    ):
        value = git_read(root, command)
        raw = value.pop("output", "")
        value["records" if label.endswith("records") or label.endswith("files") else "value"] = (
            [item for item in raw.split("\0") if item] if "-z" in command else raw.strip())
        result[label] = value
        if label == "repository_root" and not value["complete"]:
            break
    result["status_note"] = "Porcelain v1 NUL records retain rename second-path records. This is inventory, not a preservation or verification receipt. Git optional index locks and fsmonitor are disabled."
    return result


def proc_snapshot(pid):
    result = {"pid": pid, "observed_at": dt.datetime.now(dt.timezone.utc).isoformat()}
    try:
        raw = Path(f"/proc/{pid}/stat").read_text()
        fields = raw[raw.rfind(")") + 2:].split()
        result.update(state=fields[0], parent_pid=int(fields[1]),
                      process_group=int(fields[2]), session=int(fields[3]),
                      user_cpu_ticks=int(fields[11]), system_cpu_ticks=int(fields[12]),
                      start_time_ticks=int(fields[19]), virtual_bytes=int(fields[20]),
                      resident_pages=int(fields[21]))
        result["identity"] = {"boot_id": Path("/proc/sys/kernel/random/boot_id").read_text().strip(),
                              "pid": pid, "start_time_ticks": int(fields[19])}
        result["present"] = True
    except FileNotFoundError:
        result.update(present=False, note="PID absent at sampling time; coordinator/job status not inferred")
        return result
    except (OSError, ValueError, IndexError) as exc:
        result.update(present=None, error=str(exc))
        return result
    try:
        result["io"] = {key: int(value) for key, value in
                        (line.split(":", 1) for line in Path(f"/proc/{pid}/io").read_text().splitlines())}
    except (OSError, ValueError) as exc:
        result["io_error"] = str(exc)
    deleted = []
    try:
        for descriptor in Path(f"/proc/{pid}/fd").iterdir():
            try:
                target = os.readlink(descriptor)
                if target.endswith(" (deleted)"):
                    value = descriptor.stat()
                    deleted.append({"fd": descriptor.name, "target": target,
                                    "logical_bytes": value.st_size,
                                    "allocated_bytes": value.st_blocks * 512,
                                    "device_id": value.st_dev, "inode": value.st_ino})
            except OSError:
                pass
        result["deleted_open_files"] = deleted
    except OSError as exc:
        result["fd_error"] = str(exc)
    return result


def sample_pids(pids, interval=1.0):
    first = [proc_snapshot(pid) for pid in pids]
    if not pids:
        return []
    time.sleep(interval)
    values = []
    for previous in first:
        current = proc_snapshot(previous["pid"])
        stable = (previous.get("identity") is not None and
                  previous.get("identity") == current.get("identity"))
        record = {"first": previous, "second": current, "same_process_identity": stable,
                  "sample_interval_seconds": interval}
        if stable:
            record["cpu_ticks_delta"] = sum(current[x] - previous[x] for x in ("user_cpu_ticks", "system_cpu_ticks"))
            record["io_delta"] = {key: current["io"][key] - previous["io"][key]
                                  for key in current.get("io", {}) if key in previous.get("io", {})}
        values.append(record)
    return values


def positive(value):
    value = int(value)
    if value <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", action="append", required=True, help="Explicit directory; repeat for workspace/dependency mounts")
    parser.add_argument("--git-root", action="append", default=[])
    parser.add_argument("--pid", action="append", type=positive, default=[])
    parser.add_argument("--log", action="append", default=[], help="Read only log size/mtime; never content")
    parser.add_argument("--max-entries", type=positive, default=150000)
    parser.add_argument("--max-seconds", type=positive, default=30, help="Per root; bounding traversal does not bound slow filesystem syscalls")
    parser.add_argument("--top", type=positive, default=20)
    parser.add_argument("--pid-sample-seconds", type=float, default=1)
    args = parser.parse_args()
    if not 0 <= args.pid_sample_seconds <= 10:
        parser.error("PID sample interval must be between zero and ten seconds")
    report = {"schema": "riemann-storage-inventory/v1", "observed_at": dt.datetime.now(dt.timezone.utc).isoformat(),
              "host": os.uname().nodename, "uid": os.getuid(),
              "read_only": True, "roots": [], "git": [], "processes": [], "logs": [],
              "scope_note": "Run on the actual verifier host. Does not query the coordinator, submit Lean, diagnose quota, or authorize reclamation."}
    git_roots = set(args.git_root)
    for supplied in args.root:
        path = str(Path(supplied).absolute())
        try:
            if Path(path).is_symlink() or not Path(path).is_dir():
                raise ValueError("root must be an existing real directory, not a symlink")
            path = str(Path(path).resolve(strict=True))
            scan = disk_inventory(path, args.max_entries, args.max_seconds, top_count=args.top)
            report["roots"].append({"filesystem": filesystem_info(path), "inventory": scan})
            git_roots.update(scan["git_candidates"])
        except (OSError, ValueError) as exc:
            report["roots"].append({"path": path, "error": str(exc)})
    report["git"] = [git_inventory(root) for root in sorted(git_roots)]
    report["processes"] = sample_pids(sorted(set(args.pid)), args.pid_sample_seconds)
    for supplied in args.log:
        try:
            value = Path(supplied).stat()
            report["logs"].append({"path": supplied, "size": value.st_size,
                                   "mtime_ns": value.st_mtime_ns,
                                   "age_seconds": max(0, time.time() - value.st_mtime)})
        except OSError as exc:
            report["logs"].append({"path": supplied, "error": str(exc)})
    print(json.dumps(report, indent=2, ensure_ascii=True))


if __name__ == "__main__":
    main()
