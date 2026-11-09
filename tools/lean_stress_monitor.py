#!/usr/bin/env python3
"""Read-only cgroup-v2 telemetry; writes only the requested JSON output.

Limits use -1 for "max"; unavailable PSI and first-sample CPU use null.
CPU percent is per core (a multithreaded JVM can exceed 100%). Phase changes
start separate summaries, including when a previous phase name is reused.
Invalid/missing phase updates retain the previous phase and increment a counter.
"""

import argparse
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time


CGROUP_ROOT = Path("/sys/fs/cgroup")
MAX_BYTES = 100_000


def pairs(path):
    return {key: int(value) for key, value in
            (line.split() for line in path.read_text().splitlines())}


def pressure(path):
    if not path.exists():
        return None
    return {parts[0]: {key: float(value) if key != "total" else int(value)
                      for key, value in (item.split("=") for item in parts[1:])}
            for parts in (line.split() for line in path.read_text().splitlines())}


def find_cgroup(override):
    if override:
        path = override.resolve()
    else:
        result = subprocess.run(
            ["systemctl", "show", "lean-tunnel.service", "-p", "ControlGroup", "--value"],
            capture_output=True, text=True, timeout=10, check=True)
        group = result.stdout.strip()
        if not group or not group.startswith("/") or group == "/":
            raise ValueError("lean-tunnel.service has no active service ControlGroup")
        path = (CGROUP_ROOT / group.lstrip("/")).resolve()
    if not path.is_dir():
        raise ValueError(f"cgroup directory does not exist: {path}")
    return path


def java_processes(cgroup, previous, now):
    """Include JVMs in the service cgroup or descendants; never emit cmdlines."""
    relative = cgroup.relative_to(CGROUP_ROOT)
    group = "/" if relative == Path(".") else "/" + relative.as_posix()
    rows, current = [], {}
    ticks_per_second = os.sysconf("SC_CLK_TCK")
    page_size = os.sysconf("SC_PAGE_SIZE")
    for process in Path("/proc").iterdir():
        if not process.name.isdigit():
            continue
        try:
            if process.joinpath("comm").read_text().strip() != "java":
                continue
            membership = next(line[3:] for line in
                              process.joinpath("cgroup").read_text().splitlines()
                              if line.startswith("0::"))
            if not (group == "/" or membership == group or membership.startswith(group + "/")):
                continue
            stat = process.joinpath("stat").read_text().rsplit(")", 1)[1].split()
            pid, ticks = int(process.name), int(stat[11]) + int(stat[12])
            identity = (pid, int(stat[19]))  # Start time protects against PID reuse.
            before = previous.get(identity)
            cpu = None if before is None else round(
                max(0, ticks - before[0]) / ticks_per_second / (now - before[1]) * 100, 2)
            current[identity] = (ticks, now)
            args = process.joinpath("cmdline").read_bytes().decode(errors="replace").split("\0")
            row = {"pid": pid, "start_ticks": identity[1],
                   "rss_bytes": int(stat[21]) * page_size, "cpu_percent": cpu}
            for name in ("workspace_directory", "output_base"):
                option = "--" + name
                value = next((arg[len(option) + 1:] if arg.startswith(option + "=")
                              else args[i + 1] for i, arg in enumerate(args)
                              if arg.startswith(option + "=") or
                              (arg == option and i + 1 < len(args))), None)
                row[name] = value[:512] if value is not None else None
            rows.append(row)
        except (OSError, ValueError, IndexError, StopIteration):
            continue  # Processes may exit or become unreadable during the scan.
    previous.clear()
    previous.update(current)
    return sorted(rows, key=lambda row: row["pid"])


def sample(cgroup, previous):
    values = {}
    for name in ("memory.current", "memory.swap.current", "memory.high", "memory.max", "memory.swap.max"):
        raw = (cgroup / name).read_text().strip()
        values[name] = -1 if raw == "max" else int(raw)
    values.update({"timestamp": time.time(), "memory.events": pairs(cgroup / "memory.events"),
                   "cpu.stat": pairs(cgroup / "cpu.stat"),
                   "memory.pressure": pressure(cgroup / "memory.pressure"),
                   "io.pressure": pressure(cgroup / "io.pressure")})
    values["java"] = java_processes(cgroup, previous, time.monotonic())
    values["host_memory"] = {}
    try:
        for line in Path("/proc/meminfo").read_text().splitlines():
            fields = line.split()
            if fields[0] in ("MemAvailable:", "SwapFree:"):
                values["host_memory"][fields[0][:-1] + "_bytes"] = int(fields[1]) * 1024
    except OSError:
        pass
    return values


def update_phase(summaries, phase, value):
    if not summaries or summaries[-1]["phase"] != phase:
        summaries.append({"phase": phase, "samples": 0, "first_timestamp": value["timestamp"],
                          "memory_peak_bytes": 0, "swap_peak_bytes": 0, "psi_peak": {},
                          "peak_java_rss_bytes": {},
                          "event_start": value["memory.events"].copy()})
    summary = summaries[-1]
    summary["samples"] += 1
    summary["last_timestamp"] = value["timestamp"]
    summary["memory_peak_bytes"] = max(summary["memory_peak_bytes"], value["memory.current"])
    summary["swap_peak_bytes"] = max(summary["swap_peak_bytes"], value["memory.swap.current"])
    summary["event_end"] = value["memory.events"].copy()
    summary["event_deltas"] = {key: count - summary["event_start"].get(key, 0)
                               for key, count in summary["event_end"].items()}
    workspace_rss = {}
    for row in value["java"]:
        key = row["workspace_directory"] or f"pid:{row['pid']}/start:{row['start_ticks']}"
        workspace_rss[key] = workspace_rss.get(key, 0) + row["rss_bytes"]
    for key, rss in workspace_rss.items():
        summary["peak_java_rss_bytes"][key] = max(summary["peak_java_rss_bytes"].get(key, 0), rss)
    for kind in ("memory.pressure", "io.pressure"):
        for stall, numbers in (value[kind] or {}).items():
            peaks = summary["psi_peak"].setdefault(kind, {}).setdefault(stall, {})
            for key, number in numbers.items():
                if key != "total":
                    peaks[key] = max(peaks.get(key, 0), number)


def write_atomic(output, data):
    """Drop oldest history, then old phases/JVM rows if needed for the hard cap."""
    while True:
        encoded = json.dumps(data, separators=(",", ":"), allow_nan=False).encode()
        if len(encoded) <= MAX_BYTES:
            break
        if data["recent"]:
            data["recent"].pop(0)
            data["omitted"]["recent"] += 1
        elif len(data["phase_summaries"]) > 1:
            data["phase_summaries"].pop(0)
            data["omitted"]["phases"] += 1
        elif data["current"]["java"]:
            data["current"]["java"].pop()
            data["omitted"]["java"] += 1
        elif data["phase_summaries"][-1]["peak_java_rss_bytes"]:
            data["phase_summaries"][-1]["peak_java_rss_bytes"].popitem()
            data["omitted"]["java_peaks"] += 1
        else:
            raise ValueError("telemetry metadata exceeds 100000-byte output limit")
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=output.parent, prefix="." + output.name + ".",
                                         delete=False) as handle:
            temporary = handle.name
            handle.write(encoded)
        os.replace(temporary, output)
    finally:
        if temporary and os.path.exists(temporary):
            os.unlink(temporary)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--phase-file", type=Path)
    parser.add_argument("--duration", type=float, default=7200)
    parser.add_argument("--interval", type=float, default=2)
    parser.add_argument("--cgroup", type=Path)
    args = parser.parse_args()
    if not math.isfinite(args.duration) or args.duration <= 0:
        parser.error("--duration must be a finite positive number")
    if not math.isfinite(args.interval) or args.interval < 1:
        parser.error("--interval must be finite and at least 1 second")
    output = args.output.resolve()
    if not output.parent.is_dir() or any(output.is_relative_to(root) for root in (Path("/proc"), Path("/sys"))):
        parser.error("--output must be in an existing writable directory outside /proc and /sys")
    if args.phase_file and output == args.phase_file.resolve():
        parser.error("--output and --phase-file must be different files")
    try:
        cgroup = find_cgroup(args.cgroup)
        if not cgroup.is_relative_to(CGROUP_ROOT):
            parser.error("--cgroup must be a cgroup-v2 directory below /sys/fs/cgroup")
        for name in ("memory.current", "memory.swap.current", "memory.high", "memory.max",
                     "memory.swap.max", "memory.events", "cpu.stat"):
            (cgroup / name).read_text()
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        parser.error(f"cannot read service cgroup: {error}")
    data = {"schema_version": 1, "cgroup": str(cgroup), "stopped": False, "current": None, "recent": [],
            "phase_summaries": [], "phase_read_errors": 0,
            "omitted": {"recent": 0, "phases": 0, "java": 0, "java_peaks": 0}}
    previous, phase = {}, "unlabelled"
    deadline = time.monotonic() + args.duration
    reason, status = "duration", 0
    print(f"Sampling {cgroup} every {args.interval:g}s into {output}", flush=True)
    try:
        while True:
            if args.phase_file:
                try:
                    with args.phase_file.open() as handle:
                        candidate = json.loads(handle.read(4096))["phase"]
                    if not isinstance(candidate, str) or not candidate.strip() or len(candidate) > 128:
                        raise ValueError("phase must be a nonempty string of at most 128 characters")
                    phase = candidate
                except (OSError, ValueError, KeyError, TypeError):
                    data["phase_read_errors"] += 1
            value = sample(cgroup, previous)
            value["phase"] = phase
            data["current"] = value
            data["recent"].append(value.copy())
            data["recent"] = data["recent"][-20:]
            update_phase(data["phase_summaries"], phase, value)
            write_atomic(output, data)
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                break
            time.sleep(min(args.interval, remaining))
            if time.monotonic() >= deadline:
                break
    except KeyboardInterrupt:
        reason = "interrupt"
    except (OSError, ValueError) as error:
        print(f"monitor stopped: {error}", file=sys.stderr)
        reason, status = "error", 1
    finally:
        data.update(stopped=True, stop_reason=reason, stopped_at=time.time())
        try:
            write_atomic(output, data)
        except (OSError, ValueError) as error:
            print(f"cannot write final telemetry: {error}", file=sys.stderr)
            status = 1
    return status


if __name__ == "__main__":
    sys.exit(main())
