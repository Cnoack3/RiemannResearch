#!/usr/bin/env python3
"""Stream Bazel 9.2 one-line task/counter records; skip multiline records.
Inclusive durations overlap and are neither wall time nor CPU time.
"""
import argparse
import collections
import gzip
import heapq, json, math
from pathlib import Path
import sys, zlib
MAX_LINE = 1024 * 1024
SELECTED = {"Remote execution setup", "Local parse to prepare for remote execution",
            "remote action cache check", "remote output download", "remote network",
            "thread wait", "gc notification", "general information", "VFS md5",
            "VFS read", "action resource lock", "action dependency checking"}
PHASES = {"runAnalysisPhase": "runAnalysisPhase", "runExecutionPhase": "runExecutionPhase",
          "MerkleTreeComputer.buildForSpawn": "Merkle tree build", "acquiring semaphore": "semaphore wait"}
COUNTERS = {"CPU usage (Bazel)": "cpu", "Memory usage (Bazel)": "memory"}
def bounded_lines(stream):
    while True:
        line = stream.readline(MAX_LINE + 1)
        if not line:
            return
        if len(line) > MAX_LINE:
            while line and not line.endswith("\n"):
                line = stream.readline(MAX_LINE + 1)
            yield None
        else:
            yield line
def numeric(value):
    try:
        return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(value)
    except OverflowError:
        return False
def summarize(path):
    totals = collections.defaultdict(lambda: [0.0, 0, 0.0])
    phases = collections.defaultdict(lambda: [0.0, 0, 0.0])
    counters = collections.defaultdict(lambda: [0.0, 0, 0.0])
    longest, markers = [], []
    parsed = instant = skipped = malformed = oversized = unknown = 0
    first = last = None
    previous = ending = read_error = ""
    try:
        # JsonTraceFileWriter writes ISO_8859_1; ts/dur are microseconds.
        with gzip.open(path, "rt", encoding="latin-1") as stream:
            for line in bounded_lines(stream):
                if line is None:
                    oversized += 1
                    previous, ending = ending, "<oversized>"
                    continue
                text = line.strip()
                if not text:
                    continue
                previous, ending = ending, text
                typed = text.startswith('{"cat"')
                if not typed and not text.startswith('{"name"'):
                    skipped += int(text not in ("{", "}", "[", "]", "]}"))
                    continue
                try:
                    event = json.loads(text[:-1] if text.endswith(",") else text)
                    kind, name = event.get("ph"), event.get("name", "")
                    if kind == "C" and name in COUNTERS:
                        value = event.get("args", {}).get(COUNTERS[name], 0)
                        if not numeric(value) or value < 0:
                            raise ValueError("invalid counter")
                        row = counters[name]
                        row[0] += value; row[1] += 1; row[2] = max(row[2], value)
                        continue
                    if not typed or kind not in ("X", "i", "I"):
                        skipped += 1
                        continue
                    ts, duration, category = event.get("ts"), event.get("dur", 0), event.get("cat")
                    if (not numeric(ts) or not numeric(duration) or duration < 0
                            or not numeric(ts + duration) or kind == "X" and "dur" not in event
                            or not isinstance(category, str) or not isinstance(name, str)):
                        raise ValueError("invalid task fields")
                except (json.JSONDecodeError, ValueError, AttributeError, TypeError, RecursionError):
                    malformed += int(typed or any(key in text for key in COUNTERS))
                    skipped += int(not typed)
                    continue
                first = ts if first is None else min(first, ts)
                last = max(last if last is not None else ts, ts + duration)
                if kind != "X":
                    instant += 1
                    if category == "build phase marker" and len(markers) < 16:
                        markers.append((ts, name))
                    continue
                parsed += 1
                seconds = duration / 1_000_000
                if category == "Unknown event": unknown += 1; continue
                if name in PHASES:
                    row = phases[name]
                    row[0] += seconds; row[1] += 1; row[2] = max(row[2], seconds)
                if category in SELECTED:
                    row = totals[category]
                    row[0] += seconds; row[1] += 1; row[2] = max(row[2], seconds)
                if category in SELECTED or name in PHASES:
                    heapq.heappush(longest, (seconds, " ".join(name.split())[:120]))
                    if len(longest) > 6:
                        heapq.heappop(longest)
    except (OSError, EOFError, zlib.error) as error:
        read_error = str(error)
    footer = ending == "]}" or (ending == "}" and previous == "]")
    partial = bool(read_error or malformed or oversized or not footer)
    print(f"Profile: {path}")
    print(f"Status: {'PARTIAL/INVALID' if partial else 'complete one-line subset'}; duration records={parsed}, instant markers={instant}")
    if first is not None:
        print(f"Recorded event span: {(last-first)/1_000_000:.3f}s (first start to last end; not command wall time)")
    print(f"Skipped: non-task/multiline={skipped}, oversized={oversized}; malformed={malformed}; Unknown={unknown} excluded from rankings; footer={'present' if footer else 'missing'}")
    for name, label in PHASES.items():
        total, count, maximum = phases[name]
        print(f"Named {label}: records={count}, sum={total:.3f}s, max={maximum:.3f}s" if count else f"Named {label}: not recorded")
    ordered = sorted(markers)
    relevant = [(i, t, n) for i, (t, n) in enumerate(ordered) if "analy" in n.lower() or "build" in n.lower()]
    for i, ts, name in relevant[:2]:
        span = f"{(ordered[i+1][0]-ts)/1_000_000:.3f}s to next marker" if i+1 < len(ordered) else "no next marker"
        print(f"Phase marker: {name[:65]}: {span}")
    for name in COUNTERS:
        total, count, maximum = counters[name]
        if not count:
            print(f"{name}: not recorded")
            continue
        print(f"{name}: sample mean/max={total/count:.3f}/{maximum:.3f} cores (not time-weighted, n={count})" if name.startswith("CPU") else
              f"{name}: max={maximum:.1f} MiB used heap+nonheap, not RSS (n={count})")
    ranked = sorted(totals.items(), key=lambda x: x[1][0], reverse=True)[:5]
    shown = {category for category, _ in ranked}
    for category in ("remote action cache check", "gc notification"):
        if category in totals and category not in shown:
            ranked.append((category, totals[category]))
    print("Selected categories: records / inclusive sum s / max s (top five plus cache/GC):")
    for category, (total, count, maximum) in ranked:
        print(f"  {category}: {count} / {total:.3f} / {maximum:.3f}")
    print("Longest relevant recorded events (s / name):")
    for seconds, name in sorted(longest, reverse=True):
        print(f"  {seconds:.3f} / {name}")
    print("Inclusive sums overlap; not wall/CPU. Slim profiles merge short events+gaps: records != calls; Unknown excluded from rankings.")
    print("Setup can include semaphore wait. GC durations are reported collector durations; timestamps approximate, not exact pause/causality proof.")
    if read_error:
        print(f"Read error: {read_error}; partial statistics may omit events.", file=sys.stderr)
    if not parsed:
        print("No complete one-line duration events: empty, unsupported, or incomplete profile.", file=sys.stderr)
        return 2
    if partial:
        print("Incomplete or malformed/oversized trace data; partial statistics only.", file=sys.stderr)
        return 1
    return 0

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profile", help="profile.gz or a benchmark report directory")
    path = Path(parser.parse_args().profile).expanduser()
    path = path / "profile.gz" if path.is_dir() else path
    if not path.is_file():
        print(f"Profile is missing or is not a file: {path}", file=sys.stderr)
        return 2
    return summarize(path)

if __name__ == "__main__":
    sys.exit(main())
