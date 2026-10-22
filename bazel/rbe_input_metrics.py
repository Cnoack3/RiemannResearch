#!/usr/bin/env python3
"""Read recorded LeanOlean input metrics from a Bazel 9.2 compact execution log.

The log is Zstandard-compressed, length-delimited ExecLogEntry protobufs. Decode
only the needed fields without third-party Python packages or starting Bazel.
Requires the system libzstd shared library. Bytes are declared inputs, not wire
transfers or billing. Schema: bazelbuild/bazel/9.2.0/src/main/protobuf/spawn.proto.
"""

import argparse
import ctypes
import ctypes.util
import heapq
from pathlib import Path
import statistics
import sys

CHUNK = 64 * 1024
MAX_RECORD = 16 * 1024 * 1024
MAX_DECODED = 256 * 1024 * 1024
MAX_RECORDS = 1_000_000
MAX_SPAWNS = 100_000
MAX_METADATA = 64 * 1024
GIB = 1024 ** 3


class Buffer(ctypes.Structure):
    _fields_ = [("data", ctypes.c_void_p), ("size", ctypes.c_size_t), ("pos", ctypes.c_size_t)]


def decompress(path):
    name = ctypes.util.find_library("zstd")
    if not name:
        raise ValueError("system libzstd is unavailable")
    lib = ctypes.CDLL(name)
    lib.ZSTD_createDStream.restype = ctypes.c_void_p
    lib.ZSTD_freeDStream.argtypes = [ctypes.c_void_p]
    lib.ZSTD_initDStream.argtypes = [ctypes.c_void_p]
    lib.ZSTD_initDStream.restype = ctypes.c_size_t
    lib.ZSTD_decompressStream.argtypes = [ctypes.c_void_p, ctypes.POINTER(Buffer), ctypes.POINTER(Buffer)]
    lib.ZSTD_decompressStream.restype = ctypes.c_size_t
    lib.ZSTD_isError.argtypes = [ctypes.c_size_t]
    lib.ZSTD_isError.restype = ctypes.c_uint
    lib.ZSTD_getErrorName.argtypes = [ctypes.c_size_t]
    lib.ZSTD_getErrorName.restype = ctypes.c_char_p

    def check(status):
        if lib.ZSTD_isError(status):
            raise ValueError("Zstandard decode failed: " + lib.ZSTD_getErrorName(status).decode("utf-8", "replace"))
        return status

    stream = lib.ZSTD_createDStream()
    if not stream:
        raise ValueError("could not allocate Zstandard decoder")
    total = compressed = frames = 0
    remaining = 1
    try:
        check(lib.ZSTD_initDStream(stream))
        output = ctypes.create_string_buffer(CHUNK)
        with path.open("rb") as source:
            while raw := source.read(CHUNK):
                compressed += len(raw)
                if compressed > MAX_DECODED:
                    raise ValueError("compressed execution log exceeds byte limit")
                data = ctypes.create_string_buffer(raw)
                incoming = Buffer(ctypes.cast(data, ctypes.c_void_p), len(raw), 0)
                drain = False
                while incoming.pos < incoming.size or drain:
                    outgoing = Buffer(ctypes.cast(output, ctypes.c_void_p), CHUNK, 0)
                    previous = incoming.pos
                    remaining = check(lib.ZSTD_decompressStream(stream, ctypes.byref(outgoing), ctypes.byref(incoming)))
                    total += outgoing.pos
                    if total > MAX_DECODED:
                        raise ValueError("decoded execution log exceeds byte limit")
                    if remaining == 0:
                        frames += 1
                    if outgoing.pos:
                        yield output.raw[:outgoing.pos]
                    if incoming.pos == previous and not outgoing.pos:
                        if incoming.pos == incoming.size:
                            break
                        raise ValueError("Zstandard decoder made no progress")
                    drain = remaining != 0 and outgoing.pos == CHUNK
        if remaining or not frames:
            raise ValueError("empty or incomplete Zstandard execution log")
    finally:
        lib.ZSTD_freeDStream(stream)


def varint(data, offset=0, incomplete=False):
    value = 0
    for index in range(10):
        if offset + index >= len(data):
            if incomplete:
                return None
            raise ValueError("truncated protobuf varint")
        byte = data[offset + index]
        if index == 9 and byte > 1:
            raise ValueError("protobuf varint exceeds 64 bits")
        value |= (byte & 127) << (7 * index)
        if byte < 128:
            return value, offset + index + 1
    raise ValueError("protobuf varint exceeds 64 bits")


def records(chunks):
    pending = bytearray()
    count = 0
    for chunk in chunks:
        pending.extend(chunk)
        offset = 0
        while offset < len(pending):
            header = varint(pending, offset, incomplete=True)
            if header is None:
                break
            size, start = header
            if size > MAX_RECORD:
                raise ValueError("execution-log record exceeds size limit")
            end = start + size
            if end > len(pending):
                break
            count += 1
            if count > MAX_RECORDS:
                raise ValueError("execution-log record count exceeds limit")
            yield bytes(pending[start:end])
            offset = end
        if offset:
            del pending[:offset]
    if pending:
        raise ValueError("truncated length-delimited execution record")


def fields(data):
    view = memoryview(data)
    offset = 0
    while offset < len(view):
        tag, offset = varint(view, offset)
        number, wire = tag >> 3, tag & 7
        if not number:
            raise ValueError("invalid protobuf field number")
        if wire == 0:
            value, offset = varint(view, offset)
        elif wire in (1, 2, 5):
            if wire == 2:
                size, offset = varint(view, offset)
            else:
                size = 8 if wire == 1 else 4
            end = offset + size
            if end > len(view):
                raise ValueError("truncated protobuf field")
            value, offset = view[offset:end], end
        else:
            raise ValueError("unsupported protobuf wire type")
        yield number, wire, value


def spawn(data):
    label = mnemonic = ""
    cached = False
    metrics = None
    for number, wire, value in fields(data):
        if number in (7, 8) and wire == 2:
            text = bytes(value).decode("utf-8")
            if number == 7:
                label = " ".join(text.split())[:140]
            else:
                mnemonic = text
        elif number == 12 and wire == 0:
            cached = bool(value)
        elif number == 18 and wire == 2:
            metrics = value
    if mnemonic != "LeanOlean":
        return None
    size = files = 0
    if metrics is not None:
        for number, wire, value in fields(metrics):
            if number in (11, 12):
                if wire != 0 or value >= 1 << 63:
                    raise ValueError("invalid recorded input metric")
                if number == 11:
                    size = value
                else:
                    files = value
    return label, cached, size, files


def collect(path):
    sizes, file_counts, largest = [], [], []
    count = cached = 0
    for record in records(decompress(path)):
        payload = None
        for number, wire, value in fields(record):
            if 2 <= number <= 10:
                payload = (number, wire, value)
        if payload is None or payload[:2] != (7, 2):
            continue
        item = spawn(payload[2])
        if item is None:
            continue
        label, cache_hit, size, files = item
        count += 1
        cached += cache_hit
        if count > MAX_SPAWNS:
            raise ValueError("Lean spawn count exceeds limit")
        if size:
            sizes.append(size)
            heapq.heappush(largest, (size, files, label))
            if len(largest) > 5:
                heapq.heappop(largest)
        if files:
            file_counts.append(files)
    if not count:
        raise ValueError("execution log contains no LeanOlean spawns")
    return count, cached, sizes, file_counts, sorted(largest, reverse=True)


def summarize(path):
    try:
        count, cached, sizes, file_counts, largest = collect(path)
    except (OSError, ValueError, UnicodeError, AttributeError) as error:
        print(f"Recorded input metrics unavailable: {error}", file=sys.stderr)
        return 1
    print(f"Recorded input metrics: {path}")
    print(f"LeanOlean spawns: {count}; recorded cache hits: {cached}")
    if sizes:
        print(f"Declared input sizes (GiB), min/median/max: {min(sizes) / GIB:.3f}/{statistics.median(sizes) / GIB:.3f}/{max(sizes) / GIB:.3f} (available for {len(sizes)}/{count} spawns)")
    else:
        print("Declared input sizes: unavailable (zero means unavailable in this schema)")
    if file_counts:
        print(f"Declared input files, min/median/max: {min(file_counts)}/{statistics.median(file_counts):g}/{max(file_counts)} (available for {len(file_counts)}/{count} spawns)")
    else:
        print("Declared input files: unavailable (zero means unavailable in this schema)")
    if largest:
        print("Largest recorded Lean inputs: GiB / files / target (up to five):")
        for size, files, label in largest:
            print(f"  {size / GIB:.3f} / {files if files else 'unavailable'} / {label or 'unavailable'}")
    print("These are declared inputs in that saved invocation, not worker downloads, wire traffic, or billed transfers.")
    return 0


def metadata(path):
    with path.open("r", encoding="utf-8") as source:
        text = source.read(MAX_METADATA + 1)
    if len(text) > MAX_METADATA:
        raise ValueError("benchmark metadata exceeds size limit")
    return text


def signature(report):
    revision = metadata(report / "commit.txt").strip()
    if len(revision) != 40 or any(char not in "0123456789abcdef" for char in revision):
        raise ValueError("invalid benchmark source revision")
    if metadata(report / "git-status.txt").strip():
        raise ValueError("cannot match input logs for a dirty source tree")
    values = {}
    for line in metadata(report / "run.txt").splitlines():
        if "=" in line:
            key, value = line.split("=", 1)
            if key in values:
                raise ValueError("duplicate benchmark metadata field")
            values[key] = value
    result = (revision, values.get("mode"), values.get("target"), values.get("jobs"))
    if not all(result):
        raise ValueError("incomplete benchmark identity")
    return result


def find_log(report):
    if (report / "execution.log").is_file():
        return report / "execution.log"
    wanted = signature(report)
    candidates = []
    for count, candidate in enumerate(report.parent.iterdir(), 1):
        if count > 4096:
            raise ValueError("benchmark directory count exceeds limit")
        if candidate.is_symlink() or not candidate.is_dir() or candidate.name >= report.name:
            continue
        if not candidate.name.startswith(wanted[1] + "-") or not (candidate / "execution.log").is_file():
            continue
        try:
            same = signature(candidate) == wanted
        except (OSError, ValueError, UnicodeError):
            continue
        if same:
            candidates.append(candidate)
    if not candidates:
        raise ValueError("no earlier execution log matches the clean source revision, mode, target, and jobs")
    return max(candidates, key=lambda path: path.name) / "execution.log"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path, help="execution.log or benchmark report directory")
    arguments = parser.parse_args()
    try:
        path = find_log(arguments.path) if arguments.path.is_dir() else arguments.path
    except (OSError, ValueError, UnicodeError) as error:
        print(f"Recorded input metrics unavailable: {error}", file=sys.stderr)
        return 1
    return summarize(path)


if __name__ == "__main__":
    sys.exit(main())
