#!/usr/bin/env python3
"""Archive explicitly quiescent directories to another filesystem; never reclaim."""
import argparse
import base64
import datetime as dt
from decimal import Decimal
import errno
import hashlib
import io
import json
import os
from pathlib import Path
import stat
import tarfile
import uuid


class PreservationError(RuntimeError):
    pass


def signature(value):
    return {"mode": value.st_mode, "uid": value.st_uid, "gid": value.st_gid,
            "mtime_ns": value.st_mtime_ns, "ctime_ns": value.st_ctime_ns,
            "size": value.st_size, "device": value.st_dev,
            "inode": value.st_ino, "link_count": value.st_nlink}


def hash_stream(stream):
    digest = hashlib.sha256()
    for block in iter(lambda: stream.read(1024 * 1024), b""):
        digest.update(block)
    return digest.hexdigest()


def xattrs(path):
    try:
        return {name: base64.b64encode(os.getxattr(path, name, follow_symlinks=False)).decode("ascii")
                for name in sorted(os.listxattr(path, follow_symlinks=False))}
    except OSError as exc:
        if exc.errno in (errno.ENOTSUP, errno.EOPNOTSUPP):
            return {}
        raise PreservationError(f"Cannot preserve extended attributes for {path}: {exc}") from exc


def snapshot(source, label):
    source = Path(source)
    device = source.lstat().st_dev
    entries = {}
    pending = [source]
    while pending:
        path = pending.pop()
        before = path.lstat()
        if before.st_dev != device:
            raise PreservationError(f"Nested mount refused: {path}. Archive it separately.")
        name = label if path == source else label + "/" + path.relative_to(source).as_posix()
        value = signature(before)
        value["xattrs_base64"] = xattrs(path)
        if stat.S_ISDIR(before.st_mode):
            value["kind"] = "directory"
            with os.scandir(path) as iterator:
                children = sorted((Path(item.path) for item in iterator), key=lambda p: os.fsencode(p.name))
            pending.extend(reversed(children))
        elif stat.S_ISREG(before.st_mode):
            value["kind"] = "file"
            descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
            with os.fdopen(descriptor, "rb") as stream:
                if signature(os.fstat(stream.fileno())) != signature(before):
                    raise PreservationError(f"File changed before hashing: {path}")
                value["sha256"] = hash_stream(stream)
                if signature(os.fstat(stream.fileno())) != signature(before):
                    raise PreservationError(f"File changed during hashing: {path}")
        elif stat.S_ISLNK(before.st_mode):
            value.update(kind="symlink", link_target=os.readlink(path))
        else:
            raise PreservationError(f"Special file refused: {path}. Preserve it separately.")
        if signature(path.lstat()) != signature(before):
            raise PreservationError(f"Entry changed while inventorying: {path}")
        entries[name] = value
    return entries


def collect(sources):
    all_entries = {}
    for number, source in enumerate(sources):
        all_entries.update(snapshot(source, f"source_{number:03d}"))
    first_link = {}
    for name, value in all_entries.items():
        if value["kind"] == "file" and value["link_count"] > 1:
            identity = (value["device"], value["inode"])
            value["hardlink_first_member"] = first_link.setdefault(identity, name)
    return all_entries


def source_path(name, sources):
    parts = name.split("/")
    number = int(parts[0].split("_")[1])
    return sources[number].joinpath(*parts[1:])


def tar_info(name, value):
    info = tarfile.TarInfo(name)
    info.mode = stat.S_IMODE(value["mode"])
    info.uid, info.gid = value["uid"], value["gid"]
    info.mtime = value["mtime_ns"] / 1_000_000_000
    info.pax_headers = {"mtime": format(Decimal(value["mtime_ns"]) / Decimal(1_000_000_000), ".9f")}
    if value["kind"] == "directory":
        info.type = tarfile.DIRTYPE
    elif value["kind"] == "symlink":
        info.type = tarfile.SYMTYPE
        info.linkname = value["link_target"]
    else:
        info.type = tarfile.REGTYPE
        info.size = value["size"]
    return info


def verify_archive(archive, manifest_bytes, entries):
    expected = set(entries) | {"RECOVERY_MANIFEST.json"}
    seen = set()
    with tarfile.open(archive, "r:gz") as bundle:
        for member in bundle:
            name = member.name.rstrip("/")
            if name not in expected or name in seen:
                raise PreservationError(f"Unexpected/duplicate archive member: {name}")
            seen.add(name)
            if name == "RECOVERY_MANIFEST.json":
                stream = bundle.extractfile(member)
                if stream.read() != manifest_bytes:
                    raise PreservationError("Embedded manifest differs")
                continue
            entry = entries[name]
            if member.mode != stat.S_IMODE(entry["mode"]) or member.uid != entry["uid"] or member.gid != entry["gid"]:
                raise PreservationError(f"Archive mode/ownership mismatch: {name}")
            expected_mtime = format(Decimal(entry["mtime_ns"]) / Decimal(1_000_000_000), ".9f")
            if member.pax_headers.get("mtime") != expected_mtime:
                raise PreservationError(f"Archive modification-time mismatch: {name}")
            if entry["kind"] == "file":
                if not member.isfile() or member.size != entry["size"]:
                    raise PreservationError(f"Archive file type/size mismatch: {name}")
                if hash_stream(bundle.extractfile(member)) != entry["sha256"]:
                    raise PreservationError(f"Archive content hash mismatch: {name}")
            elif entry["kind"] == "symlink":
                if not member.issym() or member.linkname != entry["link_target"]:
                    raise PreservationError(f"Archive symbolic link mismatch: {name}")
            elif not member.isdir():
                raise PreservationError(f"Archive directory mismatch: {name}")
    if seen != expected:
        raise PreservationError(f"Missing archive members: {sorted(expected - seen)}")


def restore_sample(archive, job_directory, entries):
    # A bounded content restoration, never tar.extractall and never into a source.
    eligible = sorted(name for name, entry in entries.items()
                      if entry["kind"] == "file" and entry["size"] <= 8 * 1024 * 1024)
    chosen = eligible[:3]
    destination = job_directory / "sample_restore"
    destination.mkdir()
    verified = []
    with tarfile.open(archive, "r:gz") as bundle:
        for name in chosen:
            member = bundle.getmember(name)
            target = destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            with bundle.extractfile(member) as source, target.open("xb") as output:
                for block in iter(lambda: source.read(1024 * 1024), b""):
                    output.write(block)
                output.flush()
                os.fsync(output.fileno())
            with target.open("rb") as stream:
                digest = hash_stream(stream)
            if digest != entries[name]["sha256"]:
                raise PreservationError(f"Sample restoration hash mismatch: {name}")
            verified.append({"member": name, "restored_path": str(target), "sha256": digest})
    return {"verified_files": verified,
            "note": "Up to three files of at most 8 MiB restored by content only. Not a full metadata, Git usability, or build restoration test."}


def fsync_directory(path):
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def make_archive(sources, destination, quiescent=False):
    if not quiescent:
        raise PreservationError("Require explicit quiescence assertion; confirm no writers/active jobs or archive a consistent snapshot")
    if any(Path(source).is_symlink() for source in sources):
        raise PreservationError("Source root symlinks refused; supply the exact real directory explicitly")
    sources = [Path(source).resolve(strict=True) for source in sources]
    destination = Path(destination).resolve(strict=True)
    if not destination.is_dir():
        raise PreservationError("Destination must be an existing directory on a distinct filesystem")
    if not sources or len(set(sources)) != len(sources):
        raise PreservationError("Supply unique real source directories")
    for source in sources:
        if not source.is_dir() or source == Path("/"):
            raise PreservationError(f"Source must be a selected directory below /: {source}")
        if source == destination or source in destination.parents:
            raise PreservationError("Destination cannot be inside a source")
        if source.stat().st_dev == destination.stat().st_dev:
            raise PreservationError("Destination has the same device ID as a source; no second archive on the exhausted filesystem")
        if any(source != other and source in other.parents for other in sources):
            raise PreservationError("Overlapping source directories refused")
    entries = collect(sources)
    manifest = {"schema": "riemann-content-preservation/v1", "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
                "sources": [{"label": f"source_{number:03d}", "original_path": str(source),
                             "device_id": source.stat().st_dev} for number, source in enumerate(sources)],
                "entries": entries,
                "retention": "No local reclamation authorized by this tool. Preserve archive and manifest externally before retiring any original.",
                "limitations": ["Explicit quiescence is operator asserted; live-job/lease detection is outside this tool.",
                                "Symlink targets are preserved as link text; external target contents are not included.",
                                "Hard-linked file contents are stored independently; inode/link metadata in the manifest records original topology.",
                                "Extended attributes are recorded as base64 in the manifest, not restored by ordinary tar extraction.",
                                "Filesystem-specific ACL/flags, snapshots, reflinks and special files need separate preservation.",
                                "Read access may update atime; atime is not an integrity criterion."]}
    manifest_bytes = (json.dumps(manifest, indent=2, ensure_ascii=True, sort_keys=True) + "\n").encode("utf-8")
    name = "rr-preservation-" + dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:12]
    job_directory = destination / name
    job_directory.mkdir(mode=0o700)
    partial = job_directory / "content.tar.gz.partial"
    try:
        with partial.open("xb") as stream:
            with tarfile.open(fileobj=stream, mode="w:gz", format=tarfile.PAX_FORMAT) as bundle:
                for member_name, entry in entries.items():
                    info = tar_info(member_name, entry)
                    if entry["kind"] == "file":
                        path = source_path(member_name, sources)
                        descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
                        with os.fdopen(descriptor, "rb") as contents:
                            observed = signature(os.fstat(contents.fileno()))
                            if observed != {key: entry[key] for key in observed}:
                                raise PreservationError(f"File changed before archiving: {path}")
                            bundle.addfile(info, contents)
                    else:
                        bundle.addfile(info)
                info = tarfile.TarInfo("RECOVERY_MANIFEST.json")
                info.mode = 0o600
                info.size = len(manifest_bytes)
                bundle.addfile(info, io.BytesIO(manifest_bytes))
            stream.flush()
            os.fsync(stream.fileno())
        verify_archive(partial, manifest_bytes, entries)
        if collect(sources) != entries:
            raise PreservationError("Source changed since pre-archive inventory; archive is not accepted as quiescent")
        samples = restore_sample(partial, job_directory, entries)
        final = job_directory / "content.tar.gz"
        partial.rename(final)
        with (job_directory / "manifest.json").open("xb") as stream:
            stream.write(manifest_bytes)
            stream.flush()
            os.fsync(stream.fileno())
        with final.open("rb") as stream:
            archive_hash = hash_stream(stream)
        receipt = {"schema": "riemann-preservation-receipt/v1", "verified": True,
                   "archive": str(final), "archive_sha256": archive_hash,
                   "manifest_sha256": hashlib.sha256(manifest_bytes).hexdigest(),
                   "entries_verified": len(entries), "sample_restoration": samples,
                   "no_deletion_performed": True, "source_directories": [str(p) for p in sources]}
        with (job_directory / "receipt.json").open("x") as stream:
            json.dump(receipt, stream, indent=2)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        fsync_directory(job_directory)
        fsync_directory(destination)
        return receipt
    except Exception as exc:
        # Keep partial archive/sample contents; no automatic cleanup of any kind.
        failure = {"verified": False, "error": str(exc), "directory": str(job_directory),
                   "no_deletion_performed": True}
        try:
            with (job_directory / "FAILED.json").open("x") as stream:
                json.dump(failure, stream, indent=2)
        except OSError:
            pass
        raise PreservationError(f"Archive not accepted; retained partial data at {job_directory}: {exc}") from exc


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", action="append", required=True)
    parser.add_argument("--destination", required=True, help="Existing directory on another filesystem")
    parser.add_argument("--quiescent", action="store_true", help="Assert sources have no writers/active jobs, or are consistent snapshots")
    args = parser.parse_args()
    try:
        print(json.dumps(make_archive(args.source, args.destination, args.quiescent), indent=2))
    except (PreservationError, OSError) as exc:
        print(json.dumps({"verified": False, "error": str(exc), "no_deletion_performed": True}, indent=2))
        raise SystemExit(1)


if __name__ == "__main__":
    main()
