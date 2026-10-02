import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

try:
    from . import archive_verify, inventory
except ImportError:
    import archive_verify
    import inventory


class InventoryTests(unittest.TestCase):
    def test_hardlinks_and_symlink_are_not_double_counted_or_followed(self):
        with tempfile.TemporaryDirectory() as location:
            root = Path(location)
            (root / "proof.lean").write_text("theorem t : True := True.intro\n")
            os.link(root / "proof.lean", root / "second.lean")
            (root / "outside").symlink_to("/proc")
            result = inventory.disk_inventory(root)
            self.assertTrue(result["complete"])
            self.assertEqual(result["files_observed"], 2)
            self.assertEqual(result["symlinks_not_followed"], 1)
            self.assertEqual(result["hardlink_duplicate_entries_not_counted_twice"], 1)
            self.assertEqual(result["entries_observed"], 4)

    def test_entry_budget_marks_partial_scan(self):
        with tempfile.TemporaryDirectory() as location:
            for index in range(10):
                Path(location, str(index)).write_bytes(b"x")
            result = inventory.disk_inventory(location, max_entries=3)
            self.assertFalse(result["complete"])
            self.assertIn("budget", result["incomplete_reason"])
            self.assertLessEqual(result["entries_observed"], 3)

    def test_git_inventory_finds_ignored_and_untracked_proofs(self):
        with tempfile.TemporaryDirectory() as location:
            root = Path(location)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / ".gitignore").write_text("hidden/\n")
            (root / "hidden").mkdir()
            (root / "hidden" / "last proof.lean").write_text("example : True := True.intro\n")
            (root / "new\nproof.lean").write_text("example : True := True.intro\n")
            result = inventory.git_inventory(root)
            self.assertEqual(result["ignored_lean_files"]["records"], ["hidden/last proof.lean"])
            self.assertEqual(result["untracked_lean_files"]["records"], ["new\nproof.lean"])
            self.assertTrue((root / "hidden" / "last proof.lean").exists())

    def test_git_output_is_bounded(self):
        with tempfile.TemporaryDirectory() as location:
            subprocess.run(["git", "init", "-q", location], check=True)
            Path(location, "untracked.lean").write_text("x")
            result = inventory.git_read(location, ["status", "--porcelain"], max_bytes=5)
            self.assertFalse(result["complete"])
            self.assertEqual(result["cutoff"], "git child output limit")
            self.assertLessEqual(len(result["output"].encode()), 5)

    def test_pid_identity_and_absence(self):
        result = inventory.sample_pids([os.getpid()], interval=0)[0]
        if result["first"]["present"] is False:
            self.skipTest("This execution runtime does not expose its process via /proc")
        self.assertTrue(result["same_process_identity"])
        self.assertGreaterEqual(result["cpu_ticks_delta"], 0)
        self.assertFalse(inventory.proc_snapshot(2 ** 30)["present"])

    def test_proc_stat_parse_and_pid_reuse_guard_with_fixture(self):
        fields = ["R", "1", "2", "3"] + ["0"] * 48
        fields[11], fields[12] = "100", "20"
        fields[19], fields[20], fields[21] = "777", "123456", "42"
        def fake_read(path, *args, **kwargs):
            if path.name == "stat":
                return "123 (test function) " + " ".join(fields)
            if path.name == "boot_id":
                return "fixture-boot"
            if path.name == "io":
                return "rchar: 100\nwchar: 200\nread_bytes: 0\nwrite_bytes: 0\n"
            raise FileNotFoundError(str(path))
        with patch.object(Path, "read_text", new=fake_read):
            observed = inventory.sample_pids([123], interval=0)[0]
            self.assertTrue(observed["same_process_identity"])
            self.assertEqual(observed["cpu_ticks_delta"], 0)
            self.assertEqual(observed["second"]["start_time_ticks"], 777)
            self.assertEqual(observed["second"]["resident_pages"], 42)
        previous = {"pid": 123, "identity": {"pid": 123, "start_time_ticks": 1}}
        current = {"pid": 123, "identity": {"pid": 123, "start_time_ticks": 2}}
        with patch.object(inventory, "proc_snapshot", side_effect=[previous, current]):
            self.assertFalse(inventory.sample_pids([123], interval=0)[0]["same_process_identity"])


class ArchiveTests(unittest.TestCase):
    def test_quiescence_and_distinct_filesystem_required(self):
        with tempfile.TemporaryDirectory() as location:
            root = Path(location)
            source = root / "source"
            destination = root / "destination"
            source.mkdir()
            destination.mkdir()
            with self.assertRaises(archive_verify.PreservationError):
                archive_verify.make_archive([source], destination)
            with self.assertRaisesRegex(archive_verify.PreservationError, "same device"):
                archive_verify.make_archive([source], destination, True)
            self.assertEqual(list(destination.iterdir()), [])

    def cross_filesystem_fixture(self):
        if not Path("/dev/shm").is_dir() or os.stat("/dev/shm").st_dev == os.stat(tempfile.gettempdir()).st_dev:
            self.skipTest("Distinct writable /dev/shm filesystem unavailable")
        source_context = tempfile.TemporaryDirectory()
        self.addCleanup(source_context.cleanup)
        try:
            destination_context = tempfile.TemporaryDirectory(dir="/dev/shm")
        except OSError:
            self.skipTest("Distinct writable /dev/shm filesystem unavailable")
        self.addCleanup(destination_context.cleanup)
        return Path(source_context.name), Path(destination_context.name)

    def test_full_archive_hashes_manifest_links_xattrs_and_restoration(self):
        source, destination = self.cross_filesystem_fixture()
        (source / ".git").mkdir()
        (source / ".git" / "unpublished-object").write_bytes(b"private object\0")
        (source / "proof\n1.lean").write_text("example : True := True.intro\n")
        os.link(source / "proof\n1.lean", source / "copy.lean")
        (source / "dependency-link").symlink_to("/outside/dependencies")
        (source / "empty").mkdir()
        try:
            os.setxattr(source / "copy.lean", "user.fixture", b"preserve me")
        except OSError:
            pass
        before = archive_verify.collect([source])
        receipt = archive_verify.make_archive([source], destination, True)
        self.assertTrue(receipt["verified"])
        self.assertTrue(receipt["no_deletion_performed"])
        self.assertEqual(before, archive_verify.collect([source]))
        archive = Path(receipt["archive"])
        self.assertEqual(receipt["archive_sha256"], hashlib.sha256(archive.read_bytes()).hexdigest())
        manifest_bytes = (archive.parent / "manifest.json").read_bytes()
        manifest = json.loads(manifest_bytes)
        archive_verify.verify_archive(archive, manifest_bytes, manifest["entries"])
        self.assertEqual(len(receipt["sample_restoration"]["verified_files"]), 3)
        for sample in receipt["sample_restoration"]["verified_files"]:
            self.assertEqual(hashlib.sha256(Path(sample["restored_path"]).read_bytes()).hexdigest(), sample["sha256"])
        self.assertIn("source_000/.git/unpublished-object", manifest["entries"])
        self.assertEqual(manifest["entries"]["source_000/dependency-link"]["link_target"], "/outside/dependencies")
        self.assertEqual(manifest["entries"]["source_000/copy.lean"]["hardlink_first_member"],
                         manifest["entries"]["source_000/proof\n1.lean"]["hardlink_first_member"])

    def test_negative_nanosecond_mtime_is_preserved(self):
        value = {"mode": 0o100600, "uid": 1, "gid": 2, "mtime_ns": -1, "kind": "file", "size": 0}
        self.assertEqual(archive_verify.tar_info("file", value).pax_headers["mtime"], "-0.000000001")

    def test_source_change_retains_failed_archive_and_sources(self):
        source, destination = self.cross_filesystem_fixture()
        (source / "proof.lean").write_text("original")
        original_collect = archive_verify.collect
        calls = 0
        def changed(sources):
            nonlocal calls
            calls += 1
            if calls == 2:
                (source / "proof.lean").write_text("modified by simulated active writer")
            return original_collect(sources)
        with patch.object(archive_verify, "collect", side_effect=changed):
            with self.assertRaisesRegex(archive_verify.PreservationError, "Source changed"):
                archive_verify.make_archive([source], destination, True)
        failures = list(destination.glob("*/FAILED.json"))
        self.assertEqual(len(failures), 1)
        self.assertFalse(json.loads(failures[0].read_text())["verified"])
        self.assertTrue((failures[0].parent / "content.tar.gz.partial").exists())
        self.assertEqual((source / "proof.lean").read_text(), "modified by simulated active writer")
        self.assertFalse((failures[0].parent / "receipt.json").exists())

    def test_special_file_is_refused_before_archive_creation(self):
        source, destination = self.cross_filesystem_fixture()
        os.mkfifo(source / "pipe")
        with self.assertRaisesRegex(archive_verify.PreservationError, "Special file refused"):
            archive_verify.make_archive([source], destination, True)
        self.assertEqual(list(destination.iterdir()), [])

    def test_corrupted_content_cannot_pass_verifier(self):
        source, destination = self.cross_filesystem_fixture()
        (source / "proof.lean").write_text("original")
        receipt = archive_verify.make_archive([source], destination, True)
        archive = Path(receipt["archive"])
        manifest_bytes = (archive.parent / "manifest.json").read_bytes()
        entries = json.loads(manifest_bytes)["entries"]
        tampered = destination / "tampered.tar.gz"
        with tarfile.open(tampered, "w:gz", format=tarfile.PAX_FORMAT) as bundle:
            for name, entry in entries.items():
                member = archive_verify.tar_info(name, entry)
                if entry["kind"] == "file":
                    bundle.addfile(member, io.BytesIO(b"tampered"))
                else:
                    bundle.addfile(member)
            member = tarfile.TarInfo("RECOVERY_MANIFEST.json")
            member.size = len(manifest_bytes)
            bundle.addfile(member, io.BytesIO(manifest_bytes))
        with self.assertRaisesRegex(archive_verify.PreservationError, "content hash mismatch"):
            archive_verify.verify_archive(tampered, manifest_bytes, entries)


if __name__ == "__main__":
    unittest.main()
