import contextlib
import hashlib
import io
import json
import os
import sys
import tempfile
import threading
import unittest
import urllib.error
import urllib.request
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lean_gcs_bridge import CacheServer, Collision, Missing, ObjectInfo, Race, merge_maps, object_name
from lean_remote_cache import RemoteArtifactCache, run_cached_build


def mapping(key=1, out=None):
    return (json.dumps("2026-03-17") + "\n" + json.dumps([key, out or {"hash": key}]) + "\n").encode()


class MemoryStore:
    def __init__(self):
        self.objects, self.guard, self.writes = {}, threading.Lock(), 0
        self.online = True
    def probe(self):
        if not self.online:
            raise RuntimeError("offline")
    def stat(self, name):
        self.probe()
        with self.guard:
            if name not in self.objects:
                raise Missing(name)
            data, info = self.objects[name]
            return info
    def download(self, name, info, handle):
        self.probe()
        with self.guard:
            if name not in self.objects:
                raise Missing(name)
            data, current = self.objects[name]
            if current.generation != info.generation:
                raise Race(name)
            handle.write(data)
            handle.seek(0)
    def upload(self, name, handle, sha256, content_type, generation=0):
        self.probe()
        handle.seek(0)
        data = handle.read()
        with self.guard:
            actual = self.objects[name][1].generation if name in self.objects else 0
            if generation != actual:
                raise Race(name)
            self.objects[name] = (data, ObjectInfo(actual + 1, len(data), sha256, content_type))
            self.writes += 1


class BridgeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.store = MemoryStore()
        self.server = CacheServer(("127.0.0.1", 0), self.store, "lean-cache/v1", self.temp.name)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        self.url = f"http://127.0.0.1:{self.server.server_port}"
    def tearDown(self):
        self.server.shutdown()
        self.server.server_close()
        self.thread.join()
        self.temp.cleanup()
    def request(self, path, data=None, headers=None):
        req = urllib.request.Request(self.url + path, data=data,
                                     method="PUT" if data is not None else "GET", headers=headers or {})
        with urllib.request.urlopen(req, timeout=5) as response:
            return response.status, response.read()
    def test_private_roundtrip_and_deduplicated_upload(self):
        path = "/a0/research/1234567890abcdef.art"
        self.assertEqual(self.request(path, b"checked-artifact")[0], 200)
        self.assertEqual(self.request(path)[1], b"checked-artifact")
        self.request(path, b"checked-artifact")
        self.assertEqual(self.store.writes, 1)
    def test_collision_refuses_overwrite(self):
        path = "/a0/research/1234567890abcdef.art"
        self.request(path, b"first")
        with self.assertRaises(urllib.error.HTTPError) as exc:
            self.request(path, b"second")
        self.assertEqual(exc.exception.code, 409)
        self.assertEqual(self.request(path)[1], b"first")
    def test_partial_and_concurrent_maps_preserve_all_inputs(self):
        path = "/r0/research/latest.jsonl"
        errors = []
        def put(key):
            try:
                self.request(path, mapping(key))
            except Exception as exc:
                errors.append(exc)
        threads = [threading.Thread(target=put, args=(key,)) for key in range(1, 7)]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join()
        self.assertEqual(errors, [])
        data = self.request(path)[1]
        self.assertEqual({json.loads(line)[0] for line in data.splitlines()[1:]}, set(range(1, 7)))
        before = self.store.writes
        self.request(path, mapping(1))
        self.assertEqual(self.store.writes, before)
    def test_conflicting_map_does_not_poison_cache(self):
        path = "/r0/research/latest.jsonl"
        self.request(path, mapping(1, {"hash": 7}))
        with self.assertRaises(urllib.error.HTTPError) as exc:
            self.request(path, mapping(1, {"hash": 8}))
        self.assertEqual(exc.exception.code, 409)
    def test_misses_and_auth_outages_are_distinct(self):
        with self.assertRaises(urllib.error.HTTPError) as exc:
            self.request("/r0/research/latest.jsonl")
        self.assertEqual(exc.exception.code, 404)
        self.store.online = False
        with self.assertRaises(urllib.error.HTTPError) as exc:
            self.request("/readyz")
        self.assertEqual(exc.exception.code, 502)
    def test_reject_origin_and_rebinding_host(self):
        for headers in ({"Origin": "https://example.invalid"}, {"Host": "example.invalid"}):
            with self.assertRaises(urllib.error.HTTPError) as exc:
                self.request("/healthz", headers=headers)
            self.assertEqual(exc.exception.code, 403)
    def test_detect_corrupt_stored_bytes(self):
        path = "/a0/research/1234567890abcdef.art"
        self.request(path, b"checked")
        name = "lean-cache/v1" + path
        _, info = self.store.objects[name]
        self.store.objects[name] = (b"corrupt", info)
        with self.assertRaises(urllib.error.HTTPError) as exc:
            self.request(path)
        self.assertEqual(exc.exception.code, 409)


class Manager:
    def __init__(self, shared, failed_build=False, incomplete=False):
        self.shared, self.failed_build, self.incomplete = shared, failed_build, incomplete
        self.calls, self.locks, self.metrics = [], [], []
    def _dependency_cache_preflight(self, project):
        return "env-key", {"status": "incomplete" if self.incomplete else "complete"}
    @contextlib.contextmanager
    def _lock(self, path):
        self.locks.append(path)
        yield
    def _run_streaming(self, args, **kwargs):
        self.calls.append((args, kwargs))
        if args[:2] == ["lake", "build"]:
            if self.failed_build:
                raise RuntimeError("Lean rejected source")
            if "-o" in args:
                Path(args[args.index("-o") + 1]).write_bytes(mapping())
        return "build success"
    def _record_metric(self, name, **fields):
        self.metrics.append((name, fields))


class BuildIntegrationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.project = Path(self.temp.name)
        (self.project / ".lake").mkdir()
        (self.project / "lean-toolchain").write_text("leanprover/lean4:v4.33.0-rc2\n")
        (self.project / "lake-manifest.json").write_text(json.dumps({"packages": [{"name": "mathlib", "type": "git"}]}))
        self.env = patch.dict(os.environ, {"LEAN_REMOTE_CACHE_URL": "http://127.0.0.1:8765",
            "LAKE_ARTIFACT_CACHE": "true", "LAKE_CONFIG": "/tmp/lake.toml", "LAKE_CACHE_DIR": "/tmp/lake-cache",
            "LEAN_REMOTE_CACHE_REQUIRED": "1"})
        self.env.start()
    def tearDown(self):
        self.env.stop()
        self.temp.cleanup()
    def test_disabled_cache_retains_original_fallback_lock(self):
        with patch.dict(os.environ, {"LEAN_REMOTE_CACHE_URL": ""}):
            manager = Manager(self.project, incomplete=True)
            run_cached_build(manager, self.project, ["lake", "build", "RiemannResearch"])
            self.assertEqual(len(manager.calls), 1)
            self.assertEqual(len(manager.locks), 1)
    def test_lean_failure_never_uploads(self):
        manager = Manager(self.project, failed_build=True)
        with patch.object(RemoteArtifactCache, "restore"):
            with self.assertRaisesRegex(RuntimeError, "Lean rejected"):
                run_cached_build(manager, self.project, ["lake", "build", "RiemannResearch"])
        self.assertFalse(any(args[:3] == ["lake", "cache", "put"] for args, _ in manager.calls))
    def test_uploads_root_and_dependencies_after_success(self):
        manager = Manager(self.project, incomplete=True)
        with patch.object(RemoteArtifactCache, "restore"):
            _, result = run_cached_build(manager, self.project, ["lake", "build", "+RiemannResearch.RH.X"])
        self.assertEqual(result["remote_artifacts"]["uploaded"], ["project", "mathlib"])
        self.assertEqual(len(manager.locks), 1)
        builds = [args for args, _ in manager.calls if args[:2] == ["lake", "build"]]
        self.assertTrue(all("+RiemannResearch.RH.X" in args for args in builds))
        self.assertTrue(any("--package=mathlib" in args for args in builds))
    def test_outage_blocks_build_by_default(self):
        manager = Manager(self.project)
        with patch.object(RemoteArtifactCache, "restore", side_effect=OSError("offline")):
            with self.assertRaisesRegex(RuntimeError, "publication stopped"):
                run_cached_build(manager, self.project, ["lake", "build", "RiemannResearch"])
        self.assertEqual(manager.calls, [])
    def test_upload_outage_blocks_publication_after_build(self):
        manager = Manager(self.project)
        with patch.object(RemoteArtifactCache, "restore"), patch.object(RemoteArtifactCache, "publish", side_effect=OSError("offline")):
            with self.assertRaisesRegex(RuntimeError, "publication stopped"):
                run_cached_build(manager, self.project, ["lake", "build", "RiemannResearch"])
        self.assertEqual(len(manager.calls), 1)
    def test_remote_maps_are_added_lazily_for_each_package(self):
        manager = Manager(self.project)
        remote = RemoteArtifactCache(manager, self.project, "env-key")
        with patch("urllib.request.urlopen", side_effect=lambda *a, **k: io.BytesIO(mapping())):
            remote.restore()
        self.assertEqual(remote.result["restored"], ["project", "mathlib"])
        commands = [args for args, _ in manager.calls]
        self.assertTrue(all(args[:3] == ["lake", "cache", "add"] for args in commands))
        self.assertEqual(commands[1][4], "mathlib")
    def test_dependency_environment_and_toolchain_isolation(self):
        manager = Manager(self.project)
        a = RemoteArtifactCache(manager, self.project, "env-a").scope()
        b = RemoteArtifactCache(manager, self.project, "env-b").scope()
        self.assertNotEqual(a, b)
        (self.project / "lean-toolchain").write_text("leanprover/lean4:v4.34.0\n")
        c = RemoteArtifactCache(manager, self.project, "env-a").scope()
        self.assertNotEqual(a, c)
    def test_unchanged_successful_mapping_skips_remote_upload_and_dependency_replay(self):
        manager = Manager(self.project)
        with patch.object(RemoteArtifactCache, "restore"):
            run_cached_build(manager, self.project, ["lake", "build", "RiemannResearch"])
            manager.calls.clear()
            _, result = run_cached_build(manager, self.project, ["lake", "build", "RiemannResearch"])
        self.assertEqual(result["remote_artifacts"]["already_uploaded"], ["project"])
        self.assertEqual(len(manager.calls), 1)
    def test_partial_upload_failure_retries_dependency_export(self):
        manager = Manager(self.project)
        original = manager._run_streaming
        def failed_dependency(args, **kwargs):
            if args[:3] == ["lake", "cache", "put"] and any(a.endswith("/dependencies/mathlib") for a in args):
                raise OSError("dependency upload unavailable")
            return original(args, **kwargs)
        manager._run_streaming = failed_dependency
        with patch.object(RemoteArtifactCache, "restore"):
            with self.assertRaisesRegex(RuntimeError, "publication stopped"):
                run_cached_build(manager, self.project, ["lake", "build", "RiemannResearch"])
            manager._run_streaming = original
            manager.calls.clear()
            _, result = run_cached_build(manager, self.project, ["lake", "build", "RiemannResearch"])
        self.assertEqual(result["remote_artifacts"]["uploaded"], ["project", "mathlib"])


class ProtocolTests(unittest.TestCase):
    def test_path_confinement(self):
        for path in ["/a0/x/%2e%2e/1234567890abcdef.art", "/a0/x/%2f1234567890abcdef.art",
                     "/a0/x/invalid.art", "/r0/x/main.jsonl", "/r0/x/latest.jsonl?token=x"]:
            with self.assertRaises(ValueError):
                object_name(path, "lean-cache/v1")
    def test_invalid_and_conflicting_mappings(self):
        with self.assertRaises(ValueError):
            merge_maps(None, b"{}\n")
        with self.assertRaises(Collision):
            merge_maps(mapping(1, {"hash": 1}), mapping(1, {"hash": 2}))


if __name__ == "__main__":
    unittest.main()
