"""Persistent authentication tests; no real credentials or Lean builds."""
import base64
import datetime
import hashlib
import http.client
import io
import json
import os
import sys
import tempfile
import threading
import unittest
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from unittest.mock import patch
from urllib.parse import parse_qs, urlsplit

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lean_gcs_bridge import (Collision, GCSStore, Missing, Race, load_hmac_credentials,
                    sign_headers, validate_hmac_credentials)

ACCESS = "GOOG" + "A" * 20
SECRET = "A" * 40


class SigningTests(unittest.TestCase):
    def test_signature_matches_independent_curl_reference(self):
        # Captured from curl --aws-sigv4 goog:goog:auto:storage, fixed date,
        # fake credentials and this exact GET against a local HTTP fixture.
        target = "/riemann_lean_cache/lean-cache/v1/r0/fixture/latest.jsonl?generation=7"
        result = sign_headers("GET", target, {"x-goog-if-generation-match": "7"}, ACCESS, SECRET,
                              hashlib.sha256(b"").hexdigest(),
                              datetime.datetime(2026, 10, 10, 5, tzinfo=datetime.timezone.utc))
        self.assertEqual(result["authorization"].split("Signature=")[1],
                         "71786a11f8b71a453208e663d10279682eeea9dc88337b4b8044f9b78efeeda8")
        self.assertNotIn(SECRET, json.dumps(result))

    def test_user_oauth_credentials_are_rejected(self):
        with self.assertRaises(ValueError):
            validate_hmac_credentials({"type": "authorized_user", "refresh_token": "fake"})

    def test_credential_file_must_be_private(self):
        with tempfile.TemporaryDirectory() as directory:
            file = Path(directory) / "hmac.json"
            file.write_text(json.dumps({"type": "gcs_hmac", "access_id": ACCESS, "secret": SECRET}))
            file.chmod(0o644)
            with self.assertRaises(ValueError):
                load_hmac_credentials(file)
            file.chmod(0o600)
            self.assertEqual(load_hmac_credentials(file), (ACCESS, SECRET))


class XMLTests(unittest.TestCase):
    def setUp(self):
        self.objects, self.requests = {}, []
        self.failed, self.corrupt = False, False
        fixture = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"
            def log_message(self, *args):
                pass
            def reply(self, code, body=b"", info=None):
                self.send_response(code)
                self.send_header("Content-Length", str(len(info[0]) if info else len(body)))
                if info:
                    data, generation, sha256 = info
                    self.send_header("x-goog-generation", str(generation))
                    self.send_header("x-goog-meta-sha256", sha256)
                    self.send_header("Content-Type", "application/octet-stream")
                    self.send_header("x-goog-hash", "md5=" + base64.b64encode(
                        hashlib.md5(body if fixture.corrupt and self.command == "GET" else data,
                                    usedforsecurity=False).digest()).decode())
                self.end_headers()
                if self.command != "HEAD":
                    self.wfile.write(body)
            def handle_object(self):
                fixture.requests.append((self.command, self.path, dict(self.headers)))
                if fixture.failed:
                    self.reply(503)
                    return
                target = urlsplit(self.path)
                if target.path == "/riemann_lean_cache" and self.command == "GET":
                    params = parse_qs(target.query)
                    if params != {"max-keys": ["1"], "prefix": ["lean-cache/v1/"]}:
                        self.reply(400)
                        return
                    self.reply(200, b"<ListBucketResult/>")
                    return
                current = fixture.objects.get(target.path)
                if self.command == "PUT":
                    data = self.rfile.read(int(self.headers["Content-Length"]))
                    if int(self.headers["x-goog-if-generation-match"]) != (current[1] if current else 0):
                        self.reply(412)
                        return
                    if self.headers["Content-MD5"] != base64.b64encode(
                            hashlib.md5(data, usedforsecurity=False).digest()).decode():
                        self.reply(400)
                        return
                    fixture.objects[target.path] = (data, (current[1] if current else 0) + 1,
                                                    self.headers["x-goog-meta-sha256"])
                    self.reply(200)
                    return
                if current is None:
                    self.reply(404)
                    return
                condition = self.headers.get("x-goog-if-generation-match")
                if condition is not None and int(condition) != current[1]:
                    self.reply(412)
                    return
                body = b"X" * len(current[0]) if fixture.corrupt else current[0]
                self.reply(200, body if self.command == "GET" else b"", current)
            do_GET = do_HEAD = do_PUT = handle_object

        self.server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        self.patcher = patch("lean_gcs_bridge.http.client.HTTPSConnection", lambda *a, **k:
                             http.client.HTTPConnection("127.0.0.1", self.server.server_port, timeout=5))
        self.patcher.start()
        self.store = GCSStore("project-c5cfd87b-fbe8-47ea-9d0", "riemann_lean_cache", "lean-cache/v1",
                              (ACCESS, SECRET))
        self.name = "lean-cache/v1/a0/research/1234567890abcdef.art"

    def tearDown(self):
        connection = getattr(self.store.local, "connection", None)
        if connection:
            connection.close()
        self.patcher.stop()
        self.server.shutdown()
        self.server.server_close()
        self.thread.join()

    def test_private_xml_roundtrip_and_generation_conflicts(self):
        self.store.probe()
        with self.assertRaises(Missing):
            self.store.stat(self.name)
        data = b"incremental-artifact"
        sha = hashlib.sha256(data).hexdigest()
        self.store.upload(self.name, io.BytesIO(data), sha, "application/octet-stream")
        info = self.store.stat(self.name)
        output = io.BytesIO()
        self.store.download(self.name, info, output)
        self.assertEqual(output.read(), data)
        with self.assertRaises(Race):
            self.store.upload(self.name, io.BytesIO(data), sha, "application/octet-stream", generation=0)
        self.store.upload(self.name, io.BytesIO(data), sha, "application/octet-stream", generation=info.generation)
        with self.assertRaises(Race):
            self.store.download(self.name, info, io.BytesIO())
        for method, target, headers in self.requests:
            self.assertTrue(headers["authorization"].startswith("GOOG4-HMAC-SHA256 "))
            self.assertNotIn(SECRET, json.dumps(headers))
            self.assertTrue(target.startswith("/riemann_lean_cache"))

    def test_corruption_and_outages_fail(self):
        data = b"incremental-artifact"
        self.store.upload(self.name, io.BytesIO(data), hashlib.sha256(data).hexdigest(),
                          "application/octet-stream")
        info = self.store.stat(self.name)
        self.corrupt = True
        with self.assertRaises(Collision):
            self.store.download(self.name, info, io.BytesIO())
        self.failed = True
        with self.assertRaises(RuntimeError):
            self.store.probe()
        self.failed, self.corrupt = False, False
        self.store.probe()  # A failed connection is replaced for the next request.


if __name__ == "__main__":
    unittest.main()
