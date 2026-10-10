"""Loopback Lake a0/r0 service backed by private GCS with persistent HMAC auth.

Lake v4.33.0-rc2 signs S3 uploads but downloads anonymously. This bridge keeps
GCP credentials outside the Lean process, and implements only the two cache
object families. No listener is exposed beyond 127.0.0.1.
"""
from __future__ import annotations

import argparse
import base64
import contextlib
import datetime
import hashlib
import hmac
import http.client
import json
import os
import re
import ssl
import tempfile
import threading
from dataclasses import dataclass
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import quote, unquote, urlsplit

MAX_MAP_BYTES = 128 * 1024 * 1024
MAX_ART_BYTES = 2 * 1024 * 1024 * 1024


class Missing(Exception):
    pass


class Collision(Exception):
    pass


class Race(Exception):
    pass


@dataclass
class ObjectInfo:
    generation: int
    size: int
    sha256: str | None
    content_type: str


def digest_file(handle) -> str:
    handle.seek(0)
    digest = hashlib.sha256()
    while chunk := handle.read(1024 * 1024):
        digest.update(chunk)
    handle.seek(0)
    return digest.hexdigest()


def merge_maps(old: bytes | None, new: bytes) -> bytes:
    def parse(data):
        lines = data.decode("utf-8").splitlines()
        if not lines:
            raise ValueError("Missing schema")
        header = json.loads(lines[0])
        if not isinstance(header, str):
            raise ValueError("Invalid schema")
        entries = {}
        for line in lines[1:]:
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, list) or len(row) != 2:
                raise ValueError("Invalid mapping")
            key = json.dumps(row[0], sort_keys=True, separators=(",", ":"))
            if key in entries and entries[key] != row:
                raise Collision("Conflicting native input hash")
            entries[key] = row
        return header, entries
    header, incoming = parse(new)
    if old is not None:
        old_header, entries = parse(old)
        if old_header != header:
            raise Collision("Incompatible mapping schemas")
        for key, row in incoming.items():
            if key in entries and entries[key] != row:
                raise Collision("Conflicting native input hash")
            entries[key] = row
    else:
        entries = incoming
    output = "\n".join([json.dumps(header), *[
        json.dumps(entries[key], separators=(",", ":"), sort_keys=True)
        for key in sorted(entries)
    ]]) + "\n"
    data = output.encode()
    if len(data) > MAX_MAP_BYTES:
        raise ValueError("Merged map too large; rotate namespace")
    return data


def validate_hmac_credentials(data):
    if not isinstance(data, dict) or data.get("type") != "gcs_hmac":
        raise ValueError("Expected persistent GCS HMAC credentials; user OAuth ADC is unsupported")
    access_id, secret = data.get("access_id", ""), data.get("secret", "")
    if (not isinstance(access_id, str) or not isinstance(secret, str)
            or not re.fullmatch(r"(?:[A-Za-z0-9]{24}|[A-Za-z0-9]{61})", access_id)
            or not re.fullmatch(r"[A-Za-z0-9+/=]{40}", secret)):
        raise ValueError("Invalid GCS HMAC access ID or secret format")
    return access_id, secret


def load_hmac_credentials(path):
    path = Path(path)
    info = path.stat()
    if info.st_uid != os.geteuid() or info.st_mode & 0o077:
        raise ValueError("HMAC credential file must belong to this user and have mode 0600")
    return validate_hmac_credentials(json.loads(path.read_text()))


def sign_headers(method, target, headers, access_id, secret, payload_hash, now=None):
    """Cloud Storage V4 signed headers, not an expiring signed URL/OAuth token."""
    now = now or datetime.datetime.now(datetime.timezone.utc)
    stamp, day = now.strftime("%Y%m%dT%H%M%SZ"), now.strftime("%Y%m%d")
    headers = {key.lower(): " ".join(value.split()) for key, value in headers.items()}
    headers.update({"host": "storage.googleapis.com", "x-goog-date": stamp,
                    "x-goog-content-sha256": payload_hash})
    names = sorted(headers)
    signed = ";".join(names)
    canonical_headers = "".join(key + ":" + headers[key] + "\n" for key in names)
    path, separator, query = target.partition("?")
    canonical = "\n".join([method, path, query if separator else "",
                            canonical_headers, signed, payload_hash])
    scope = day + "/auto/storage/goog4_request"
    to_sign = "\n".join(["GOOG4-HMAC-SHA256", stamp, scope,
                          hashlib.sha256(canonical.encode()).hexdigest()])
    key = ("GOOG4" + secret).encode()
    for part in [day, "auto", "storage", "goog4_request"]:
        key = hmac.new(key, part.encode(), hashlib.sha256).digest()
    signature = hmac.new(key, to_sign.encode(), hashlib.sha256).hexdigest()
    headers["authorization"] = (f"GOOG4-HMAC-SHA256 Credential={access_id}/{scope}, "
                                 f"SignedHeaders={signed}, Signature={signature}")
    return headers


class GCSStore:
    """XML API over verified TLS; persistent HMAC key and one connection per thread."""
    def __init__(self, project: str, bucket: str, prefix: str, credentials):
        self.project, self.bucket_name, self.prefix = project, bucket, prefix
        self.access_id, self.secret = credentials
        self.local = threading.local()
        self.tls = ssl.create_default_context()

    @contextlib.contextmanager
    def request(self, method, name=None, *, query=None, headers=None, body=None,
                payload_hash=None):
        if name is not None and not name.startswith(self.prefix + "/"):
            raise ValueError("Object lies outside the cache prefix")
        target = "/" + quote(self.bucket_name, safe="")
        if name is not None:
            target += "/" + quote(name, safe="/-_.~")
        if query:
            encoded = sorted((quote(str(k), safe="-_.~"), quote(str(v), safe="-_.~"))
                             for k, v in query.items())
            target += "?" + "&".join(k + "=" + v for k, v in encoded)
        signed = sign_headers(method, target, headers or {}, self.access_id, self.secret,
                              payload_hash or hashlib.sha256(b"").hexdigest())
        if not hasattr(self.local, "connection"):
            self.local.connection = http.client.HTTPSConnection(
                "storage.googleapis.com", timeout=60, context=self.tls)
        connection, response = self.local.connection, None
        try:
            connection.request(method, target, body=body, headers=signed)
            response = connection.getresponse()
            if response.status == 404:
                raise Missing(name)
            if response.status == 412:
                raise Race(name)
            if not 200 <= response.status < 300:
                # Never include remote error bodies or signed headers in logs.
                raise RuntimeError(f"GCS XML request failed with HTTP {response.status}")
            yield response
        except BaseException:
            connection.close()
            del self.local.connection
            raise
        finally:
            if response is not None:
                response.close()

    def probe(self):
        # Listing one object checks bucket access without storage.buckets.get.
        with self.request("GET", query={"max-keys": 1, "prefix": self.prefix + "/"}) as response:
            if len(response.read(65537)) > 65536:
                raise RuntimeError("Unexpectedly large bucket probe response")

    def stat(self, name: str) -> ObjectInfo:
        with self.request("HEAD", name) as response:
            response.read()
            return ObjectInfo(int(response.getheader("x-goog-generation")),
                              int(response.getheader("Content-Length")),
                              response.getheader("x-goog-meta-sha256"),
                              response.getheader("Content-Type"))

    def download(self, name, info: ObjectInfo, handle):
        with self.request("GET", name, headers={"x-goog-if-generation-match": str(info.generation)}) as response:
            expected = dict(part.strip().split("=", 1)
                            for part in (response.getheader("x-goog-hash") or "").split(",")
                            if "=" in part).get("md5")
            digest, sha256, size = hashlib.md5(usedforsecurity=False), hashlib.sha256(), 0
            while chunk := response.read(1024 * 1024):
                size += len(chunk)
                if size > info.size:
                    raise Collision("Oversized object download")
                digest.update(chunk)
                sha256.update(chunk)
                handle.write(chunk)
            if size != info.size:
                raise Collision("Truncated object download")
            if expected and base64.b64encode(digest.digest()).decode() != expected:
                raise Collision("GCS download checksum mismatch")
            if not info.sha256 or not hmac.compare_digest(sha256.hexdigest(), info.sha256):
                raise Collision("Missing or mismatched SHA256 object metadata")
        handle.seek(0)

    def upload(self, name, handle, sha256, content_type, generation=0):
        handle.seek(0)
        digest, size = hashlib.md5(usedforsecurity=False), 0
        while chunk := handle.read(1024 * 1024):
            digest.update(chunk)
            size += len(chunk)
        handle.seek(0)
        headers = {"content-length": str(size), "content-type": content_type,
                   "content-md5": base64.b64encode(digest.digest()).decode(),
                   "x-goog-if-generation-match": str(generation),
                   "x-goog-meta-sha256": sha256, "x-goog-meta-cache-protocol": "lake-v4.33"}
        with self.request("PUT", name, headers=headers, body=handle, payload_hash=sha256) as response:
            if len(response.read(65537)) > 65536:
                raise RuntimeError("Unexpectedly large upload response")


def object_name(path: str, prefix: str) -> tuple[str, str]:
    parsed = urlsplit(path)
    if parsed.query or parsed.fragment:
        raise ValueError("Query strings are not cache objects")
    parts = unquote(parsed.path, errors="strict").split("/")
    if (len(parts) < 4 or parts[0] != "" or parts[1] not in {"a0", "r0"}
            or any(p in {"", ".", ".."} or not re.fullmatch(r"[A-Za-z0-9_.-]+", p)
                   for p in parts[2:])):
        raise ValueError("Invalid cache path")
    kind, leaf = parts[1], parts[-1]
    if kind == "a0" and not re.fullmatch(r"[0-9a-f]{16}\.art", leaf):
        raise ValueError("Invalid Lake artifact name")
    if kind == "r0" and leaf != "latest.jsonl":
        raise ValueError("Only successful merged mapping indexes are supported")
    return prefix + "/" + "/".join(parts[1:]), kind


class CacheServer(ThreadingHTTPServer):
    daemon_threads = True
    def __init__(self, address, store, prefix, temp_dir, workers=8):
        if address[0] != "127.0.0.1":
            raise ValueError("Cache server must listen on loopback")
        self.store, self.prefix, self.temp_dir = store, prefix, temp_dir
        self.slots = threading.BoundedSemaphore(workers)
        super().__init__(address, Handler)

    def process_request(self, request, client_address):
        self.slots.acquire()
        try:
            super().process_request(request, client_address)
        except Exception:
            self.slots.release()
            raise

    def process_request_thread(self, request, client_address):
        try:
            super().process_request_thread(request, client_address)
        finally:
            self.slots.release()


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    def setup(self):
        super().setup()
        self.connection.settimeout(120)

    def log_message(self, fmt, *args):
        pass  # Never echo credentials, arbitrary URLs or GCS error responses.

    def allowed(self):
        expected = f"127.0.0.1:{self.server.server_address[1]}"
        if self.headers.get("Host") != expected or self.headers.get("Origin"):
            self.reply(403, b"Loopback clients only\n")
            return False
        return True

    def reply(self, code, data=b"", content_type="text/plain"):
        self.close_connection = True
        self.send_response(code)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Content-Type", content_type)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Connection", "close")
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(data)

    def handle_expect_100(self):
        if not self.allowed():
            self.close_connection = True
            return False
        return super().handle_expect_100()

    def do_GET(self):
        if not self.allowed():
            return
        try:
            if self.path == "/healthz":
                self.reply(200, b"ok\n")
                return
            if self.path == "/readyz":
                self.server.store.probe()
                self.reply(200, b"gcs-ready\n")
                return
            name, kind = object_name(self.path, self.server.prefix)
            info = self.server.store.stat(name)
            cap = MAX_MAP_BYTES if kind == "r0" else MAX_ART_BYTES
            if info.size > cap:
                raise ValueError("Remote object too large")
            with tempfile.TemporaryFile(dir=self.server.temp_dir) as handle:
                self.server.store.download(name, info, handle)
                if info.sha256 and digest_file(handle) != info.sha256:
                    raise Collision("SHA256 mismatch")
                if kind == "r0":
                    merge_maps(None, handle.read())  # validate without changing bytes
                    handle.seek(0)
                self.send_response(200)
                self.send_header("Content-Length", str(info.size))
                self.send_header("Content-Type", info.content_type or "application/octet-stream")
                self.send_header("Cache-Control", "no-store")
                self.send_header("Connection", "close")
                self.end_headers()
                self.close_connection = True
                while chunk := handle.read(1024 * 1024):
                    self.wfile.write(chunk)
        except Missing:
            self.reply(404)
        except ValueError:
            self.reply(400, b"Invalid cache request\n")
        except Collision:
            self.reply(409, b"Cache integrity conflict\n")
        except (BrokenPipeError, ConnectionResetError):
            self.close_connection = True
        except Exception as exc:
            print(json.dumps({"event": "cache_read_error", "type": type(exc).__name__}), flush=True)
            self.reply(502, b"GCS cache unavailable\n")

    def do_PUT(self):
        if not self.allowed():
            self.close_connection = True
            return
        try:
            name, kind = object_name(self.path, self.server.prefix)
            if self.headers.get("Transfer-Encoding"):
                raise ValueError("Chunked uploads are unsupported")
            size = int(self.headers.get("Content-Length", "-1"))
            cap = MAX_MAP_BYTES if kind == "r0" else MAX_ART_BYTES
            if not 0 <= size <= cap:
                raise ValueError("Invalid content length")
            with tempfile.TemporaryFile(dir=self.server.temp_dir) as handle:
                remaining = size
                while remaining:
                    chunk = self.rfile.read(min(remaining, 1024 * 1024))
                    if not chunk:
                        raise ValueError("Truncated upload")
                    handle.write(chunk)
                    remaining -= len(chunk)
                sha256 = digest_file(handle)
                if kind == "a0":
                    self.put_artifact(name, handle, sha256)
                else:
                    self.put_mapping(name, handle.read())
            self.reply(200)
        except ValueError:
            self.close_connection = True
            self.reply(400, b"Invalid cache upload\n")
        except Collision:
            self.reply(409, b"Cache integrity conflict\n")
        except (BrokenPipeError, ConnectionResetError):
            self.close_connection = True
        except Exception as exc:
            print(json.dumps({"event": "cache_write_error", "type": type(exc).__name__}), flush=True)
            self.reply(502, b"GCS cache unavailable\n")

    def put_artifact(self, name, handle, sha256):
        try:
            current = self.server.store.stat(name)
        except Missing:
            try:
                self.server.store.upload(name, handle, sha256,
                                         "application/vnd.reservoir.artifact", generation=0)
                return
            except Race:
                current = self.server.store.stat(name)
        if current.sha256 != sha256:
            raise Collision("Native artifact hash collision or corrupt object")
        # An identical artifact is never uploaded to GCS a second time.

    def put_mapping(self, name, data):
        for attempt in range(8):
            try:
                current = self.server.store.stat(name)
                if current.size > MAX_MAP_BYTES:
                    raise ValueError("Oversized mappings")
                with tempfile.TemporaryFile(dir=self.server.temp_dir) as old_file:
                    self.server.store.download(name, current, old_file)
                    if current.sha256 and digest_file(old_file) != current.sha256:
                        raise Collision("Stored mappings SHA256 mismatch")
                    old = old_file.read()
                generation = current.generation
            except Missing:
                old, generation = None, 0
            except Race:
                continue
            merged = merge_maps(old, data)
            if merged == old:
                return
            with tempfile.TemporaryFile(dir=self.server.temp_dir) as handle:
                handle.write(merged)
                try:
                    self.server.store.upload(name, handle, hashlib.sha256(merged).hexdigest(),
                                             "application/vnd.reservoir.outputs+json-lines", generation)
                    return
                except Race:
                    continue
        raise RuntimeError("Concurrent mapping updates exceeded retry limit")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--project", required=True)
    parser.add_argument("--bucket", required=True)
    parser.add_argument("--prefix", default="lean-cache/v1")
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument("--temp-dir", required=True)
    parser.add_argument("--credentials-file", required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"[a-z][a-z0-9-]{4,61}[a-z0-9]", args.bucket):
        # Dotted bucket names are accepted by GCS, too.
        if not re.fullmatch(r"[a-z0-9][a-z0-9._-]{1,220}[a-z0-9]", args.bucket):
            parser.error("Supply a bucket name, without gs://")
    if any(p in {"", ".", ".."} or not re.fullmatch(r"[A-Za-z0-9_.-]+", p)
           for p in args.prefix.split("/")):
        parser.error("Invalid GCS prefix")
    temp_dir = Path(args.temp_dir)
    temp_dir.mkdir(parents=True, exist_ok=True, mode=0o700)
    store = GCSStore(args.project, args.bucket, args.prefix,
                     load_hmac_credentials(args.credentials_file))
    store.probe()  # A startup auth failure must be visible, not a false cache miss.
    server = CacheServer(("127.0.0.1", args.port), store, args.prefix, temp_dir)
    print(json.dumps({"event": "cache_ready", "port": args.port}), flush=True)
    server.serve_forever()


if __name__ == "__main__":
    main()
