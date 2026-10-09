# RiemannResearch storage recovery tools

These Python 3 tools use the standard library. They do not invoke Lean, submit a
verification job, open a server workspace, edit Git history, or reclaim content.
No remote-host execution has been performed merely by creating this bundle.

## Read-only inventory

Run **on the actual verifier host** with its exact existing project path. Send
stdout to another filesystem or stream it to the administrator when the host is
full. Replace `YOUR_PROJECT_ROOT` and any PID/log placeholders with observed
values; do not invent a process identity from a coordinator job ID.

```bash
python3 inventory.py \
  --root YOUR_PROJECT_ROOT \
  --root /home/cri_2025/.cache/lean-agent-dependencies \
  --root /home/cri_2025/lean-agent-workspaces \
  --git-root YOUR_PROJECT_ROOT \
  --max-entries 150000 --max-seconds 30
```

For a **confirmed existing process**, add `--pid 12345`. Optional `--log PATH`
records only log size and modification time. PID sampling defaults to one second;
identity includes PID creation ticks and the boot ID to catch PID reuse. It
reports CPU/I/O deltas and visible deleted-open file descriptors. It does not
stop a process or infer that an unchanged task counter means a stalled proof.

The output includes the observed mount, available blocks and inodes, bounded
directory and file consumers, Git status, and ignored/untracked `.lean` files.
Git optional locks and fsmonitor are disabled. Git child output is limited to
2 MiB per command and 30 seconds; truncation/error is explicit. Timeout or output
limit terminates only that own read-only Git child, never a supplied PID.

The scan never follows symlinks or crosses filesystem devices. A scan budget,
permission failure or excluded mount is explicitly incomplete. Byte counts for
incomplete scans are lower bounds and **not** safe reclamation estimates. Counted
blocks are unique per inode within one root; overlapping roots are not additive.
Shared copy-on-write extents, quota, snapshots and filesystem metadata need
administrator tools. Time budgets bound traversal loops, not slow filesystem
syscalls. Reads may update filesystem access times. The script does not read
shell credentials, environment contents or process command lines.

## Archive and verify selected inactive content

Use only for selected inactive directories with no writer/active job/lease, or
for a consistent read-only snapshot. `--quiescent` asserts that the administrator
has established this; the tool cannot establish it from coordinator state.

```bash
python3 archive_verify.py \
  --source /exact/inactive/workspace \
  --destination /mounted/other-filesystem/archives \
  --quiescent
```

Repeat `--source` for nonoverlapping directories. The destination must already
exist and have a **different filesystem device ID** from every source. This is
intentional: it refuses to add another large archive to the exhausted volume.
Use an authenticated mounted private archive destination or another private
volume; these tools do not provision cloud credentials or upload objects.

Every selected regular file is included, with **no `.git`, `.lake`, scratch,
ignored-file or log exclusions**. A SHA-256 inventory records content, original
paths, mode, ownership, modification/creation metadata, symlink targets,
hard-link identity and readable extended attributes. The archive stores file
contents, modes, UID/GID, nanosecond modification times, directory and symlink
entries. Hard-linked contents are stored independently; original link topology
is in the manifest. Xattrs are base64 in the manifest, requiring a suitable
restorer. Symlinks are preserved as link text; external target contents are not
implicitly archived. Include those dependencies separately. Nested mounts and
special files are refused for separate preservation.

The tool verifies **every archived regular-file hash**, embedded manifest,
listing, types, modes, ownership, links and modification times. It then repeats
the complete source inventory and rejects changes. Up to three files no larger
than 8 MiB each are restored to the archive destination and hash checked. These
are content restoration tests, not full metadata restoration, Git usability,
or a Lean rebuild. The archive and JSON records are synced to the filesystem.

Output is a new private directory containing:

- `content.tar.gz`
- `manifest.json`
- `receipt.json` with archive/manifest SHA-256 and sample restoration details
- `sample_restore/` with the bounded restored sample

Failure retains `.partial` data and `FAILED.json` where possible; it never cleans
up originals or partial output. A verified receipt means the observed selected
content was archived, **not** that deletion is now approved or that a proof was
verified. No delete, kill, reset, cache-eviction, or `extractall` operation exists.
An independent durable copy, complete restoration plan and inactive-reference
review remain necessary before a separate reclamation action. Filesystem ACLs,
flags, reflinks, snapshots and special files require separate preservation.

## Tests

```bash
python3 -m unittest -v test_tools
```

Recommended repository destination: `tools/storage_recovery/`. The package has
an `__init__.py` for recursive unittest discovery. CI can run it explicitly:

```bash
python3 -m unittest discover -s tools/storage_recovery -p 'test_*.py'
```

Tests create only disposable fixtures. The cross-filesystem archive tests use
temporary directories on `/dev/shm` when it has a distinct writable device ID;
otherwise they explicitly skip. They cover source-change rejection, retained
partial output, same-filesystem refusal, ignored proofs, hardlinks, symlinks,
bounded scan/output, special-file rejection, full hashes, sample restoration,
and corruption rejection. Real server diagnostic coverage requires running the
inventory on that server after an authorized execution capability is available.
