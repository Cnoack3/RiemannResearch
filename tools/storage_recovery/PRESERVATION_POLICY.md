# Preserving research content while controlling build copies

## Production diagnosis, October 2, 2026

The measured WSL filesystem had 955 GiB used and only 710 MiB available to
ordinary users. The home directory contained 806 workspace directories using
848 GiB, 66 GiB of project-build snapshots, and 26 GiB of shared dependencies.
One inspected workspace contained 28 MiB of research source and 6.6 GiB of
compiled project builds. These measurements identify accumulated workspace
trees and build snapshots as the main storage consumers. They do not establish
that all their files are identical or that every directory contains a complete
build.

The ext4 superblock confirmed 268435456 blocks of 4096 bytes and a 5% reserved
allocation. The operator reduced this allocation to 1%, retaining 10.24 GiB for
privileged processes and making another 40.96 GiB available. The subsequent
measurement was 955 GiB used, 42 GiB available. No research content was deleted,
moved, archived, rebuilt, or reclaimed by that setting change.

## Default policy

`LEAN_STORAGE_POLICY=preserve` is the default. Unknown values are rejected.

- Workspace opening does not run destructive automatic cleanup.
- Cleanup becomes an inventory; project-cache pruning retains existing trees.
- Existing workspaces and dependency directories are not deleted and replaced
  by rehydration, synchronization, dependency updates, or reset.
- Full project-build seed copies and extra successful-build snapshots are
  disabled. Existing snapshots remain on disk.
- Continue work with an existing workspace token and its build. Publication
  that requires an integration checkout returns a continuation token and path
  for that retained, validated checkout.
- Failed or incomplete provisioning retains its path and identifies its token.
  Capacity-related provisioning failures can be retried by resuming the token.
  Inconsistent dependency files require inspection; they are not removed to
  make a retry succeed.
- Failed integration work retains a requirement for validation before any
  later publication. Retaining a checkout never makes it verified.
- The original source revision remains readable and can be checked by Lean;
  its provenance is distinguished from the published integration revision.

`LEAN_STORAGE_POLICY=retention` explicitly opts into the older destructive
retention behavior. Do not select it when all existing research and build
content must be retained.

## Admission and verification

Managed large operations share a cross-process storage lease and recheck each
destination filesystem's user-available blocks and inodes before expensive
work. Storage admission errors report the operation, available and required
capacity, and instructions to reuse a workspace or add capacity. They are not
permission to delete content.

The default byte estimates are:

| Setting | Default |
|---|---:|
| `LEAN_STORAGE_RESERVE_BYTES` | 10 GiB |
| `LEAN_NEW_CLONE_BUDGET_BYTES` | 1 GiB |
| `LEAN_NEW_DEPS_BUDGET_BYTES` | 32 GiB |
| `LEAN_BUILD_GROWTH_BUDGET_BYTES` | 8 GiB |

The manager's reserve is additional to ext4's privileged reserve. Estimates
are admission floors, not hard quotas or guarantees about future compiler
output. Independent external writers can still consume capacity. An existing
dependency environment can be reused; a missing environment is admitted
separately. Do not lower admission floors solely to bypass a refusal.

The full build remains `lake build RiemannResearch --quiet`. Existing
affected-module checkpoint validation, source audits, and actual Lean
compilation remain required. Neither a cache hit, a retained build, a queued
job, nor a stored checkout is proof of a successful new verification.

This policy prevents storage maintenance from deleting retained trees. It is
not a backup of every historical byte version: requested source edits and
normal Lean/Lake compilation still write their normal outputs. Existing
versioned source continues to be preserved through Git checkpoints.

## Deployment and remaining capacity work

The infrastructure branch must be installed into the actual verifier launcher
before these manager behaviors apply. A GitHub commit alone does not update a
running WSL service. Identify the launcher and its source path, retain its
current code/configuration, and verify that active processes are quiescent
before restarting it. Do not infer that a terminal job record alone proves
that all child processes exited.

The 848 GiB of existing workspace data remains intact. The immediate reserved
allocation adjustment provides recovery headroom, while this policy limits
new copying and avoids destructive cleanup. If all content must remain online,
increase the actual storage capacity after checking the VHD's host drive and
available host capacity. A separately verified complete migration is another
option; a Git commit or a sample archive restore cannot establish preservation
of ignored files, builds, dependencies, or every workspace's unpublished work.

Do not hardlink writable build trees as a deduplication shortcut. A future
shared artifact store must bind the complete compiler/source/import/dependency
inputs and keep shared objects immutable, with private writable outputs.
