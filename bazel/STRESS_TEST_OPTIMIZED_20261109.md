# Optimized Bazel verification tests — 2026-11-09

The tested repository revision is `4bcfcc114d2d6de516e5fd17a76f07aa78ae85ec`,
which shares Lean action inputs and defers setup serialization. These are
infrastructure measurements. Experimental proof variants remain unpublished.

## Full-project concurrency

Every build used the repository's Bazel configuration with `--config=buildbuddy`.
The full target configured 46,184 targets and reused cached Lean artifacts.
These runs measure whole-project verification with populated compilation caches.

| Run | Outcome | Server verification wall time |
| --- | --- | ---: |
| One full build with a fresh Bazel server | Passed | 168.994 s |
| Five simultaneous full builds | All five passed | 419.020–626.938 s each |
| Five-build batch, first worker start to last completion | Passed | 631.332 s |
| Ten simultaneous full builds | All ten cancelled by the operator after prolonged paging | No completion measurement |

All five workers overlapped for 415.668 seconds. No cross-workspace collision
was observed. The five-build phase peaked at 28.773 GiB of service swap. The
ten-build phase peaked at 53.261 GiB. Neither phase recorded an OOM kill. The
ten-build outcome does not establish deadlock or successful completion.

The initial solo full build had a sampled peak JVM RSS of about 3.99 GiB,
compared with about 8.50 GiB in the earlier test. After idle collection, its
sampled RSS was about 0.893 GiB. Cache warmth, host policy and background work
differed between the old and new samples, so these observations do not isolate
a causal speedup. The five-build phase also produced individual JVM RSS peaks
above the initial solo sample.

Three simultaneous cold-server focused checks passed in 37.557, 39.636 and
47.725 seconds. Their service memory peak was 7.728 GiB, with a peak ten-second
full memory-pressure average of 0.33% and no memory-high events.

## Resource policy and method

The solo full build and initial cold focused checks ran with a 9 GiB service
memory-high threshold, 10 GiB memory maximum and 1 GiB service swap cap. Before
the ten-build phase, the operator applied 11 GiB memory-high, 12 GiB memory-max
and unlimited service swap. That policy remained in place for the five-build
and subsequent invalidation tests. WSL had 128 GiB of swap available.

Bazel had an 8 GiB heap ceiling per server. Global Bazel admission was uncapped,
with one active job per workspace. Every workspace used an independent Bazel
server. Remote Lean execution did not remove local analysis or cache-checking
costs. Telemetry was sampled every two seconds and includes charged filesystem
cache and the service's other processes.

The old serial 4/42/100-module invalidation measurements were 83.486, 315.328
and 538.558 seconds. The old simultaneous measurements were 194.589, 362.206
and 476.274 seconds. Fresh proof variants are used in this round to make the
invalidation measurements perform real compilation work. Sources and imports
are otherwise preserved.

## Fresh cache invalidations

Every measurement below passed. Each refactor changed a proof while preserving
its theorem statement and imports. Distinct proof variants were used in the
serial and concurrent rounds. The reported remote counts confirm that the
concurrent checks performed fresh compilation work.

| Changed module and checked consumer | Fresh remote compilations | Serial wall time | Concurrent wall time |
| --- | ---: | ---: | ---: |
| `Analysis/FiniteGramSchurBounds` → `RH/QCanonicalSchurVariance` | 4 | [97.398 s](https://app.buildbuddy.io/invocation/2e04a438-5663-4b05-a0bf-3ccaad8a5f30) | [43.793 s](https://app.buildbuddy.io/invocation/d6473864-9a96-4698-8ee0-b16a1722378d) |
| `Analysis/FiniteHilbertGram` → `RH/QCRTGramMinimizer` | 42 | [335.198 s](https://app.buildbuddy.io/invocation/adc5de7e-4651-49f2-884c-850c4aedd292) | [208.809 s](https://app.buildbuddy.io/invocation/aca673b9-918c-453f-a44c-beebd6aa484b) |
| `RH/ZetaTwoProbability` → `RH/QFullIsometricTransport` | 100 | [512.063 s](https://app.buildbuddy.io/invocation/5cd25a06-b2bd-48ac-af48-89c05be65ae6) | [332.994 s](https://app.buildbuddy.io/invocation/f63589b2-7f15-4260-b9a9-1355629a1d23) |

Paths are relative to `RiemannResearch/` and omit the `.lean` suffix. The
unchanged action-cache counts were 196, 225 and 266 for the respective sizes.
All three concurrent jobs overlapped for 42.588 seconds. The batch spanned
333.065 seconds from first worker start to last completion. The sampled
concurrent phase peaked at 10.17 GiB of service memory and 2.22 GiB of swap,
with no full memory-pressure stalls or new memory-high, memory-max or OOM
events. The serial wall times sum to 944.659 seconds.

These samples demonstrate concurrent progress. They do not isolate a
parallel speedup factor. The rounds used different proof variants and their
local and remote cache warmth differed. Lightweight correctness probes also
ran during parts of the serial measurements.

## Full project alongside a fresh edit

The final full-project run used an existing clean checkout with a fresh Bazel
JVM. It ran alongside a new four-module proof refactor in another workspace.

| Check | Wall time | Actions |
| --- | ---: | --- |
| Full aggregate | [194.885 s](https://app.buildbuddy.io/invocation/4a0b9496-ebb9-475a-b25e-39ad71150624) | 3,942 remote-cache hits |
| Fresh small edit | [42.689 s](https://app.buildbuddy.io/invocation/c79073d9-129e-4e97-984b-49f00f4ce73a) | 4 remote compilations and 196 action-cache hits |

Both passed, with about 42.8 seconds of actual overlap. The sampled phase
peaked at 11.00 GiB of service memory and 2.236 GiB of swap. Full memory
pressure averaged over ten seconds peaked at 3.18%. There were 20,483
memory-high events and no memory-max or OOM events.

An unrelated workspace also performed work during this phase. Its two most
recent jobs were terminal and successful at the final read-only check. That
background work limits comparisons with the solo full build.

All three edited source files were restored byte-for-byte to their original
contents. A second readback confirmed the originals and clean Git status in
each experimental workspace. No experimental proof changes were published.

## Subsequent 3 GiB heap change

Commit `4ff1ffb3bc8e36d7d4d3f2fe8b53a186ef5768e7` landed after the main suite
and lowered the per-server heap ceiling from 8 GiB to 3 GiB. A clean test
workspace was synced to that exact revision and its full aggregate build
passed in [155.025 seconds](https://app.buildbuddy.io/invocation/e8a4997a-4976-48ee-9c2f-b0748b6516ca),
reusing 3,942 action-cache entries. The changed startup flags started a new
JVM. Its sampled peak RSS was about 1.99 GiB. The phase recorded no memory-max
or OOM events, with 3,697 memory-high events and a peak full memory-pressure
ten-second average of 2.35%.

The five-way and mixed-invalidation measurements above used the earlier
8 GiB heap ceiling. Five-way concurrency has not been rerun with 3 GiB heaps.
The service still reported uncapped admission during this additional build.

## Five-build admission policy

Commit `68c9cdb2a90a3c01ad335350ea9d9d16493aaf83` changes the default global
Bazel capacity from unlimited to five and updates the service profile.
Additional jobs remain queued until a shared capacity lease is available.
Their execution timer begins after capacity is acquired. Each workspace
continues to admit one pending job. Explicit `LEAN_BAZEL_JOB_WORKERS=0` remains
available for uncapped operation.

The updated infrastructure suite passed all 88 tests. Its concurrency test
holds five jobs, submits a sixth through a second manager, verifies that the
sixth stays queued, releases one slot and verifies progress. The lease limit
is shared across cooperating processes. The `active_job_count` response field
continues to count the responding process's jobs.

This source change was published after the measurements above. Deployment
requires updating the existing service environment and restarting when idle.

After the test jobs are terminal, deploy the cap with these commands.

```bash
cd "$HOME/lean-projects/RiemannResearch"
git pull --ff-only
sudo install -d /etc/systemd/system/lean-tunnel.service.d
printf '[Service]\nEnvironment=LEAN_BAZEL_JOB_WORKERS=5\n' |
  sudo tee /etc/systemd/system/lean-tunnel.service.d/99-bazel-admission.conf >/dev/null
sudo systemctl daemon-reload
sudo systemctl restart lean-tunnel.service
```

Refresh the Lean plugin connection after restart. Confirm a subsequent job
reports `worker_count: 5`. The local unit tests establish the new source
behavior, while that live response establishes the service's effective cap.

## Correctness checks

All 86 repository infrastructure unit tests passed. An additional 18 tests of
the optimized input helpers passed, covering 200 seeded dependency graphs and
512 modeled setup-argument comparisons. These helper tests used stand-ins for
Starlark depsets and JSON encoding. They do not replace live Bazel action-input
equivalence checks.

The complete repository path inventory passed the BUILD-package coverage
audit, covering 3,930 Lean source paths and 66 package files. The local audit
used exact package files and source-path placeholders. Live nested-directory
testing also generated the required parent and leaf BUILD files and compiled
the new source successfully.

| Live case | Result |
| --- | --- |
| Valid Bazel snippet | Passed |
| Duplicate pending request | Reused the original job |
| Different request in a busy workspace | Rejected |
| False equality proved using `rfl` | Rejected by Lean |
| Named theorem using warning-suppressed `sorry` | Rejected by the compiled audit |
| Anonymous `example` using warning-suppressed `sorry` | Incorrectly accepted |
| One-second Bazel timeout | Failed with `wall_timeout`, temporary source removed |
| Valid Bazel job immediately after timeout | Passed |
| Explicit Lake core-only rollback check | Passed with `backend=lake` |

The anonymous `sorry` gap reproduced at both the optimized revision and the
earlier `d55848e` checkout, using identical source bytes. It predates the input
sharing optimization. The existing compiled-output audit cannot see an
anonymous example that Lean discards from the final environment. This gap
prevents describing the complete acceptance suite as passing.

The live Bazel verifier incorrectly reported success for this input.

```lean
import Mathlib.Data.Nat.Basic
set_option warn.sorry false
example : (0 : Nat) = 1 := by sorry
```

The optimized run was `job_PEvqefVO7j45P1PD9hnKYIM1NSyxYH_T`. The old-revision
comparison was `job_odUjJscDkVX2uxFrCp8jhmq7DE1gMFwR`. Giving the theorem a
name triggered the existing compiled-placeholder rejection.

Lean's source elaborates examples inside `withoutModifyingEnv`, and its normal
placeholder warning depends on `warn.sorry`. The investigation confirmed these
mechanisms against the pinned toolchain sources.
[Example elaboration](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Elab/MutualDef.lean#L1196)
and [placeholder warnings](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/AddDecl.lean#L81).

A proposed command callback inspects elaborated expression trees before
anonymous declarations disappear. Live prototype tests accepted valid proofs
and rejected suppressed, macro-generated and message-captured placeholders.
The integration candidate uses a native compiler plugin. Native linking,
plugin preloading and the complete project gate have not been validated, so
the fix has not been published or deployed. These prototype results do not
certify the live acceptance path.

## Remaining validation limits

- The actual `lean_share_inputs=0` rollback and `lean_verify_shared_inputs=1`
  comparison modes were not exercised through the MCP build API, which does
  not expose arbitrary Bazel flags.
- The remote patch API rejected deletion of three valid functional-test
  fixture files. They remain untracked in their isolated workspace and were
  not published.

The companion JSON records exact job IDs, invocation links, timing bounds,
resource observations and verification limitations.

The deletion API blocked cleanup of these three files created by the nested
package test. They can be removed after that workspace is idle.

```bash
lean_test_project="$HOME/lean-agent-workspaces/ws_E1lB2gP7I33f6mf4XvlTaALLfdqcXKes/RiemannResearch"
rm -- \
  "$lean_test_project/RiemannResearch/Verification/OptimizedFunctional/NestedIdentity.lean" \
  "$lean_test_project/RiemannResearch/Verification/OptimizedFunctional/BUILD.bazel" \
  "$lean_test_project/RiemannResearch/Verification/BUILD.bazel"
```

## Proposed compiler audit callback

This tested callback is retained as an investigation record. It is not loaded
by the deployed compiler. Production integration still requires a native
plugin build, loader tests, shared-input checks and full-project validation.
The callback must run in the separate compiler process because a rejected
proof terminates that process. The post-compilation named-declaration audit
continues to provide an independent check.

```lean
import Lean.Elab.Command
import Lean.Elab.InfoTree.Main
import Lean.Util.Sorry

open Lean Lean.Elab

namespace BazelForbidSorry

/-- Inspect elaborated terms before anonymous declarations leave the environment. -/
partial def containsIncompleteProof (tree : InfoTree)
    (context? : Option ContextInfo := none) : IO Bool := do
  match tree with
  | .context info child =>
    containsIncompleteProof child (info.mergeIntoOuter? context?)
  | .hole _ =>
    throw <| IO.userError "unresolved elaboration information in proof audit"
  | .node info children =>
    let context? := info.updateContext? context?
    if let .ofTermInfo term := info then
      let some context := context?
        | throw <| IO.userError "missing elaboration context in proof audit"
      let incomplete ← term.runMetaM context do
        return (← instantiateMVars term.expr).hasSorry
      if incomplete then
        return true
    for child in children do
      if ← containsIncompleteProof child context? then
        return true
    return false

def auditCommand (stx : Syntax) : Command.CommandElabM Unit := do
  let state ← get
  let failure? ← liftM <| do
    try
      if !state.infoState.enabled then
        return some "proof audit could not complete: elaboration information is disabled"
      let infoState := state.infoState.substituteLazy.get
      for tree in infoState.trees do
        if ← containsIncompleteProof tree then
          return some "proof contains a placeholder, but forbid_sorry is enabled"
      return none
    catch error =>
      return some s!"proof audit could not complete: {error}"
  if let some failure := failure? then
    let fileName ← getFileName
    let fileMap ← getFileMap
    let pos := fileMap.toPosition (stx.getPos?.getD 0)
    let stderr ← liftM IO.getStderr
    liftM <| stderr.putStrLn s!"{fileName}:{pos.line}:{pos.column}: error: {failure}"
    liftM stderr.flush
    -- A diagnostic can be consumed by #guard_msgs. This compiler-only
    -- verifier must fail the action even when the source catches errors.
    liftM <| IO.Process.exit 1

initialize Command.addLinter {
  run := auditCommand
  name := `BazelForbidSorry.auditCommand
}

end BazelForbidSorry
```
