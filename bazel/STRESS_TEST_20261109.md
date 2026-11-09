# Mixed cache-invalidation stress tests — 2026-11-09

These are measured infrastructure tests on the NucBoxK6 WSL service, not new
mathematical results. No experimental Lean source changes were published.
Machine-readable job identifiers, timestamps and hashes are in
[stress_test_20261109.json](stress_test_20261109.json).

## Workloads and method

Three agents prepared isolated proof refactors. Each changed one existing
declaration without changing its statement or imports. We traversed the target
import closures to predict invalidation sizes, then checked those predictions
against actual remote compilation counts. Shared disk and BuildBuddy caches
were retained. Distinct proof variants were used for serial and concurrent runs
so the concurrent round did real compilation work.

| Workload | Changed source | Checked consumer | Remote compilations per variant |
| --- | --- | --- | --- |
| Small | Analysis/FiniteGramSchurBounds.lean | RH/QCanonicalSchurVariance.lean | 4 |
| Medium | Analysis/FiniteHilbertGram.lean | RH/QCRTGramMinimizer.lean | 42 |
| Large | RH/ZetaTwoProbability.lean | RH/QFullIsometricTransport.lean | 100 |

Paths are relative to RiemannResearch/. All checks used Bazel with
--config=buildbuddy. The server reported no global worker cap and one job per
workspace. Three-way admission took 1.834–3.292 ms and examined no completed-job
history records.

The retained full-build checkout was b1283de; small/large were d55848e and
medium was 5e84d19. Their relevant Lean sources were identical before the test
refactors. These runs predate the package-index sharing optimization ae18a9a;
they do not measure its memory or speed effect.

## Serial and concurrent invalidations

Times are server-side verification wall times, excluding clone/RPC/polling time.

| Workload | Serial | Concurrent round | Actual compilation/cache counts |
| --- | ---: | ---: | --- |
| Small | [83.486 s](https://app.buildbuddy.io/invocation/ebdb5112-b047-4e12-a7ce-945ee52eaa99) | [194.589 s](https://app.buildbuddy.io/invocation/61b73dbb-79d4-417e-bb10-f1db3a82ba9d) | 4 remote + 196 action-cache hits |
| Medium | [315.328 s](https://app.buildbuddy.io/invocation/3d172dc5-018f-4829-94b0-52a8eb3a778d) | [362.206 s](https://app.buildbuddy.io/invocation/50f03cba-1d3b-4f51-8972-7e05b70f894f) | 42 remote + 225 action-cache hits |
| Large | [538.558 s](https://app.buildbuddy.io/invocation/a60be95a-363d-404b-8d68-f67d9fe5a9f3) | [476.274 s](https://app.buildbuddy.io/invocation/2107ea7b-5c8e-4fae-95f2-e90aac074707) | 100 remote + 266 action-cache hits |

Every row passed. The three concurrent jobs overlapped for 194.714 s; the batch
spanned 476.408 s from first worker start to last finish. Serial wall times sum
to 937.372 s. No cross-workspace collision was observed.

This is not a controlled speedup measurement. The concurrent round started at
9 GiB MemoryHigh / 10 GiB MemoryMax / 1 GiB swap allowance and suffered heavy
reclaim. The operator raised RAM limits to 11/12 GiB during the round and later
removed the unit-specific swap cap. The small workspace's five-minute idle timer
also expired before launch, so its run included a fresh JVM startup. Proof
variants, run order and remote-worker cache warmth differ.

## Full aggregate alongside a fresh invalidation

After all three jobs finished, WSL was restarted with 16 GiB swap. The effective
service policy was verified before launch: 11 GiB MemoryHigh, 12 GiB MemoryMax,
and unlimited unit-specific swap. Both Bazel servers started fresh.

| Test | Time | Result |
| --- | ---: | --- |
| Earlier full aggregate alone | [202.687 s](https://app.buildbuddy.io/invocation/68bcc691-0760-4375-b606-0c507e32dfb8) | Passed; 3,942 action-cache hits |
| Full aggregate alongside small D | [227.152 s](https://app.buildbuddy.io/invocation/890ba8fa-5c7f-48fa-ad69-fa36322da07c) | Passed; 3,942 action-cache hits |
| Fresh small D alongside full aggregate | [57.289 s](https://app.buildbuddy.io/invocation/1ae0aa05-97e4-42ec-9c33-a12905ac29cc) | Passed; 4 remote compilations + 196 action-cache hits |

The jobs overlapped for 55.651 s. The full aggregate took about 12% longer than
the earlier solo sample. That comparison also includes changed host limits and
cache conditions; it is one observation, not a general slowdown bound.

Both full runs configured 46,184 targets in 150 packages. They validated the
whole aggregate using cached compilation artifacts; neither was a complete
source recompilation or an empty-remote-cache benchmark.

During the stable-policy overlap window:
- Service memory peaked at about 11.00 GiB; swap peaked at 1.264 GiB.
- Ten-second full memory pressure peaked briefly at 6.93%, then returned to zero.
- There were no memory.max, OOM, or OOM-kill events.
- The full-build JVM peaked at about 8.50 GiB RSS and still held about 8.50 GiB
  roughly 31 seconds after completion. Increasing swap did not remove the
  retained analysis graph.

The monitor sampled every two seconds. Service memory includes more than JVM
RSS, including charged file-cache pages. Phase summaries include startup and a
short post-build idle window; they are not heap profiles.

## Earlier pressure failures are part of the result

An initial three-way cold analysis warmup, before any proof edits, reached about
99% full memory pressure at the old 9 GiB soft limit with the 1 GiB swap allowance
exhausted. The operator killed the small and large test JVMs. Those two jobs
ended with Bazel exit 37; they were infrastructure/operator cancellations, not
Lean proof failures. The medium warmup passed in 319.921 s.

The later two-JVM pressure episode involved an idle medium JVM and an active
large JVM. Cancelling the active large job was unnecessary; the completed
medium server could have been released instead. Job state must be checked
before choosing a process to stop. Sequential warm recovery succeeded without
purging shared caches.

The real three-way invalidation round also reached 98.98% peak full pressure
before the RAM limit increase. It ultimately passed all three jobs, with a
9.866 GiB service-memory peak and no OOM events. This validates progress after
relief, not adequate performance under the old limits.

## Conclusions and remaining limits

Independent workspaces can concurrently rebuild nontrivial changed dependency
closures through RBE. The counts above demonstrate 146 real remote compilations
in the three-way round. The measured admission path was negligible; local
analysis memory and retained JVM state were the demonstrated bottleneck.

The stable-policy full-plus-small round made concurrent progress with only a
brief pressure episode. This does not establish that three simultaneous full
analyses fit, or that arbitrary job counts are safe. A fully controlled rerun of
all three sizes under one unchanged policy would be needed for scaling claims.

The retained-memory concern remains confirmed. Bazel 9.2's Linux low-memory
shutdown consults VM-wide /proc/meminfo and waits five idle minutes; it does not
react promptly to this service's cgroup budget. Memory-aware eviction of idle
servers and reducing the analysis graph are the remaining priorities. Keep
workspace output bases separate to preserve isolation.

## Restoration and correctness

All three changed source files were restored byte-for-byte to their saved
originals, with independent full-file readbacks and matching SHA-256 values.
The three workspaces have no tracked modifications; existing isolated
VerificationStress fixtures remain untracked and unpublished.

The full-build checkout remained clean. This report records no new Lean source
or build-rule changes. Deliberately broken-proof and suppressed-sorry rejection
tests are recorded in [VERIFICATION.md](VERIFICATION.md#observed-verification-tests-2026-11-08-to-2026-11-09).

References:
- [Bazel 9.2 server low-memory watcher](https://github.com/bazelbuild/bazel/blob/9.2.0/src/main/java/com/google/devtools/build/lib/server/ServerWatcherRunnable.java)
- [Bazel memory tradeoffs](https://bazel.build/advanced/performance/memory)
