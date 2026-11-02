# RiemannResearch

Persistent, kernel-checked Lean research library focused on the Riemann
hypothesis and related analytic, spectral, operator-algebraic, and geometric
approaches.


The Serre II Lean program and its supporting research files are preserved on
[`serre-ii-archive-20260904`](https://github.com/Cnoack3/RiemannResearch/tree/serre-ii-archive-20260904).

## Source of truth

The `.lean` files in this repository are the mathematical record. Chat
conversations may propose work, but a result belongs to the library only after
it has been:

- saved in a project module;
- accepted by Lean;
- checked for placeholders and project-local axioms;
- built with the pinned toolchain and dependencies;
- committed to Git; and
- automatically pushed to the configured private remote.

## Layout

- `RiemannResearch/RH/`: zeta-function, finite certificates, and RH-oriented reductions
- `RiemannResearch/LinearAlgebra/`: finite-energy, Green-projection, Schur, and common-optimizer support used by the RH program
- `RiemannResearch/GroupTheory/AddSubgroupCRT.lean`: exact CRT support for prime-phase work
- `RiemannResearch/THEOREM_CATALOG.md`: RH declaration and research-obligation ledger

## Current research status — 1 November 2026

RH remains open. The latest weighted CRT series is complete: all ten principal
results were published individually, ending with
[`e83acbe4`](https://github.com/Cnoack3/RiemannResearch/commit/e83acbe435711d1197772afe30adb011971041da).
The [weighted CRT catalog](RiemannResearch/THEOREM_CATALOG_WEIGHTED_CRT_20261101.md)
records the declarations, publication commits, and recovery verification.
Nine results establish identities, structural properties, or an obstruction;
the tenth is a **conditional research reduction**.

| Development | Established scope | Remaining obligation or limitation |
| --- | --- | --- |
| [Weighted arithmetic residues and legal primitives](RiemannResearch/THEOREM_CATALOG_WEIGHTED_CRT_20261101.md) | Complete finite-residue energy identity, positive weights, exact refinement, pullback isometry, weighted adjoint and left inverse, full Pythagorean remainder, tower law, and nesting of legal primitives. | Construct a cofinal legal exact-head family with zero lower logarithmic growth of normalized complete residue energy. The checked RH criterion assumes this growth condition. |
| [Weighted-adjoint obstruction](RiemannResearch/RH/WeightedCRTLegalObstruction.lean) | The legal period-6 primitive of `4 r₂ - 3 r₃` has a weighted period-2 average with a strictly negative zero-residue value, so that average is not legal. | Ambient weighted averaging cannot be assumed to preserve the legal primitive space. A construction using it must prove legality separately. |
| [Complete dyadic Cesàro energy](RiemannResearch/RH/CesaroDyadicEnergyResearch20261101.md) | Exact complete head/tail decomposition, two-sided dyadic energy comparison, signed mean-neutral Möbius remainder, and conditional RH endpoints under P and Q. | Prove the required cancellation for an actual legal family across the complete moving tail. Sublinear energy alone does not give zero lower logarithmic growth. |
| [P/Q change of measure and squarefree restrictions](RiemannResearch/RH/CesaroMeasureSquarefreeResearch20261101.md) | Actual conditional-iid models, exact path-measure change, complete energy comparison, and transfer of the normalized growth criterion. A checked counterexample shows Cesàro averaging does not preserve the squarefree conductor closure. | Supply the arithmetic growth estimate. Legality belongs to the input; the smoothed output cannot silently be treated as an element of the unsmoothed squarefree space. |

The remaining growth condition permits nonzero amplitudes tending to zero and
requires only a zero lower logarithmic exponent along cofinal heads. It does
not require uniformly bounded energy. Exact finite CRT identities, positive
weights, and conditional-iid replication do not supply that arithmetic
estimate. The [final criterion's Lean type](RiemannResearch/RH/WeightedResidueRHCriterion.lean)
lists legality, positive periods, nonzero amplitudes, exact heads, cofinality,
and the open growth premise explicitly.

These are previously published results. This overview refresh changes
documentation only and does not constitute a new Lean verification.

### Earlier milestones — 18 October 2026

The following records distinguish Lean declarations from informal arguments
and numerical experiments.

| Development | Established scope | Remaining obligation |
| --- | --- | --- |
| [Bagchi dilation and Q/P energy](RiemannResearch/RH/BagchiDilationEnergyResearch20261018.md) | Exact complete quotient-block energy and nonnegative remainder; the squared Q-norm bound improves from `2/m` to `1/m`; normalized energies recover the Pareto quadratic form with `O(1/m)` error. | Dilation also changes the target. It does not supply vanishing constant-approximation error. The RH-to-squarefree-closure analytic providers remain unformalized. |
| [Pareto overshoot and signed innovations](RiemannResearch/RH/ParetoOvershootSignedInnovationsResearch20261018.md) | Limiting overshoot criteria, absolute summability with complete tail budgets, and the exact signed total `sum firstInnovation = -limitResidual(1)`. | Prove that this signed endpoint is zero, or supply one of the explicit arithmetic overshoot/first-coordinate estimates. Absolute summability alone does not do so. |
| [Primorial regularization](RiemannResearch/RH/QPrimorialRegularizationResearch20261018.md) | Exact stage identities, strong convergence at each fixed positive penalty, and squarefree constant closure equivalent to cofinal finite-stage objective values strictly below penalties tending to zero. | Produce the required complete-energy budgets or signed certificates along a positive penalty sequence tending to zero. |
| [Period-210 certificate and signed correction](RiemannResearch/RH/QPeriod210CertificateResearch20261018.md) | Rational legal trials with complete infinite tails: `J_(1/10)(F) < 1/10`, improved to `J_(1/10)(F + g_11/3) < 469/5000`. | Extend finite positive-penalty certificates to the vanishing-penalty family required by the closure criterion. |

The Bagchi audit distinguishes squarefree **constant membership** from
totality of the squarefree family. Comparable Pareto and Q weights preserve
closure membership, but the identity map is not an isometry.

The five-publication sparse power-cost program is complete and halted, as
recorded in [its durable state](RiemannResearch/RH/QSparsePowerCostIterationState.json).
Its finite composite-anchor gain does not establish an exponent below one or
the infinite annihilator implication. Separately authorized later work does
not restart that bounded program.

See the [theorem catalog](RiemannResearch/THEOREM_CATALOG.md) for declaration
names, assumptions, and the full research-obligation ledger.

## Mellin mixture and quantitative gap results

The compact-frequency and countable critical-line mixture obstructions are
formalized, including their analytic inputs. A further continuous Cauchy
frequency mixture has an exact coordinate identity: averaging the critical
modes with location `gamma` and positive scale `delta` gives the Mellin mode
at `s = 1/2 + delta + i*gamma`. Every coordinate integral converges absolutely,
and the resulting sequence has positive finite Pareto energy. The Cauchy
measure is atomless, gives every countable frequency set measure zero, and
has unbounded support. Its moments of order `0 <= alpha < 1` are finite,
but its first absolute moment is infinite. Thus this continuous construction
lies outside the earlier compact-frequency and pure-point hypotheses.

For `0 < delta < 1/2`, `cauchyMellinMixture_annihilates_iff` proves that
the mixture annihilates every normalized residue exactly when the shifted
parameter is an actual zeta zero. An actual zero
`s = beta + i*gamma`, with `1/2 < beta < 1`, also supplies an explicit positive
lower bound for the sharp first-coordinate tail gap:

```text
(2*beta-1) * 2^(2*beta-1) * |1-2^(-s)|^2 / |s|^2 <= firstCoordinateTailGap.
```

These are exact identities, energy estimates, and implications from a stated
zero. They do not establish the existence of an off-line zero or prove or
disprove RH. The classical implication from RH to density of the actual
residue span remains an explicit formalization dependency in the full
gap/RH equivalences. See `RiemannResearch/THEOREM_CATALOG.md` and
`RiemannResearch/RH/RHToDensityDependencyAudit20260921.md` for exact scope.

## Reproducibility

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin the
environment. Run `lake build RiemannResearch --quiet` from the repository
root to verify the project library and its transitive imports. Lake stores
compiled artifacts under `.lake`; subsequent builds traverse the dependency
graph but rebuild only stale modules and their affected dependents.

The Lean workspace service queues heavyweight validation and checkpoints.
Submissions return a job ID; clients wait for a terminal result. Dependency
artifacts are shared by the pinned environment key, while each clone has its
own writable project build directory. Native Lake artifacts use the shared
content-addressed remote cache. Resume retained workspaces to preserve their
source and build state. See [AGENTS.md](AGENTS.md) for the publication policy.

Queue responses include `retry_after_seconds`; polling sooner only wastes model
turns. Successful status responses omit verbose logs unless explicitly
requested. Bounded operational metrics are written to
`~/.local/state/lean-agent-workspaces/metrics.jsonl` without proof text or full
workspace tokens.

## Verification and publication

Publish through `agent_workspace_checkpoint` with push enabled. Lean source
or dependency changes require successful server audit and validation before
publication; any integrated source must also pass that gate. GitHub-hosted CI
is not the verification path. A queued job or successful isolated snippet is
not a completed project checkpoint.

Documentation-only checkpoints may skip Lean compilation and must be reported
as documentation changes. Preserve dirty trees and unpublished work; never
force-push, rebase, create merge commits, or discard work to publish an update.
