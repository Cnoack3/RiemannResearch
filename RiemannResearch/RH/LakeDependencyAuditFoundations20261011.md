# Lake dependency audit: stable foundations and wider cleanup — 2026-10-11

Baseline: `18e90ef30ba6d699a6033623d564a110e87fcf3f`, the published third
dependency refactor. This fourth pass changes imports and declaration placement
without mathematical or functional changes. It includes no Bazel, toolchain,
Lake configuration, package revision, compiler option, or cache-policy changes.

## What causes the remaining broad invalidation

A module can import only genuinely needed foundations and still be a poor
cache boundary if it mixes widely used definitions with specialized proofs.
For example, the arithmetic energy module supplied elementary sequence
definitions to 600 downstream modules. The geometric-mixture module supplied
the Pareto weight and its normalization to 1,119 downstream modules. Editing
an unrelated proof in either source file still changed a shared build input.

The new boundaries separate those stable primitives from the specialized
applications. An edit to a shared definition still correctly affects its
consumers. An edit confined to a separated application proof now reaches a
much smaller part of the project. This benefit can exist even when introducing
the foundation adds a node and increases the total number of import paths.

## Changes

Eight new modules own existing declarations:

| New module | Existing material extracted |
| --- | --- |
| `RH/ArithmeticCumulativeBasic` | 19 arithmetic primitives and cumulative-sum identities |
| `RH/ParetoWeights` | Weight, normalization, limiting and summability lemmas; two private helpers |
| `RH/ParetoHilbertPhysical` | Ten physical-coordinate definitions and identities |
| `RH/ResidueTailCertificate` | Certificate predicate and four elementary annihilator declarations |
| `Analysis/CesaroMeanEnergy` | Conditional weight, positivity, and bounded mean-energy summability |
| `Analysis/ActualZeroOrdinateSummability` | Reciprocal-ordinate summability theorem |
| `NumberTheory/PositiveDilationSum` | Positive-dilation finite-sum identity |
| `RH/WeilExplicitFormula/Tail/WindowCount` | `Zeta23.Tail.LocalCount.ofWindowCount` |

Five declarations also move into appropriate existing modules:

- `sum_mobiusDifference` goes to `ParetoResidueDuality`.
- `RiemannResearch.Probability.ConditionalIID.cesaro` goes to
  `Analysis/CesaroFiniteCalculus`, reversing an unnecessary probability import.
- `riemannHypothesis_of_bounded_exact_subspace_heads` goes to
  `BalancedExactHeadEnergy`; `ParetoExactHeadClosure` retains its three general
  closed-subspace results and avoids the RH application chain.
- `Zeta23.trivial_chain` goes to `Statement/SeamClosed`, keeping counting
  definitions out of general statement consumers.
- Root `deriv_ofReal` goes to `FromPNTPlus/Auxiliary`, allowing zeta bounds to
  avoid the Fourier/Sobolev application import.

The coordinated wider IWYU batch changes 35 modules: 14 consumers receive
narrower imports and 21 downstream consumers explicitly name needed owners.
Other corrections narrow gamma series, square-partition localization,
determinantal windows, and the Möbius bootstrap imports. Direct owning imports
are restored wherever a downstream consumer genuinely uses the removed branch.
No import is removed solely because its module name is absent from the proof.

## Source preservation

Exactly **55 existing declarations move verbatim: 53 public declarations and
two private helpers**. Statements, hypotheses, attributes, and proof/definition
text are byte-identical. Public names and namespaces remain unchanged; generated
private names follow their new module. The two private helpers are
`reciprocal_shift_tendsto` and `abs_le_square_add_one`.

After removing each exact moved block from the old and new locations, all
remaining existing Lean code matches under comment/whitespace normalization
with imports excluded. The checker explicitly accounts for added or removed
namespace/section frames for the Cesàro definition, dilation identity, and RH
criterion, and declaration-scoped `open Complex in` for `deriv_ofReal`. These
frames preserve the original declaration names and name resolution. The unused
`MeasureTheory` namespace opening is also removed from `ConditionalMeanEnergy`.

The machine-readable record includes block SHA-256 hashes and all source and
destination paths. There are no rewritten proofs, new hypotheses, forwarding
aliases, duplicate results, or changes to research-obligation status.

## Combined measurements

Counts concern project modules only, exclude each module itself and external
packages, and include the aggregate in reverse-importer counts. The complete
combined graph is measured after explicit downstream import repairs.

| Measure | Before | After |
| --- | ---: | ---: |
| Project modules including aggregate | 2,510 | 2,518 |
| Direct project import edges | 7,015 | 7,072 |
| Ordered transitive dependency relationships | 102,993 | 87,397 |

There are **15,596 fewer relationships (15.1%)**. **1,038 existing modules have
smaller closures**, while 63 have larger closures because of new foundations
or required direct owners. The graph remains acyclic, has no missing project
imports, and the aggregate exports all 2,517 child modules.

| File containing specialized proofs | Transitive importers before | After |
| --- | ---: | ---: |
| `RH/ParetoGeometricMixture` | 1,119 | 43 |
| `RH/ArithmeticCumulativeEnergy` | 600 | 39 |
| `RH/ParetoGibbsHilbert` | 555 | 14 |
| `RH/ExactHeadCharges` | 500 | 52 |
| `RH/FiniteSeedComponentCharge` | 520 | 40 |
| `RH/ResidueTailCertificateRegularity` | 266 | 15 |
| `RH/WeilExplicitFormula/Tail` | 202 | 34 |

| Consumer | Transitive project dependencies before | After |
| --- | ---: | ---: |
| `RH/ParetoExactHeadClosure` | 55 | 11 |
| `RH/ParetoTailCapacityDuality` | 73 | 49 |
| `RH/ConditionalMeanEnergy` | 21 | 9 |
| `Analysis/ActualZeroOrdinate` | 40 | 21 |
| `RH/WeilExplicitFormula/WeilEF/ZeroSummability` | 36 | 22 |
| `RH/WeilExplicitFormula/GammaFacts/Series` | 2 | 0 |

These figures overlap and must not be added. The arithmetic and Pareto-weight
splits are primarily improvements to the scope of application edits; their
value is not captured by total relationship reduction alone. Details are in
[the machine-readable audit](LakeDependencyAuditFoundations20261011.json).

## Cache implications and limits

The [earlier audit](LakeDependencyAuditFollowup20261011.md#why-these-splits-can-help)
records the pinned Lake implementation and its module/input-trace behavior.
Narrower paths preserve more reusable artifacts when an isolated application
file changes. They do not promise a uniform speedup for every edit or a cold
build. The refactor itself changes shared foundations and therefore requires
a substantial initial rebuild before those new artifacts can be reused.

The checked-in workspace implementation keys the shared dependency environment
from `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`; ordinary source,
documentation, and Bazel edits do not enter that environment key. This source
inspection is not a live cache-miss trace. Eviction, unavailable artifacts, and
transfer/startup costs require separate operational measurements.

No before/after timing or cache-hit benchmark is claimed. A useful benchmark
would apply the same harmless application-file edit on both revisions, measure
warm local rebuilds and restoration from the previous revision's remote cache,
and include an actual shared-foundation edit as a control.

## Verification

Static preservation checks passed, and the import graph has no cycles or
missing project modules. The declaration-use screen repaired actual downstream
dependencies. Its remaining 59 flagged rows are reviewed short-name collisions
with Mathlib declarations, not uses of removed Sobolev `CS`, `W1`, or `W21`
declarations. Compilation remains the authoritative check for elaboration,
tactics, instances, notation, and attributes.

The first focused check found an unused `MeasureTheory` opening in
`ConditionalMeanEnergy`, a missing direct Mathlib import for `Summable.norm` in
`NearbyDilationGram`, and a missing `ThresholdHilbertAdjoint` import for
`hilbertSequence_sub` in the new `ResidueTailCertificate`. These were corrected
without altering any proof or definition. A second check identified two more
required direct owners: `Mathlib.Algebra.BigOperators.Field` in `CRTGCDGram`
and `MellinFrequencyKernel` in `MellinProjectionKernel`; only imports changed.

The first full-project checkpoint, `job_zQ2gD0YDHWBiXrvfLnDtCDT4aTk9kEzX`,
found eight additional downstream missing dependencies and did not publish.
Five consumers needed `Mathlib.Algebra.BigOperators.Field` for `Finset.sum_div`:
`BoundedSeedConductorObstruction`, `ThresholdAffineBranches`,
`ThresholdConductor36DualLower`, `CoupledSeedComponentObstruction`, and
`ThresholdConductor360DualLower`. `MeanOneThirtyTrial` needed the existing
`moebius_six` simp lemma from `ParetoFiniteCertificates`; `DigammaAsymptotic`
needed `GammaFacts`; and `RamanujanLaguerreResearchTargets` needed the Mathlib
owners of real volume and `IntegrableOn`. All eight repairs add direct imports
without changing declarations or proofs.

Focused server job `job_OBChImCni9nz0X4OLxLRW1PRn95BSE8z` succeeded with
exit code 0, importing all 112 changed child modules together. Its code SHA-256
is `9cad35c664eb87948d24712155727922a4d7ed5ec034283f9a8809b337fc5d56`.
The five sampled axiom prints report only `propext`, `Classical.choice`, and
`Quot.sound`. This records kernel foundations, not the local hypotheses in
the theorem types. This focused check precedes the full-project publication
gate.

Publication requires the checkpoint's terminal successful source audit and
aggregate-plus-changed-modules build, including validation after any upstream
integration. The final checkpoint job, scope, and published commit are reported
with delivery. An accepted or running job does not establish verification.
