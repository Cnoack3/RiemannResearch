# Lake dependency audit: follow-up — 2026-10-11

Baseline: `0e9d0f2e0e205dbbd1a558a3506deaf969587da9`, the published first
dependency refactor. Scope: imports and declaration placement for Lake's
existing native remote cache. No mathematical or functional change is intended.
No Bazel, Lake configuration, toolchain, package revision, cache policy, or
compiler option changes are included.

## Why these splits can help

Lake builds Lean modules, not independently cached individual declarations.
The pinned `v4.33.0-rc2`
[`Lake/Build/Module.lean`](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/lake/Lake/Build/Module.lean)
hashes source in `recFetchInput`, combines imported module/artifact traces in
`ModuleImportInfo.addImport`, and incorporates these and compiler/options/module
inputs in `recFetchPreSetup`. This agrees with the official
[Lake build and cache documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).

Splitting a file helps isolate later edits only when consumers can import a
smaller part and no other import path reintroduces the unrelated part. If all
consumers still import everything, the split does not provide that isolation
and adds module overhead. The splits below were selected by inspecting actual
consumers and checking complete transitive import paths, not file length.
Removing a real import path removes a corresponding build-trace dependency;
the exact recompilation and elapsed-time effect still depends on the edit and
the affected artifacts. Neither the graph analysis nor a successful build is
a warm-cache performance benchmark.

## Changes

The largest improvement is an unnecessary application import:
`ThresholdRiemannHypothesis` used `Zeta23.zeta_reflect_zero` but imported
`WeilSpectralPairing`. It now imports the owning
`WeilExplicitFormula/ZetaReflect` module. The two detector/tail criteria using
the same lemma receive the same correction. This one threshold import change
alone removed 67,473 transitive relationships in the baseline graph simulation.

Three new modules isolate reusable material from larger applications:

| Reusable material | New owner | Consumer that avoids the application |
| --- | --- | --- |
| Completed-zeta analyticity and zero/nonzero lemmas | `RH/WeilExplicitFormula/RvM/CompletedZeta` | `RH/RiemannHypothesisStrip` avoids `RvM/CountByIntegral` |
| Reflection of strip zeros | `RH/ZetaStripReflection` | `RH/RiemannHypothesisRightHalfStrip` avoids `RH/NymanAutocorrelationNullity` |
| Smooth superexponential decay and general closure lemmas | `Analysis/SmoothSuperexponentialDecay` | Correlation, translation, and zero-removal modules avoid `RH/NymanCompletionAdmissibility` |

The original application modules import their new foundations and retain their
application results. `PolynomialWeilCriterion` explicitly imports the reflection
lemma it previously obtained incidentally. `SmoothCompactCutoff` needs no
project import; its unnecessary Nyman application import is removed.

The dual-square definition and its nonnegativity lemma move from
`RH/ConditionalMeanRHBridge` into the existing
`Analysis/MellinCesaroSummability` module. `ConditionalMellinFunctional` can
then avoid the RH bridge. `WeightedComplexPairing` drops an unrelated
`RH/ArithmeticCumulativeEnergy` import and names its required Mathlib modules.
All three new modules are exported by the aggregate.

## Preservation

Exactly 16 existing declarations move verbatim. Namespaces, declaration names,
statements, hypotheses, attributes, and proof/definition bodies are unchanged:

- `Zeta23.RvM`: `analyticAt_completedRiemannZeta`,
  `completedRiemannZeta_eq_Gammaℝ_mul`,
  `completedRiemannZeta_eq_zero_iff_of_re_pos`,
  `completedRiemannZeta_ne_zero_of_one_le_re`,
  `completedRiemannZeta_ne_zero_of_re_nonpos`, and
  `completedRiemannZeta_eq_zero_iff`.
- `RiemannResearch.RH`: `riemannZeta_one_sub_eq_zero_of_strip`.
- `RiemannResearch.Analysis`: `SmoothSuperexponentialDecay`,
  `SuperexponentialDecay.sub`, `SuperexponentialDecay.const_smul`,
  `SmoothSuperexponentialDecay.decay`, `SmoothSuperexponentialDecay.deriv`,
  `SmoothSuperexponentialDecay.sub`, and `SmoothSuperexponentialDecay.const_smul`.
- `RiemannResearch.RH.Pareto`: `conditionalMellinDualSquare` and
  `conditionalMellinDualSquare_nonneg`.

The audit checks moved blocks byte-for-byte and records their SHA-256 hashes.
After accounting for moved blocks and their namespace frames, every remaining
existing Lean body is unchanged under comment/whitespace normalization with
import lines excluded. No proof is repaired or rewritten to make an import
change compile. No declaration is duplicated or supplied with a forwarding alias.
The catalog records the new owners. `AGENTS.md` gains three short dependency
rules covering IWYU (including tactics, notation, instances, and attributes),
separating foundations from applications, and measuring transitive paths.

## Measurements

Counts concern project modules only, excluding external packages and each
module itself. Transitive importer counts include the aggregate. Counts describe
potential dependency scope, not the number of rebuilds after every edit.

| Measure | Before | After |
| --- | ---: | ---: |
| Project modules, including aggregate | 2,501 | 2,504 |
| Direct project import edges | 6,952 | 6,960 |
| Ordered transitive dependency relationships | 195,008 | 121,024 |

There are **73,984 fewer transitive relationships (37.9%)**, and **725 existing
modules have smaller dependency closures**. The additional direct imports
explicitly name foundations that previously arrived through application modules;
direct import count alone would miss the improvement.

| Module edited in a later change | Transitive importers before | After |
| --- | ---: | ---: |
| `RH/WeilSpectralPairing` | 666 | 11 |
| `RH/WeilExplicitFormula/RvM/CountByIntegral` | 897 | 199 |
| `RH/NymanAutocorrelationNullity` | 700 | 20 |
| `RH/NymanCompletionAdmissibility` | 723 | 31 |

| Consumer | Transitive project dependencies before | After |
| --- | ---: | ---: |
| `RH/ThresholdRiemannHypothesis` | 153 | 38 |
| `RH/RiemannHypothesisStrip` | 12 | 5 |
| `RH/RiemannHypothesisRightHalfStrip` | 49 | 7 |
| `Analysis/SmoothCompactCutoff` | 12 | 0 |
| `Analysis/SmoothCorrelationClosure` | 14 | 4 |
| `Analysis/ConditionalMellinFunctional` | 180 | 25 |

These savings overlap; individual reverse-importer reductions must not be added
to estimate total savings. The smooth-decay split has a modest incremental
graph effect after the larger fixes, despite improving module ownership.
The graph remains acyclic and has no missing local imports. The aggregate
exports all 2,503 child modules. Detailed closure counts and preservation hashes
are in [the machine-readable audit](LakeDependencyAuditFollowup20261011.json).

## Verification

Focused server job `job_GzcbU4po_V86us9HvaJaah7y-aJVRHya` succeeded with exit
code 0 and `verified: true`, importing the initial 20 changed or new child modules.
The snippet SHA-256 is
`504bf44e9ee3c5ae3428fe0e1314e948edd27750749fe0b3992fed0ec0b9872f`.
It checks the smooth-decay class and prints axioms for the completed-zeta zero
equivalence, strip reflection, RH/strip equivalence, and dual-square
nonnegativity. Each reports only `propext`, `Classical.choice`, and `Quot.sound`.
These axiom checks do not discharge hypotheses in theorem statements.

The initial focused attempt exposed two missing Mathlib owning imports:
complex normed structure and zeta nonvanishing. Those imports were made
explicit; declaration bodies were unchanged. Style warnings remain.

The first full checkpoint, `job_FGFj2hnXAwgJBotFQJVUfSzx9wQ4898d`, correctly
blocked publication after finding two downstream consumers with missing direct
imports. `RH/ArgumentDoublingClosure` now explicitly imports Mathlib
`Analysis/Normed/Group/Tannery` for `tendsto_tsum_of_dominated_convergence`.
`Analysis/CompactCutoffConvergence` now explicitly imports
`Analysis/SmoothSuperexponentialDecay`. Neither proof body changes. Repair job
`job_8S4X1AhmW7-0ih6ObqyVJX402mXxwrR1` then verified both modules successfully
with exit code 0.

The next checkpoint, `job_aW4UwxEywmdZ27namQhBRWM6cy0dS6WX`, exposed one
further missing direct Mathlib import in `RH/HarmonicToeplitz`. Adding
`Mathlib.NumberTheory.Harmonic.Bounds` supplies `log_add_one_le_harmonic`
without changing its proof. Complete server diagnostics then reported success
with no errors. The final delta contains 23 changed or new child modules.

Focused verification and static preservation checks do not certify the full
project. Publication is gated by the checkpoint's source audit and incremental
build of the aggregate plus all changed child modules, including validation of
any integrated upstream changes. The terminal checkpoint result, validation
scope, and published commit are reported with delivery. No cache-hit rate or
elapsed-time improvement is claimed without a controlled before/after workload.
