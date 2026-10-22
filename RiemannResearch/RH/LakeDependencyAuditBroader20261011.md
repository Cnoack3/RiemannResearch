# Lake dependency audit: broader cleanup — 2026-10-11

Baseline: `7ae3d0c13a9ad9fad3bc24f5ec0da8c31a4c5b0a`, the published second
dependency refactor. Scope: declaration placement and imports for Lake's existing
native remote cache. No mathematical or functional changes are intended.
No Bazel, Lake configuration, toolchain, package revision, cache policy, or
compiler option changes are included.

## Structural changes

The recurring problem was reusable definitions or general bounds living in the
same module as specialized applications. Consumers of those foundations then
depended on entire application proof chains. This pass separates six new
foundation modules and moves other declarations to appropriate existing owners.

| Reusable material | New module | Application consumers can avoid |
| --- | --- | --- |
| Conditional mean energy and elementary lemmas | `RH/ConditionalMeanEnergy` | RH bridge and head-obstruction assemblies |
| Reciprocal Möbius sum and scalar Cesàro identities | `NumberTheory/MobiusReciprocalSum` | Canonical Hilbert-space applications |
| PNT limit for the reciprocal Möbius sum | `NumberTheory/PrimeNumberTheorem/MobiusReciprocal` | Canonical Möbius energy application |
| Anchored evaluation and Möbius continuous linear maps | `RH/MobiusDifferenceCLM` | Balanced-coordinate dictionary |
| Critical-line point and its basic properties | `RH/MellinCriticalPoint` | Mellin frequency-kernel construction |
| Wide-strip digamma growth bound | `RH/WeilExplicitFormula/GammaFacts/DigammaGrowthWide` | Character explicit-formula proof |

General residue/packet bounds move from `ParetoSequenceCertificates` to
`ParetoResidueDuality`; bounded-error and summability lemmas move to
`ParetoDilation`. Conversely, the specialized finite-certificate theorem
`primePowerCombination_noiseSignal_floor` moves from `ParetoNoiseSignal` to
`ParetoSequenceCertificates`. General sequence analysis consequently avoids
the finite-certificate and primorial-obstruction applications.

The existing `riemannHypothesis_of_bounded_conditionalHeadMinimum` theorem
moves to `ConditionalMeanMinimumCriteria`, keeping the head-minimum foundation
independent of that RH criterion. `hilbertDilation_digit_one_sequence` moves
from `ArithmeticMellinIdentity` to `DilationWaveletAlgebra`, and
`fullSquaredNorm` moves from `CoupledCorrectionRHBridge` to
`ArithmeticCumulativeEnergy`.

Other import corrections use actual owning modules: completed-zeta facts
instead of ordinate-counting proofs, residue Mellin continuation instead of
the arithmetic identity assembly, and direct prime-packet/legal-Hilbert imports
only where used. `WeilExplicitFormula.Statement` drops its unused
`Hypotheses` import; `RvM.GammaSide` names that genuine dependency directly.
`HarmonicToeplitz` drops its unrelated Mellin asymptotics import and names the
Mathlib modules it uses. Consumers needing application theorems keep explicit
imports for those theorems.

## Preservation

Exactly **32 declarations move verbatim: 31 public declarations and one private
helper**. Their statement, hypotheses, attributes, and proof/definition text are
byte-identical. Public names and namespaces are preserved; Lean's generated
internal name for the private helper follows its new module. An existing
`#print axioms` command moves with its theorem unchanged.

The machine-readable audit records every moved block's source, destination,
declaration names, and SHA-256 hash. After accounting for these moves, all
remaining existing Lean code is unchanged under normalization of comments,
whitespace, and import lines. No proof is rewritten to make an import change
compile; no result is duplicated or replaced by a forwarding alias. The theorem
catalog records the new owners. No research obligation or theorem status changes.

## Measurements

Counts include project modules only, exclude each module itself, and exclude
Mathlib and other external packages. Transitive importer counts include the
aggregate. An importer count describes dependency scope, not an unconditional
number of rebuilt modules for every possible edit.

| Measure | Before | After |
| --- | ---: | ---: |
| Project modules, including aggregate | 2,504 | 2,510 |
| Direct project import edges | 6,960 | 7,015 |
| Ordered transitive dependency relationships | 121,024 | 102,993 |

This removes **18,031 transitive relationships (14.9%)**. **1,099 existing
modules have smaller dependency closures**. More direct imports explicitly
name the foundations previously obtained through unrelated applications.

| Module edited in a later change | Transitive importers before | After |
| --- | ---: | ---: |
| `RH/ParetoSequenceCertificates` | 909 | 1 |
| `RH/ParetoFiniteCertificates` | 911 | 13 |
| `RH/ParetoPrimorialObstruction` | 910 | 1 |
| `RH/BalancedContinuousCoordinates` | 530 | 14 |
| `RH/ArithmeticMellinIdentity` | 669 | 14 |
| `RH/WeilExplicitFormula/Hypotheses` | 1,045 | 275 |
| `RH/ConditionalMeanHeadObstruction` | 295 | 46 |

| Consumer | Transitive project dependencies before | After |
| --- | ---: | ---: |
| `RH/CompactFrequencyMellinRigidity` | 141 | 2 |
| `RH/MobiusReciprocalCutoff` | 108 | 9 |
| `RH/MobiusQuotientEnergy` | 108 | 35 |
| `RH/ConditionalMeanHeadMinimum` | 63 | 22 |
| `RH/MobiusHilbertCoordinates` | 38 | 24 |
| `Analysis/ActualZetaGoodLandauHorizontals` | 92 | 65 |
| `Analysis/CesaroPulseObstruction` | 66 | 22 |
| `RH/HarmonicToeplitz` | 144 | 0 |

Savings overlap: individual rows must not be added to estimate total savings.
The graph is acyclic, has no missing project imports, and the aggregate exports
all 2,509 children. Complete closure changes and preservation hashes are in
[the machine-readable audit](LakeDependencyAuditBroader20261011.json).

The [previous audit](LakeDependencyAuditFollowup20261011.md#why-these-splits-can-help)
documents the pinned Lake implementation: modules and imported artifact traces
are the relevant dependency units. These splits help because consumers now
avoid complete transitive paths to unrelated applications. They do not establish
a particular wall-clock speedup or remote-cache hit rate.

## Verification

Focused server job `job_c5k_5cn1-tH8-iJ3xkMHmwtQXwnIACUm` succeeded with
exit code 0 and `verified: true`. It imports all **76 changed or new child
modules** together. The snippet SHA-256 is
`665c152b7d597ac1e6e85414d4c3925c87c0142fb599838014bc5b1dbcdfaf29`.

It prints axioms for `riemannHypothesis_of_bounded_conditionalHeadMinimum`,
`primePowerCombination_noiseSignal_floor`, `digamma_growth_wide`, and
`mobiusReciprocalSum_tendsto_zero`. Each reports only `propext`,
`Classical.choice`, and `Quot.sound`. These checks do not discharge hypotheses
in the theorem statements. Existing style warnings remain.

Focused compilation and static preservation checks do not certify the entire
project. Publication is gated by the checkpoint's source audit and incremental
build of the aggregate plus all changed child modules, including validation of
any integrated upstream changes. The terminal checkpoint result, validation
scope, and published commit are reported with delivery. No cache-hit or timing
improvement is claimed without a controlled before/after workload.
