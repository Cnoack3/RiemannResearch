# RH chat formalization audit — updated 9 September 2026

The discussion is **not completely proved in Lean**. The first two publications
provided 80 public theorems: 39 in `454a2ef` and 41 more in `b9491a3`.
This continuation adds **40 public theorems**. These counts exclude
definitions, instances, private helpers and additional research merged on
main during this work. The latter includes actual zeta-detector existence,
forward approximation-to-RH and exact CRT optimization providers reused here. This report replaces historical gap descriptions that are now
superseded.

Source: `RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md` and the associated
conversation. Claims which were proposals or mathematical research targets
remain explicitly distinguished from proved results. No unconditional RH
proof or converse for the restricted optimizer is asserted.

## Established in this continuation

| Part | Exact verified scope |
|---|---|
| Actual compact zeta detector | The newer main's CountableZetaDetector already establishes countability and constructs a nonzero smooth compact test annihilating centered-transform values at 0 and 1 and detecting every actual strip zeta zero. This continuation reuses that construction. One fixed choice is independent of the tail family and scale. This does not prove nonvanishing at every other point of the strip. |
| Fixed-test RH implication | Detector existence and detection are discharged. The resulting theorem concludes actual Mathlib RH from the four tail obligations listed below. |
| Quantitative zero-free consequence | A supplied energy bound `C exp(2θ log(M+1))`, with θ≥0, excludes zeros with `1/2+θ < Re(s) < 1`, provided the actual L², support and signature hypotheses hold. |
| Actual conductor inverse | Continuous operators on Lebesgue L², both inverse identities, a convergent operator-valued geometric series, norm bound `n/(sqrt(n)-1)` and bijectivity for n>1. These are genuine operators, not only reciprocal-symbol calculations. |
| Support counterexample | The compact indicator of `[0,log(n))` has an inverse equal to a nonzero constant almost everywhere on each successive left interval. For every real r, its inverse is nonzero on a positive-measure set below r. |
| Actual Pareto legal closure | Complete Pareto error equals the actual squared Hilbert distance. Every finite legal synthesis has a Hilbert realization. Arbitrarily small error, legal closure membership, and arbitrarily small variance/mean² are equivalent. |
| Variance approximation implies RH | For any positive seed set, arbitrarily small complete noise/signal ratios among finite legal syntheses imply actual Mathlib RH. No unproved RH bridge or convergence rate is assumed. The approximation property itself remains an explicit input. |
| Prime-pair packet formulation | The same closure condition is expressed with the sum of the two prime packet spans. All positive integer dilation parameters remain available; no approximating sequence is constructed. |
| Genuine centered Plancherel | The full spectral energy has exact normalization `1/(2π)` for every Schwartz function, with actual spectral integrability. The smooth-superexponential corollary uses a proved Schwartz conversion. No Plancherel or energy-identity premise is assumed. |

## Current claim ledger

| Claim from the conversation | Status |
|---|---|
| Reciprocal-floor Pareto law and pointwise fractional-part identity | Proved for the actual uniform law and positive conductors, including the zero-mass convention at K=0. |
| Complete finite Nyman error equals complete Pareto error | Proved, with all cross terms, the infinite Pareto sum and finiteness. |
| Residue mean log(n), packet mean Λ(q), prime-power/mixed distinction | Proved for the precise natural-conductor statements. |
| Ramanujan packet increments and Green identity | Proved for q>1; the unqualified increment formula needs that restriction. The exact finite boundary term and remaining infinite Pareto tail are retained. |
| Exact two/three head matching forces Möbius coefficients | Proved for the actual coefficient synthesis and stated matching constraints. Finite support and reciprocal-moment cancellation are proved. |
| Remote tail lower bound and subpower obstruction | Actual analytic lower-bound providers already exist. The general subpower and power-bound implications are proved with explicit L²/support/signature hypotheses. |
| A single test suffices to detect every possible actual off-line zero | Proved using the fixed smooth compact actual-zero detector. |
| The note's stronger explicit whole-strip detector | Still unformalized: its infinite-convolution construction and transform nonvanishing at every open-strip point are not the same statement as actual-zero detection. |
| Exact variance scaling and finite covariance optimization | Proved over the complete Pareto law. The finite block optimizer retains the explicit invertible Gram action and its coordinate identification. The newer main's ExactHeadCRT additionally constructs an inverse and attained minimum for bounded periodic exact-head controls with injective finite synthesis. Neither result provides a uniform asymptotic bound. |
| Concrete legal error/variance/closure equivalence | Proved in this continuation, without assuming that any of these approximation properties holds. Combined with the newer main's actual Mellin argument, the small-ratio property now implies RH. |
| Classical integer-dilation Nyman–Beurling equivalence with RH | Known mathematical theorem still requiring formalization here. Exact norm transfer alone does not establish it. The forward implication from positive-seed closure to actual RH is now proved in ThresholdRiemannHypothesis. The reverse implication, including the two-seed converse, remains open in this development. |
| Bounded conductor inverse and failure of support preservation | Proved in actual Lebesgue L². |
| Centered Fourier/Plancherel normalization | Proved for Schwartz and smooth-superexponential functions. The exact mixed-completion factorization and application to its particular tails remain separate formalization obligations. |
| Complete returned channels preserve the signed Weil obstruction | Existing source-confirmed modules include NymanFullReturnWeilNullity, NymanActualTailWeilAccounting, ActualArithmeticTailExistence and WeilSpectralPairing. Their full signed terms and analytic hypotheses remain in force. |
| Prime-square compensation and its limits | Existing source-confirmed modules NymanBroadPrimeSquareCompensation, NymanBroadSquareAsymptotic and NymanBroadPrimeAsymptotic. Compensation does not itself prove positivity for general tests. |
| CRT and the actual Pareto weights | Existing progression-weight, normalization, compatibility and regrouping results retain the actual nonuniform measure. Product coordinates do not justify independent uniform prime coordinates. |
| Binary numerical example | Exact complete-Pareto optimum 1−log(2) proved. Its rounded decimal is not an interval certificate. |
| Larger decimals 0.095748 and 0.078293, special-function evaluations | Not interval certified or fully identified by this formalization. The finite general optimization identities do not certify these numerical outputs. |
| Subpower growth or all-scale optimized variance/mean²→0 | Mathematically unproved research targets, not missing routine Lean syntax. No unconditional such theorem is added. |
| A converse from RH to growth of the restricted mixed optimizer | Not established in the discussion or in this development. |
| Research recommendations and judgments of difficulty | Commentary, not mathematical propositions certified by Lean. |

## Exact remaining RH hypotheses

`RH.FixedZetaDetectorCriterion.riemannHypothesis_of_fixed_zeta_detector_subpower_tail`
(the namespace is `RiemannResearch.RH`) uses the already established
`fixedZetaDetector`. It still requires:

1. Every supplied actual tail belongs to Lebesgue L².
2. Every tail vanishes for `y < a+log(M+1)`.
3. At every actual open-strip zeta zero, the tail's actual centered transform
   equals the negative transform of the fixed detector.
4. For every ε>0, its actual energy multiplied by
   `exp(-ε log(M+1))` tends to zero.

These hypotheses are not proved for the restricted mixed optimizer.
Existing canonical one-conductor providers do not identify that optimizer,
and the bounded inverse does not preserve the required support gap.

The full proposition
`RiemannResearch.RH.Pareto.ThresholdRiemannHypothesisBridgeTarget` in
`GibbsArithmeticResearchTargets.lean` still denotes the equivalence
`(hilbertOne ∈ hilbertLegalClosure {2, 3}) ↔ RiemannHypothesis`.
Its forward implication is now established without an assumed bridge by
`riemannHypothesis_of_twoSeed_closure`. The Gibbs RH consumers use that
proved implication. The reverse implication remains open. The new
`riemannHypothesis_of_legal_noiseSignalRatio` uses the proved forward
direction and retains only the actual approximation property as its
domain-specific hypothesis.

## Verification and publication evidence

Initial retained workspace: `ws_Gqnh98P7JuYG7ox5bTsQ6llwMk03gH-X`, base
`b9491a3c7ebea74ab75769637d17aa83c8ab7c19`.
Final integration workspace: `ws_AFW6t93oFOcI0c_fNehbCyM94nFVwVh0`, based on
`465e38f90ab625d03ccf16ddfad051630f92e2fa`.
Lean version checked this turn: 4.33.0-rc2.

Successful serialized checks, all `verified: true`, exit code 0:

- `job_-OEQcl4Uf3bqfWo4gDsmyjgsiAOs0Jwp`: fresh imports and representative
  axiom checks for the already published continuation.
- `job_OnMWad_e-pqsMqvPOtlELXTSIPHsMJ4b`: 28 new inverse, legal-closure,
  detector and quantitative-obstruction theorems (4.609 seconds).
- `job_la2Cm2T55EMUp8l9Ntz1g9w7Gu3Bjhzi`: the nine support theorems together
  with the actual inverse source (4.057 seconds).
- `job_yW_lhvobr_jyDJQ7mQ9GgJn-IXqXbbRT`: four centered Plancherel
  theorems (2.931 seconds).

- `job_reni1wNvaMch_B1lGwb_KypzKXdKzwxY`: integrated detector/criteria and
  legal-variance-to-RH bridge against newer main (6.700 seconds). Its four
  endpoint axiom reports again list only standard foundations.

Representative endpoint axiom reports list only `propext`,
`Classical.choice` and `Quot.sound`. No admitted proofs, project axioms or
unsafe proof shortcuts were introduced. Successful checks had no compiler
errors; some nonessential style/deprecation warnings remain.
The checkpoint containing this report is responsible for the final audit,
affected-module/dependency validation, commit and publication. These checks
are not an independent re-audit of every older project declaration.

The first publication attempt `job_tzjsIbUZAVtZcAjF63GKPmNlPy7uanuJ`
failed while cherry-picking into newer main because of a theorem-catalog
conflict, after creating retained local commit `ff02504`. No failed
publication is represented as a pushed commit. Recovery started from a clean
clone of the newer main; the old clone and unpublished commit were preserved.
The integrated version reuses the already published actual detector,
removes the duplicate existence/countability proofs, and adds the
variance-approximation-to-RH corollary using the newer proved provider.
Existing upstream modules and catalog additions are preserved.

All five new modules are exported by `RiemannResearch.lean`; the extended
`Analysis.SubpowerTailObstruction` was already exported.

## New inventory: this continuation's 40 public theorems

| Module | Count | Theorems |
|---|---:|---|
| `Analysis/CenteredTransformPlancherel` | 4 | `centeredTransform_critical_fourier`; `integrable_centeredTransform_critical_sq`; `centeredTransform_plancherel`; `centeredTransform_plancherel_of_smoothSuperexponential` |
| `Analysis/ConductorL2Inverse` | 17 | `translate_coe_ae`; `translate_zero`; `translate_mul`; `norm_translate_apply`; `norm_translate_le`; `contraction_powers_summable`; `inverse_mul_conductor`; `conductor_mul_inverse`; `inverse_hasSum`; `inverse_norm_bound`; `contraction_pow`; `inverse_hasSum_translations`; `natInverse_mul_natConductor`; `natConductor_mul_natInverse`; `natInverse_hasSum`; `natInverse_norm_bound`; `natConductor_bijective` |
| `Analysis/ConductorL2Support` | 9 | `box_coe_ae`; `restrict_coe_ae`; `inverse_box_restrict`; `inverse_box_value_ae`; `leftBlock_volume`; `inverse_box_nonzero_block_measure`; `inverse_box_not_bounded_below`; `box_zero_outside_ae`; `natInverse_box_not_bounded_below` |
| `Analysis/SubpowerTailObstruction` | 1 | `signature_eq_zero_of_supported_power_bound` |
| `RH/ParetoLegalApproximationClosure` | 6 | `hilbertOne_sub_norm_sq_eq_paretoError`; `legalSeedSpan_exists_hilbert`; `hilbertOne_mem_legalClosure_iff_paretoError`; `hilbertOne_mem_legalClosure_iff_noiseSignalRatio`; `hilbertOne_mem_prime_pair_closure_iff_packet_noiseSignalRatio`; `riemannHypothesis_of_legal_noiseSignalRatio` |
| `RH/FixedZetaDetectorCriterion` | 3 | `fixedZetaDetector_spec`; `riemannHypothesis_of_fixed_zeta_detector_subpower_tail`; `zeta_ne_zero_of_fixed_detector_power_energy_bound` |

## Historical inventory: previously published 41-theorem continuation

Publication `b9491a3` followed serialized verification and integration with
the newer main `126b563`. Its successful combined check was
`job_nExKbVWLTN-2hCeKRL3FgNdi9MNwbOyZ`; its successful publication checkpoint
was `job_JQEnkS2OC875HiPPfSme9wGErWIhblsu`. Earlier candidate-only status is
superseded. Current remaining gaps are given above.

| Module | Theorems | Exact scope |
|---|---:|---|
| RH/ConductorBoundedReciprocal | 6 | Actual conductor-symbol lower bound, positive gap, uniform reciprocal bound, and convergent exact geometric reciprocal series for n>1 and Re(s)<1. This module concerns the symbol; actual L² results are supplied by the later modules below. |
| RH/ParetoApproximationRatio | 3 | Complete Pareto error decomposition, exact mean normalization, and equivalence of arbitrarily small approximation error and noise/signal ratio in a scalar-closed bounded-function class. Neither approximation property is asserted to hold. |
| RH/ParetoFiniteSchur | 20 | Actual complete Pareto Gram optimizer, mean preservation, exact signed covariance remainder, Schur value, and joint coefficient/scale optimum. The Gram linear equivalence and its coordinate identification remain explicit hypotheses. |
| Analysis/CountableLaplaceDetector | 10 | Countable entire zero set, a real tilt avoiding it at a specified countable spectrum, actual normalized bump and transform shift, and existence of a smooth compact detector. |
| RH/CountableTiltDetector | 1 | A nonzero smooth compact test annihilating 0 and 1 and detecting every member of a specified countable set excluding 0 and 1. Does not claim a whole-strip zero-free transform. |
| RH/SingleZetaDetectorCriterion | 1 | Conditional actual RH criterion requiring detection only at actual strip zeta zeros; tail L², support, exact transform cancellation, and subpower growth remain explicit. |

## Historical inventory: original 39 theorems

Counts exclude definitions, instances, and private helper lemmas.

| Module | Public theorems | Declarations |
|---|---:|---|
| `Analysis/SubpowerTailObstruction` | 1 | `signature_eq_zero_of_supported_subpower_tail` |
| `RH/NymanInverseMobius` | 8 | `finite_divisor_sums_force_moebius`; `nymanConductorSynthesis_apply`; `nymanConductorSynthesis_eq_moebius_return`; `nymanTwoThreeSynthesis_forced_moebius_head`; `nymanConductorSynthesis_zero_above`; `nymanTwoThreeSynthesis_zero_above`; `nymanConductorSynthesis_reciprocal_sum`; `nymanTwoThreeSynthesis_reciprocal_sum` |
| `RH/ParetoBinaryApproximation` | 3 | `paretoError_scale_residue_two`; `paretoError_residue_two`; `paretoError_residue_two_minimizes` |
| `RH/ParetoNymanPointwise` | 2 | `fract_div_sub_fract_div_eq_floor_mod`; `pareto_nyman_pointwise` |
| `RH/ParetoPacketGreenGram` | 5 | `ramanujanPacket_increment`; `ramanujanPacket_prefix`; `ramanujanPacket_green_gram`; `ramanujanPacket_green_gram_with_tail`; `ramanujanSum_gcd_divisors` |
| `RH/ParetoResidueMean` | 5 | `residue_partial_sum_harmonic`; `paretoMean_residue`; `paretoMean_ramanujanPacket`; `paretoMean_ramanujanPacket_of_not_isPrimePow`; `paretoMean_ramanujanPacket_of_isPrimePow` |
| `RH/SingleTestTailCriterion` | 1 | `riemannHypothesis_of_single_subpower_tail_test` |
| `RH/ParetoUniformLaw` | 10 | `reciprocalFloor_measurable`; `uniformUnit_univ`; `reciprocalFloor_fiber`; `uniformUnit_reciprocalFloor_mass`; `reciprocalFloor_map_mass`; `reciprocalFloor_zero_fiber`; `reciprocalFloor_map_zero_mass`; `reciprocalFloor_map_mass_all`; `uniformUnit_lintegral_reciprocalFloor`; `uniformUnit_lintegral_square` |
| `RH/ParetoNymanNorm` | 3 | `nyman_finite_lintegral_error`; `nyman_finite_lintegral_error_le`; `nyman_finite_lintegral_error_lt_top` |
| `RH/RiemannHypothesisStrip` | 1 | `riemannHypothesis_iff_strip_zeros_on_line` |

All modules are exported by `RiemannResearch.lean`. Pareto theorem names
use namespace `RiemannResearch.RH.Pareto`; the analytic helper uses
`MeasureTheory.RemoteLaplaceTail`; the RH formulation and criterion use
`RiemannResearch.RH`. The extended Nyman declarations remain in their
existing module namespace.
