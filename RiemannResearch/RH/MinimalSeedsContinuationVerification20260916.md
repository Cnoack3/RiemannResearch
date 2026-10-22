# Minimal-seed continuation: Lean verification and remaining obligations

Source: [RH_Minimal_Seeds_Continuation_20260916.md](RH_Minimal_Seeds_Continuation_20260916.md), sections 10–14. The source is the user-requested continuation of the supplied 14 September note; it supports the statements and proof strategies, not a claim of mathematical priority.

The development uses the existing **actual** Pareto Hilbert space, the balanced one-generator-per-integer dictionary, and its continuous Möbius-cut coefficient maps. It does not replace those objects with an abstract model or assume the desired approximation theorem.

## Checked scope

Names below are relative to `RiemannResearch.RH.Pareto`, except for the general Gram results in `RiemannResearch.Analysis.FiniteHilbertGram`.

| Source result | Lean declarations and modules | Exact scope |
|---|---|---|
| Theorem 10.1: finite interpolation after all zero-target deletions | `balancedTargetHead_mem_nonzeroTargetSpan`, `balancedTargetHead_exact` in `BalancedHeadInterpolation.lean` | The literal packet with coefficients `scalarBalancedCoefficient m hilbertOne` is supported in the proposed minimal family and equals one at every positive coordinate through N. No norm bound is assumed or obtained. |
| Lemma 11.1: outward dilation coercivity | `commonDilation_coercivity` in `CommonDilationCoercivity.lean` | For every actual Hilbert vector f, real q, and integer A ≥ 2: A‖f‖²/(1+2√2)² ≤ ‖D_A f+qR_A‖². |
| Equation (11.6): signed fifth-charge lower bound | `fifthChargeObserver_sq_le` in `CommonScaleRepairObstruction.lean`; `commonScaleRoughPacket_norm_sq_lower` in `CommonScaleRoughPackets.lean` | The observer is literally f(5)−f(4)−f(1), its squared estimate uses 52, and the actual finite signed packet has lower bound 25Aq₅²/[52(1+2√2)²]. Arbitrary varying finite supports are allowed, subject to roughness. |
| Common-scale divergence mechanism | `commonScaleRoughPacket_norm_tendsto_atTop`, `commonScale_repaired_norm_tendsto_atTop` | Persistent nonzero fifth charge and outward scales force divergence; subtracting bounded original packets cannot repair it. The hypotheses are present in the exact theorem types. |
| Equations (11.8)–(11.12): forced charge from actual approximation | `fifthRoughComponentCharge_eq_four`, `fifthRoughComponentCharge_tendsto`, `commonScale_repaired_norm_tendsto_of_approximation` in `CommonScaleApproximationCharge.lean` | The charge is extracted from the four physical remainder coefficients at 5, 10, 15, 30, and its limit 1/15 is derived from Hilbert convergence. The repair theorem assumes the explicit exact identification of its fifth coefficient with that extracted charge; the limit is not assumed. |
| Section 12: rational-symbol and resonance algebra | `minimalSeedDampingSymbol_clear_denominator`, `minimalSeedDampingSymbol_undamped`, `minimalSeedDampingNumerator_at_resonance`, `minimalSeedPowerDampingResidue_ne_zero`, `minimalSeedPowerDampingResidue_norm_lower` in `MinimalSeedPowerDamping.lean` | Concrete algebra, the actual exponential phase of modulus one, and noncancellation of the candidate residue. The zeta/Mellin identification is not asserted by these results. |
| Section 12: actual pointwise damped sequence | `balancedPowerDampedSequence` in `BalancedPowerDamping.lean` | An actual finite arithmetic sum at each coordinate. `BalancedPowerDampingNonmembership` records the intended nonmembership statement as a proposition definition only. |
| Section 13: bounded exact heads yield closure membership | `hilbertOne_mem_closure_of_bounded_exact_heads`, `hilbertOne_mem_closure_of_bounded_exact_head_energy` in `ParetoExactHeadClosure.lean` | Actual coordinate tests are dense; bounded exact heads in any subspace force one into its closure. No compactness-provider hypothesis is used. |
| Theorem 13.1: unrestricted minimal-support energy criterion | `BalancedExactHeadEnergy.energy_bddAbove_iff_closure`, `energy_tendsto_one_of_bddAbove`, `energy_tendsto_atTop_of_not_closure`, `energy_limit_dichotomy` | The infimum is over all actual finite supported combinations with exact head, without a fixed budget. It is monotone; boundedness is equivalent to supported closure membership; the limit is one or positive infinity. |
| Equation (13.7): exact signed inverse-Gram minimum | `FiniteHilbertGram.gram_injective`, `gramEquiv`, `residual_completion`, `residual_minimizer_unique`, `additive_inverse_schur_value` | The full Gram inverse is constructed from linear independence. Completion of squares proves the minimum and its unique coefficient vector; no inverse-provider assumption remains. |
| Equations (13.7)–(13.8): actual balanced tail specialization | `BalancedFiniteTailGram.optimizedHead_norm_sq`, `optimizedHead_feasible`, `energy_le_schur_value` | Arbitrary finite allowed tail sets use actual balanced generators. The simultaneous optimum preserves every head constraint and bounds the unrestricted energy. |

## Conditional routes to RH

The following are **conditional research reductions** with conclusion equal to Mathlib's `RiemannHypothesis` proposition:

- `riemannHypothesis_of_bounded_exact_subspace_heads`: requires a uniformly bounded exact-head sequence in a subspace of the original legal span.
- `BalancedExactHeadEnergy.riemannHypothesis_of_energy_bddAbove`: requires `BddAbove (Set.range BalancedExactHeadEnergy.energy)`.
- `BalancedFiniteTailGram.riemannHypothesis_of_uniform_tail_gain`: requires a constant C and, for every N, an actual finite supported tail S with `‖balancedTargetHead N‖² - gain N S ≤ C`.

**Open:** no provider for any of these uniform bounds is supplied. The boundedness/closure equivalence identifies the obstacle; it does not discharge it. Nor is RH proved equivalent to the minimal-support criterion: the existing `BalancedSupportThinning` conjecture and the RH-to-full-density formalization obligation remain open.

## Analytic work not yet formalized

The full Theorem 12.1 is **not** checked in Lean. Its outstanding components are:

1. The infinite Mellin identity for `balancedPowerDampedSequence`, including absolute convergence on the initial half-plane.
2. Realization of the candidate residue as the residue of that actual Mellin expression, with the zeta and elementary factors accounted for.
3. Hilbert-membership holomorphy on the right half-plane and the analytic-continuation contradiction.
4. The strengthened nonmembership range under RH and Hilbert-norm absolute convergence for ε > 1/2.

`BalancedPowerDampingNonmembership` is a named **Open formalization obligation**, not an axiom, admitted theorem, or extra hypothesis silently assumed by another result. The algebraic noncancellation results do not by themselves establish it.

## Validation boundary

The proof candidates were checked with Lean against this repository's Mathlib environment, including explicit axiom reports for interpolation, coercivity, the 52 estimate, the Gram minimum, the energy dichotomy, the RH reductions, and candidate-residue noncancellation. The reported dependencies are only `propext`, `Classical.choice`, and `Quot.sound`. Such reports do not discharge theorem hypotheses; the open hypotheses above are recorded separately.

The publication checkpoint checks the actual module import graph and affected reverse dependents before committing. The changes introduce no `sorry`, `admit`, project-local axiom, or unsafe declaration. This development does not prove RH.
