# Boundary-observability handoff: Lean coverage

Source: user-provided
RH_Global_Approximation_and_Resonance_Blind_Patterns_Handoff_2026-09-16(1).md,
Sections 23–31 (with matched-filtration definitions from Sections 17–20).

This continuation adds verified results about the actual two-seed Pareto
generators and actual constant-target projection residuals. It does not
prove RH and does not claim that all analytic arguments in the source have
been formalized.

## Established declarations

Names in the RH rows have prefix
RiemannResearch.RH.Pareto.AdjacentPacket.

| Source | Declarations | File and exact scope |
|---|---|---|
| 23.1 | generator_gram_periodic, generator_gram_lcm, generator_gram_digamma | RH/TwoThreeChordGram.lean. Complete infinite-tail Gram entries reduced to finite positive-residue sums; actual digamma provider reused. All signed mixed terms retained. |
| 23.2 | chord_gram_exact | RH/TwoThreeChordGram.lean. Four-term signed chord kernel for the actual ternary generators. |
| 23.3–23.4 | residual_bilinear_schur, residual_cross_source | Analysis/FiniteHilbertGram.lean. Exact inverse-Gram bilinear screening and source corrections under actual linear independence; inverse constructed by the existing Gram equivalence. |
| 23.3–23.4 | screened_chord_gram, screened_chord_source | Analysis/ProjectionChordObservability.lean. Intrinsic orthogonal-projection form, retaining the signed correction. |
| 24 | chord_dilation, chord_norm_sq_dilation, unit_chord_log_bound, aligned_chord_log_bound | RH/TwoThreeChordGram.lean. Exact integer-dilation law and an unconditional logarithmic estimate for aligned dyadic chords, with a different explicit constant; not the full constant-160 theorem. |
| 24.2 | gain_ge_single_correlation | Analysis/ProjectionChordObservability.lean. Exact one-direction gain lower bound from a supplied positive upper bound on the actual chord energy. |
| 25 | innovation_source, innovation_energy | Analysis/ProjectionChordObservability.lean. Exact successive-source correction and nested-projection energy identity. The arbitrary-block LDL existence theorem remains to be formalized. |
| 26 | gain_ge_sourceSquare, gain_ge_charge, normalized_sourceSquare, matched_chord_gain | Analysis/ProjectionChordObservability.lean and RH/TwoThreeChordObservability.lean. Redundant finite-family gain consumer; actual source square, actual signed synthesis energy, and actual matched residual. |
| 26 | tendsto_zero_of_harmonic_loss | Analysis/ResidualHarmonicGain.lean. Nonnegative energy tends to zero under a positive harmonic relative-loss bound. Finite termination is included; strict positivity of every residual is unnecessary. |
| 27 | arithmeticCharge_summable, arithmeticCharge_tsum, correlation_arithmeticMoment, arithmeticMoment_summable, arithmeticMoment_head_zero | RH/TwoSeedAnnihilatorCharge.lean. Absolutely summable actual charges and exact binary/ternary moment formulas, including vanishing terms below the dilation cutoff. |
| 27 | limitingResidual_moments, limitingResidual_charge, positive_charge_pattern_of_not_rh, limitingResidual_mellin_lower_bound | RH/TwoSeedAnnihilatorCharge.lean. The actual closed-space residual satisfies every moment; failure of RH forces positive charge. A right-half-plane zeta zero supplies the original Mellin lower bound. |

The matched space is implemented using all binary generators through 3M
and all ternary generators through 2M. This is the redundant
full-generator presentation; membership, finite-dimensionality, monotonicity,
and both normal-equation families are proved. This implementation does not
assert the four-column rank count or construct the canonical block-LDL
factorization.

## Conditional research reductions

These are checked implications, not providers of their hypotheses.

- riemannHypothesis_of_moment_unique_continuation concludes Mathlib's
  RiemannHypothesis from the explicit assertion that every Hilbert vector
  satisfying all two-seed moments has zero total arithmetic charge.
  This moment unique-continuation assertion remains Open.
- riemannHypothesis_of_dyadic_chord_bessel_charge concludes Mathlib's
  RiemannHypothesis for actual normalized chord families in the matched
  filtration. Its two substantive hypotheses are a synthesis bound
  B*(j+1) at dyadic stage j and a uniform positive lower charge
  c*matchedEnergy(2^j). Both remain Open. The factor j+1 is the dyadic
  logarithm, with the constant log(2) absorbed into B.
- riemannHypothesis_of_matchedEnergy_convergence proves the actual
  projection-approximation-to-RH bridge for any sequence of matched budgets.
  It does not assume an external Nyman–Beurling criterion.

## Unfinished formalization versus open mathematics

RH/TwoThreeChordTargets.lean defines, but does not prove:

| Proposition | Status |
|---|---|
| CriticalLineChordGram | Formalization obligation for the informal Plancherel proof, Section 29.4. Its exact zeta-weighted integral and finite signed phases are typed. |
| FullChordEnergy160 | Formalization obligation for the arbitrary-interval constant-160 bound, Section 24.1. The aligned logarithmic version is already proved. |
| SameScaleChordBessel | Open mathematical estimate, Section 30.1, using actual normalized chord vectors. |
| BlockBoundaryObservability | Open mathematical estimate for the actual successive matched residual, Section 18. |

Further formalization work includes the arbitrary-block LDL construction and
its triangular fixed-to-sequential source transformation, the full
logarithmic Fourier/Plancherel bridge, and the strong-limit/l1 estimate
(27.1). These have not been silently promoted to checked theorems.

The source's logarithmic map should be called an isometric embedding into
L2(R), or unitary onto its image; no surjectivity onto all of L2(R) is used.
Also, failure of a particular quantitative block estimate need not yield a
nonzero limiting residual: the checked positive-charge counterpattern is
a consequence of failure of RH, not of failure of an arbitrary sufficient
bound.

## Explicit aligned-chord estimate

For positive integers L,k, the checked bound is

  ||g_(3,2L(k+1)) - g_(3,2Lk)||²
    <= L * (8 log(2k+1) + 8 ||digitHilbert(3,1)||² + 996).

Thus the dyadically aligned family has the required
O(L*(1+log(a/L))) scale. The proof uses exact dilation scaling and the
already verified adjacent-packet estimates. It supplies no off-diagonal
Bessel bound.

## Verification evidence and publication gate

The coherent combined proof candidate passed Lean with exit code 0.
Axiom inspection of the actual Gram/digamma formula, aligned logarithmic
bound, positive-charge obstruction, and conditional dyadic RH theorem
reported only propext, Classical.choice, and Quot.sound.
Domain-specific hypotheses are visible in the theorem types; axiom
inspection does not discharge them.

Saved modules are separately checked before publication. The final
checkpoint gates publication on source audit, changed-module validation,
and local reverse-dependency validation. No proof placeholders or
project-local axioms are introduced.
