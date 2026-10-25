# Measure-change regularity: theorem catalog supplement

25 October 2026. Source: the user's ProjectionMeasureChangeResearch20261025.md.

## Established identities, implications, and obstructions

- RH/QScaledTailPerturbation.lean, namespace QAnnihilatorTailEscape:
  tail_sub, tail_sub_energy_exact, scaled_tail_transfer_sub.
- RH/QSquarefreeDisplacementRigidity.lean:
  witness_mem_orthogonal and witness_mean_energy retain the exact equality
  zeta(2)<1,u>=zeta(2)<r,B r>+||T d||^2 for u=B r_P-d.
  residual_eq_zero_iff_displacement_physically_bounded and
  residual_zero_iff_frequently_bounded_displacement_tail are equivalences.
  displacement_scaled_tail_tendsto describes the nonzero-residual branch.
- RH/QSquarefreeSmoothedProjection.lean:
  screened_mean_eq_energy, correction_bounded_iff_residual_zero,
  correction_scaled_tail_tendsto,
  residual_zero_iff_correction_frequently_bounded_scaled_tail.
  finiteCorrection_tendsto, movingCorrection_error_bound,
  movingCorrection_tendsto establish actual finite-stage convergence.
- RH/QSquarefreeReciprocalObstruction.lean:
  fourSiteFunctional_B_qResidue_two, B_qResidue_two_not_mem,
  B_not_preserves_closure prove the exact 1/8 multiplier obstruction.

All four modules use actual QHilbert vectors. Pareto projections use the same
physical squarefree closed span. No RH or target-membership premise is hidden
in these identities or equivalences.

## Conditional research reductions

- QSquarefreeDisplacementRigidity.riemannHypothesis_of_displacement_bounded.
  Open: a global physical bound for the actual Q/P projection displacement.
- QSquarefreeDisplacementRigidity.riemannHypothesis_of_frequently_bounded_displacement_tail.
  Open: one cofinal bound for the complete scaled Q tail of that displacement.
- QSquarefreeSmoothedProjection.riemannHypothesis_of_correction_bounded.
  Open: physical boundedness of P_V(B r).
- QSquarefreeSmoothedProjection.riemannHypothesis_of_frequently_finite_bound,
  riemannHypothesis_of_frequently_moving_bound, riemannHypothesis_of_uniform_moving_bound.
  Open: their displayed common coordinate bounds.
- QSquarefreeSmoothedProjection.riemannHypothesis_of_moving_head_bound.
  Open: C>=0 with |P_{V_N}B(1-F_N)(n)|<=C for all 1<=n<=N.

The concluding proposition is Mathlib's RiemannHypothesis, supplied by the
existing QSquarefreeCapacity bridge after target membership is established.
No theorem discharges the listed regularity obligations.

## Signed regularity continuation

- Analysis/ResidualizedProjectionKernel.lean: exact signed residualized pairing,
  Schur norm subtraction, squared Cauchy--Schwarz, complementary centered kernel.
- LinearAlgebra/FiniteHilbertNormalUniqueness.lean: finite normal solutions
  have unique synthesized vectors, including singular dictionaries.
- RH/QSquarefreeCorrectionKernel.lean: actual physical evaluation kernels,
  movingCorrection_eq_pairing, kernelEnergy_exact and centered-complement bounds.
- RH/QSquarefreeSignedNormal.lean: exists_signed_system, exists_kernel_system,
  correction_signed_scalar, error_signed, kernelEnergy_signed, signed_scalar_sq_le;
  exact metric Gram identities and forcing_rank_one_bound.
- RH/QSmoothedResidueAsymptotic.lean: exact conductor-scaled atom error and
  complete energy bound zeta(2)||d B g_d-(1-B1)||^2 <= 1/d;
  signed_forcing_sq_bound for every Q vector and positive conductor.
- RH/QShiftedReciprocalBounds.lean: centered quarter contraction, half multiplier
  bound, quarter projected correction bound, and the factor-eight displacement estimate.
- RH/QSquarefreeFiniteDisplacement.lean: matched squarefree Pareto stages,
  finiteDisplacement_tendsto, finite_resolvent, finiteDisplacement_energy_bound,
  finitePareto_residual_energy_bound; also the limiting displacement energy bound.

Additional conditional reductions (premises remain Open):
- QSquarefreeCorrectionKernel.riemannHypothesis_of_head_kernel_product_bound.
- QSquarefreeSignedNormal.riemannHypothesis_of_signed_normal_head_bound.
- QSquarefreeFiniteDisplacement.riemannHypothesis_of_finiteDisplacement_head_bound.

The new forcing expansion does not prove inverse-Gram regularity. The common
physical head bound and cofinal scaled-tail bound remain Open. See
RH/SignedRegularityDevelopment20261025.md for exact statements, numerical
diagnostics, verification boundary, and the narrowed arithmetic agenda.

## Signed forcing and lower-site localization continuation

Unconditional declarations (exact hypotheses remain visible in source):

- RH/QSquarefreeForcingDecomposition.lean: masked site-1 leadingCoordinate,
  leadingCoordinate_eq_evaluation, leading_response, signed_decomposition,
  remainder_eq_inner, inactive_remainder, exists_separated_systems,
  remainder_choice_independent, remainder_response_choice_independent,
  active_remainder_sq_bound, residual_forcing_uniform_little_o.
- RH/QSmoothedResidueAsymptotic.lean: atomError_sequence_abs_le_ratio,
  atomError_weighted_square_le; atomError_energy_le now has constant 1/d,
  signed_forcing_sq_bound has constant one. New inner_atomError_eq_tail and
  signed_forcing_tail_sq_bound use the complete residual tail.
  QSquarefreeSignedNormal.forcing_rank_one_bound is correspondingly strengthened.
- RH/QUniformTail.lean: tail_norm_le, tail_norm_le_sub_add,
  uniform_tail_tightness_of_tendsto, without a scaled-tail rate.
- Analysis/DiscreteTailHardy.lean: weighted_square_difference_sum,
  tail_recurrence_energy_le_four, truncatedTail, truncatedTail_energy_le_four,
  triangular_matrix_bessel, retaining exact finite endpoints.
- RH/QSmoothedResidueBessel.lean (namespace QSmoothedResidueAsymptotic):
  atomError_finite_bessel, signed_forcing_finite_bessel,
  atomError_pairing_square_summable, atomError_bessel. For every Q vector r,
  zeta(2)*sum_d |<r,E_(d+1)>|^2 <= 4*||r||^2, including the complete conductor sum.
- RH/QSquarefreeCorrectionKernel.lean: kernel_physical_symmetry,
  residualizedKernel_centered, kernelEnergy_centered_exact,
  movingCorrection_eq_centered_pairing, centeredKernel_physical,
  centeredKernel_diagonal_zero, kernelEnergy_centered_complement_exact.
- RH/QShiftedReciprocalTail.lean: centered_upperTail_energy_le.
- RH/QSquarefreeKernelLocalization.lean (namespace QSquarefreeCorrectionKernel):
  evaluation_norm_sq, kernel_norm_sq_le, centeredKernel_upperTail_energy_le,
  centeredKernel_upperTail_pairing_sq_le, movingCorrection_lowerHead_upperTail,
  movingCorrection_lowerHead_remainder_sq_le,
  kernelEnergy_lowerHead_upperTail_exact, kernelEnergy_le_lowerHead_add_zeta,
  lowerHead_response_uniform_error.

Open: a common bound for the actual signed finite lower-site response on
1<=n<=N, or the corresponding error-weighted kernel-energy provider retaining
its Schur subtraction. The complete upper-site response is uniformly negligible;
this does not bound the finite lower-site response. No unconditional RH theorem
was obtained. See RH/SignedRegularityLocalization20261025.md.

## Shrinking-head and complete forcing-tail continuation

Unconditional formal declarations:
- RH/QSmoothedResidueBessel.lean: inner_atomError_eq_cutoff_tail,
  atomError_block_bessel, atomError_selected_tail_bessel, atomError_tail_bessel,
  atomError_difference_bessel, forcing_blocks_uniformly_tight_of_tendsto,
  forcing_tails_uniformly_tight_of_tendsto.
- RH/QSquarefreeForcingDecomposition.lean:
  residual_forcing_tails_uniformly_tight, residual_forcing_blocks_uniformly_tight.
- RH/QShiftedReciprocalTail.lean: centered_tail_energy_le_of_interval,
  centered_relativeTail_energy_le, midpoint_tail_energy_le.
- RH/QSquarefreeKernelLocalization.lean: centeredKernel_relativeTail_energy_le,
  movingCorrection_head_tail, movingCorrection_relativeHead_remainder_sq_le,
  relativeHead_response_uniform_error, shrinkingHead_response_uniform_error,
  kernelEnergy_head_tail_exact, kernelEnergy_relativeHead_le.
- RH/QAdjacentConductorPacket.lean: packet_block, packet_block_abs,
  packet_block_abs_sum, packet_block_abs_sum_le, packet_abs_le,
  packet_weighted_block_le, packet_eq_residue_combination,
  packet_eq_zero_of_lt, packet_first_site.

Conditional research reduction:
- QSquarefreeCorrectionKernel.riemannHypothesis_of_lowerHead_bound.
  Open: its common signed lower-head bound.

The shrinking-head result applies to every sufficiently large evaluation site.
It does not bound the response inside the selected head. The complete forcing
tail is uniformly small, but Gram amplification is still uncontrolled.
An ordinary mathematical proof now rules out the uniform bare weighted
coefficient-response norm; its full infinite/asymptotic argument is not yet
Lean-formalized. Only the listed finite packet estimates are checked source.
See RH/ShrinkingHeadAndInverseResponse20261025.md for proofs and exact limits.

## Arithmetic screening of correction kernels

Unconditional declarations in RH/QSquarefreeKernelScreening.lean:
- fourSiteVector_norm_sq: the exact denominator is 30*zeta(2).
- residual_inner_fourSiteVector and residualized_inner_fourSiteVector.
- movingCorrection_sq_le_fourSite: an extra arithmetic square is subtracted.
- fourSiteScreenedKernel_norm_sq and fourSiteScreenedKernel_pairing:
  exact energy subtraction and preservation of the signed response.
- fourSiteEnergy_nonneg, fourSiteEnergy_le, fourSiteScore_physical.
- omittedVector_inner, omitted_stage, residual_inner_omitted,
  residualized_inner_omitted.
- exists_omitted_screening: actual finite-family normal solutions, exact energy,
  and coupled bound. Repeated indices are allowed; no inverse hypothesis.

Analysis/OrthogonalKernelScreening.lean supplies rankOne_norm_sq,
pairing_sq_le_rankOne, and pairing_sq_le_finite.

Conditional research reduction: riemannHypothesis_of_fourSiteEnergy_bound.
Open: a common C>=0 with error N * fourSiteEnergy N n <= C^2 for 1<=n<=N.
No uniform provider or unconditional RH theorem was obtained.
See RH/ArithmeticKernelScreening20261025.md and its diagnostic companion.

## Complete prime-square screening and effective truncation

Unconditional results in RH/QPrimeSquareKernelScreening.lean:
- Odd-prime-square radical rows annihilate the actual stage and residual;
  both their original supports and their B-images are pairwise orthogonal.
- primeSquareVector_norm_sq: zeta(2)*(2p^4-2p+2).
- finite_primeSquare_screening: exact finite norm subtraction and coupled bound.
- primeSquareGain_summable, completePrimeSquareEnergy_nonneg,
  completePrimeSquareEnergy_exact, movingCorrection_sq_le_completePrimeSquare:
  complete infinite screening with every Schur subtraction retained.
- primeSquareGain_complete_tail: complete gain above P is <=4*||k||^2/P^4.
- kernel_primeSquareGain_complete_tail: actual kernel bound <=4*zeta(2)*n^2/P^4.
- primeSquareGain_truncation, finite_complete_energy_gap,
  finite_complete_energy_gap_le_constant: an explicit finite prime cutoff
  differs from complete screening by <=4*zeta(2) when n^2<=P^4.

Analysis/OrthogonalKernelScreening.lean adds weighted finite/complete Bessel
bounds and exact orthogonal-family screening.

Open: a common bound on error N * completePrimeSquareEnergy N n, or on the
corresponding finite-cutoff energy, for every 1<=n<=N. The truncation estimate
does not discharge that obligation. No unconditional RH theorem was obtained.

RH/PrimeSquareScreeningAndRadicalPulses20261025.md records a separate
ordinary complete-tail proof for F_p-F_q and the resulting obstruction to
a generic sublinear evaluation bound on the local radical space W.
That pulse argument and its use of bounded prime gaps are not Lean-verified.

## Finite odd-pair constraint projection

Analysis/FinitePairBlockProjection.lean, namespace FinitePairBlockProjection:
- block_common_difference and block_mean_preserved establish the projected values.
- block_residual_norm, block_orthogonal, and block_pythagorean prove the exact
  weighted orthogonal minimizer for a finite common-difference block.
- block_sup_bound_of_ratios gives the physical bound (1+2A)M.
- inverseSquare_pair_identities and inverseSquare_block_sup_bound give the
  explicit physical bound (31/13)M for inverse-square adjacent-pair weights,
  uniformly in finite block size and in all real sites j>=3.

These are unconditional finite weighted-array results. The arithmetic embedding
and complete infinite odd-radical projection are ordinary arguments recorded in
RH/OddRadicalProjectionAndActualResponse20261025.md, not Lean formalizations.
That report gives R=I-P_U, ||R f||_infinity <= (31/13)||f||_infinity and
b_N=P_N(RBr_N), and explains why the latter does not bound b_N.

Open: stability of the actual stage projection on the specific bounded family
RBr_N; the original uniform signed-response and surviving-energy providers.
No unconditional RH theorem was obtained.

## Finite head boundary and solved tail response

- RH/QSquarefreeHeadBoundary.lean: headSynthesis_prefix and
  exists_stage_head_match_iff characterize actual stage heads by omitted
  Mobius coordinates plus one explicit charge. stage_head_injective gives
  uniqueness; residual_headCharge and movingCorrection_headCharge give the
  actual residual defect and zero correction defect.
- RH/QSquarefreeTailResponse.lean: tailStage, tailResponse, headResponse;
  response_split and response_pythagorean; headResponse_minimum_identity;
  tailResponse_pairing retains every signed term. tailResponse_norm_le and
  tailResponse_physical_bound bound the already projected legal zero-head
  response by ||tail_H r_N||/[2(H+2)] in norm and sqrt(zeta(2))*n times this
  bound physically. tailResponse_uniform_window gives uniform decay on
  n<=A(H+2), with stage N unrestricted.
  normalized_contrast_mem_tailStage and headResponse_normalized_moments_eq
  give the exact common normalized high-conductor normal moment.

## Weighted Bessel after head orthogonalization

- Analysis/TriangularWeightedBessel.lean: layered_bessel combines finite
  nonnegative support layers for orthogonal families of norm at most one.
- RH/QTriangularWeightedBessel.lean: reciprocal_layer_energy_le,
  reciprocal_onset_bessel, reciprocal_onset_tail_bessel prove exact-constant
  weighted bounds with physical weight (s_i+1)^2. The actual-stage
  movingCorrection_onset_bessel bounds coefficient energy by error N;
  movingCorrection_onset_tail_bessel bounds high-onset coefficient energy
  by the complete residual-tail norm squared.

All new estimates are unconditional for their stated structural data.
Open: uniform actual physical response, the minimum-norm head extension,
or a bound for the weighted physical reconstruction diagonal jointly with
error N. Basis construction and the physical diagonal Cauchy--Schwarz
corollary are ordinary mathematics in the report, not separately formalized.
The original B/KPS/KF providers and the infinite odd-radical construction
retain their previous statuses. RH is not proved.
See RH/HeadBoundaryTailResponseAndWeightedBessel20261025.md.
