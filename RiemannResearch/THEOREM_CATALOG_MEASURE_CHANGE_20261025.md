# Measure-change regularity: theorem catalog supplement

25 October 2026. Source: the user's ProjectionMeasureChangeResearch20261025.md.

## Exact arithmetic displacement energy (28 October 2026)

Unconditional results:

- RH/QShiftedReciprocalBounds.lean:
  displacement_energy_remainder_param is the exact one-parameter certificate.
  twice_B_inner_le_norm_sq and displacement_energy_remainder identify the
  nonnegative remainders at parameter four.
  strict_displacement_energy_bound shows that a nonzero residual makes the
  factor-eight inequality strict under the displayed orthogonality and normal
  equations.
- RH/QSquarefreeDisplacementEnergy.lean:
  B_inner_le_four_site_coordinates, fourSite_coordinates, and
  B_inner_le_four_site prove <f,Bf> <= (89/180)||f||^2 on the four-site kernel.
  residual_fourSite, displacement_fourSite, residual_displacement_orthogonal,
  and displacement_normal discharge all inputs for the actual limiting vectors.
  arithmetic_displacement_energy_exact retains the complete equality
  ||r||^2 = (65520/7921)||d||^2
    + (180/89)<r-(182/89)d,B(r-(182/89)d)>
    + ||r+(360/89)d||^2
    - (180/89)<r+(360/89)d,B(r+(360/89)d)>.
  arithmetic_displacement_energy_bound and arithmetic_displacement_energy_strict
  prove the improved coefficient 65520/7921 (strict when r is nonzero).

These results have no RH, target-membership, projection-agreement, or physical
regularity premise. They do not prove residual vanishing.
Open: the actual displacement's uniform/eventual polylogarithmic bound, or the
existing cofinal complete-tail regularity condition. Stronger global Hilbert
energy constants alone do not discharge those obligations.

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

## Logarithmic two-residual continuation (26 October 2026)

- RH/QSquarefreeLogDisplacement.lean: squarefree_annihilator_log_tail,
  displacement_log_scaled_tail_tendsto,
  residual_zero_iff_frequent_log_displacement_tail.
  These use the complete exact-head energy provider and prime-anchored
  squarefree legality, without a full-conductor annihilator assumption.
- RH/QScaledTailPerturbation.lean: weighted_tail_transfer_sub permits
  any eventually nonnegative weight and eventually bounded perturbation tails.
- Conditional research reduction:
  QSquarefreeLogDisplacement.riemannHypothesis_of_frequent_log_displacement_tail.
  Open: for some fixed k, bounded N/(6+log N)^k times the complete squared
  displacement tail along arbitrarily large N. No provider is supplied.
- Analysis/PolylogTailProfile.lean: logProfile_antitoneOn,
  logProfile_sqrt_le, log_pow_div_sq_le prove the analytic majorant.
- RH/QPolylogTailEnergy.lean: polylog_tail_energy_le gives the sharp
  complete-tail constant 2*C^2/zeta(2) for natural logarithmic exponents;
  eventually_polylog_scaled_tail_le handles an eventual physical envelope.
- RH/QSquarefreeLogDisplacement.lean:
  residual_zero_iff_eventually_polylog_displacement is an equivalence for
  each fixed natural exponent. Conditional research reductions
  riemannHypothesis_of_eventually_polylog_displacement and
  riemannHypothesis_of_eventually_real_polylog_displacement cover natural
  and arbitrary real exponents, respectively.
  Open: the eventual physical envelope for the actual displacement.
- TwoResidualLogRegularity20261026.md records the remaining paper
  stretched-exponential extension, the actual signed kernel localization
  (paper only), and reproducible Wolfram finite-stage/CRT computations.
  These computations do not discharge the open displacement envelope.

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
- RH/QSquarefreeDisplacementResolvent.lean:
  displacement_eq_projected_pResidual and displacement_fixed_point give the
  exact response equation d=b+Pi(Bd). displacement_centered_fixed_point,
  centeredFeedback_norm_le, resolvent_error_succ, and
  resolvent_error_norm_le give its centered finite Neumann resolvent with
  contraction factor 1/3 and geometric Q-Hilbert remainder. This does not
  supply physical weighted-supremum stability for Pi.
- RH/QSquarefreeResolventHeads.lean: resolvent_error_physical_le and
  resolvent_error_head_le give the physical evaluation error and simultaneous
  Nat.clog-depth head error. uniform_head_bound_iff_displacement_bounded and
  uniform_head_bound_iff_residual_zero show that this is equivalent to the
  existing regularity criterion. No arithmetic head-bound provider is proved.
  See RH/QSquarefreeResolventHeadsResearch20261028.md for the signed-kernel
  investigation, full infinite tails, and verification boundary.
- RH/QSquarefreeFiniteDisplacement.lean: matched squarefree Pareto stages,
  finiteDisplacement_tendsto, finite_resolvent, finiteDisplacement_energy_bound,
  finitePareto_residual_energy_bound; also the limiting displacement energy bound.

Additional conditional reductions (premises remain Open):
- QSquarefreeCorrectionKernel.riemannHypothesis_of_head_kernel_product_bound.
- QSquarefreeSignedNormal.riemannHypothesis_of_signed_normal_head_bound.
- QSquarefreeFiniteDisplacement.riemannHypothesis_of_finiteDisplacement_head_bound.
- QSquarefreeResolventHeads.riemannHypothesis_of_positive_head_bound.
  Open: for one fixed m, a common C>=0 bounds d_(Nat.clog 3 N + m)(n)
  for every positive physical site n<=N. The exact closed projection is
  still used at every finite recursion depth.

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

All estimates are unconditional for their stated structural data.
Open: uniform actual physical response, the minimum-norm head extension,
or a bound for the weighted physical reconstruction diagonal jointly with
error N. The following continuation formalizes basis construction and the
physical diagonal inequality. The original B/KPS/KF providers and infinite
odd-radical construction retain their previous statuses. RH is not proved.
See RH/HeadBoundaryTailResponseAndWeightedBessel20261025.md.

## Ordered basis, signed prediction, and residual-screened onset energy

- RH/QSquarefreeCorrectionKernel.lean: inner_kernel_of_stage.
- RH/QSquarefreeEvaluationBasis.lean: span_evaluationFamily, innovation_mem_stage,
  orderedVector_physical_zero and orderedVector_onset; orderedBasis after
  removing zero pivots; stage_synthesis and movingCorrection_physical_synthesis;
  movingCorrection_sq_le_diagonal. The actual complete Q stage is used.
- RH/QSquarefreeHeadPrediction.lean: headKernelSpace_eq, headResponse_eq_projection,
  exists_headResponse_prediction, prediction_normal, response_prediction,
  response_prediction_error_bound. Redundant and singular heads are permitted.
- RH/QSquarefreeResponseBasis.lean: headResponse_synthesis and tailResponse_synthesis
  identify the exact existing response split with low/high-onset basis expansions.
  orderedVector_eq_zero_of_nonsquarefree proves exact arithmetic pivot sparsity:
  every nonsquarefree physical pivot m>=2 is zero.
- Analysis/TriangularWeightedBessel.lean: layered_screened_bessel retains a
  nonnegative rank-one subtraction from every support layer.
- RH/QTriangularWeightedBessel.lean: residualLayerGain,
  reciprocal_onset_screened_bessel, movingCorrection_onset_screened_bessel.
- RH/QSquarefreeEvaluationBasis.lean: residualScreeningGain N M and
  movingCorrection_weighted_coefficients_screened for every M>=N+1;
  movingCorrection_sq_le_screened_diagonal proves
  |b_N(n)|^2 <= (error N - residualScreeningGain N M) * reconstructionDiagonal N n.

These are unconditional constructions and inequalities with only structural
index, support, and orthogonality hypotheses. R1 and R2 of the incoming handoff
are implemented. The uniform arithmetic provider remains Open: a common C
such that for every 1<=n<=N some M>=N+1 makes the displayed product <=C^2,
or a direct uniform signed minimum-norm head-response bound. No theorem of
unconditional type RiemannHypothesis has been obtained. The complete-gain
infinite sum and its truncation bound are ordinary arguments, not separately
formalized in this continuation. Numerical tables are not certificates.
See RH/OrderedBasisHeadPredictionResidualScreening20261025.md.

## Complete residual screening and exact pivot classification

- RH/QResidualScreeningSeries.lean: weightedResidualLayerGain_summable,
  completeResidualGain_eq_finite_add_tail, completeResidualGain_sub_finite_nonneg,
  completeResidualGain_sub_finite_le_tail. The complete omitted gain lies
  between zero and the full residual-tail norm squared.
- reciprocalLayerRemainder_eq_tsum retains the explicit complete coordinate
  remainder. residualLayerSlack_nonneg and residual_screening_full_identity
  retain coefficient energy, screening gain, every layer slack, and the remainder.
- RH/QSquarefreeEvaluationBasis.lean: stage_physical_synthesis;
  movingCorrection_screening_full_identity, movingCorrection_layerSlack_nonneg;
  completeScreeningGain and residualScreeningGain_tendsto;
  movingCorrection_weighted_coefficients_complete_screened and
  movingCorrection_sq_le_complete_screened_diagonal; exists_screening_cutoff
  realizes the complete product to arbitrary positive tolerance at a cutoff
  beyond any requested lower bound.
- RH/QSquarefreeHeadBoundary.lean: stage_eq_zero_of_head_zero sharpens the
  necessary prefix to N sites; stage_le_of_active_cutoff restricts stages to
  their largest active conductor.
- RH/QSquarefreeResponseBasis.lean: orderedVector_ne_zero_of_onset_witness,
  orderedVector_ne_zero_of_active_lt, orderedVector_first_ne_zero,
  orderedVector_zero_stage, orderedVector_eq_zero_of_active_cutoff,
  orderedVector_ne_zero_iff, exists_largest_active. The nonzero physical pivots
  are exactly the squarefree sites below the largest active conductor, including 1.

This completes the complete-gain/cutoff construction and exact pivot classification.
Open: the uniform actual screened product, the sharper actual-coefficient product,
or direct signed-response provider. RH is not proved. The exact arbitrary-data
prediction amplification and variance/strict-budget arguments in the research
report are ordinary proofs, not separately formalized Lean results.
See RH/CompleteResidualScreeningAndPivots20261025.md.

## Certified finite moving corrections and residual variance

- RH/QShiftedReciprocalBounds.lean: movingCorrection_variance_exact retains
  the arbitrary scalar shift and the complete nonnegative remainder;
  movingCorrection_variance_bound proves rho*||b_N||^2+e^2 <= rho*v,
  where rho=||r_N||^2, e=<r_N,B r_N>, and v=||B r_N||^2.
  These declarations have no RH or open arithmetic premise.
- RH/FiniteMovingCorrectionInvestigation20261025.md records exact-rational
  complete-tail finite-system certificates, singular-dictionary handling,
  reproducible numerical code, and a separate floating scan through N=255.
  The numerical certificates are not a Lean-verified implementation.

Open: a stage-independent physical-head bound. Total Hilbert-energy control,
finite certificates, and signed source asymptotics do not discharge this
obligation. No unconditional RH theorem is claimed.

## Squarefree logarithmic tail escape and arithmetic correction bounds

- Analysis/LogTailWeights.lean: comparable logarithmic weights and monotone
  polylogarithmic tail profiles, independent of Hilbert and RH hypotheses.
- RH/QPolylogTailEnergy.lean: exists_log_scaled_tail_bound_of_polylog converts
  a complete physical polylogarithmic envelope into a finite weighted-tail bound.
- RH/QScaledTailPerturbation.lean: reuses the upstream weighted_tail_transfer_sub
  with eventual nonnegativity and an eventually bounded perturbation.
- RH/QSquarefreeLogResidualTail.lean:
  squarefree_annihilator_log_scaled_tail_tendsto proves that every squarefree
  annihilator with nonzero mean escapes N/(6+log N)^k for every fixed k.
  squarefree_annihilator_eventual_stretched_tail_bound gives uniform arithmetic
  constants over the actual squarefree annihilator space. Prime anchors make
  the existing exact heads squarefree legal without assuming full-conductor
  orthogonality. correction_log_scaled_tail_tendsto transfers this to b.
  Frequent-tail equivalences characterize limitingResidual=0, and cofinal
  bounded-tail hypotheses imply RH via the existing squarefree capacity bridge.
  riemannHypothesis_of_polylog_moving_head_bound weakens the physical head
  target to C(6+log n)^m for one fixed finite m. Its zero-exponent specialization recovers the original criterion.
- RH/QSquarefreeReciprocalGap.lean: reciprocal_gap_exact retains the full
  spectral deficit and a finite sum of squares; parameter_two_coercive gives
  the constant 1/60 on the four-site kernel; movingCorrection_norm_le_squarefree
  gives ||b_N|| <= (59/240)||r_N||.
- RH/QParityReciprocalBounds.lean: B_centered_oneSixth_exact retains the full
  nonnegative tail. movingCorrection_actual_parity_energy_bound proves, for
  N>=1, 9*zeta(2)*||b_N||^2 <= (zeta(2)-1)*rho_N-(3*zeta(2)-4)*rho_N^2;
  correction_actual_parity_energy_bound supplies the limiting version.
  residual_first_sq_actual_parity_bound gives the refined first-coordinate bound.

The finite-stage head hypotheses are sufficient conditions; no converse from
RH to these envelopes is claimed. The original uniform bound and the weaker
polylogarithmic envelope remain Open. No unconditional RH theorem has been
obtained. Arbitrary-partition quadratic variation and the scalar 1/12 norm
corollary are ordinary arguments, not additional formalized theorems here.
See RH/SquarefreeLogTailRegularity20261026.md for proofs and verification status.

### Weaker cofinal head-energy and stretched-tail criteria

- Analysis/PointwiseEnergyDivergence.lean: fixed_prefix_le_of_frequently_head_bound
  and summable_of_frequently_head_bound transfer frequent bounds on growing
  nonnegative finite sums to summability of their pointwise limit.
- RH/QPolylogTailEnergy.lean: polylogWeightedEnergyTerm_eq gives the exact
  positive-site physical formula; the single-coordinate majorant is shared
  by the full-energy and finite-head envelope arguments.
- RH/QPolylogMovingHeadEnergy.lean: weightedHeadEnergy,
  polylog_head_envelope_implies_uniform_head_budget, and
  weightedEnergy_summable_of_frequently_moving_head_bound.
- RH/QSquarefreeMovingHeadEnergy.lean:
  residual_zero_of_frequently_moving_head_energy_bound and
  riemannHypothesis_of_frequently_moving_head_energy_bound require only a
  frequent finite budget of sum |b_N(n)|^2/[zeta(2)*n*(k+6+log n)^k] on any
  prescribed head H(N)->infinity. The old all-stage pointwise polylog bound
  implies this hypothesis with k=2m+2 and H(N)=N.
  moving_head_energy_tendsto_atTop_of_residual_ne_zero proves divergence for
  every divergent head schedule when the actual squarefree residual is nonzero.
- Analysis/StretchedTailWeights.lean and RH/QStretchedTailEnergy.lean: scalar
  decay/weight and the complete reciprocal-source tail limit.
- RH/QSquarefreeStretchedTailCriterion.lean: a fixed unconditional a>0 gives
  critical cofinal residual/correction tail criteria at
  W_a(N)=N*exp(-a*((6+log N)*log(6+log N))^(1/11)).
  exists_stretched_annihilator_tail_escape and
  exists_stretched_correction_tail_escape strengthen logarithmic divergence
  to one fixed stretched scale on the nonzero-mean/nonzero-residual branch.

The weighted head budget and critical-tail vanishing remain Open arithmetic
providers. These reductions do not claim RH=>squarefree residual vanishing.
Targeted import/axiom checks passed for the saved sources; publication is
controlled by the final server checkpoint. The explicit physical envelope
exp(A*(6+log n)^(1/11)) is justified in ordinary analysis in the report but is
not a separately formalized declaration here.


### Unconditional normalized moving-head growth

- Analysis/WeightedHeadEnergy.lean: normalized_weighted_head_tendsto_zero,
  normalized_weighted_head_le_tsum, and
  normalized_weighted_head_tendsto_zero_of_l1. These general finite-sum
  estimates use a nonnegative increasing divergent weight and l1 convergence
  of nonnegative energies; no weighted summability hypothesis is imposed.
- Analysis/LogTailWeights.lean: polylogTailProfile_tendsto_atTop.
- RH/QPolylogMovingHeadEnergy.lean:
  weightedHeadEnergy_div_profile_tendsto_zero applies to every norm-convergent
  sequence in the actual Q Hilbert space, via qSquareL1Dist_tendsto_zero.
- RH/QSquarefreeMovingHeadEnergy.lean:
  moving_head_energy_div_profile_tendsto_zero and
  moving_head_energy_isLittleO_profile prove, for every fixed k and every
  H(N)->infinity, E_{k,H}(N)=o(H(N)/(k+6+log H(N))^k) for the actual corrections.

The specialized theorem has only the structural cutoff-divergence hypothesis.
It assumes neither RH nor residual vanishing nor a finite weighted-energy
budget. The cofinal constant-budget provider sufficient for RH remains Open:
little-o relative to this divergent profile still permits unbounded energy.

### Uniform head growth and the bounded zero-head response

- Analysis/WeightedHeadEnergy.lean: normalized_weighted_head_le_l1_add and
  normalized_weighted_head_uniformly_small_of_l1.
- RH/QPolylogMovingHeadEnergy.lean: weightedHeadCross,
  weightedHeadEnergy_add_exact, weightedHeadEnergy_neg,
  weightedHeadEnergy_add_le, weightedHeadEnergy_le_profile_norm_sq,
  weightedHeadEnergy_div_profile_uniformly_small,
  weightedHeadEnergy_uniform_subprofile.
- RH/QSquarefreeMovingHeadEnergy.lean:
  moving_head_energy_uniform_subprofile makes the normalized estimate uniform
  over every actual squarefree stage, for each fixed natural exponent.
- RH/QSquarefreeResponseEnergy.lean:
  movingCorrection_weighted_energy_exact retains the weighted cross term;
  tailResponse_weighted_energy_le and tailResponse_weighted_energy_quadratic
  control the actual zero-head response's energy on quadratic windows;
  tailResponse_weighted_energy_le_quarter gives the numerical budget 1/4;
  tailResponse_weighted_energy_uniform_quadratic gives uniform vanishing.
  movingCorrection_weighted_energy_le_twice_head_add_half and
  headResponse_weighted_energy_le_twice_correction_add_half identify the
  remaining complementary-response obligation without assuming weighted
  orthogonality.

The bounded zero-head response is only one component of the actual correction.
The full cofinal constant-energy budget remains Open and no RH conclusion is
claimed. See RH/SquarefreeLogTailRegularity20261026.md for the exact distinction.

## Complete-Q CRT source estimates and infinite-modulus passage (2026-10-26)

Established, unconditional source results:

- RH/QResidueConditional.lean: conditionalValue_abs_le and the complete-fiber
  periodic-factor identities preserve signed data and use the full Q law.
- RH/QResidueConditionalBounds.lean: fiberSum_first_tail separates the first
  atom exactly; conditionalValue_deviation_tail_bound,
  conditionalValue_deviation_mass_bound, and conditionalValue_deviation_bound
  control the remaining complete progression by an O(L^(-2)) anchor bound.
- RH/QReciprocalConditioning.lean: reciprocalMean_defect_exact retains every
  signed tail summand; reciprocalMean_defect_bound gives the quantitative
  bias. conditionalReciprocal_energy_summable and
  conditionalReciprocal_energy_le give a complete k=2 source-energy budget.
  conditionalReciprocal_weighted_error_tendsto_zero proves convergence in
  that complete energy for arbitrary norm-bounded moving inputs and any
  positive moduli tending to infinity. No periodicity or input convergence
  hypothesis is required.
- RH/QSquarefreeCRTResponse.lean:
  conditionalReciprocal_residual_head_energy_le bounds every finite head
  uniformly over all stages and positive moduli.
  movingCorrection_eq_conditioned_projection identifies the actual correction
  with the legal projection of the conditioned source when every active
  conductor divides the modulus. conditionedRemainder_mem_orthogonal records
  ordinary Q orthogonality; conditioned_source_weighted_energy_exact retains
  the weighted cross term instead of setting it to zero.
  conditionalReciprocal_residual_weighted_error_tendsto_zero specializes the
  infinite-modulus result to any schedule of actual squarefree residuals.

Open: the cofinal constant-energy bound for the actual correction after
legal projection. The source budget and convergence do not establish weighted
stability of that projection. There is no unconditional RH conclusion.
See RH/CRTReciprocalConditioningResearch20261026.md for exact statements,
proofs, finite Wolfram diagnostics, literature boundaries, and verification.

## Raw positive moments: exact comparison and arithmetic boundary (2026-10-26)

Established comparisons and equivalences:

- RH/QHeadTailLayerEnergy.lean: positiveCrossVariation_sub_layer_quadratic,
  positiveCrossVariation_sub_layer_sq_le, positiveCrossVariation_le_layer_add_source,
  weightedEnergy_summable_iff_frequently_positiveCrossVariation_bounded,
  uniform_cappedTailEnergy_iff_positiveCrossVariation,
  cappedTailEnergy_le_profile_norm_sq.
  These retain the existing exact signed layer identity and endpoint tail.
- RH/QSquarefreeRawMomentCriterion.lean: raw_source_layer_le,
  raw_positiveCrossVariation_sub_layer_sq_le,
  raw_positive_variation_fixed_head_tendsto_zero,
  residual_zero_iff_fixed_head_frequently_positive_variation_bounded,
  raw_positive_tendsto_atTop_of_residual_ne_zero, raw_layer_bound_of_relative_gap.
  The exact equivalence has quantifiers exists C, forall H, frequently N.
  It characterizes zero squarefree residual; no RH-to-squarefree-density
  implication is assumed or newly proved.
- Analysis/CoupledProjectionWeightedObstruction.lean:
  projection_idempotent, projection_orthogonality, correction_exact,
  residual_energy_exact, correction_energy_exact, reciprocal_energy_le,
  source_energy_le, correction_coordinate_lower, correction_energy_lower,
  correction_energy_tendsto_atTop.
  This finite two-site model has uniformly bounded raw-source energy and
  divergent weighted correction energy. Its ranges are not squarefree stages;
  it obstructs only arguments based on abstract coupling plus smoothing.

Conditional research reductions in QSquarefreeRawMomentCriterion:

- residual_zero_of_frequently_raw_positive_bound and
  riemannHypothesis_of_frequently_raw_positive_bound.
  Open: one finite common raw positive-variation bound along a cofinal
  sequence of stages with expanding physical heads.
- riemannHypothesis_of_frequently_raw_relative_gap.
  Open: fixed theta < 1 and C with Phi-plus <= theta * cappedTailEnergy + C
  at cofinally many stages on expanding heads.

Neither open provider is supplied. The sharp squared comparison is
(Phi-plus - X)^2 <= e_N * X / 256, not an upper bound on X alone.
See RH/RawPositiveMomentResearch20261026.md for the full statements,
proofs, diagnostics, and continuation agenda. The single-atom smoothing and
parity-preserving infinite-dimensional example in
RH/OneAtomSmoothingAndParityObstruction20261026.md are explicitly paper-only.

## Probabilistic control: additive estimate and research criteria (2026-10-26)

Established unconditional deterministic results:

- Analysis/PolylogAbelBudget.lean: polylog_two_shifted_multiplier_le proves
  a(n)/(n+1) <= 1/64 for the k=2 profile.
- RH/QReciprocalWeightedEnergy.lean: layer_abs_tail_inner_B_le,
  positiveCrossVariation_sub_layer_B_product_le, and
  positiveCrossVariation_sub_layer_B_le bound the absolute layer discrepancy
  by the complete absolute mixed product, then by ||b||^2/32 + ||r||^2/512.
  The previously established full signed identity remains in force.
- RH/QSquarefreeRawMomentCriterion.lean:
  raw_positiveCrossVariation_sub_layer_abs_le proves
  |Phi-plus - X| <= e_N/256 for every actual stage and physical head.
  raw_layer_bound_of_relative_gap is strengthened to
  X <= (C + e_N/256)/(1-theta), for theta < 1.
  Its conditional RH consumer now uses (C+1/256)/(1-theta).

The strict-gap provider remains Open. The additive estimate bounds the
discrepancy, not either energy separately, and does not prove RH.

RH/ProbabilisticRawMomentResearch20261026.md contains explicitly paper-only
probability arguments: a fixed-Q nonnegative expectation approximating Phi
within e_N/1024; one-sided uniform integrability; a three-series equivalence
to zero residual; fourth-moment and Berry--Esseen retained-mass criteria;
and a countable Efron--Stein prime-resampling sufficient condition.
Open: the common retained-mass bound, the weighted negative-part expectation
bound, or the cofinal prime-resampling influence budget. No provider is
asserted, no independence of the arithmetic moments is assumed, and no
RH-to-squarefree-density implication is claimed.

## Prime-resampling source control and the projection obstruction (2026-10-27)

Established deterministic results:

- Analysis/ReversibleJumpEnergy.lean: finiteJumpEnergy_eq_rate_square_sub_cross
  retains the exact signed cross term; finiteJumpEnergy_offDiagonal,
  finiteJumpEnergy_le_twice_total_rate, finiteJumpEnergy_le_twice_exit_rate,
  finiteJumpEnergy_le_of_exit_rate_le, and geometric_resampling_exit_le
  provide finite reversible algebra and a geometric-coordinate rate bound.
- Analysis/PolylogAbelBudget.lean:
  polylog_two_rate_reciprocal_multiplier_le and
  polylog_two_log_reciprocal_multiplier_le.
- RH/QReciprocalWeightedEnergy.lean: reciprocal_rateWeightedEnergyTerm_le,
  reciprocal_rateWeightedEnergy_summable, reciprocal_rateWeightedEnergy_le,
  and finiteRawSourceJumpEnergy_le. A nonnegative rate at most n+1 costs
  at most ||f||^2/64 before the reversible factor 2; the finite jump energy
  of sqrt(a) Bf is at most ||f||^2/32 under its explicit row-rate hypothesis.
- RH/QParityProjectionDefect.lean:
  parity_projection_residual_centered_norm_sq gives exact variance 3 e^2.
  parity_projection_residual_mean_independent_iff shows that mean-independence
  from parity already requires constant membership in a space containing g_2.

## Actual countable prime kernel and sharp Poincare (2026-10-27)

Established in the actual Q space:
- PrimeResamplingCore, PrimeResamplingGeometric, PrimeResamplingExitBound,
  PrimeResamplingKernel, PrimeResamplingTransition: exact exponent replacement,
  geometric normalization, detailed balance and Q stationarity; complete
  symmetric flow with row bound Q(n)(n+1).
- QPrimeResampling, QPrimeResamplingFormula, QPrimeResamplingCommutation,
  QPrimeInvariantIntersection: actual orthogonal averaging projections, full
  geometric formula, commutation, and joint fixed space exactly the constants.
- Analysis/CommutingProjectionEnergy, DecreasingProjectionLimit,
  CountableProjectionPoincare and InvariantProjectionCommutation supply the
  generic countable Hilbert argument without an unproved product-limit premise.
- Analysis/CountableJumpEnergy and ReversibleCountableEnergyIdentity supply
  extended nonnegative complete forms and exact signed identities with proved
  summability. QPrimeJumpEnergyIdentity identifies actual full kernel energy
  with the full sum of squared projection defects.
- QPairVariance, Analysis/CountablePairVariance, ClippedEnergyExtension and
  QPrimeResamplingPoincare: prime_resampling_poincare holds for every real
  sequence, with no L1 or L2 assumption. QPrimeDirichletSharpness proves
  optimality through a positive finite equality witness.
- Analysis/AnchoredPairEnergy and QCountablePairEnergy: finite pair energy
  forces square integrability using the positive atom at one.
- QCountableJumpEnergy and QPrimeRawSourceEnergy:
  rawSourceDirichletEnergy_le gives D(sqrt(a) Bf) <= ||f||^2/32 unconditionally.
- QSquarefreePrimeDirichletCriterion:
  correctionDirichletEnergy_ne_top_iff_residual_zero and
  correctionDirichletEnergy_eq_zero_iff_residual_zero prove the actual
  weighted limiting correction's zero-or-infinity dichotomy.
- Analysis/CountableJumpEnergyLimit and QSquarefreePrimeFiniteGrid:
  residual_zero_iff_frequently_finiteGrid_bound permits different arbitrarily
  late good stages for each fixed grid. Nonzero residual forces divergence
  for every physical-head schedule tending to infinity.
- QPrimeResamplingParity: actual C_2 g_2 = 3/8, exact signed commutator and
  noncommutation with the dyadic legal space.
- QLegalMixedConductorJumpObstruction: actual complete prime energy divergence
  and no_uniform_prime_dirichlet_transfer for the legal mixed-conductor
  family, whose raw energy <=1/128 and residual norm <=1/2.

Conditional research reductions:
- riemannHypothesis_of_correctionDirichletEnergy_ne_top.
- riemannHypothesis_of_frequently_finiteGrid_bound.

Open: finite actual limiting correction energy, or one common finite bound
on the canonical moving-correction grids at cofinally many stages per grid.
The legal-family obstruction does not refute a special estimate for canonical
nested stages. The near-pole covariance provider and mixture argument remain
paper derivations. No unconditional RH theorem or RH-to-squarefree-density
converse is asserted. See RH/PrimeResamplingFormalization20261027.md.
