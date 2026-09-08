# Theorem catalog

This catalog is the orientation layer for the RH-focused `main` branch. Lean source files
and successful builds remain authoritative. The complete Serre II development as it
stood on 4 September 2026 is preserved on
[`serre-ii-archive-20260904`](https://github.com/Cnoack3/RiemannResearch/tree/serre-ii-archive-20260904).

## Status conventions

- **Kernel checked** means Lean has verified a proof of the declaration's exact
  type.
- **Established local declaration** means the result is not currently serving
  as a stand-in for an unfinished named research theorem. It may still have the
  ordinary hypotheses appropriate to a general reusable lemma.
- **Conditional research reduction** means Lean has checked the implication,
  but domain-specific inputs needed for the motivating theorem remain
  unresolved.
- **Open obligation** means no project declaration currently supplies that
  input. Local hypotheses do not appear in `#print axioms`, so a clean axiom
  report alone does not make a result unconditional.

## Two-seed threshold paper: partial formalization (8 September 2026)

Kernel-checked support results below do not prove the paper's main RH equivalences. The September 8, 32-page edition has 195 source labels. See `RH/ThresholdPaperCoverage.md` for the historical 151-label audit and `RH/ThresholdAffineCoverage.md` for the 22-module extension, all 44 new Section 11 labels, exact hypotheses, and open obligations. Names have the common prefix `RiemannResearch` unless an ordinary algebraic namespace is shown.

| Declaration family | Module | Exact scope |
|---|---|---|
| `CoarseLift.coarse_lift_energy_lower_bound` | `Analysis.CoarseLiftObstruction` | Exact signed Hilbert coarse-lift obstruction; symmetric map and annihilator explicit |
| `WeightedFiniteProjection.fiber_pairwise_variance`, `fiber_defect_eq_zero_iff`, `optimal_partial_correction` | `LinearAlgebra.WeightedFiniteProjection` | Actual finite weighted error, defect nullspace and scalar repair; mass/positivity hypotheses explicit |
| `Pareto.progressionWeight_certificate_bounds`, `progressionWeight_partial_split` | `RH.ParetoProgressionTails` | Actual infinite progression masses, exact heads and certified tails |
| `Pareto.progressionWeight_normalization`, `progressionWeight_compatibility`, `periodic_paretoInner_mixed` | `RH.ParetoPeriodicRegrouping` | Positive compatible weighted finite quotients and exact periodic mixed norms |
| `Pareto.legalSeedSpan_dilation`, `power_seed_mem_legalSeedSpan`, `paretoMean_rawPullback` | `RH.ThresholdDilationAlgebra` | Every positive integer dilation, legal span and boundary pushforward |
| `Pareto.weighted_square_dilation`, `paretoMean_dilation_of_square`, `paretoInner_dilation_boundary_of_square` | `RH.ThresholdDilationEnergy` | Arbitrary real weighted square-summable input; exact norms, means, mixed laws and anchor anomaly |
| `TwoSeedThreshold.legalWitness36_full_error_lt`, `legalWitness36_mem_legalSeedSpan` | `RH.ThresholdFiniteCertificate`, `RH.ThresholdInfiniteCertificate` | Genuine legal period-36 full squared error <53/1000; no unresolved analytic or RH premise |
| `TwoSeedThreshold.period36Basis_linearIndependent`, `period36_omitted_3_2`, `period36_omitted_3_4`, `period36_omitted_3_6`, `period36_omitted_3_12` | `RH.ThresholdPeriod36Basis` | Exact independence of eight functions and four omitted-generator identities; not coarse-6 rank |
| `Pareto.hilbertSequence_range`, `hilbert_norm_weighted_sq`, `hilbertDilation_comp`, `hilbertDilationAdjoint_one` | `RH.ThresholdHilbertSpace`, `ThresholdHilbertDilation`, `ThresholdHilbertMean` | Actual complete real weighted H, all-positive-integer bounded dilations/isometries, exact inner product, mean and adjoint-fixed unit target; joint rigidity remains open |
| `Pareto.hilbertLegalClosure_dilation`, `hilbertLegalClosure_power_list` | `RH.ThresholdHilbertLegal` | Actual legal closures in H, all-integer invariance and common-base finite-list classification |
| `Pareto.legalSeedSpan_list_gcd_one`, `legalSeedSpan_prime_eq_packetSpan`, `legalSeedSpan_error_summable` | `RH.ThresholdSeedEuclidean`, `ThresholdPrimePackets`, `ThresholdLegalIntegrability` | Actual algebraic synthesis and prime-packet identification; full finite-legal error is summable; no density/RH conclusion |
| `TwoSeedThreshold.phaseDelta_le_twelfth_weight`, `phaseDelta_lower_correction`, `universalPhaseConstant_certificate` | `RH.ThresholdPhaseConstant`, `ThresholdPhaseSharpBound`, `ThresholdPhaseLowerBound`, `ThresholdPhaseTail` | Actual logarithmic phase constant, two-sided tails with cubic correction 1/[144(N+1)^3], and exact rational enclosure; arithmetic witness identification remains open |
| `Analysis.PhaseWitness.error_eq_floor_add_excess`, `error_eq_floor_iff` | `Analysis.PhaseWitnessGeometry` | Conditional research reduction: arithmetic witness, its moments and legal annihilation are explicit open inputs |
| `WeightedFiniteQuotient.averageMatrix_apply`, `average_tower`, `error_decomposition`, `defect_finrank` | `LinearAlgebra.WeightedFiniteQuotient`, `WeightedQuotientDefectRank` | Actual weighted finite matrices, full projection defect and ambient complementary rank; nonzero masses explicit |
| `Pareto.refinementAverage_formula`, `refinement_error_decomposition`, `progressionWeight_refinement_tower` | `RH.ThresholdWeightedCRT` | Concrete specialization to genuine infinite progression weights for every positive integer refinement factor |
| `Pareto.affineBranch_positive_partition`, `affineBranchCoefficient_uniform_defect`, `affineProjection_block_discrepancy` | `RH.ThresholdAffineBranches`, `ThresholdAffineProjectionBlocks` | Actual arithmetic head, normalized weighted branch coefficients and finite projection blocks; infinite operator and HS assembly remain open |
| `Ring.compression_product_defect`, `hom_difference_cocycle`; `StarRing.compression_square_defect_finite_gram`; `Real.unit_rankOne_difference_sum_sq` | `LinearAlgebra.CompressionProductDefect`, `RankOneProjectionDistance` | Exact ordered operator algebra and complete finite mixed Gram/rank-one identities |
| `LinearAlgebra.SpectralCutoff.diagonal_half_cutoff`, `certified_half_cutoff_bounds`, `repeatedError_nondecreasing` | `LinearAlgebra.SpectralCutoffRepair`, `SpectralRepeatedFit`, `SpectralDiagonalRealization` | Explicit finite diagonal synthesis, factor-two bounds and repeated-fit full-error growth; actual weighted legal covariance realization remains open |

## Adjoint operators and quantitative affine phase limit (8 September 2026)

These 64 additional public declarations are established support results, not a proof of RH. All scales are actual positive integers. See `RH/ThresholdAdjointPhaseProgress.md` for exact definitions, verification receipts, and remaining bridges.

| Declaration family | Module | Exact scope |
|---|---|---|
| `Pareto.hilbertDilationAdjoint_coordinate`, `hilbert_coordinate_recovery`, `hilbertDilationAdjoint_all_fixed_iff`, `hilbert_coordinate_defect_bound` | `RH.ThresholdHilbertAdjoint` | Actual finite weighted-block adjoint formula on every real H vector; signed coordinate recovery and stability; constants are precisely the fixed vectors for ALL integer adjoints. Two-selected-seed rigidity and legal annihilator identification remain open. |
| `Pareto.hilbertDilationAdjoint_dilation`, `hilbertBlockProjection_coordinate`, `hilbertBlockProjection_pythagoras`, `hilbertBlockProjection_best_approximation` | `RH.ThresholdHilbertProjection` | Actual bounded projection `P_m=(1/m)T_m T_m*`, symmetry, idempotence, full energy/least-squares equalities, zero exceptional head and genuine weighted block means; not a finite legal projection. |
| `Pareto.affineProjectionEnergyTail_le`, `affineColumnEnergy_le_quarter_successor_sq` | `RH.ThresholdAffineTailBounds` | Actual complete squared-entry tail at most `1/[6(N+1)]` uniformly in m, and actual squared-column discrepancy at most `1/[4(j+1)^2]`; infinite comparison operator assembly is separate. |
| `Pareto.affineProjection_phase_gap_rate`, `affineProjectionEnergyTotal_tendsto`, `affineProjectionEnergyTotal_positive_floor` | `RH.ThresholdAffinePhaseLimit` | Actual numerical discrepancy satisfies `0 <= 2s-E_m <= 2/(3m^2)`, tends to `2s`, and is at least `17/216` for m>=3. No RH or unproved analytic input. Identifying this series with the infinite operator HS norm remains open. |

## Established RH and support declarations

| Declaration | Module | Statement / purpose | Status |
|---|---|---|---|
| `RiemannResearch.RH.Pareto.geometricProbability_integral`, `geometricProbability_product_integral`, `paretoWeight_hasSum`, `geometricKernel_hasSum` | `RiemannResearch.RH.ParetoGeometricMixture` | Actual geometric-mixture beta integrals, probability normalization, and complete infinite kernel marginals | Kernel checked; no spectral hypothesis |
| `RiemannResearch.RH.Pareto.geometricKernel_gram_integral`, `geometricKernel_cutoff_energy_identity`, `geometricKernel_double_energy_identity` | `RiemannResearch.RH.ParetoGeometricEnergy` | Exact finite Gram integral with explicit boundary; absolutely convergent full double-series energy for bounded sequences | Kernel checked; every tail and mixed term retained |
| `RiemannResearch.RH.Pareto.geometricTransform_integral`, `geometricTransform_sq_integral`, `geometricTransform_full_energy` | `RiemannResearch.RH.ParetoGeometricTransform` | Actual infinite geometric transform: mean, squared integral, and exact positive energy loss | Kernel checked for bounded sequences; all interchanges proved |
| `RiemannResearch.RH.Pareto.positiveWeight_block`, `dilation_partial_sum`, `paretoMean_dilation`, `paretoInner_dilation` | `RiemannResearch.RH.ParetoDilation` | Full Pareto block law, mean preservation, and exact inner-product scaling | Kernel checked; bounded sequences, positive dilation, anchoring explicit |
| `RiemannResearch.RH.Pareto.packetCombination_error_summable`, `primePowerCombination_full_error_floor`, `linear_square_summable_iff` | `RiemannResearch.RH.ParetoSequenceCertificates` | Genuine full-tail packet error bound; nonzero linear sequences are not Pareto square-summable | Kernel checked; arithmetic boundedness and convergence discharged |
| `RiemannResearch.RH.Pareto.paretoInner_optimal_scalar_gain`, `ramanujanPacket_enlargement_covariance`, `ramanujanPacket_prime_power_mul_mean_zero` | `RiemannResearch.RH.ParetoCovariance` | Actual infinite-sum covariance and scalar Schur gain; exact mixed-packet means for positive powers of a new prime | Kernel checked; scalar norm nonzero and arithmetic prime hypotheses explicit |
| `RiemannResearch.RH.Pareto.smoothingSeed_head`, `smoothingSeed_linear_head_energy`, `smoothingSeed_packet_expansion` | `RiemannResearch.RH.ParetoSmoothing` | Exact general-order smoothing head, signed energy expansion, and genuine multiples-sum packet coefficients | Kernel checked finite arithmetic; no asymptotics assumed |
| `ArithmeticFunction.logWeight_mul`, `sum_moebius_mul_log_sq`; `RiemannResearch.RH.Pareto.smoothingSeed_quadratic_head_error` | `RiemannResearch.NumberTheory.ArithmeticLogWeight`, `RiemannResearch.RH.ParetoQuadraticSmoothing` | Logarithmic Dirichlet-convolution derivation and quadratic Mobius-Mangoldt smoothing identity | Kernel checked finite algebra; includes the Lambda convolution term |
| `ProbabilityTheory.integral_const_sub_sq_total_variance`, `integral_const_sub_sq_condExp_pythagoras`, `integral_condVar_eq_integral_sq_residual` | `RiemannResearch.Probability.ConditionalVarianceError` | Exact bias/conditional-variance decomposition for genuine probability measures | Kernel checked; probability measure, L2 membership, sub-sigma-algebra explicit |
| `RiemannResearch.RH.Pareto.residue_mul_floor`, `residue_difference`, `mobiusDifference_residue`, `mobiusDifference_packet`, `ramanujanPacket_divisor_sum` | `RiemannResearch.RH.ParetoResidueDuality` | Genuine residue dilation, first differences, Mobius duality, packet incidence, and divisor reconstruction | Kernel checked; dual indices m > 1, packet q > 0 |
| `RiemannResearch.RH.Pareto.prime_divisor_transform`, `ramanujanPacket_mul_prime_of_not_dvd`, `ramanujanPacket_mul_prime_of_dvd` | `RiemannResearch.RH.ParetoPrimePackets` | Both prime enlargement identities, including repeated-prime channels | Kernel checked; p prime and q > 1; no independence assumption |
| `RiemannResearch.RH.Pareto.dualSix_normSq`, `dualSix_error_floor`, `witnessGram_eq_certificateMatrix`, `certificateMatrix_mul_numerators`, `primePowerCombination_error_floor` | `RiemannResearch.RH.ParetoFiniteCertificates` | Genuine Mobius rows have exact norm 92 and explicit signed Gram matrix; arbitrary prime-power combinations have finite weighted error at least 3562158/256250081 | Kernel checked arithmetic instantiation; infinite Hilbert closure is not asserted |
| `RiemannResearch.RH.Pareto.primorialDual_normSq`, `primorialDual_primorialPacket_zero`, `primePowers_primorials_error_floor` | `RiemannResearch.RH.ParetoFiniteCertificates`, `RiemannResearch.RH.ParetoPrimorialObstruction` | Norm 3880 and error floor 1/3880 for arbitrary combinations of prime powers and Mathlib primorials | Kernel checked finite coordinate bound; signal and annihilation discharged |
| `RiemannResearch.RH.Pareto.exists_squarefree_large_prime_support`, `boundedPrimeSupport_no_pointwise_limit` | `RiemannResearch.RH.ParetoBoundedInteraction` | No fixed distinct-prime interaction order admits pointwise convergence to 1 on positive integers | Kernel checked; positive conductors and a uniform fixed primeFactors.card bound |
| `RiemannResearch.RH.Pareto.anchoredGreen_inverse`, `anchoredGreen_solves_dirichlet`, `anchoredLaplacian_energy_with_boundary`, `anchoredLaplacian_energy` | `RiemannResearch.RH.ParetoAnchoredGreen` | Genuine max-kernel inverse action and exact finite energy, retaining the right boundary flux | Kernel checked operator formulation; zero-boundary specialization explicit |
| `RiemannResearch.RH.Pareto.mobiusPotential_difference`, `finiteMobiusRiesz_eq_gradient`, `mobiusPotential_energy`, `mobiusPotential_laplacian_energy` | `RiemannResearch.RH.ParetoMobiusPotential` | Actual finite Mobius potential and witness energy identities, including the last gradient summand | Kernel checked; boundary vanishing requires support in 1..M; multiples inversion remains open |
| `RiemannResearch.LinearAlgebra.finite_weighted_square_completion`, `finite_weighted_dual_bound` | `RiemannResearch.LinearAlgebra.FiniteWeightedEnergy` | Reciprocal-weight square completion and dual lower bound used by actual Pareto certificates | Kernel checked; nonzero/positive weights and positive dual norm explicit |
| `RiemannResearch.GroupTheory.AddSubgroupCRT.diagonal_injective_iff` | `RiemannResearch.GroupTheory.AddSubgroupCRT` | The simultaneous quotient map for two additive subgroups is injective exactly when their intersection is trivial | Kernel checked generalized CRT |
| `RiemannResearch.GroupTheory.AddSubgroupCRT.exists_diagonal_eq_iff` | `RiemannResearch.GroupTheory.AddSubgroupCRT` | A pair of residue classes has a common lift exactly when its overlap difference vanishes | Kernel checked; image equals kernel in the two-subgroup CRT sequence |
| `RiemannResearch.GroupTheory.AddSubgroupCRT.difference_surjective` | `RiemannResearch.GroupTheory.AddSubgroupCRT` | Every class modulo the sum of two additive subgroups is represented by a residue difference | Kernel checked surjectivity endpoint |
| `RiemannResearch.RH.PrimePhaseCRT.intPrimeLogRelation` | `RiemannResearch.RH.PrimePhaseCRT` | Every integer linear relation between logarithms of two distinct primes is trivial | Kernel checked from positivity of logarithm and uniqueness of prime powers |
| `RiemannResearch.RH.PrimePhaseCRT.periodSubgroup_inf` | `RiemannResearch.RH.PrimePhaseCRT` | The period subgroups generated by `2π / log p` and `2π / log q` have trivial intersection for distinct primes | Kernel checked unconditional prime specialization |
| `RiemannResearch.RH.PrimePhaseCRT.modularMap_injective` | `RiemannResearch.RH.PrimePhaseCRT` | The exact two-prime phase-residue map is injective | Kernel checked; does not assert topological density |
| `RiemannResearch.RH.PrimePhaseCRT.modularMap_exact` | `RiemannResearch.RH.PrimePhaseCRT` | A two-prime residue pair has a common real ordinate exactly when its overlap difference vanishes | Kernel checked exact algebraic CRT |
| `RiemannResearch.RH.StrictDiagonalDominance.posDef_of_strictlyRowDiagonallyDominant` | `RiemannResearch.RH.StrictDiagonalDominance` | A real Hermitian matrix with each positive diagonal strictly dominating its absolute off-diagonal row sum is positive definite | Kernel checked via the spectral theorem and Gershgorin |
| `RiemannResearch.RH.Log3Bounds.two_mul_logThreePartialSum_le_log_three` | `RiemannResearch.RH.Log3Bounds` | Every finite odd-power partial sum at one half gives a rigorous lower bound for `Real.log 3` | Kernel checked Mathlib series specialization |
| `RiemannResearch.RH.Log3Bounds.log_three_interval_15` | `RiemannResearch.RH.Log3Bounds` | `1098612288668109 / 10^15 < Real.log 3 < 1098612288668110 / 10^15` | Kernel checked from 27 exact terms plus a proved tail bound |
| `RiemannResearch.RH.Log3FiniteMatrixFormula.summable_aInfinitySummand` | `RiemannResearch.RH.Log3FiniteMatrixFormula` | The infinite archimedean-mode series used in the candidate exact-real formula scaffold is summable | Kernel checked by comparison with the convergent inverse-cube series |
| `RiemannResearch.RH.Log3FiniteMatrixFormula.evenFiniteLowerFormula`, `RiemannResearch.RH.Log3FiniteMatrixFormula.oddFiniteLowerFormula` | `RiemannResearch.RH.Log3FiniteMatrixFormula` | Candidate exact-real 20-by-20 formulas faithfully transcribed from the user-provided recovered verifier | Formula scaffold only; denominator validity, high-mode order bounds, Hermitianity, interval enclosures, and localized-Weil operator provenance remain open |
| `RiemannResearch.RH.CombinedGain.dualCapture_mono` | `RiemannResearch.RH.CombinedGain` | Restricting to a compressed legal dual-witness family cannot increase supremal capture | Kernel-checked order-theoretic compression lemma |
| `RiemannResearch.RH.CombinedGain.gain_lowerBound_of_actualDirectionOverlap` | `RiemannResearch.RH.CombinedGain` | A Cauchy quadratic certificate and an actual-direction overlap bound yield the inverse-free standardized gain lower bound | Kernel-checked implication; the concrete Gram Cauchy premise is explicit |
| `RiemannResearch.RH.CombinedGain.classwiseSecondMoment` | `RiemannResearch.RH.CombinedGain` | Finite-set Cauchy bounds squared class signal by class cardinality times its second moment | Kernel checked |
| `RiemannResearch.RH.CombinedGain.participation_of_secondMoment` | `RiemannResearch.RH.CombinedGain` | Converts a positive second-moment estimate into the global participation lower bound | Kernel checked |
| `RiemannResearch.RH.CombinedGain.exponentialAccumulation_le_exactProductGain` | `RiemannResearch.RH.CombinedGain` | The exact greedy product ledger dominates the cumulative exponential participation certificate | Kernel checked |
| `RiemannResearch.RH.CombinedGain.weightedCapture_of_exponential` | `RiemannResearch.RH.CombinedGain` | Pointwise exponential capture implies a threshold-free weighted rational capture estimate | Kernel checked |
| `RiemannResearch.RH.CombinedGain.jointProduct_closure` | `RiemannResearch.RH.CombinedGain` | Certified capture and certified absolute cross-flux multiply to a lower bound for the factorized observable | Kernel-checked implication; arithmetic providers remain open |
| `RiemannResearch.RH.CombinedGain.jointProduct_forces_absoluteScale` | `RiemannResearch.RH.CombinedGain` | A joint product certificate with capture at most one still forces an absolute cross-flux lower bound | Kernel checked scale obstruction |
| `RiemannResearch.RH.CombinedGain.TwoChannel.gain_eq_first_add_schur`, `gain_eq_first_iff`, `first_lt_gain_iff` | `RiemannResearch.RH.TwoChannelConditionalGain` | Exact unequal-norm two-channel Gram gain equals the first-channel gain plus the signed-overlap-residualized Schur increment, with exact zero and strict-gain criteria | Kernel checked algebra; actual legal arithmetic witnesses and quantitative residual-correlation bounds remain open |
| `RiemannResearch.RH.CombinedGain.TwoChannel.gain_sub_score_eq_schur_squares`, `score_eq_gain_iff` | `RiemannResearch.RH.TwoChannelConditionalGain` | One common two-channel optimizer has an exact sum-of-squares deficit and is the unique maximizer under positive pivots | Kernel checked; does not add independently optimized raw gains |
| `RiemannResearch.RH.CombinedGain.TwoChannel.gain_mul_gram_sub_pairing_sq`, `normalized_actualDirection_defect` | `RiemannResearch.RH.TwoChannelConditionalGain` | Exact signed Cauchy defect supplies the concrete actual-direction premise for inverse-free gain bounds and quantifies information discarded by that bound | Kernel checked; arithmetic overlap, legal support, return-covariance, and asymptotic sampling remain open |
| `RiemannResearch.RH.Statement` | `RiemannResearch.RH.Basic` | Stable local name for mathlib's RH proposition | Kernel checked |

## Conditional RH reductions

These declarations are complete proofs of implications, but they are not unconditional
proofs of the motivating RH statements.

| Declaration | Module | Verified consequence | Status |
|---|---|---|---|
| `ProbabilityTheory.conditional_energy_gap_of_variance_contraction`, `integral_const_sub_sq_le_bias_add_conditional_energy` | `RiemannResearch.Probability.ConditionalVarianceError` | Converts a supplied conditional-mean contraction into an energy gap and an error bound | Conditional research reduction; the actual pi/4 contraction provider is Open |
| `RiemannResearch.RH.Log3IntervalCertificate.evenBlock_posDef` | `RiemannResearch.RH.Log3IntervalCertificate` | The exact rational even-block preconditioner and row certificate imply positive definiteness for any supplied Hermitian 20-by-20 matrix satisfying the displayed `hdiag` and `hrow` bounds | Kernel checked conditional certificate; identification of the exact-real formula layer with the localized Weil operator and both enclosure hypotheses remain open |
| `RiemannResearch.RH.Log3IntervalCertificate.oddBlock_posDef` | `RiemannResearch.RH.Log3IntervalCertificate` | The exact rational odd-block preconditioner and repaired row certificate imply positive definiteness for any supplied Hermitian 20-by-20 matrix satisfying the displayed `hdiag` and `hrow` bounds | Kernel checked conditional certificate; identification of the exact-real formula layer with the localized Weil operator and both enclosure hypotheses remain open |

## Pareto noise and arithmetic repair (8 September 2026)

Source: RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf; detailed coverage and
source hashes: RH/ParetoNoiseSignalReport.md.

| Declarations | Module | Scope and status |
|---|---|---|
| scale_error_completion; finite_pair_remainder_identity | LinearAlgebra.NoiseSignalQuadratic | Kernel checked scalar optimization and exact finite weighted-pair remainder |
| paretoError_at_optimal_scale; paretoError_optimal_scale_minimizes; primePowerCombination_noiseSignal_floor | RH.ParetoNoiseSignal | Actual complete Pareto variance/NSR; bounded sequences and nonzero mean explicit; prime-power NSR at least 1/91 |
| mobiusDifference_arithmeticRepair; arithmeticRepair_eq_mixedPrimeLift | RH.ParetoArithmeticRepair | Genuine four-residue construction, full defect response, head preservation and finite packet legality |
| paretoInner_scaleRepair; arithmeticRepair_variance; arithmeticRepair_variance_le | RH.ParetoRepairCovariance | Exact full covariance and actual arithmetic diagonal bound; no correlation omitted |
| packetCombination_fixedSupport_full_error_lower_bound; packetCombination_fixedSupport_noiseSignal_lower_bound | RH.ParetoCoprimeObstruction | Actual full infinite reciprocal-square mass and fixed-support error/NSR floors; conductor divisibility witnesses explicit |
| smooth35Repairs_fixed_base_no_pointwise_limit | RH.ParetoRepairObstruction | Automatic composite invariant for all smooth35 repair scales plus any fixed finite packet base; varying coefficients allowed |
| hiddenNoise_mean_zero; hiddenNoise_interval_mass; hiddenNoise_interval_energy_odd; hiddenNoise_interval_energy_even | RH.ParetoHiddenNoise | Genuine sequence, exact finite interval laws and energies; asymptotics not asserted |
| paretoError_tendsto_mobiusDifference; boundedPrimeSupport_no_paretoError_limit | RH.ParetoDefectContinuity | Full-error convergence forces genuine arithmetic defects; boundedness separately for each approximant |
| coprimeReciprocalSquareMass_eulerProduct; coprimeReciprocalSquareMass_six; packetCombination_two_three_noiseSignal_lower_bound | RH.ParetoEulerProduct | Kernel checked complete Euler mass, with exact pi-squared floors |
| primeDualRepresenter_norm_sq; packetResidueCoefficient_prime_error_bound | RH.ParetoPrimeDualNorm | Kernel checked exact dual norm 2(p²+1) for p≥3 and actual packet coefficient bound |
| paretoInner_residue_four; paretoMean_residue_two; paretoInner_residue_two | RH.ParetoResidueMoments | Kernel checked complete infinite moments from digamma series |
| hiddenNoise_secondMoment_log_bound; hiddenNoise_firstMoment_log_bound | RH.ParetoHiddenNoiseAsymptotics | Kernel checked error≤18 from 2 log n, all n≥3; exact blocks and full tails supplied by RH.ParetoHiddenNoiseMoments |
| hiddenNoise_conditioned_limit_all; hiddenNoiseConditionedLimit | RH.ParetoHiddenConditioningVerified | Kernel checked actual conditioned limit (π²−6)/9; all indices; substitution, domination and constant evaluation proved |
| integral_fermi_first; integrable_fermi_first | RH.FermiIntegral | Kernel checked actual integral π²/12 and integrability |
| arithmeticRepair_binary_variance_log_bound | RH.ParetoRepairModulus | Kernel checked full discrete variance≤8(h/n²)(1+log(n/h)) for 0<h≤n |
| summable_prime_inv_mul_log_rpow; summable_prime_loglog_div_mul_log_rpow | RH.PrimeLogSummability | Kernel checked unconditional prime-weight convergence from Chebyshev |
| prime_repairs_limit_and_summable_of_log_gap | RH.ParetoRepairSummability | Kernel checked conditional reduction from an explicit quantitative gap; all variance and limit estimates discharged |
| summablePrimeRepairs_of_leastSmooth35_log_gap | RH.Smooth35RepairCompletion | Exact named SummablePrimeRepairs target follows from only the missing quantitative least-smooth gap input; conditional arithmetic reduction |
| residual_tendsto_zero_iff_not_summable | Analysis.ResidualGainProduct | Kernel checked exact recurrence/product and strict-gain exhaustion criterion; Analysis.ResidualGainTermination covers a gain equal to one |
| not_repairBesselBound_leastSmooth35Above | RH.ParetoBesselSmoothObstruction | Kernel checked NEGATIVE resolution of the report's proposed normalized Bessel bound for its actual least-smooth scale choice |
| repairBessel_commonScale_card_sq_le | RH.ParetoBesselClusters | Actual full Pareto cluster energy forces square-root cardinal bounds; Analysis.SmoothScaleReciprocal and RH.PrimeReciprocalTail contradict them |
| leastSmooth35Above_spec; leastSmooth35Above_le_twice | RH.Smooth35Choice | Actual minimal smooth scale and elementary factor-two bound, without a quantitative gap theorem |
| arithmeticRepair_common_anchor_cancel; arithmeticRepair_common_anchor_sum; arithmeticRepair_adjacent_chain | RH.ParetoRepairAnchorCancellation | Exact shared-scale and adjacent-scale changes of basis, retaining collective and terminal anchor coefficients |
| arithmeticRepair_binary_neighbor_defect; arithmeticRepair_common_anchor_variance_bound | RH.ParetoRepairAnchorCancellation | Compensating defect transfers to the neighboring scale; full variance bound uses the neighbor gap |
| tailOrthogonalize_energy_split; tailOrthogonalize_preserves_defect; arithmeticRepair_tail_elimination | RH.ParetoTailOrthogonalization | Exact Schur energy, preserved arithmetic head/defect, positive anchored pivot; the binary invariant is preserved |
| paretoInner_finsetCombination; paretoInner_finsetCombination_of_orthogonal | RH.ParetoFiniteGram | Exact full signed Gram expansion and Parseval for finite bounded orthogonal families with their actual coefficients |
| paretoInner_finsetCombination_le_total_energy; paretoInner_finsetCombination_le_tsum_energy | RH.ParetoFiniteGram | Valid Cauchy--Schwarz bound by unweighted coefficient square sum times total diagonal energy; not the refuted normalized Bessel bound |
| finiteTailProjection_orthogonal; finiteTailProjection_energy_split; finiteTailProjection_preserves_head; finiteTailProjection_pos_of_anchor | RH.ParetoFiniteTailProjection | Simultaneous finite projection for an already orthogonal bounded tail family, exact norm split and positive anchored pivot |

Four of the original six named targets have unconditional positive providers:
ResidueFourMoment, HiddenNoiseSecondMoment, HiddenNoiseFirstMoment and
HiddenNoiseConditionedLimit. The proposed RepairBesselBound is disproved for
the actual least-smooth choice (and all eventually comparable smooth choices).
This was an open suggestion in the PDF, not a theorem claimed proved there.

The finite covariance step now has proved replacements: exact anchor cancellation,
reverse orthogonal elimination, finite tail projection, and exact Gram identities.
See RH/ParetoCovarianceRepairReport.md. Transformed coefficients and all final
anchors are retained. The finite projection assumes an already orthogonal tail
family; a full recursive existence theorem is not claimed. These operations do
not remove the binary composite obstruction or prove infinite convergence.

The remaining named positive target is SummablePrimeRepairs. Its analytic
steps and exact conditional assembly are proved; the published quantitative
smooth35 gap theorem itself is still unformalized. It is an explicit hypothesis
of the conditional provider, not an axiom or an assumed variance estimate.

Other open translations include the fixed-old-space gain asymptotic, full
Hilbert infimum/closure results, and cited spectral and RH-criterion literature.
RH and global convergence of a sufficient repair system remain unresolved.

## Pareto analytic obligations (7 September 2026)

The exact bounded-sequence geometric error identity is now established as
`RiemannResearch.RH.Pareto.geometricTransform_full_error_identity` in
`RiemannResearch.RH.ParetoGeometricTransform`. The following obligations remain Open:

- The Kalvoda–Šťovíček weighted Hankel diagonalization and the actual sharp pi/4
  contraction on the constant-orthogonal subspace; no project axiom supplies it.
- Cyclotomic logarithmic-derivative identification of the conditional packet means;
  the present geometric transform is the actual infinite power series.
- Smoothing mean asymptotics from Mertens estimates, fixed-conductor large-prime
  asymptotics, Mellin/Plancherel specialization, and finite Euler-product growth.
- Full Hilbert-space dual closure, bounded pointwise/convex-average approximation,
  and matrix-valued multichannel Schur optimizers with arithmetic providers.
- Mixed-radix conditional independence and martingale energy specialization.
- Extension of the geometric identities from bounded sequences to arbitrary
  weighted L2 sequences, and a joint-measure conditional-expectation identification.
- Uniform corrected-energy decay, growing-conductor convergence, and RH remain
  mathematically unproved; these are not merely unfinished Lean translations.

The generic conditional-variance declarations assume ordinary probability/L2
hypotheses. The two contraction corollaries additionally assume `hcontract` and
are classified as conditional reductions above. Floating-point illustrations
from the research notes have not been converted to interval certificates.

## RH combined-audit import (3 September 2026)

The original combined-audit development is collected under
`RiemannResearch.RH.CombinedAudited` and imports the unique Lean content from
the audited-source archive.  The present extension records the subsequently
supplied `rh_irreducible_targets_progress_package_2026-09-03.zip`.  The package
archive has SHA-256 digest
`443ec212dfb2d6e23ee3687c5ffddcbafb80b973e5a48dd4206635aab34188eb`,
which agrees with the previously supplied manifest.  The staged
`ProgressManifest` update records the archive and extracted-payload hashes;
`SourceClaimIndex` separates formal declarations from numerical or documentary
source material.

### Verified finite and functional-analytic results

- The original import retains the exact Boolean-sign, raw-count/reciprocal,
  weighted-Pythagoras, scalar-counterterm, scalar-Schur, two-polar-mode,
  finite Morse-index, limit-positivity, and norm-contraction results.  The
  associated research targets remain definitions or propositions unless a
  proof is actually present.
- `RiemannResearch.RH.PrimeGapCurvature` contains `gap`, `adjacentSlope`, and
  `adjacentCurvature`, together with the exact affine-kernel theorems
  `adjacentCurvature_eq_zero_iff`, `adjacentCurvature_affine`,
  `adjacentCurvature_add_affine`,
  `exists_affine_on_range_of_curvature_eq_zero`, and
  `curvature_eq_zero_iff_exists_affine_on_range`.  The determinant identities
  `tripleDet_eq_gap_mul_gap_mul_slopeDiff` and `consecutiveTripleDet_eq` are
  supplemented by `tripleDet_eq_weighted_adjacentCurvatures` and its ordered
  specialization `tripleDet_eq_weighted_adjacentCurvatures_of_lt`.  The latter
  pair gives the exact telescoping compression of an arbitrary three-point
  determinant into adjacent curvatures.  The same module retains the scalar
  two-block mean/Schur and bandwidth-two recurrence families.  These are exact
  finite identities, not asymptotic prime-gap estimates.
- `RiemannResearch.RH.FiniteCurvatureGreen` packages adjacent curvature as
  the concrete linear map `finiteCurvatureMap` between finite coordinate
  spaces.  It proves
  `ker_finiteCurvatureMap_eq_range_affineProfileMap` and the equivalent
  range and coordinate forms of “equal curvature iff affine difference.”
  The two-prefix construction `profilePrefixLinearMap` is an explicit right
  inverse; `finiteCurvatureMap_comp_profilePrefixLinearMap` and
  `finiteCurvatureMap_surjective` give the exact section and surjectivity
  statements.  These are finite algebraic results, not a Weil-form
  identification or an RH proof.
- `RiemannResearch.RH.FiniteMeanZeroSlope` packages adjacent slope
  differences and arithmetic-mean centering as linear maps. It proves that
  centered curvature-prefix slopes have coordinate sum zero, that adjacent
  differences recover the original curvature vector, and that every zero-sum
  slope vector is recovered by centering its adjacent differences.
  `curvatureMeanZeroSlopeEquiv` gives the resulting exact linear equivalence,
  while `finiteAdjacentSlope_profilePrefix_eq_centeredSlope_add_mean` records
  the constant-slope gauge change from the anchored prefix profile. This is
  finite-dimensional algebra, not dyadic density, a Weil-form identification,
  or an RH proof.
- `RiemannResearch.RH.FiniteEndpointProfile` prefix-integrates arbitrary
  finite slope vectors on the unit grid and proves exact telescoping in both
  directions. It packages profiles with zero initial and final coordinates as
  `endpointZeroProfileSubmodule`, proves that centered curvature-prefix
  slopes integrate into that submodule, and reconstructs every member from its
  finite curvature. `curvatureEndpointZeroProfileEquiv` is the resulting
  linear equivalence from `Fin n → ℝ` curvature data to endpoint-zero
  profiles, including `n = 0`. This closes a finite coordinate chain; it is
  not dyadic density, a Weil-form identification, or an RH proof.
- `RiemannResearch.RH.FiniteDirichletGreenMatrix` gives the closed
  piecewise formula for the unit-grid endpoint-zero Green kernel. Its columns
  are the profiles of standard curvature vectors, arbitrary centered profiles
  are their finite Green superpositions, and the interior restriction is a
  symmetric, entrywise nonpositive matrix whose `mulVec` recovers the
  interior profile. `finiteCurvature_green_sum` proves the exact inverse
  identity, including the vacuous `n = 0` case. This is a finite-dimensional
  coordinate result, not dyadic density, a Weil-form identification, or an RH
  proof.
- `RiemannResearch.RH.FiniteDirichletGreenEnergy` proves the exact
  finite summation-by-parts identity
  `finiteDirichletGreenMatrix_quadraticForm_eq_neg_slopeEnergy`, identifying
  the Green quadratic form with the negative sum of squares of the centered
  slope vector. Theorems
  `finiteDirichletGreenMatrix_quadraticForm_nonpos` and
  `finiteDirichletGreenMatrix_quadraticForm_eq_zero_iff` establish
  nonpositivity and negative definiteness, including `n = 0`. This is a
  finite-dimensional energy identity, not a Weil-form identification or an RH
  proof.
- `RiemannResearch.RH.FiniteDirichletGreenGram` proves the exact mixed
  bilinear summation-by-parts identity, realizes the centered-slope map as
  multiplication by `finiteCenteredSlopeMatrix`, and factors the finite
  Dirichlet Green matrix as the negative Gram matrix of that slope transform,
  uniformly including `n = 0`. This is a finite-dimensional coordinate
  factorization, not a dyadic/Haar density result, a Weil-form identification,
  or an RH proof.
- `RiemannResearch.RH.FiniteSlopeCompression` defines the curvature-space
  pullback `Tᵀ K T` of an arbitrary real finite slope-space kernel `K`
  through `finiteCenteredSlopeMatrix`, proves its exact mixed bilinear
  identity, and shows that symmetry is preserved. This is a finite-dimensional
  generic kernel congruence, not a Weil-form identification, a positivity claim
  for a concrete arithmetic kernel, dyadic/Haar density, or an RH proof.
- `RiemannResearch.RH.FiniteCenteredSlopeMatrixFormula` proves the exact
  two-branch entries of `finiteCenteredSlopeMatrix` on the standard curvature
  basis, including the centering normalization. This is finite coordinate
  algebra, not a concrete Weil-kernel construction, positivity or density
  theorem, or an RH proof.
- `RiemannResearch.RH.FiniteDyadicHaarSlope` constructs literal dyadic
  Haar atoms and proves zero-sum membership, exact squared norms, pairwise
  orthogonality, and the three-jump curvature formula.
- `RiemannResearch.RH.FiniteDyadicHaarBasis` proves the full finite
  mean-zero slope basis, coefficient normalization, Parseval, and sparse
  curvature basis, including dimension zero.
- `RiemannResearch.RH.FiniteDyadicHaarCompression` proves exact literal
  Haar/curvature congruence and equivalence of finite nonnegativity in all
  directions. `FiniteSlopeCompression` supplies general family/basis versions.
  Actual cell-integral Weil kernels, arithmetic positivity, analytic density
  and limits remain open; these results are finite coordinate algebra.
- `RiemannResearch.Analysis.FiniteCellKernel` proves actual iterated-integral
  reconstruction for finite real cell steps and jointly continuous kernels,
  with all integrability used. Separated one-variable terms cancel on
  mean-zero steps. It also supplies continuous-kernel subtraction and
  uniform rectangle-integral error bounds, global finite-step norm bounds,
  and square integrability without disjoint-cell assumptions. Quadratic
  subtraction carries explicit inner and outer integrability evidence.
- `RiemannResearch.Analysis.SupportL2Bound` proves the support Cauchy bound
  `(∫ |u|)^2 ≤ 2R * ∫ u^2` with explicit L1/L2 integrability and vanishing
  outside `[-R,R]`, including the zero-length interval without division.
- `RiemannResearch.Analysis.CompactKernelQuadraticContinuity` proves product
  and iterated integrability for bounded measurable kernels on a fixed support
  window, exact quadratic subtraction, and quantitative L1/L2 continuity.
  It shows that square-integral convergence on the common window implies
  convergence of the actual full-line quadratic integrals. For jointly
  continuous kernels it also gives an explicitly conditional transfer of
  nonnegativity from a mean-zero L2-dense test class. The density and
  approximating-test positivity inputs remain hypotheses; no arithmetic
  positivity, Weil identification, or RH conclusion is supplied.
- `RiemannResearch.Analysis.ComplexKernelQuadratic` defines the actual
  conjugate-first complex quadratic form for real kernels and proves absolute
  product and outer integrability before Fubini. For symmetric continuous
  kernels it identifies the form exactly with the sum of the real quadratic
  forms of the real and imaginary parts. Its positivity transfer retains real
  positivity as an explicit premise and concludes zero imaginary part plus a
  nonnegative real part; complex numbers are not assigned an order.
- `RiemannResearch.Analysis.PrimitiveEnergy` proves the exact signed identity
  `q_abs(u) = -2 * ∫ U^2` for compactly supported real integrable mean-zero
  tests, where `U(t)=∫ x in Iic t, u x`. Joint measurability and absolute
  triple integrability precede Fubini; primitive-square integrability and
  component nonpositivity are also proved, including empty support intervals.
- `RiemannResearch.Analysis.HingeKernel` defines the common hinge and proves
  continuity, evenness, and exact finite-window inactivity. This previously
  published module is retained and used by HingeKernelIntegral and ScrewPrimePart.
- `RiemannResearch.RH.FiniteDyadicCellKernel` constructs equal dyadic cells,
  proves their support bounds and Haar-step mean zero, and identifies actual
  kernel integrals with the exact Haar compression, including R=0 and m=0.
  It also proves pointwise vanishing outside the support window, square
  integrability, and the exact support-length L1-to-L2 estimate. It specializes
  the primitive-energy identity and cumulative-square integrability to Haar steps.
- `RiemannResearch.RH.DyadicL2Density` constructs genuine averages on the
  literal Ioc dyadic cells, proves their exact zero-sum Haar reconstruction
  in the existing unnormalized basis, and establishes whole-line squared-L2
  convergence for every integrable, square-integrable, compact-window-supported
  mean-zero real test. The proof handles R=0 before positive-width cancellation
  and includes m=0. This closes the real fixed-window dyadic density bridge;
  arithmetic positivity, completed-Weil agreement, and support
  exhaustion, and the RH endpoint remain open.
- `RiemannResearch.RH.ArithmeticDyadicPositivityTransfer` is a conditional
  research reduction: positivity of the exact arithmetic-screw quadratic form
  on every dyadic Haar coefficient vector at every level transfers to every
  real integrable, square-integrable, mean-zero test on the same compact
  support window. A matrix-facing form uses the existing unnormalized
  `arithmeticScrewHaarMatrix` without rescaling. The all-level matrix
  premise also conditionally yields zero imaginary part and nonnegative real
  part for the actual complex form on mean-zero tests with integrable component
  squares. The all-level positivity premise, support exhaustion, completed Weil
  identification, and RH endpoint remain open.
- `RiemannResearch.RH.ArithmeticFiniteApproxPositivity` defines the literal
  Haar compression of the exact finite arithmetic approximation and proves its
  quadratic reconstruction and the signed implication `q_approx ≤ q_actual`.
  It now also proves approximation evenness, cell and Haar symmetry, Hermitian
  structure, an exact native `Matrix.PosSemidef` interface, and conditional
  fixed/all-level real and complex transfers. A generic entrywise interval
  certificate implies native PSD when its exact enclosures and strict margins
  are supplied. No finite certificate, completed-Weil agreement, or RH endpoint
  is proved.
- `RiemannResearch.Analysis.TranslationKernelCellIntegral` proves a generic
  four-corner double-integral theorem and exact cells for exponential,
  absolute-value, and exponential-absolute-value translation kernels on
  arbitrary oriented intervals. The exponential-absolute-value second
  primitive is globally `C²`, including at the origin.
- `RiemannResearch.RH.ArithmeticFiniteEntryFormulas` evaluates the finite
  approximation cell as the exact signed sum of the polar cell, the full finite
  von Mangoldt prime-power cells, the linear absolute-value cell, and the
  subtracted truncated archimedean cells. It then expands every entry of the
  literal unnormalized Haar matrix as a finite double sum. These are exact
  finite formulas, not positivity certificates.
- `RiemannResearch.RH.ArithmeticFiniteFirstLevel` proves that the first
  nonempty Haar matrix is PSD exactly when its unique diagonal is nonnegative,
  with a literal four-cell formula. At `R = 1/4`, `N = 2`, `J = 0`,
  Lean certifies the admissible cutoff but proves that diagonal is below
  `-5/1536`. This is an exact obstruction to that finite truncation, not to
  the actual arithmetic form, whose signed comparison remains
  `q_approx ≤ q_actual`. The module also records the vacuous level-zero PSD
  and zero-window matrix boundaries.
- `RiemannResearch.RH.ArithmeticFiniteFirstLevelCertificate` proves the
  exact level-one, cutoff-two scalar formula and rigorous rational lower
  bounds for its polar and first four archimedean contributions. Exact bounds
  for Euler's constant, `log π`, `log 2`, and π give the live linear/pole
  coefficient an upper bound of `269/100`. At `R = 1/16`, `J = 4`,
  the unique diagonal is above `1/500000`, yielding native finite PSD and,
  through the signed comparison, native PSD of the actual arithmetic Haar
  matrix at that same window and level. This is not all-level positivity,
  completed-Weil positivity, or RH.
- `RiemannResearch.RH.ArithmeticFiniteSecondLevelCertificate` proves the
  exact three-dimensional unnormalized Haar compression at level two,
  including all nine Toeplitz entries and a sum-of-squares quadratic
  decomposition. At `R = 1/16`, `N = 2`, and `J = 4`, certified
  rational Taylor enclosures give the finite quadratic form the unconditional
  lower bound `21/100000000` times the sum of squares of its three Haar
  coefficients. Hence the finite matrix is natively positive semidefinite,
  and the signed tail comparison transfers the same lower bound and native
  PSD to the actual arithmetic Haar matrix at this fixed window and level.
  The complete range-two von Mangoldt sum, polar correction, live
  gamma/pole coefficient, four archimedean modes, and Haar normalization are
  retained. This is not all-level or all-window arithmetic positivity,
  completed-Weil positivity, or RH.
- `RiemannResearch.RH.ArithmeticFiniteThirdLevelCertificate` proves the
  exact seven-dimensional unnormalized Haar compression at level three.
  At `R = 1/16`, `N = 2`, and `J = 4`, exact rational exponential
  enclosures, reflection blocks, rational shears, and strict row diagonal
  dominance give the unconditional lower bound `1/1000000000` times the
  sum of squares of all seven Haar coefficients. An exact eight-cell
  prefix-sum identity proves the auxiliary form is below the literal finite
  arithmetic form, and the signed tail comparison transfers the same bound
  and native PSD to the actual arithmetic Haar matrix at this fixed window
  and level. The complete range-two von Mangoldt sum, polar correction,
  live gamma/pole coefficient, four archimedean modes, and Haar normalization
  are retained. This is not all-level or all-window arithmetic positivity,
  completed-Weil positivity, or RH.
- `RiemannResearch.RH.ArithmeticFiniteFourthLevelCertificate` proves the
  exact fifteen-dimensional unnormalized Haar compression at level four.
  At `R = 1/16`, `N = 2`, and `J = 5`, all sixteen primitive
  values are enclosed by rigorous rational exponential bounds. Exact
  jump-stencil and Toeplitz identities, an eight-plus-seven reflection split,
  denominator-1000 rational shears, and strict row diagonal dominance give
  the unconditional lower bound `1/1000000000` times the sum of squares of
  all fifteen Haar coefficients. The exact auxiliary comparison retains the
  complete range-two von Mangoldt sum, polar correction, live gamma/pole
  coefficient, all five archimedean modes, and Haar normalization. The
  established signed tail comparison transfers the same lower bound and native
  PSD to the actual arithmetic Haar matrix at this fixed window and level.
  This is not all-level or all-window arithmetic positivity, completed-Weil
  positivity, or RH.
- The seven-module level-five certificate package, culminating in
  `RiemannResearch.RH.ArithmeticFiniteFifthLevelCertificate`, extracts reusable
  endpoint-jump, reflection-block, coefficient-Gram, rational interval, and
  integer-shear certificate infrastructure. At `R = 1/16`, `m = 5`,
  `N = 2`, and `J = 5`, exact rational exponential enclosures and
  denominator-10000 unit-upper shears give the unconditional lower bound
  `1/1000000000` times the sum of squares of all thirty-one native
  unnormalized Haar coefficients. The odd sixteen-dimensional and even
  fifteen-dimensional reflected blocks have certified positive margins
  `7500436/10^15` and `12178181/10^15`. The literal finite form retains the
  complete range-two von Mangoldt sum, polar correction, live gamma/pole
  coefficient, and all five archimedean modes. The signed comparison proves
  the same quantitative bound and native PSD for the actual arithmetic Haar
  matrix at this fixed window and level. This is not all-level or all-window
  arithmetic positivity, completed-Weil positivity, or RH.
- `RiemannResearch.Analysis.HingeKernelIntegral` proves positive-part
  power derivatives at every point, hinge primitives, and the exact
  four-corner double cell formula, including threshold crossings.
- `RiemannResearch.RH.ScrewPrimePart` defines the von Mangoldt weighted
  prime-power hinge series, proves local finiteness and continuity, and
  evaluates its finite-sum rectangle integrals exactly.
- `RiemannResearch.RH.ScrewArchimedeanSeries` constructs the continuous,
  even archimedean series and proves summability, an explicit uniform
  tail majorant `B_J`, and `tendsto_archimedeanTailMajorant_zero`.
- `RiemannResearch.Analysis.ExponentialKernelGram` proves an integrable
  Volterra-feature product identity and the square-integral Gram formula
  `exponentialKernel_finite_gram`. For every positive rate this gives
  nonnegativity on arbitrary finite configurations of real points.
  It now also proves absolute integrability of the three-variable Volterra
  product and `exponentialKernel_integral_gram`, so the actual convolution
  quadratic form is nonnegative for every measurable integrable real test.
- `RiemannResearch.RH.ScrewArchimedeanPositivity` proves
  `neg_archimedeanScrewTail_finite_nonneg` and
  `neg_archimedeanScrewSeries_finite_nonneg`: the negative archimedean
  series and every infinite tail are nonnegative on finite configurations
  with zero-sum real coefficients. Summability and interchanges are proved.
  For actual integrals, `neg_archimedeanScrewTerm_dyadic_integral_eq`
  isolates each exponential Gram term exactly.
  `neg_archimedeanScrewTail_integral_eq_tsum` proves the infinite-tail
  interchange on every integrable real test by an absolute product-space
  majorant, while `neg_archimedeanScrewTail_dyadic_integral_bounds_l1`
  gives dyadic nonnegativity and the explicit bound
  `4 * B_J * (∫ |u|)^2`. The sharp support-based theorem
  `neg_archimedeanScrewTail_dyadic_integral_bounds_l2` strengthens the upper
  bound to `8 * R * B_J * ∫ u^2`. This controls one signed component,
  not complete arithmetic positivity.
- `RiemannResearch.RH.ArithmeticScrewKernel` defines the full elementary
  arithmetic expression with polar, prime-power, linear, and archimedean
  terms. It proves continuity, evenness, value zero at zero, symmetry of the
  anchored kernel, and `arithmeticScrewHaarMatrix_quadratic`, the exact
  actual integral/Haar-matrix identity. Its finite approximation has
  explicit pointwise errors on bounded windows.
- `RiemannResearch.RH.ScrewPolarQuadratic` proves the exact polar
  quadratic identity for integrable real tests with integrable positive and
  negative exponential moments. It retains the constant correction
  `8 * (∫ x, u x)^2`, derives the mean-zero reduction, and specializes it
  to dyadic Haar steps. Its hyperbolic version gives `-8 C^2 + 8 S^2`
  for mean-zero tests, retaining the mean correction in the general theorem.
  These are signed component identities; no
  nonnegativity of the full arithmetic form or RH consequence is asserted.
- `RiemannResearch.LinearAlgebra.FiniteQuadraticError` proves
  `quadratic_error_of_entrywise_bound` for arbitrary real finite matrices.
- `RiemannResearch.RH.ArithmeticScrewCellBounds` proves exact finite
  prime-power cell sums for N>exp(2R), entry errors at most
  `4*B_J*h^2`, and `dyadicCell_arithmeticScrewApprox_quadratic_error`
  with bound `4*B_J*h^2*(sum_i |s_i|)^2` in every slope direction.
  On mean-zero Haar steps, its exact actual-minus-approximation identity is
  the negative archimedean tail quadratic form, yielding the one-sided
  enclosure `q_approx ≤ q_actual ≤ q_approx + 8*R*B_J*∫u^2` for N>exp(2R).
  This lower approximation need not be nonnegative.
- `RiemannResearch.RH.ArithmeticScrewQuadraticDecomposition` proves
  `dyadicHaarStep_arithmeticScrewFunction_quadratic_decomposition` and
  `arithmeticScrewHaarMatrix_quadratic_decomposition`: exact signed polar
  squares, all active von Mangoldt prime-power hinge quadratics, negative
  cumulative-primitive energy, and the infinite positive Volterra Gram series.
  Every sign and coefficient is inherited from the defined elementary function.
  This assembles components; it does not prove full arithmetic positivity.
  Source-normalization/Lerch agreement, identification with the zeta
  zero sum or Weil distribution, analytic density, complexification,
  the Weil/RH endpoint, and all-window full arithmetic positivity remain
  **Open**. No theorem in this batch proves or assumes the RH-strength
  arithmetic positivity target.
- `RiemannResearch.RH.FiniteCurvatureWeightedGreen` constructs the explicit
  weighted least-energy representative in every finite-curvature fiber.  Its
  moment formula `weightedAffineProjection` removes the weighted-orthogonal
  affine component, while `weightedOrthogonalPrefix` is a right inverse to
  `finiteCurvatureMap`.  Theorems
  `weightedOrthogonalPrefix_orthogonal_affineRange`,
  `weightedOrthogonalGreen_pythagoras`,
  `weightedOrthogonalGreen_minimizes`, and
  `weightedOrthogonalPrefix_unique_minimizer` give orthogonality,
  Pythagoras, minimization, and uniqueness under positive weights.  This is a
  finite-dimensional auxiliary Green construction, not a Weil-form
  identification or an RH proof.
- `RiemannResearch.RH.TripleCurvatureCompression` defines
  `tripleCurvatureLinearMap`, `selectedTripleCurvatureMap`, and the finite
  weighted form `selectedTripleCurvatureEnergy`.  The theorem
  `sum_weight_mul_tripleDet_sq_eq_selectedTripleCurvatureEnergy` factors any
  selected finite family of ordered triple-determinant squares through
  adjacent curvature, while `selectedTripleCurvatureEnergy_nonneg` proves
  positivity for nonnegative weights.  This auxiliary PSD result is not an
  identification with the Weil form.
- `RiemannResearch.RH.InnovationLittleOObstruction` proves that the literal
  fixed-prefix condition `ActualInnovationLittleO` forces the nonnegative
  monotone bandwidth-two energy to vanish.  In particular,
  `bandwidthTwoInnovation_eq_zero_of_actualLittleO` shows that every
  bandwidth-two innovation is zero when all pivots are positive.  This is a
  formal obstruction/guardrail and does not establish an RH criterion.
- `RiemannResearch.LinearAlgebra.DualGreenProjection` defines `greenOperator`
  and `dualGreenProjection`.  The declarations `dualGreenProjection_apply`,
  `dualGreenProjection_mapsTo`, `dualGreenProjection_residual_mem_ker`,
  `dualGreenProjection_idempotent`, `dualGreenProjection_factorization`, and
  `dualGreenProjection_orthogonal_ker` establish the abstract Green projection
  mechanism.  `dualGreen_energy`, `dualGreen_pythagoras`, and
  `dualGreen_minimizes` give the exact energy, Pythagoras, and minimization
  statements.  Their hypotheses remain explicit and do not assume the
  analytic realization required by the RH program.
- `RiemannResearch.LinearAlgebra.TwoBlockCommonOptimizer` packages the
  vector common-optimizer and exact Schur-mismatch argument.  Its distinct-form
  layer proves `twoBlockForm_commonOptimizer_identity`,
  `twoBlockFormMismatch_eq_commonFlux`, minimization, and equality rigidity.
  The basis-free `twoBlockFormOptimizer` inverts the summed normal map via
  bilinear duality; `existsUnique_twoBlockForm_minimizer` proves existence
  and uniqueness for finite-dimensional symmetric blocks when one block is
  positive definite and the other is nonnegative.  Its scalar-weighted
  same-form layer defines `weightedTwoBlockOptimizer` and proves the closed
  parallel-sum formula `weightedTwoBlockLoss_completion`, minimization, and
  equality and mismatch rigidity.  These theorems vectorize the earlier scalar
  two-block identities while retaining one global optimizer.  They are finite
  linear algebra and do not identify the block forms with the completed Weil
  form or establish RH.
- `RiemannResearch.LinearAlgebra.FiniteWeightedEnergy` proves the exact finite
  identities and dual certificates `affine_normal_det_double_sum`,
  `affine_normal_det_nonnegative`, `affine_normal_det_positive`,
  `weighted_functional_sq_le`, and
  `weighted_functional_energy_lower_bound`.  These results are independent of
  the numerical scripts and of any limiting argument.
- `RiemannResearch.LinearAlgebra.RankOneSchur` contains the scalar identities
  and bounds `rank_one_scalar_identity`, `rank_one_scalar_lower_bound`,
  `rank_one_elimination_lower_bound`, and `rank_one_elimination_attained`, plus
  the Hilbert-space theorems `rankOne_highMode_lower_bound`,
  `rankOne_highMode_attains`, and `rankOne_highMode_lower_bound_neg`.  They
  isolate the finite algebra required by the proposed high-mode elimination
  without identifying a truncated matrix with the full operator.

The new declarations above were individually kernel checked before
integration and are included in the repository-wide validation performed by
the publication checkpoint.  This verification covers the exact finite and
functional-analytic statements only, not any unresolved asymptotic or RH
claim.

### Evidence not promoted to a Lean theorem

The two `L = log 3` interval runs, including the larger robustness run, remain
reproducible candidate computer-assisted evidence.  Their output and hashes
are recorded for provenance, but the printed pivots are not treated as Lean
proofs.  Promotion would still require a formally verified interval
implementation together with the analytic reduction, Hermitianity and entry
enclosures, operator provenance, and the passage from finite compressions to
the relevant infinite operator.

These additions materially strengthen the exact finite-dimensional part of
the program, but they do **not** prove the Riemann Hypothesis.  The decisive
remaining work includes quantitative control of the actual signed endpoint
moments and adjacent-prime curvature innovations, the common-optimizer
boundary/Schur term, certified finite-block positivity, high-mode positivity
and tail bounds, and a noncircular spectral or trace construction connecting
those estimates to RH.

## Planned research areas

| Area | Initial target |
|---|---|
| Nyman–Beurling | Define the fractional-part generators in `L²(0,1)` |
| de Branges theory | Hermite–Biehler functions and reproducing-kernel spaces |
| Hilbert–Pólya | A precise conditional spectral formulation |
| Operator theory | Closed, densely defined, and self-adjoint operators |
| Spectral triples | Finite-dimensional prototype, then compact resolvent |
| Noncommutative geometry | C*-algebra representations and commutators |
| Field with one element | Select and encode a precise F₁ framework |

## Exact arithmetic-channel effects (7 September 2026)

Source: the user-provided paper argument
`RH_Exact_Arithmetic_Channel_Effects_2026-09-07.md`, sections 2–10.
The publication checkpoint checks the exact declarations below and their imports.
This is a substantive partial formalization of that paper, not a claim that every
paper proof, the complete Weil identification, or an RH implication is formalized.
The table below records the declaration scopes and the outstanding obligations.

| Module | Principal reusable declarations | Exact verified scope |
|---|---|---|
| `LinearAlgebra.SignedChannelUpdate` | `LinearMap.IsSymm.signed_change_synthesis`, `signed_gain_sum`, `signed_complete_square`, `signed_schur_nonnegative_iff`, `signed_universal_monotone_iff`, `signed_null_coupling_negative_witness`, `signed_minimum_eq_iff_normal`; `LinearMap.signed_change_sum_forms`, `signed_hilbert_projection_accounting`, `signed_no_gain_of_existing_span` | Native complex sesquilinear signed expansions with all mixed terms; signed completion and minimization assuming a supplied signed normal-equation solution; universal monotonicity iff channel positivity and vanishing signed mixed couplings; actual Hilbert accounting and redundant-channel obstruction. Existence of a Moore–Penrose/range solution is not proved. |
| `LinearAlgebra.GreenChannelBoundaryUpdate` | `RiemannResearch.LinearAlgebra.GreenChannelBoundary.woodbury_inverse`, `gluing`, `schur_update_inverse`, `innovation_update`, `boundary_migration`, `symmetric_schur_update`, `symmetric_inverse_energy_drop`, `update_nonsingular`, `MigrationExample.exact_migration` | Exact real finite-matrix inverses, screened updates and gluing under explicit ordinary invertibility/symmetry assumptions. The rational example proves total 1→2/3 and boundary 0→1/6. A general Loewner-order theorem and complex/operator extensions are not claimed. |
| `RH.PrimePowerReturnBoundary` | `RiemannResearch.RH.PrimePowerReturn.finiteAR1_inverse`, `finiteAR1_det_ne_zero`, `compressedPrimeGreen_inverse`, `compressedPrimeGreen_det_ne_zero`, `compressedPrimeGreen_inverse_singleton` | Direct multiplication proves all nonempty finite chain inverses and both endpoint corrections, including the coincident endpoints for the singleton. Only p>1 is needed for the prime-parameter identity. Identification with compression of an infinite operator remains separate. |
| `RH.PrimeCurvaturePolarBridge` | `RiemannResearch.RH.PrimeCurvaturePolarBridge.halfDensity_existsUnique_iff`, `halfDensity_complex_existsUnique_iff`, `translated_polarNull_iff_unique_curvature`, `halfDensity_polar_annihilation`, `halfDensity_complex_polar_annihilation`, `halfDensity_coefficientMass_positive`; `Matrix.signed_complex_congruence`, `physicalMass_identity`; `LinearMap.sesquilinear_curvature_compression` | Constructive unique real/complex curvature coordinates for exactly two polar constraints at positive nodes with nonzero adjacent gaps. The actual translated-bump integral equivalence has explicit integrability and nonzero base-moment hypotheses. Full signed congruence and distinct coefficient/physical mass are retained. No prime-grid density or signed positivity is assumed or established. |
| `Analysis.SquarePartitionLocalization` | `RiemannResearch.Analysis.SquarePartitionLocalization.partitionDefect_eq_half_sum_sq`, `partitionDefect_nonneg`, `sum_autocorrelation_localized`, `gluingCorrelation_zero`, `autocorrelation_add` | Exact finite square-partition defect and actual complex autocorrelation integrals, with their necessary integrability hypotheses. Both mixed correlations remain. No uniform gluing bound is asserted. |
| `RH.SignedWeilCorrelation` | `RiemannResearch.RH.SignedWeilCorrelation.correlationValue_sub`, `correlationValue_sum`, `correlationValue_net_effect`, `correlationValue_gluing`, `primePowerCorrelationValue_localization`, `primePowerCorrelationValue_cutoff_stable` | Signed finite von-Mangoldt correlation value with both pole terms, gamma regularizer and arbitrary diagonal constant. Actual-test localization under explicit integrability assumptions; exact cutoff invariance assumes omitted weighted values vanish. Full Weil/zero-side identification and the fixed archimedean constant are not supplied by these declarations. |
| `Analysis.WeightedAbelDiscrepancy` | `RiemannResearch.Analysis.weighted_abel_discrepancy` | Actual finite Abel summation against an arbitrary differentiable comparison primitive, retaining both endpoints; local differentiability/continuity assumptions only. |
| `RH.PrimePowerDiscrepancy` | `RiemannResearch.RH.primePowerHalfCutoff_exact_discrepancy`, `primePowerHalfCutoff_add_density` | Actual Λ(n)/sqrt(n) partial summation against 2(sqrt(x)−1), with the upper discrepancy boundary and continuous-density cancellation retained. No arithmetic estimate is assumed. The logarithmic-variable full Weil assembly is still open. |
| `RH.PrimeSquarePartialSummation` | `RiemannResearch.RH.primeSquareSector_eq_cutoff`, `primeSquareCutoff_exact_remainder`, `primeSquareSector_exact_remainder`, `primeSquareProfile_variation`, `abs_primeSquareSector_remainder_le` | Actual prime-square weights log(p)/p; supported-profile full sum equals its finite cutoff; exact main integral and discrepancy remainder; variation bound conditional on the displayed uniform discrepancy bound. Mertens and the autocorrelation/profile asymptotic assembly are not proved. |
| `RH.BroadTestNormalization` | `MeasureTheory.integral_sq_secondDeriv_sub_quarter`, `integral_exp_mul_secondDeriv_sub_quarter_eq_zero`; `RiemannResearch.RH.broadProfileNormalizer_sq`, `broadProfileNormalizer_lower`, `broadPolarOperator_broadBump_integral_sq`, `broadTest_eq_dilated_profile`, `broadTest_integral_sq`, `broadTest_polarMoments`, `normalizedBroadProfile_integral` | Actual compact C² broad-test construction, exact norm formula, positive lower bound, unit L² mass, both vanishing polar moments, dilation and profile mean. These are established analytic statements; no Mertens or RH hypotheses are used. |

### Remaining formalization obligations

- **Open:** identify the completed Weil distribution and zero-side pairing with
  the full explicit arithmetic correlation formula; evaluate the archimedean
  constant and complete the discrepancy representation (paper (3.4)/(4.3)).
- **Open:** discharge the correlation integrability/compact-cutoff hypotheses
  uniformly for the intended smooth test family; derive the discrepancy gluing
  expression (5.3) and compact-potential inverse/uniqueness plus its derivative
  localization repair (5.4)–(5.6).
- **Open:** complete Moore–Penrose range-existence/inertia and infinite Green
  operator provenance where needed; none is inferred from a finite inverse.
- **Open:** prime-log mesh density, common-bump approximation and exact two-moment
  correction in the compact-test topology, and the all-window Weil criterion.
- **Open:** the Mertens estimate, actual autocorrelation assembly of the square
  asymptotic, higher-prime-power/gamma limits and their O(R⁻²) errors.
- **Open:** the semiboundedness⇒RH proof, including an actual Weil distribution,
  Bochner–Schwartz temperateness, half-line Laplace holomorphy and the exact
  logarithmic-derivative pole obstruction.

The normal-equation and discrepancy-bound hypotheses in the corresponding
general theorems are explicit; kernel checking does not supply the missing
research inputs. No statement here establishes the desired all-window signed
arithmetic positivity.

## Nyman–Weil arithmetic completions (7 September 2026)

Source: user-provided argument,
`RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md`,
sections 4, 5, 7, 9, and 10.
The four candidates passed serialized isolated checks and key-declaration axiom
audits using only propext, Classical.choice, and Quot.sound. The final
publication checkpoint validates the actual modular imports and retained work.

| Module | Principal declarations | Established scope |
|---|---|---|
| `RH.NymanConductorArithmetic` | `RiemannResearch.RH.vonMangoldt_mul_nymanConductorBeta`, `nymanConductorBeta_mul_inverse`, `nymanConductorInversePrefix_exact`, `nymanTwoThree_prefix_feasible` | Actual full prime-power convolution, constructive Dirichlet inversion, exact finite-prefix matching, and concrete 2/3 feasibility. |
| `RH.ArithmeticConductorCommonZeros` | `RiemannResearch.RH.ArithmeticConductorCommonZeros.conductorSymbol_zero_iff_phase`, `conductorSymbol_zero_re`, `conductorSymbol_two_three_common_zero_iff`, `common_conductor_products_zero_iff` | Actual complex symbols; phase lattice and real part one; only common 2/3 zero is one; shared-factor product characterization away from one. Integer log independence is proved. |
| `Analysis.RemoteLaplaceTail` | `MeasureTheory.RemoteLaplaceTail.integral_kernel_norm_sq`, `norm_integral_mul_sq_le`, `remote_energy_lower_bound`, `null_completion_energy_lower_bound` | Evaluated kernel norm and actual Bochner-integral bound. The last result explicitly assumes supported L2 tail, weighted integrability, and actual transform nullity; no requested inequality is an input. |
| `LinearAlgebra.NullChannelTail` | `LinearMap.IsSymm.null_sub_diagonal`, `null_completion_mixed`, `null_completion_diagonal`, `null_completion_cross`, `null_compactification_change` | Exact Hermitian null-channel and head–tail identities, including full mixed terms. Radical membership is an explicit hypothesis. |

### Conditional research reductions and open providers

- **Completed below:** actual arithmetic completion, support, regularity, and transform nullity.
- **Completed below:** the full Weil distribution and actual arithmetic radical membership.
- **Completed below:** removable zeta-multiplier values and actual analytic multiplicities.
- **Open:** the optimized mixed-tail subexponential upper bound and its all-window RH implication.

The four modules prove reusable arithmetic, complex-analysis, integral, and
Hermitian-form results. They do not prove RH or its missing upper bound.

### Isolated verification evidence

| Module | Successful job | Runtime |
|---|---|---:|
| `RH.NymanConductorArithmetic` | `job_kgsqlFuPuZmPodfH1_Phd8YzCgy0HPxc` | 2.108 s |
| `RH.ArithmeticConductorCommonZeros` | `job_dy3c8yGmVXI0og2C8DF1t1K04Gy1mkiJ` | 2.266 s |
| `Analysis.RemoteLaplaceTail` | `job_lWfGz1EfW0z4pMidsDYav2pvXSNFMFDM` | 3.622 s |
| `LinearAlgebra.NullChannelTail` with its exact dependency source | `job_dznjEZ6WPZ-breuErkv6acQyz_UK2k-G` | 3.192 s |

Each returned verified true and exit code zero. The last check included the
unchanged SignedChannelUpdate source because isolated file checks do not
emit importable object files. The integrated module keeps its normal import.
Repairs concerned pinned APIs, cast normalization, the already-declared
Hermitian hypothesis's inclusion, and symmetry rewrite orientation.
Unused tactic arguments and draft status comments were removed before integration.
These isolated checks alone do not establish checkpoint publication.

## Nyman–Weil analytic and arithmetic completion

Source argument: §§2–10 of `RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md`.
This entry records the completion providers below; it does not certify every statement or numerical experiment in that note. The exact mathematical statements passed the combined Lean check recorded below. Publication also requires the native module-compilation checkpoint.

Write `E = SmoothSuperexponentialDecay`: a test is C∞ and every actual iterated derivative decreases faster than every positive exponential. The arithmetic return, integral transforms, correlations, and differential operator below are concrete functions. Their identities and admissibility are conclusions of the listed providers.

| Established coverage | Principal modules / endpoints |
|---|---|
| Actual arithmetic synthesis, local finiteness, C∞ regularity, and Dirichlet-convolution composition | `ArithmeticReturnSupport`, `ArithmeticReturnConvolution`: `arithmeticReturn_eq_sum`, `arithmeticReturn_contDiff`, `arithmeticReturn_mul`. |
| Closed Möbius coefficients of the actual constructive inverse | `NymanInverseMobius`: `nymanConductorInverse_eq_mobius_sum`, `nymanConductorInverse_eq_mobius_tsum`. For `n≥2` and `k>0`, these identify the existing Dirichlet inverse with `n ∑_{n^j∣k} n^j μ(k/n^j)` and prove that the apparent infinite series terminates. |
| Explicit coefficient and crude tail-size bounds | `NymanInverseCoefficientBound`: `sum_abs_nymanConductorInverse_div_sqrt_le` proves the actual coefficient bound 2n√M(1+Nat.log n M). `ActualL2Norm` and `NymanTailCrudeBound`: `nymanCompletedTest_eq_finite_translates`, `nymanCompletionTail_actualL2Norm_crude_upper_bound` prove the literal finite-translation identity and note (9.8) for the actual constructed tail. The L² triangle and translation bounds concern ordinary integrals, with finite-energy hypotheses supplied. |
| Actual finite inverse potential and remote support after applying `L = D²−1/4` | `ArithmeticInverseCompact`, `ArithmeticCompletionDifferential`: `nymanCompletionTail_tsupport`. For a seed supported in `[a,b]`, the inverse potential has support in `[a,b+log M]`, and the differential tail has support in `[a+log(M+1),∞)`. |
| Poisson cancellation and full output regularity | `NymanPoissonCancellation`, `ArithmeticReturnPoisson`, `LogarithmicSchwartzTransport`, `ArithmeticReturnDerivatives`, `NymanReturnRapidDecay`. The actual logarithmic kernel is Schwartz; the zero frequency cancels; every derivative of the actual return has arbitrary exponential decay. |
| Actual completed-test and tail membership in E | `NymanCompletionAdmissibility`: `smoothSuperexponentialDecay_nymanCompletedTest`, `smoothSuperexponentialDecay_nymanCompletionTail`, `nymanCompletionTail_admissible_and_tsupport`. |
| Actual transform factorization, including absolute Fubini, entire continuation, and both integrations by parts | `ArithmeticReturnMellin`, `BilateralLaplaceEntire`, `BilateralLaplaceDifferential`, `NymanTransformNullity`. The entire formula is `M(L R_n u)(s) = s(s−1) conductorZeta_n(s) M(u)(s)`. |
| Actual tail transform and its negative zero signature | `NymanTailTransform`: `centeredTransform_nymanCompletionTail`, `centeredTransform_nymanCompletionTail_zeta_signature`, `centeredTransform_nymanCompletionTail_polar`. |
| Compact smooth potential for every compact smooth polar-annihilating input | `CompactPolarPotential`, `CompactPolarPotentialUniqueness`: `existsUnique_compact_smooth_polarPotential`. The actual conditions `M f(0)=M f(1)=0` supply a unique smooth `v` in the original support interval with `Lv=f`. Both support and uniqueness are proved. |
| Removable value and actual zero multiplicities | `ZetaConductorRegularization`, `NymanPeriodicLFunction`, `NymanConductorContinuation`: the actual coefficient L-function equals the entire continuation of `ζ(s)(1/n−n^(−s))`; its value at 1 is `log n/n`. Analytic orders, conductor simple zeros, and the exact conductor-2/3 common-zero and minimum-order statements are proved for the stated conductor conditions. |
| Actual full Weil form on E | `SmoothCompactCutoff`, `CompactCutoffConvergence`, `CompactCutoffVerticalDecay`, `WeilZeroSumConvergence`, `WeilCutoffArchimedeanConvergence`, `WeilNoncompactExplicitFormula`: `actual_noncompact_Weil_explicit_formula_of_smooth`. These supply compact approximation, all weighted derivative L1 limits, a uniform spectral majorant, the multiplicity-weighted zero-sum limit, the complete von Mangoldt limit, and both pole/gamma limits. |
| Actual arithmetic Weil nullity, including signed terms | `WeilGammaFourierAdapter`, `NymanWeilNullity`, `NymanFullReturnWeilNullity`, `NymanWeilRadicalNullity`. The Fourier gamma term is identified with the regulated spatial term, retaining its exact diagonal constant. Actual completed returns have zero complete Weil value; the corresponding mixed radical statements use the actual form. |
| Exact full-form spectral pairing and head–tail accounting | `WeilSpectralPairing`: `arithmeticWeilPairing_eq_zero_sum`, `arithmeticWeilPairing_hermitian`, `arithmeticWeilPairing_self_eq`. `NymanActualTailWeilAccounting`: `infinitePrimePowerCorrelationValue_nymanCompletionTail_eq_head`, `arithmeticWeilPairing_head_nymanCompletionTail_eq_neg_head`. These prove the actual complete-form identities `Q(τ)=Q(Lv)` and `W(Lv,τ)=−Q(Lv)`. |
| Actual arithmetic completion of every compact smooth polar-annihilating test beyond any prescribed gap | `ActualArithmeticTailExistence`: `exists_actual_arithmetic_tail_after`. Given compact smooth `f`, the actual conditions `M f(0)=M f(1)=0`, a conductor `n≥2`, and any real gap `Y`, this constructs a compact smooth potential `v` and finite inverse cutoff `M`. The resulting actual arithmetic tail belongs to E, has support in `[Y,∞)`, annihilates both poles, and satisfies `Q(τ)=Q(f)` and `W(f,τ)=−Q(f)`. |
| Complete prime/square/higher-power split and exact arithmetic-return compensation | `PrimePowerSectorDecomposition`: `primePowerSeries_eq_prime_add_square_add_higher`. `NymanPrimeSquareCompensation`: `primeCorrelationSector_smul_poleCancellation_nymanFullReturn_compensation`. This partitions the convergent actual von Mangoldt series and proves compensation for each real scalar multiple of `L R_n u` with compact smooth `u`. It retains the complete square sector, the higher-power diagonal and displacement correction, the exact gamma diagonal, and the gamma displacement integral. |
| Arithmetic and limiting ingredients for prime–square compensation | `MertensElementary`, `MertensPrimeDiscrepancy`, `PrimeCompensationLimits`, `NoncompactPrimeSquareLimit`, `NoncompactPrimeSquareScaling`, `ArchimedeanCorrectionLimit`, `RealAutocorrelationSquare`. These provide the unconditional bounded prime Mertens discrepancy, the complete signed noncompact square identity, actual gamma/higher-power second moments, and vanishing displacement corrections under the stated profile hypotheses. Fixed-profile limits do not substitute for the varying arithmetic-return family. |
| Generic normalized broad-kernel bounds and quantitative mean-square limit | `BroadKernelUniformBounds`: `eventually_normalizedBroadKernel_bounds`, `integral_sq_normalizedBroadKernelProfile`, `tendsto_mean_normalizedBroadKernelProfile`. `BroadKernelMeanSquareRate`: `eventually_mean_sq_normalizedBroadKernelProfile_error`. Under the explicitly stated kernel moment, profile integrability, boundedness, and nondegeneracy hypotheses, these prove eventual uniform bounds, exact normalization, the limiting squared mean, and an `O(1/R)` error for that squared mean. They do not assume the target convergence. The actual arithmetic-return instantiation and its stronger weighted estimates are supplied below. |
| Second-order broad-profile energy estimate, including the actual return kernel | `BroadKernelEnergySecondOrder`: `differentialBroadKernelEnergy_second_order_bound`, `nymanBroadKernelEnergy_second_order_bound`. The first-order profile correction is a derivative whose cross integral vanishes for a compact smooth seed. The resulting energy error is bounded by `C/R²`, and the actual `nymanReturnKernel` satisfies the required moment hypotheses. |
| Actual scaled arithmetic family, its norm, and its literal zeta coefficient | `NymanReturnAbel`, `NymanBroadKernelBridge`, `NymanBroadKernelEnergy`, `NymanKernelZetaMass`: the actual return equals the spatial kernel convolution, the scaled test equals the differential broad profile, its energy equals the actual integral of the squared norm, and the kernel mass gives the exact coefficient at ζ(1/2). |
| Positive normalization at every positive scale | `NymanBroadNormalizationPositive`: `nymanBroadNorm_pos`, with exact unit norms for both the real scaled profile and the physical complex arithmetic test. These require conductor n≥2, a compact C∞ real seed, nonzero seed integral, and R>0; they are not restricted to eventual positivity. |
| Actual Schwartz convergence with all weighted derivatives | `ScaledKernelWeightedApproximation`, `BroadKernelWeightedApproximation`, `WeightedNormalizationConvergence`, `SuperexponentialSchwartz`, `NymanBroadSchwartzConvergence`, `NymanBroadSchwartzTopology`: `tendsto_nymanBroadSchwartzMap`. For the stated nondegenerate compact seed, the actual scaled normalized family converges to the negative normalized seed in Mathlib's Schwartz topology. Uniform bounds and convergence in every weighted derivative seminorm are proved. |
| Complete varying-family compensation and both linear asymptotics | `NymanBroadCorrelationBounds`, `NymanBroadCorrelationScaling`, `NymanBroadCorrectionLimits`, `NymanBroadSquareAsymptotic`, `NymanBroadPrimeSquareCompensation`, `NymanBroadPrimeAsymptotic`. The actual square sector is −R(∫φ)²/(2∫φ²)+O(1), and the actual prime sector is +R(∫φ)²/(2∫φ²)+O(1). Their sum tends to the explicitly retained full diagonal constant. The entire gamma and higher-power displacement corrections are O(R⁻²) and tend to zero. No limit of the bounded signed square remainder is asserted. |
| Exponential lower bound for the actual remote arithmetic tails | `NymanActualTailEnergy`: `nymanCompletionTail_energy_lower_bound`, `nymanPolarCompletionTail_energy_lower_bound`. At an actual zeta zero ρ with Reρ>1/2, the constructed tail has energy at least (2Reρ−1)exp((2Reρ−1)Y)|M f(ρ)|². Its L² membership, supported-transform identity, and weighted integrability are derived from the actual completion providers. |

The arithmetic/transform chain passed `nullity2`; cutoff and correlation providers passed `cutoff2`; the noncompact explicit-formula/nullity chain passed `fullweil2`; the compact potential, uniqueness, and prime-power sector decomposition passed `kernel_clean2`. The exact spectral pairing, universal tail existence, head–tail accounting, and actual-return compensation passed `tails1`. The generic normalized broad-kernel bounds and quantitative mean-square rate passed `profile4`. The actual inverse's Möbius formulas and second-order broad-profile energy estimates passed `remaining_algebra2`. Earlier successful checks supply the stated elementary Mertens and sector-moment providers. The coordinator's verification ledger remains authoritative for individual module inclusion.

The compact Weil foundation is imported from **Anthropic's Zeta23**, [anthropics/formal-math at commit `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`](https://github.com/anthropics/formal-math/tree/fbdc36bbf17d20af3fd0447c6d1a8a02773c9844/zeta23), under **Apache License 2.0**, copyright 2026 Anthropic, PBC, with original contributor notices retained. The exposed unconditional theorem is `Zeta23.WeilEF.EF_lit_zetaZeroConfig`. Its zero carrier is the actual nontrivial zeros of `riemannZeta`, and its multiplicities are `(analyticOrderAt riemannZeta ρ).toNat`. The imported dependency closure, relocation, license, and source audit are documented in `RH/WeilExplicitFormula/PROVENANCE.md`, `NOTICE.md`, and `LICENSE.md`. This foundation is credited upstream; the new transport, extension, and completion providers connect it to this project's actual arithmetic tests.

### Combined verification and remaining RH target

The complete chain above passed job `job_Krj1svNf3MBDoFYei95fp6xuWVuq_WxM` with `verified: true`, exit code 0, and 70.777 seconds of compiler time. Its exact combined-source SHA-256 is `f2e7e50f4b562650118381dcf77205a82a7930d8fca69dc6a2d06ee7bf26f59b`. The check included 176 source modules: 106 authored completion modules, 58 credited upstream/adapter modules, and 12 pre-existing project dependencies. Every import remains modular in the persistent project; source inlining was only the isolated-check mechanism.

The environment is Lean `v4.33.0-rc2` and Mathlib commit `51e6992efd06126df61a496bebf8f49482a4e129`. Eleven final endpoint axiom audits, including the actual explicit formula, universal arithmetic completion, common-zero multiplicities, exact compensation, prime asymptotic, Schwartz convergence, normalization, and tail-energy bound, use only `propext`, `Classical.choice`, and `Quot.sound`.

The additional coefficient/crude-tail-size chain passed job `job_-r8DwnTrVWQiTUe4yCyohmVnhlzVB81Z` with verified true, exit code 0, and 6.202 seconds. Its 32-module combined-source SHA-256 is `c7c0a6786436cc4ac332f8ba7b4a2a0c86f5d2693528e8f88e241d95d86c630c`. It adds three authored modules to the completion set, for 109 authored modules in total.

The RH target remains open: an appropriate subexponential upper bound for the optimized **mixed-conductor** remote tails has not been proved. These unconditional completion identities, null channels, and prime–square compensation do not establish that upper bound or RH. This entry also does not certify every earlier optimizer calculation, truncated-residual endpoint formula, or numerical experiment in the source note.
