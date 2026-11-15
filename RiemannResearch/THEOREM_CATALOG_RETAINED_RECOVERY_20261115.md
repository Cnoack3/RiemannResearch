# Retained research recovery — 15 November 2026 UTC

This change reconciles retained workspaces `ws_Zc2GDeYR_6AQeljCtBv0mJCOjS-pFNK_`
and `ws_cFM0TMufSAwwe3E2c9erVSCyB7rRsKaS` against current main at
`c8374f82a71e51af647074d8d6087fa557d5788a`.

The current finite screened-coordinate assembly, nested-cutoff prime-power
estimates, Schur inversion, and existing catalogs are preserved. The older
continuous-synthesis statements are recovered separately in
`RH/QCRTContinuousSynthesis.lean`. The later prime-depth package supersedes
the earlier depth-budget draft. The dyadic cardinality bound moves from
`RH/PrimeLogSummability.lean` to `NumberTheory/PrimeReciprocalBounds.lean`;
its known local consumer uses the new owning namespace, without a forwarding
declaration.

## Verification status

The combined saved-module import check and 40 guarded transitive-axiom checks
passed on the current reconstructed source. See
`THEOREM_CATALOG_V_SPACE_SYNC_20261114.md` for the precise run and scope.
The managed publication checkpoint additionally verifies the full project;
its exact source SHA and terminal receipt are recorded in the synchronized Sites.
Historical saved-source receipts retain their original scope.

## Open arithmetic obligations

- The actual canonical one-step bound `hstep` is an explicit hypothesis of
  the prime-power energy-transfer theorem. Summability of higher prime powers
  does not prove that bound.
- The positive-relative-variation and positive-logarithmic-variation small-o
  estimates remain open hypotheses.
- Complete reciprocal head repairs do not establish the required norm-times-tail
  decay; the dilation-budget criterion retains that provider explicitly.
- Finite interval certificates, inverses, exact head interpolation, and
  countermodels do not provide an unconditional RH proof.

## Recovered declarations by module

### `RiemannResearch/Analysis/EuclideanEnergyOperatorNorm.lean`

- `norm_sq_eq_maximalRayleigh_of_energy`

### `RiemannResearch/Analysis/FiniteAffineGramConstraints.lean`

- `projectedRows`
- `projectedRows_inner`
- `minimumInterpolation`
- `minimumInterpolation_mem`
- `minimumInterpolation_observation`
- `minimumInterpolation_completion`
- `minimumInterpolation_matrix_value`
- `affineOptimizer`
- `affineOptimizer_mem`
- `affineOptimizer_observation`
- `affine_error_completion`
- `affineOptimizer_minimizes`
- `projection_feasible_iff_mismatch_zero`
- `projectedRows_gramMatrix`
- `finiteDictionary_error_completion`

### `RiemannResearch/Analysis/FiniteAffineGramOperatorNorm.lean`

- `minimumInterpolationLinear`
- `minimumInterpolationCLM`
- `minimumInterpolationCLM_apply`
- `minimumInterpolationCLM_energy`
- `minimumInterpolationCLM_sup_norm_sq_max`
- `euclideanInterpolationCLM`
- `euclideanInterpolationCLM_energy`
- `euclideanInterpolationCLM_norm_sq`
- `euclideanInterpolationCLM_norm_sq_leastEigenvalue`

### `RiemannResearch/Analysis/LogFloorConvolution.lean`

- `logWeight`
- `six_le_logWeight`
- `logWeight_pos`
- `majorant`
- `majorant_nonneg`
- `power_le_double_power`
- `summable_majorant`
- `logWeight_power_eventually_le_index`
- `global_envelope_of_eventual`
- `logWeight_floor_mul`
- `floorConvolution`
- `floorConvolution_le`

### `RiemannResearch/Analysis/LogRationalCertificates.lean`

- `logOnePlusInvInterval`
- `logOnePlusInvInterval_contains`

### `RiemannResearch/Analysis/MultiplicativeBudget.lean`

- `prod_one_add_le_exp_sum`
- `prod_one_add_mul_le_exp`
- `energy_le_initial_mul_prod`
- `energy_le_exp_of_sum_le`

### `RiemannResearch/Analysis/ObliqueLiftCounterexample.lean`

- `oblique_example_energy`
- `oblique_example_test_pairings`
- `basisVector`
- `basisVector_norm_sq`
- `basisVector_inner_zero`
- `actual_oblique_example`
- `actual_oblique_energies_unbounded`

### `RiemannResearch/Analysis/ParetoProgressionCertificates.lean`

- `square_summable`
- `squareProgression`
- `paretoProgression`
- `integral_unit_eq_Ioo`
- `inversePower_intervalIntegrable`
- `integral_inversePower_succ`
- `integral_inversePower_one`
- `integral_square_kernel`
- `paretoProgression_summable`
- `squareProgression_integrableOn`
- `paretoProgression_eq_integral_squareProgression`
- `integral_enclosure`
- `paretoProgression_eq_progressionWeight`
- `correctionCoefficient`
- `squareApprox`
- `paretoApprox`
- `squareApprox_nine_eq_scaled`
- `squareApprox_ten_eq_scaled`
- `squareApprox_intervalIntegrable`
- `integral_squareApprox`
- `complete_tail_ten_bounds`
- `prefix_tail_identity`
- `prefix_tail_ten_bounds`
- `paretoRationalPart`
- `paretoApprox_eq_log_add_rationalPart`
- `paretoRationalPart_nine_cast`
- `paretoRationalPart_ten_cast`
- `paretoProgressionInterval`
- `paretoProgressionInterval_contains`

### `RiemannResearch/Analysis/PositiveGramMinimumEigenvalue.lean`

- `leastEigenvalue`
- `leastEigenvalue_le`
- `leastEigenvalue_attained`
- `leastEigenvalue_pos`
- `inverse_eigenvector`
- `diagonal_inner`
- `basis_parseval`
- `inverse_quadratic_spectral`
- `inverse_quadratic_le`
- `norm_sq_eq_reciprocal_leastEigenvalue`

### `RiemannResearch/Analysis/RationalIntervalDecimal.lean`

- `decimalHull`
- `contains_decimalHull`

### `RiemannResearch/Analysis/ReciprocalProgressionCertificates.lean`

- `reciprocalProgression`
- `reciprocal_kernel_signed`
- `reciprocalProgression_summable`
- `reciprocalProgression_eq_signed`
- `reciprocalProgression_nonneg`
- `squareProgression_eq_rawResidueSquareWeight`
- `reciprocalProgression_eq_raw_signed`
- `reciprocalProgressionInterval`
- `reciprocalProgressionInterval_contains`

### `RiemannResearch/Analysis/ReciprocalSquareRootSum.lean`

- `reciprocal_sqrt_succ_le`
- `sum_inverse_sqrt_range_le`
- `sum_inverse_sqrt_Icc_le`

### `RiemannResearch/Analysis/RightInverseNullPerturbation.lean`

- `perturbation`
- `perturbation_apply`
- `perturbation_energy`
- `perturbation_rightInverse`
- `perturbation_mem`
- `perturbation_output_unbounded`
- `perturbation_opNorm_unbounded_of_value`
- `perturbation_opNorm_unbounded`

### `RiemannResearch/Analysis/ScreenedCollocation.lean`

- `synthesisGram_injective`
- `synthesisGramEquiv`
- `synthesisGramInverse`
- `synthesisGramInverse_right`
- `screenedSynthesis`
- `screenedSynthesis_apply`
- `screenedSynthesis_joint_injective`
- `adjoint_screenedSynthesis_eq_zero`
- `inner_old_screenedSynthesis`
- `screenedSynthesis_inner`
- `screened_response_gram`
- `screened_energy_update`
- `screened_collocation_schur`

### `RiemannResearch/Analysis/StretchedFloorConvolution.lean`

- `profile`
- `profile_nonneg`
- `profile_le_self`
- `profile_double_le`
- `logWeight_floor_add`
- `profile_floor_le`
- `kernel`
- `kernel_nonneg`
- `summable_kernel`
- `scale`
- `scale_nonneg`
- `scale_pos`
- `scale_eventually_one_le`
- `global_envelope_of_eventual`
- `floorConvolution_le`

### `RiemannResearch/Analysis/SupNormSignVertices.lean`

- `exists_sign_vector_norm_ge`
- `signVertex`
- `signVertex_norm_le_one`
- `exists_signVertex_opNorm`

### `RiemannResearch/LinearAlgebra/NonsymmetricSchur.lean`

- `blockSchur`
- `blockSchur_injective`
- `blockSchurEquiv`
- `blockSchurEquiv_apply`
- `block_solution_eq_schur_inverse`

### `RiemannResearch/LinearAlgebra/RationalLinearInvertibility.lean`

- `linearDefect_isUnit`
- `certified_inverse_solution`

### `RiemannResearch/LinearAlgebra/RationalLinearSolveCertificate.lean`

- `coordinate_error_bound`
- `preconditioned_error_identity`
- `absBound`
- `abs_le_absBound`
- `linearDefect`
- `linearResidual`
- `linearDefect_contains`
- `linearResidual_contains`
- `linearSolution`
- `linearSolution_contains`

### `RiemannResearch/LinearAlgebra/RationalMatrixIntervalCertificate.lean`

- `pointMatrix`
- `pointMatrix_contains`
- `matrixProduct`
- `matrixProduct_contains`
- `leftCongruence`
- `rightCongruence`
- `stagedCongruence_contains`
- `posDef_of_dominant_enclosure`
- `posDef_of_congruence_enclosure`

### `RiemannResearch/LinearAlgebra/RationalPositiveDefiniteCertificate.lean`

- `congruence`
- `congruence_contains`
- `cast_matrix_isUnit_of_right_inverse`
- `CongruenceDominates`
- `posDef_of_congruence_certificate`

### `RiemannResearch/LinearAlgebra/RationalQuadraticCertificate.lean`

- `bilinear`
- `bilinear_contains`
- `quadratic`
- `quadratic_contains`
- `linearForm`
- `linearForm_contains`
- `squaredError`
- `squaredError_contains`

### `RiemannResearch/NumberTheory/FinitePositiveHyperbola.lean`

- `sum_positive_hyperbola`

### `RiemannResearch/NumberTheory/PrimePowerDepthBudget.lean`

- `reciprocalBudget`
- `reciprocalBudget_nonneg`
- `sum_reciprocalBudget`
- `sum_reciprocalBudget_le_one`
- `summable_reciprocalBudget`
- `tsum_reciprocalBudget_le_one`
- `hasSum_higher_prime_powers`
- `summable_prime_reciprocalBudget`
- `tsum_prime_reciprocalBudget_le_one`
- `higher_prime_power_budget`
- `higher_prime_power_budget_le_one`
- `summable_higher_prime_powers`
- `finite_higher_prime_power_budget_le_one`
- `higher_depth_product_le_exp`
- `hasSum_positive_prime_powers`
- `finite_prime_power_budget_le`
- `exp_prime_power_budget_eq`
- `prime_power_product_le_polylog`
- `energy_le_polylog_of_prime_power_steps`
- `energy_le_polylog_of_eventual_prime_power_steps`

### `RiemannResearch/NumberTheory/PrimeReciprocalBounds.lean`

- `prime_dyadic_card_mul_le`
- `prime_dyadic_reciprocal_sum_le`
- `prime_reciprocal_sum_le`
- `prime_subtype_reciprocal_sum_le`

### `RiemannResearch/RH/CanonicalReviewCertificates.lean`

- `collocationMatrix`
- `collocationRhs`
- `valueInterval`
- `periodicEnergyInterval`
- `realCollocationMatrix`
- `realCollocationRhs`
- `realValue`
- `collocationMatrix_contains`
- `collocationRhs_contains`
- `valueInterval_contains`
- `periodicEnergyInterval_contains`
- `zetaInterval`
- `zetaInterval_contains`
- `zetaInterval_pos`
- `weights2`
- `weights2_refines`
- `weights2_contains`
- `rows2`
- `cols2`
- `matrix2`
- `rhs2`
- `inverse2`
- `center2`
- `solution2`
- `energy2`
- `actualWeights2`
- `actualMatrix2`
- `actualRhs2`
- `actualEnergy2`
- `defect2_checked`
- `residual2_checked`
- `solution2_contains`
- `energy2_contains`
- `energy2_checked`
- `actualEnergy2_bounds`
- `weights6`
- `weights6_refines`
- `weights6_contains`
- `rows6`
- `cols6`
- `matrix6`
- `rhs6`
- `inverse6`
- `center6`
- `solution6`
- `energy6`
- `actualWeights6`
- `actualMatrix6`
- `actualRhs6`
- `actualEnergy6`
- `defect6_checked`
- `residual6_checked`
- `solution6_contains`
- `energy6_contains`
- `energy6_checked`
- `actualEnergy6_bounds`
- `weights12`
- `weights12_refines`
- `weights12_contains`
- `rows12`
- `cols12`
- `matrix12`
- `rhs12`
- `inverse12`
- `center12`
- `solution12`
- `energy12`
- `actualWeights12`
- `actualMatrix12`
- `actualRhs12`
- `actualEnergy12`
- `defect12_checked`
- `residual12_checked`
- `solution12_contains`
- `energy12_contains`
- `energy12_checked`
- `actualEnergy12_bounds`
- `weights60`
- `weights60_refines`
- `weights60_contains`
- `rows60`
- `cols60`
- `matrix60`
- `rhs60`
- `inverse60`
- `center60`
- `solution60`
- `energy60`
- `actualWeights60`
- `actualMatrix60`
- `actualRhs60`
- `actualEnergy60`
- `defect60_checked`
- `residual60_checked`
- `solution60_contains`
- `energy60_contains`
- `energy60_checked`
- `actualEnergy60_bounds`

### `RiemannResearch/RH/MatchedReciprocalIntervals.lean`

- `vectorSub`
- `realVectorSub`
- `vectorSub_contains`
- `matvec`
- `realMatvec`
- `matvec_contains`
- `crossVector`
- `realCrossVector`
- `crossVector_contains`
- `headPair`
- `realHeadPair`
- `headPair_contains`
- `metrics`
- `realMetrics`
- `metrics_contains`

### `RiemannResearch/RH/QBinaryReciprocalExample.lean`

- `target`
- `projectionCoefficient`
- `tsum_odd`
- `gram`
- `pareto_gram`
- `target_inner`
- `raw_odd_weight`
- `raw_even_weight`
- `pareto_odd_weight`
- `reciprocal_odd_weight`
- `target_norm_sq`
- `error_formula`
- `first_head_error_formula`
- `projection_error_formula`
- `projection_normal_equation`
- `error_completion`
- `projection_minimal`
- `first_head_iff`
- `log_two_ge_two_thirds`
- `projectionCoefficient_lt_half`
- `first_head_extra_cost_pos`
- `first_head_error_strict`

### `RiemannResearch/RH/QCRTCellCoordinateSystem.lean`

- `TrialIndex`
- `trialSpace_eq_span_nontrivial`
- `trialSpace_eq_span_range`
- `exists_trial_coefficients`
- `canonicalCoefficients`
- `canonicalCoefficients_spec`
- `cellMatrix`
- `cellTarget`
- `canonical_cell_system`
- `canonical_coefficient_energy`

### `RiemannResearch/RH/QCRTContinuousSynthesis.lean`

- `difference_synthesis_kernel`
- `difference_collocation_injective`
- `differenceCollocationEquiv`
- `difference_block_kernel_trivial`
- `canonical_increment_difference_trial_test`
- `canonical_increment_synthesis_test`
- `screenedSynthesis_mem_trial`

### `RiemannResearch/RH/QCRTPeriodicCellSystem.lean`

- `residueFraction_abs_le_one`
- `cellMatrix_eq_residue_sum`
- `gcdCell_mass_eq_residue_sum`
- `cellTarget_eq_mass`
- `cellTarget_eq_residue_sum`

### `RiemannResearch/RH/QCRTPrimePowerSourceBudget.lean`

- `lcm_coprime_admission`
- `lcm_scaled_coprime_admission`
- `actual_admission_rows`
- `actual_admission_source_sq_le`
- `prime_power_admission_source_sq_le`

### `RiemannResearch/RH/QCRTRawSourceBudget.lean`

- `sum_inverse_sq_le_zetaTwo`
- `sum_new_difference_source_sq_exact`
- `sum_new_difference_source_sq_le`

### `RiemannResearch/RH/QFullDilatedMobiusRepair.lean`

- `dilatedMobiusStep`
- `dilatedMobiusStep_mem`
- `dilatedMobiusStep_head`
- `dilatedMobiusStep_norm_sq_le`
- `dilatedMobiusStep_norm_sq_defect`
- `repair`
- `repair_mem`
- `repair_sequence`
- `sum_forward_difference`
- `repair_head_sub`
- `repair_head`
- `repair_norm_sq_exact`
- `repair_norm_sq_le_trace`
- `repair_norm_sq_le_dilation_budget`
- `reciprocalRepair`
- `reciprocalRepair_mem`
- `reciprocalRepair_physical_head`
- `reciprocalRepair_head`

### `RiemannResearch/RH/QFullHeadNullPerturbation.lean`

- `headNull`
- `headNull_mem`
- `headNull_sequence`
- `headNull_head`
- `headNull_next`
- `headNull_ne_zero`
- `headMap_headNull`
- `perturbedHeadRepair`
- `perturbedHeadRepair_rightInverse`
- `perturbedHeadRepair_mem`
- `perturbedHeadRepair_energy`
- `perturbedHeadRepair_opNorm_unbounded`

### `RiemannResearch/RH/QFullMobiusRepairConductors.lean`

- `floorDilation_atom_sum`
- `floorDilation_exactHead_atoms`
- `dilatedMobiusStep_main_conductor_le`
- `dilatedMobiusStep_final_conductor_le`
- `dilatedMobiusStep_final_conductor_le_two_head`
- `dilatedMobiusStep_mem_bounded_span`
- `repair_mem_bounded_span`

### `RiemannResearch/RH/QFullMobiusRepairRates.lean`

- `dilationBudget_eq_floorConvolution`
- `exactHead_global_log_power_energy`
- `dilationBudget_global_log_power`
- `reciprocalRepair_global_log_power_energy`
- `reciprocalRepair_global_log_power_norm`

### `RiemannResearch/RH/QFullMobiusRepairStretched.lean`

- `exactHead_global_stretched_energy`
- `dilationBudget_global_stretched`
- `reciprocalRepair_global_stretched_energy`

### `RiemannResearch/RH/QFullReciprocalHeadAsymptotic.lean`

- `reciprocal_head_numerator_tendsto`
- `reciprocal_head_projected_pairing_bound`
- `reciprocal_projected_head_norm_le_tail`
- `reciprocal_head_product_eventually_lower`
- `reciprocal_head_projected_product_eventually_lower`

### `RiemannResearch/RH/QFullReciprocalHeadCompletion.lean`

- `reciprocal_head_norm_completion`
- `reciprocal_head_energy_lower`
- `reciprocal_head_pairing_bound`

### `RiemannResearch/RH/QFullReciprocalRepairBudget.lean`

- `reciprocal_sequence_square_le_weighted`
- `reciprocal_sequence_square_summable`
- `reciprocal_sequence_square_tsum_le`
- `reciprocal_sequence_square_sum_le`
- `reciprocal_forward_difference_square_sum_le`
- `gramTrace`
- `dilationBudget`
- `gramTrace_nonneg`
- `dilationBudget_nonneg`
- `dilationBudget_sub_gramTrace`
- `gramTrace_le_dilationBudget`
- `reciprocalRepair_norm_sq_le_trace`
- `reciprocalRepair_norm_sq_le_dilationBudget`

### `RiemannResearch/RH/QFullReciprocalRepairCriterion.lean`

- `reciprocalRepair_tail_product_of_trace`
- `reciprocalRepair_tail_product_of_budget`
- `displacement_eq_zero_of_gramTrace_tail_decay`
- `riemannHypothesis_of_dilationBudget_tail_decay`

### `RiemannResearch/RH/QFullTriangularHeadMatrix.lean`

- `fixedSynthesis`
- `physicalHeadMatrix`
- `fixedSynthesis_head`
- `bounded_span_le_fixed_span`
- `fixed_span_expansion`
- `physicalHeadMatrix_mulVec_surjective`
- `physicalHeadMatrix_isUnit`
- `physicalHeadMatrix_det_ne_zero`
- `fixedSynthesis_coefficients_unique`
- `triangularRepair_unique`

### `RiemannResearch/RH/QFullTriangularMobiusRepair.lean`

- `triangularStep`
- `triangularStep_sequence`
- `triangularStep_head`
- `triangularStep_mem_bounded_span`
- `triangularRepair`
- `triangularRepair_mem_bounded_span`
- `triangularRepair_mem_legalSpan`
- `triangularRepair_head`
- `qResidue_norm_sq_le_two_div_pos`
- `atom_norm_le_factor`
- `mobius_sum_atom_norm_le`
- `triangular_compensator_norm_le`
- `growthConstant`
- `growthConstant_nonneg`
- `triangularStep_norm_le`
- `reciprocal_square_sum_le_zetaTwo`
- `triangularRepair_norm_le`
- `triangularReciprocalRepair`
- `triangularReciprocalRepair_mem`
- `triangularReciprocalRepair_physical_head`
- `triangularReciprocalRepair_head`
- `triangularReciprocalRepair_norm_le`
- `triangularReciprocalRepair_norm_le_explicit`

### `RiemannResearch/RH/QGcdCellLCMObstruction.lean`

- `lcmOddPart`
- `factorization_before_two_pow`
- `lcm_before_two_pow_decomposition`
- `lcmOddPart_coprime_two`
- `lcmOddPart_pos`
- `lcmOddPart_ge_three`
- `lcmWitness`
- `lcmWitness_norm_sq_le`
- `lcmWitness_inner_old_cell`
- `lcmWitness_revealed_norm_sq_lower`
- `lcmWitness_revealed_relative_lower`

### `RiemannResearch/RH/QGcdCellObstruction.lean`

- `residueEvent`
- `evenEvent`
- `residueMass`
- `evenResidueMass`
- `signedResidueMoment`
- `witness`
- `residueEvent_disjoint`
- `scaled_residueEvent_eq`
- `eventSequence_residue`
- `scaled_residue_periodic`
- `witness_periodic`
- `witness_zero_on_multiples`
- `scaledEvent_disjoint`
- `eventVector_inner_of_disjoint`
- `residueMass_sum_le_one`
- `residueMass_one_lower`
- `evenResidueMass_two_lower`
- `evenResidueMass_one_upper`
- `signedResidueMoment_le`
- `witness_norm_sq`
- `witness_norm_sq_le`
- `residueEvent_subset_gcdCell`
- `scaledEvent_subset_gcdCell`
- `event_inner_divisor_of_gcd_support`
- `witness_inner_old_divisor`
- `witness_inner_old_cell`
- `scaled_residue_inter_new_cell`
- `witness_inner_new_cell`
- `new_cell_subset_old_cell`
- `old_cell_mem_new_space`
- `innovation`
- `innovation_mem_new_space`
- `innovation_norm_sq`
- `witness_inner_innovation`
- `witness_revealed_norm_sq_lower`
- `witness_revealed_relative_lower`

### `RiemannResearch/RH/QGcdCellProjection.lean`

- `gcdCell_mass_pos`
- `gcdCell_inner`
- `divisor_eq_sum_gcdCells`
- `cellAverage`
- `cellAverage_mem`
- `cellAverage_inner_cell`
- `conditionalProjection_eq_cellAverage`
- `conditionalProjection_norm_sq`

### `RiemannResearch/RH/QGcdCellRefinement.lean`

- `eventSequence`
- `eventSequence_abs_le_one`
- `eventVector`
- `qSequence_eventVector`
- `eventMass`
- `eventMass_nonneg`
- `eventMass_summable`
- `eventMass_mono`
- `eventMass_empty`
- `eventMass_univ`
- `eventMass_le_one`
- `eventMass_singleton`
- `eventMass_compl`
- `eventMass_union_of_disjoint`
- `eventVector_norm_sq`
- `eventVector_inner`
- `eventVector_inner_of_subset`
- `scaledEvent`
- `eventSequence_scaledEvent_mul`
- `positiveQWeight_mul`
- `eventMass_scaledEvent`
- `gcdCell`
- `eventVector_gcdCell_eq_sum`
- `eventVector_gcdCell_mem`
- `gcdCell_mul`
- `gcdCell_mass_mul`
- `gcdCell_refinement_mass`
- `event_innovation_norm_sq`
- `event_innovation_inner_old`

### `RiemannResearch/RH/QHeadProjectedResidual.lean`

- `matching_head_finiteHead_eq`
- `matching_head_tail_norm_le`
- `matching_head_complete_pairing_bound`
- `matching_head_projected_pairing`
- `matching_head_projected_pairing_bound`
- `projected_residual_head_eq_neg_tail`
- `projected_residual_head_norm_le`

### `RiemannResearch/RH/QHeadResidualCompletion.lean`

- `matching_head_tail_pairing`
- `matching_head_residual_completion`
- `matching_head_energy_lower`
- `matching_head_pairing_bound`

### `RiemannResearch/RH/QHyperplaneCountermodel.lean`

- `alpha`
- `alpha_weighted_tsum`
- `alpha_inverseCube_tsum`
- `alpha_nonneg`
- `denominator_pos`
- `c`
- `c_pos`
- `pResidual`
- `displacement`
- `reciprocalTarget`
- `meanZero`
- `mem_meanZero`
- `pResidual_mean`
- `displacement_mem`
- `pResidual_sub_reciprocal`
- `pareto_residual_pairing`
- `paretoMeanZero`
- `mem_paretoMeanZero`
- `toPareto_mem_iff`
- `paretoMeanZero_eq_image`
- `q_projection`
- `p_fit_mem`
- `p_projection`
- `displacement_eq_fit_difference`
- `pResidual_physical`
- `displacement_physical`
- `displacement_ne_zero`
- `displacement_physical_abs_le`
- `reciprocalTarget_physical_decay`
- `matched_energy`
- `pareto_displacement_ne_zero`
- `target_mean_pos`
- `target_mean_formula`

### `RiemannResearch/RH/QHyperplaneFiniteDensity.lean`

- `meanAnchor`
- `first_head_ne_zero`
- `meanAnchor_mean`
- `meanAnchor_supported`
- `centeredHead`
- `centeredHead_mem`
- `centeredHead_supported`
- `centeredHead_tendsto`
- `finite_support_meanZero_dense`

### `RiemannResearch/RH/QHyperplaneFiniteLimit.lean`

- `blockRepair_product_sq`
- `quadratic_blockRepair_product_tendsto`
- `quadratic_countermodel_positive_product_limit`
- `finite_countermodel_certificate`

### `RiemannResearch/RH/QHyperplaneFiniteRepairs.lean`

- `finiteHead_eq_self_of_supported`
- `finiteHead_nested_of_le`
- `finiteHead_outer_of_le`
- `blockTail`
- `blockRepair`
- `blockTail_supported`
- `blockTail_ne_zero`
- `blockTail_norm_sq_pos`
- `blockTail_mean`
- `blockRepair_mem`
- `blockRepair_head`
- `blockRepair_supported`
- `blockRepair_raw_completion`
- `blockRepair_energy`
- `blockRepair_completion`

### `RiemannResearch/RH/QHyperplaneRepairs.lean`

- `residualTail`
- `headMean`
- `tailRepair`
- `qOne_coordinate_ne_zero`
- `residualTail_ne_zero`
- `residualTail_norm_sq_pos`
- `residualTail_mean`
- `tailRepair_mem`
- `tailRepair_head`
- `tailRepair_energy`
- `tailRepair_completion`
- `tailRepair_unique`
- `residualTail_tendsto`
- `headMean_tendsto`
- `tailRepair_product_sq`
- `tailRepair_product_tendsto`
- `countermodel_positive_product_limit`

### `RiemannResearch/RH/QHyperplaneTailMass.lean`

- `qOne_coordinate_sq`
- `residualTail_mass`
- `qWeight_pareto_comparison`
- `residualTail_mass_lower`
- `residualTail_mass_upper`
- `quadratic_tail_mass_ratio_bound`
- `quadratic_tail_mass_ratio_tendsto`
- `blockTail_mass`
- `quadratic_block_mass_ratio_tendsto`

### `RiemannResearch/RH/QMatchedFiniteProjection.lean`

- `qDictionary`
- `pDictionary`
- `qDictionary_independent`
- `pDictionary_independent`
- `qSpace`
- `pSpace`
- `qCoefficients`
- `pCoefficients`
- `qFit`
- `pFitPhysical`
- `toPareto_synthesis`
- `qFit_eq_projection`
- `pFit_eq_projection`
- `rawGram`
- `rawMean`
- `paretoGram`
- `paretoMean`
- `rawGram_posDef`
- `rawInverse`
- `rawInverse_normal`
- `rawInverse_posDef`
- `rawInverse_symmetric`
- `raw_projection_normal`
- `qCoefficients_normal`
- `pCoefficients_normal`
- `displacementCoefficients`
- `displacement`
- `reciprocalTarget`
- `projectionCoefficients`
- `displacement_synthesis`
- `toPareto_displacement_synthesis`
- `reciprocal_projection_synthesis`
- `projectionCoefficients_normal`
- `scaled_dictionary_quadratic`
- `rawGram_quadratic`
- `paretoGram_quadratic`
- `rawReciprocalGram`
- `reciprocalTarget_synthesis`
- `displacement_raw_norm`
- `displacement_pareto_norm`
- `reciprocalTarget_raw_norm`
- `reciprocalCross`
- `projected_target_energy`
- `qSequence_synthesis`
- `residual`
- `residual_physical`
- `reciprocalTarget_physical`

### `RiemannResearch/RH/QMatchedFullHeadRepair.lean`

- `physicalHeadMatrix`
- `reciprocalHeadDiagonal`
- `physicalHead_synthesis`
- `reciprocalTarget_head_matrix`
- `fullHead_coefficients_injective`
- `fullHeadRepairCoefficients`
- `fullHeadRepair`
- `fullHeadRepair_head`
- `trial_synthesis`
- `fullHeadRepair_unique`
- `fullHeadRepair_norm_completion`
- `fullHeadRepair_error_completion`

### `RiemannResearch/RH/QPeriodicCertifiedWeights.lean`

- `rawResidueSquareWeight`
- `rawResidueSquareWeight_eq_normalized`
- `rawResidueSquareWeight_prefix_exact`
- `rawResidueSquareInterval`
- `rawResidueSquareInterval_contains`
- `rawResidueSquareWeight_one_one`
- `zetaTwoInterval_contains`
- `residueSquareInterval`
- `residueSquareInterval_contains`
- `rawResidueSquareInterval_thirty_two_normalizer_pos`
- `zetaTwo_reciprocal_review_interval`

### `RiemannResearch/RH/QPeriodicParetoGram.lean`

- `rationalResidue`
- `rationalResidue_cast`
- `residue_bound`
- `paretoGram_eq_weighted`
- `paretoMean_eq_weighted`
- `paretoGramInterval`
- `paretoGramInterval_contains`
- `paretoMeanInterval`
- `paretoMeanInterval_contains`

### `RiemannResearch/RH/QPeriodicReciprocalGram.lean`

- `reciprocal_inner_eq_periodic`
- `reciprocalGram_eq_weighted`
- `reciprocalGramInterval`
- `reciprocalGramInterval_contains`

### `RiemannResearch/RH/QPrimePowerCellInnovations.lean`

- `oldCell`
- `newCell`
- `splitRatio`
- `cellInnovation`
- `innovationWeight`
- `newCell_mass`
- `newCell_subset_oldCell`
- `oldCell_mem`
- `cellInnovation_norm_sq`
- `cellInnovation_inner_old_divisor`
- `cellInnovation_inner_old`
- `cellInnovation_inner`
- `innovationWeight_pos`
- `new_divisor_shape`
- `new_divisor_eq_sum_cells`
- `cellInnovation_mem_new`
- `innovationProjection`
- `innovationProjection_mem_new`
- `innovationProjection_inner_old`
- `innovationProjection_inner_innovation`
- `innovationProjection_inner_newCell`
- `conditionalProjection_eq_innovations_of_rows`
- `innovationProjection_norm_sq`
- `prime_power_revealed_parseval`
- `canonical_prime_power_revealed_parseval`

### `RiemannResearch/RH/QReciprocalSpectralGeometry.lean`

- `rawGram`
- `rawGram_isHermitian`
- `castMatrix`
- `castMatrix_mul`
- `castMatrix_transpose`
- `castMatrix_diagonal`
- `physicalHeadMatrix`
- `operatorGram`
- `operatorGram_isHermitian`
- `repairVector`
- `repairLinear`
- `repairCLM`
- `repairCLM_apply`
- `repairVector_site`
- `repairVector_head`
- `qSequence_normalized_coordinate`
- `repairVector_reciprocal_head`
- `repairVector_norm_sq`
- `repairVector_norm_sq_le_of_posDef_shift`
- `repairCLM_norm_le_of_posDef_shift`
- `repairCLM_norm_lower_of_witness`

### `RiemannResearch/RH/QResidueGramCertificates.lean`

- `rationalResidue`
- `rationalResidue_cast`
- `rawGram_pairing_eq`
- `rawMean_pairing_eq`
- `rawGramInterval`
- `rawGramInterval_contains`
- `rawMeanInterval`
- `rawMeanInterval_contains`

### `RiemannResearch/RH/QTriangularMobiusCoefficients.lean`

- `mobiusHeadCoefficient`
- `reciprocalHeadSlope`
- `mobiusHeadCoefficient_eq`
- `reciprocalHeadSlope_reindex`
- `reciprocalHeadSlope_abs_le`
- `inverse_square_Icc_sum_le`
- `forwardDifference_weighted_sum_le`
- `reciprocalHeadSlope_abs_le_difference_energy`
- `floor_sqrt_weight_le`
- `mobiusHeadCoefficient_sqrt_mass_le`
- `mobiusHeadCoefficient_sqrt_mass_le_difference_energy`
- `triangularRepair_mobius_normal_form`
- `triangularRepair_sequence_full`

## Extensions of existing modules

### `RiemannResearch/Analysis/InverseSquareTailCertificates.lean`

- `complete_tail_ten_bounds`
- `finite_lowerTen`
- `finite_upperNine`
- `lowerTen`
- `lowerTenNumerator`
- `lowerTen_step`
- `lowerTen_tendsto_zero`
- `scaled_complete_tail_ten_bounds`
- `upperNine`
- `upperNineNumerator`
- `upperNine_step`
- `upperNine_tendsto_zero`

### `RiemannResearch/Analysis/PositiveLogVariation.lean`

- `log_ratio_tendsto_zero_of_positiveRelativeVariation`
- `positiveRelativeVariation`
- `positiveRelativeVariation_nonneg`
- `positiveVariation_log_one_add_le_relative`
- `positiveVariation_ratio_tendsto_zero_of_relative`
- `positive_log_increment_le_relative`

### `RiemannResearch/RH/QCRTPositiveLogVariation.lean`

- `canonicalEnergy_pos`
- `canonicalRelativeVariation`
- `riemannHypothesis_of_positive_relative_variation`

### `RiemannResearch/RH/PrimeLogSummability.lean`



Moved declaration: `prime_dyadic_card_mul_le`.
