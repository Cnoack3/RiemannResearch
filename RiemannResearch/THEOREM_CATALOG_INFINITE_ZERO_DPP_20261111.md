# Infinite zero-ordinate FMZ DPP and pair-transfer catalog

Research note: [FMZ_Infinite_Zero_DPP_20261111.md](FMZ_Infinite_Zero_DPP_20261111.md).
Starting revision: 8d91c2e44fa978205f4d8b4a59a636398f4bca9d.

## Established finite and infinite constructions

* Probability/DeterminantalPairTransfer.lean:
  pairDefect_exact, IsDPP.pairDefect_bounds,
  pairMass_sub_expected_exact, IsDPP.pairMass_error_le,
  pairVacancyBudget_eq_degrees, IsDPP.pairStatistic_integrable,
  IsDPP.expected_pairStatistic, IsDPP.pairStatistic_error_le,
  IsDPP.totalVacancy_bounds, IsDPP.pairVacancyBudget_le_count.
* Probability/ZeroOrdinateInfiniteDPP.lean:
  bounded_sites_finite, selected_sites_locally_finite, enumeration_surjective,
  limitingLaw_probability, limitingLaw_isDPP, kernel_tendsto,
  inclusion_tendsto, vacancy_eq_projection_residual, limitingLaw_two_point,
  cutoffVector_coordinate, collision_projection_eq,
  collision_pair_probability_zero, ordinate_injective_ae,
  collision_vacancy_lower, zero_pair_transfer_bound.
  The ground set is all actual positive zeta zeros with analytic multiplicity.
  Neither RH nor distinct-ordinate nor Selberg assumptions are used.

## November 18 extension

Write `m(τ)` for the number of positive zero labels at ordinate `τ`, counting
analytic multiplicities and horizontally reflected companions. Write `N(T)`
for the number of labels and `D(T) = N(T) − # distinct ordinates` up to height
`T`. All finite-cutoff identities below use the actual zero occurrences.

| Lean module | Principal declarations and consequences |
| --- | --- |
| [DeterminantalWeakConvergence](Probability/DeterminantalWeakConvergence.lean) | `boolLaw_unique`, `tendsto_boolLaw_of_kernel`. Finite inclusion correlations determine the Boolean law. Entrywise convergence on a countable ground set gives weak convergence of the laws. |
| [ZeroOrdinateFiberDPP](Probability/ZeroOrdinateFiberDPP.lean) | `logarithmic_limitingKernel`, `exactly_one_per_ordinate_ae`, `inclusion_of_distinct_ordinates`, `finiteLaw_weak_tendsto`, `finite_marginal_eventually_eq_of_fiber_span`. A complete short harmonic progression yields the uniform rank-one kernel on each fibre. Different fibres choose their representatives independently. Every fixed finite marginal eventually stabilizes exactly. |
| [ZeroOrdinatePrimeDPP](Probability/ZeroOrdinatePrimeDPP.lean) | `fiberVector_mem_span_of_frequency_mesh`, `primeFrequencies_limitingKernel`, `primeFrequencies_limitingLaw`, `primeFrequencies_finite_marginal_eventually_eq`. The logarithms of primes alone yield the same full law. The prime number theorem supplies asymptotic frequency approximation. Finite-dimensional closure within each unit shell gives algebraic interpolation. |
| [ZeroOrdinateDPPSampling](Probability/ZeroOrdinateDPPSampling.lean) | `logarithmic_cutoff_vacancy`, `expected_inverse_weighted_pair`, `all_ordinate_pair_sums_ae`. Multiplicity weights reconstruct every ordinate pair statistic, including its zero-gap part, simultaneously for all heights and tests on one event of probability one. Expected logarithmic deletions equal `D(T)` exactly. |
| [ZeroOrdinateQuotientDPP](Probability/ZeroOrdinateQuotientDPP.lean) | `ordinate_inclusion_mass`, `selectedOrdinates_isDPP`, `cutoffVacancy_eq_excess_add_residual`. For every dictionary the law on represented ordinates is determinantal. Label vacancy is the unavoidable multiplicity loss plus the squared error of projecting a whole fibre. |
| [DeterminantalCardinality](Probability/DeterminantalCardinality.lean) and [DeterminantalConfiguration](Probability/DeterminantalConfiguration.lean) | The rank and trace determine the almost-sure total count and exact configuration probabilities on arbitrary countable label sets. |
| [MixedParityProjectionDPP](RH/MixedParityProjectionDPP.lean) | `entry_ratio_eq_relativeGain`, `full_probe_vacancy_eq_limitEnergy`, `full_probe_vacancy_pos_of_zero`, `full_probe_ae_iff_relativeGain_not_summable`. A shared uniform threshold couples the one-site mixed-conductor probes. Their conditional next-entry probabilities are the actual relative projection gains of the centered parity packet. Almost-sure limiting entry is a sufficient RH condition. |
| [IntegerDPPExistence](RH/IntegerDPPExistence.lean) | `integerLaw_weak_tendsto`, `limitingLaw_eq_dirac_iff_odd_carry`, `riemannHypothesis_of_integerLaw_tendsto_dirac`. The full arithmetic laws converge weakly. The limiting law is full occupation precisely when every odd doubling carry lies in the closed residue span. |
| [ZeroDPPFiniteRank](Probability/ZeroDPPFiniteRank.lean) | `finite_window_trace_identity`, `finite_window_trace_le_finrank`, `finite_feature_vacancy_lower`. A prefix of `n` features has expected deletions at least `N(T) − n`. `finiteLaw_cardinality` and `finiteLaw_full_configuration` identify the exact total rank and its determinant-weighted configurations. |
| [ZeroOrdinateDPPVisibility](Probability/ZeroOrdinateDPPVisibility.lean) | `one_le_kernel_mul_unit_count`, `exists_inverse_kernel_le_unit_log`. A label in `(n,n+1]` has inclusion probability at least the reciprocal of the actual unit-shell count, uniformly over all dictionaries. |
| [DeterminantalFiberMarks](Probability/DeterminantalFiberMarks.lean) | `IsDPP.expected_normalizedMark`, `IsDPP.normalizedMark_product_moment`. Inverse-square-root inclusion weighting reproduces the counting-measure inner product whenever one of the two marks is centred on each fibre. |
| [ZeroDPPHorizontalVariance](Analysis/ZeroDPPHorizontalVariance.lean) | `horizontalStatistic_product_moment`, `horizontal_fourier_cross_moment`, `variance_horizontalStatistic`, `eventually_variance_le_ingham`, `moving_horizontalStatistic_tail_tendsto_zero`, `riemannHypothesis_iff_cofinal_variance_small`. Reflection realizes horizontal energy as the variance under every dictionary. Ingham's estimate is uniform in the dictionary and the bounded ordinate test at scale `sqrt(T)`. |
| [ZeroDPPHorizontalReflection](Analysis/ZeroDPPHorizontalReflection.lean) | `measurePreserving_reflection`, `horizontalStatistic_reflection`, `integral_vertical_mul_horizontal_eq_zero`. Reflection fixes the complete selected ordinate set and negates the signed horizontal statistic. Every integrable mixed moment against a nonlinear vertical observation is zero. |
| [ZeroDPPHorizontalAnticoncentration](Analysis/ZeroDPPHorizontalAnticoncentration.lean) | `measurePreserving_relabel`, `linear_tail_lower_of_collision`, `persistent_tail_of_offline`, `riemannHypothesis_iff_cofinal_interval_concentration`. One off-line zero forces a fixed positive probability outside every open interval of radius its horizontal displacement, at every higher cutoff. The lower bound holds for moving dictionaries and arbitrary centres. |
| [ZeroDPPMontgomery](Analysis/ZeroDPPMontgomery.lean) | `sampledPositiveGapMass_eq_ae`, `positiveGapPCC_iff_sampled`, `riemannHypothesis_iff_cofinal_offCriticalVacancy`, `logarithmic_relativeVacancy_tendsto_zero_iff`. Relative logarithmic vacancy tends to zero exactly when simple critical copies have density one. Absolute off-critical vacancy below one cofinally is equivalent to RH. |
| [ZeroDPPWindowVariance](Analysis/ZeroDPPWindowVariance.lean) | `variance_sampledWindowCount_zero`, `sampledUnfoldedWindowVariance_eq_ae`, `pcc_and_relativeVacancy_of_sampled_variance`. `prime_ordinate_statistics_ae` simultaneously recovers the gaps, counts and translation variances using prime frequencies alone. The count of a fixed window has zero variance under label selection. Integrating the centered count over translated windows gives the actual Montgomery variance. Its rational-width sine limit implies ordinary positive-gap PCC and vanishing relative logarithmic vacancy. `logarithmic_meanWindowVacancy_iff_simpleCritical_density` identifies vanishing translated mean vacancy at any fixed positive unfolded width with density one of simple critical zeros. |
| [ZeroDPPMarkedGeneratingFunctional](Probability/ZeroDPPMarkedGeneratingFunctional.lean) | `expected_product_fiberMarks` factors the joint expectation of arbitrary real or complex marks into uniform fibre averages. `critical_representatives_probability` gives the exact product of critical-line fractions. `riemannHypothesis_iff_cofinal_hit_small` covers any moving dictionary. |
| [ZeroDPPWindowLattice](Analysis/ZeroDPPWindowLattice.lean) | `variance_eq_latticeExcess` gives Yamada's integer-count variance identity on the actual translated windows. `exists_variance_polynomial_near_zero` identifies the finite-height slope with normalized coincident pairs. `collision_limit_iff_exists_shrinking_variance_slope` characterizes the collision limit by one adaptive width. `density_one_and_vacancy_of_shrinking_window_upper` needs only a one-sided upper bound on one shrinking width. |
| [PairVacancyMoment](Analysis/PairVacancyMoment.lean) | `integral_pair_error_le_sqrt`, `integral_pair_error_le_holder`, `integral_tendsto_zero_of_square_tails`. The optimized third-moment bound and the real-exponent bound for every `p > 2` are formalized. Uniform integrability of squared counts suffices for vanishing mean vacancy to transfer the signed pair statistic. |

## Analytic obligations

The absolute concentration criterion for RH requires concentration on fixed
real intervals at arbitrarily large cutoffs. The unconditional Ingham tail
bound has a radius proportional to the square root of height. For ordinary
PCC the open input is the microscopic sine law of the actual translated
ordinate windows, or another sufficient estimate such as the signed
half-width argument-moment contrasts. Multiplicity-weighted sampling
preserves those statistics at every height.

With `θ = R − floor(R)`, the unconditional lower bound for the actual translated variance at fixed `R ≥ 0` is `θ(1−θ)` in the limit inferior. Its finite-height form has an explicit nonnegative integer-count excess. At any fixed positive unfolded width, twice the mean number of logarithmic deletions is eventually at most `V(T,R) − μ(T,R)(1−μ(T,R))`, where `μ` is the translated mean count.

For each fixed height above one, the variance at all sufficiently small
unfolded widths is exactly
`R C(T)/A(T) − R² (N(T)/A(T))²`, where `C(T)` counts ordered equal-ordinate
pairs including the diagonal and `A(T) = T log(T)/(2π)`. A positive path
`R(T) → 0` with `V(T,R(T))/R(T) ≤ 1+o(1)` would imply density one of
simple critical zeros and negligible relative logarithmic vacancy. Finding
such an upper bound is an analytic obligation. The fixed-width sine variance
remains the sufficient input for ordinary positive-gap PCC.

For the logarithmic unweighted transfer, vanishing translated mean vacancy at
one fixed positive unfolded width is equivalent to simple critical zeros having
density one. The same-family microscopic pair limit and the accompanying
count-moment estimates remain separate inputs. Published Fujii count moments
are external inputs to that approach.

## Literature

- M. Yamada, [Geometrical study of the pair distribution function in the many-body problem](https://doi.org/10.1143/PTP.25.579).
- T. Kuna, J. L. Lebowitz and E. R. Speer, [Realizability of point processes](https://arxiv.org/abs/math-ph/0612075), equations (2.7)–(2.8).
- Russell Lyons, [Determinantal probability measures](https://doi.org/10.1007/s10240-003-0016-0).
- J. B. Hough, M. Krishnapur, Y. Peres and B. Virág, [Determinantal processes and independence](https://doi.org/10.1214/154957806000000078).
- A. Soshnikov, [Determinantal random point fields](https://arxiv.org/abs/math/0002099).
- K. Ford, X. Meng and A. Zaharescu, [Simultaneous distribution of the fractional parts of Riemann zeta zeros](https://arxiv.org/abs/1511.06814).
- D. A. Goldston, J. Lee, J. Schettler and A. I. Suriajaya, [Pair correlation conjecture for the zeros of the Riemann zeta-function I](https://doi.org/10.1112/mtk.70127).
- S. Chourasiya and A. Simonič, [An explicit form of Ingham's zero density estimate](https://arxiv.org/abs/2507.15184).
- J. Arias de Reyna and B. Rodgers, [On convergence of points to limiting processes, with an application to zeta zeros](https://arxiv.org/abs/2311.13441).

## Finite symbolic checks

For the finite ordinate multiset `2, 2, 5, 9, 9, 9`, height `10`, and physical width `0 < h < 2`, direct integration over the translated windows in Wolfram gives `7h/5 − 9h²/25`. The ordered collision count is `14` and the occurrence count is `6`. For two independent uniform fibres with marks `(2+i, −3i)` and `(4, −2, i)`, explicit summation over all six choices and multiplication of the two fibre means both give `1 − i/3`.

## Lean verification

The [focused Bazel verification](https://app.buildbuddy.io/invocation/86e478cd-7d55-4e4e-9138-91fb3a68a960) imported the changed modules and used `Lean.collectAxioms` to audit all 155 declarations in the inventory. Their transitive axioms are drawn from `propext`, `Classical.choice`, and `Quot.sound`.

<details>
<summary>Public declarations added, generalized, or exposed in the November 18 extension</summary>

- [ActualZeroCollisionDensity.lean](Analysis/ActualZeroCollisionDensity.lean) — `exceptional_has_companion`.
- [PairVacancyMoment.lean](Analysis/PairVacancyMoment.lean) — `integral_pair_error_le_sqrt`, `integral_pair_error_le_square_tail`, `integral_tendsto_zero_of_square_tails`, `integral_pair_error_le_holder`.
- [ZeroDPPHorizontalAnticoncentration.lean](Analysis/ZeroDPPHorizontalAnticoncentration.lean) — `measurePreserving_relabel`, `linear_tail_lower_of_collision`, `persistent_tail_of_offline`, `riemannHypothesis_iff_cofinal_interval_concentration`.
- [ZeroDPPHorizontalReflection.lean](Analysis/ZeroDPPHorizontalReflection.lean) — `measurePreserving_reflection`, `selectedOrdinates_reflection`, `horizontalStatistic_reflection`, `integral_vertical_mul_horizontal_eq_zero`.
- [ZeroDPPHorizontalVariance.lean](Analysis/ZeroDPPHorizontalVariance.lean) — `weighted_horizontal_first_moment`, `horizontalMark_fiberCentered`, `logarithmic_horizontalStatistic`, `expected_horizontalStatistic`, `horizontalStatistic_product_moment`, `horizontal_fourier_cross_moment`, `variance_horizontalStatistic`, `eventually_variance_le_ingham`, `riemannHypothesis_iff_cofinal_variance_small`, `variance_horizontalStatistic_weighted`, `variance_horizontalStatistic_le`, `eventually_horizontalStatistic_tail`, `moving_horizontalStatistic_tail_tendsto_zero`.
- [ZeroDPPMontgomery.lean](Analysis/ZeroDPPMontgomery.lean) — `sampledPositiveGapMass_eq_ae`, `positiveGapPCC_iff_sampled`, `limitingKernel_le_half_of_collision`, `offCount_le_twice_vacancy`, `offCriticalVacancy_lt_one_iff`, `riemannHypothesis_iff_cofinal_offCriticalVacancy`, `nonsimpleCritical_count_le_twice_cutoffVacancy`, `logarithmic_cutoffVacancy_sandwich`, `logarithmic_relativeVacancy_tendsto_zero_iff`, `logarithmic_relativeVacancy_of_positiveGapPCC`.
- [ZeroDPPWindowLattice.lean](Analysis/ZeroDPPWindowLattice.lean) — `actualWindowCount_eq_card`, `windowLatticeExcess_nonneg`, `variance_eq_latticeExcess`, `eventually_unfolded_lattice_identity`, `eventually_lt_variance_of_lt_lattice`, `sampled_lattice_lower_ae`, `collision_limit_of_shrinking_window_upper`, `density_one_and_vacancy_of_shrinking_window_upper`, `twice_logarithmic_vacancy_add_count_le_collision`, `twice_mean_logarithmic_vacancy_le_window_excess`, `exists_variance_polynomial_near_zero`, `exists_shrinking_width_reading_collisions`, `collision_limit_iff_exists_shrinking_variance_slope`.
- [ZeroDPPWindowVariance.lean](Analysis/ZeroDPPWindowVariance.lean) — `sampledWindowCount_eq_ae`, `variance_sampledWindowCount_zero`, `sampledUnfoldedWindowVariance_eq_ae`, `rationalSineWindowVariance_iff_sampled`, `pcc_and_relativeVacancy_of_sampled_variance`, `integral_windowVacancy`, `eventually_meanWindowVacancy_eq`, `meanWindowVacancy_tendsto_zero_iff`, `logarithmic_meanWindowVacancy_iff_simpleCritical_density`, `prime_ordinate_statistics_ae`, `positiveGapPCC_iff_prime_sampled`, `rationalSineWindowVariance_iff_prime_sampled`.
- [DeterminantalCardinality.lean](Probability/DeterminantalCardinality.lean) — `setCount_le_of_no_embedding`, `IsDPP.expected_setCount`, `IsDPP.setCount_le_ae_of_rank`, `IsDPP.setCount_eq_ae_of_rank_trace`.
- [DeterminantalConfiguration.lean](Probability/DeterminantalConfiguration.lean) — `finset_card_le_setCount`, `set_eq_range_of_setCount_le`, `IsDPP.full_configuration_of_setCount`.
- [DeterminantalFiberMarks.lean](Probability/DeterminantalFiberMarks.lean) — `IsDPP.expected_normalizedMark`, `IsDPP.normalizedMark_product_moment`.
- [DeterminantalWeakConvergence.lean](Probability/DeterminantalWeakConvergence.lean) — `IsDPP.restrict_bool`, `boolLaw_unique`, `tendsto_boolLaw_of_kernel`.
- [ZeroDPPFiniteRank.lean](Probability/ZeroDPPFiniteRank.lean) — `kernel_eq_finite_basis_sum`, `finite_window_trace_identity`, `finite_window_trace_le_finrank`, `finiteSpace_finrank_le`, `finiteLaw_expected_count_le_features`, `finite_feature_vacancy_lower`, `finiteKernel_rank_trace`, `finiteKernel_det_zero_above_rank`, `finiteLaw_cardinality`, `finiteLaw_full_configuration`.
- [ZeroDPPMarkedGeneratingFunctional.lean](Probability/ZeroDPPMarkedGeneratingFunctional.lean) — `expected_product_fiberMarks`, `prime_expected_product_fiberMarks`, `allowed_representatives_probability`, `critical_representatives_probability`, `persistent_offCriticalHit`, `riemannHypothesis_iff_cofinal_hit_small`.
- [ZeroOrdinateDPPSampling.lean](Probability/ZeroOrdinateDPPSampling.lean) — `liftCopy_surj_below`, `ordinateFiber_liftCopy`, `ordinateFiber_card_liftCopy`, `sum_copies_by_ordinate`, `logarithmic_cutoff_vacancy`, `expected_inverse_weighted_pair`, `sum_weighted_ordinate_of_transversal`, `all_ordinate_pair_sums_ae`, `all_unweighted_ordinate_sums_ae`.
- [ZeroOrdinateDPPVisibility.lean](Probability/ZeroOrdinateDPPVisibility.lean) — `one_le_kernel_mul_unit_count`, `exists_inverse_kernel_le_unit_log`.
- [ZeroOrdinateFiberDPP.lean](Probability/ZeroOrdinateFiberDPP.lean) — `mem_ordinateFiber`, `ordinateFiber_card_pos`, `inner_coordinate_fiberVector`, `coordinate_ext`, `harmonicPhase_pow`, `harmonicPhase_re`, `harmonicPhase_im`, `exists_shell_cardinal_fourier`, `fiberVector_mem_span_of_harmonics`, `logarithmic_containsHarmonics`, `starProjection_coordinate_of_harmonics`, `limitingKernel_of_harmonics`, `logarithmic_limitingKernel`, `limitingKernel_eq_logarithmic_of_fiber_mem`, `limitingLaw_eq_logarithmic_of_fiber_mem`, `eventually_finiteKernel_row_eq_of_fiber_span`, `eventually_finiteKernel_row_eq_of_harmonics`, `inclusion_of_distinct_ordinates`, `inclusion_eq_zero_of_repeated_ordinate`, `exactly_one_per_ordinate_ae`, `selected_ordinate_image_ae`, `limitingKernel_diagonal_pos`, `finiteLaw_weak_tendsto`, `finite_marginal_eventually_eq_of_fiber_span`, `finite_marginal_eventually_eq`.
- [ZeroOrdinatePrimeDPP.lean](Probability/ZeroOrdinatePrimeDPP.lean) — `fiberVector_mem_span_of_frequency_mesh`, `prime_log_mesh_tendsto`, `fiberVector_mem_span_of_all_prime_logs`, `limitingLaw_eq_logarithmic_of_all_prime_logs`, `primeFrequencies_limitingLaw`, `primeFrequencies_limitingKernel`, `primeFrequencies_finite_marginal_eventually_eq`.
- [ZeroOrdinateQuotientDPP.lean](Probability/ZeroOrdinateQuotientDPP.lean) — `mem_ordinateLabels`, `ordinate_inclusion_mass`, `selectedOrdinates_isDPP`, `vacancy_eq_fiber_residual`, `ordinate_vacancy_eq_residual`, `cutoffVacancy_eq_excess_add_residual`, `logarithmic_cutoffVacancy_minimal`.
- [IntegerDPPExistence.lean](RH/IntegerDPPExistence.lean) — `integerLaw_weak_tendsto`, `limitingLaw_eq_dirac_iff_odd_carry`, `riemannHypothesis_of_integerLaw_tendsto_dirac`.
- [MixedParityProjectionDPP.lean](RH/MixedParityProjectionDPP.lean) — `target_pos`, `one_sub_occupancy`, `occupancy_bounds`, `occupancy_monotone`, `occupancy_tendsto`, `fullOccupancy_bounds`, `probe_isDPP`, `finite_probe_vacancy`, `entry_ratio_eq_relativeGain`, `full_probe_vacancy_eq_limitEnergy`, `full_probe_vacancy_pos_of_zero`, `full_probe_ae_iff_relativeGain_not_summable`, `riemannHypothesis_of_full_probe_ae`.

</details>

## Omitted pairs and the diagonal-restored prime projection

Fix a positive rational interval $I=[a,b]$. Each zeta zero contributes its analytic multiplicity. An ordinate class has total multiplicity $m_\gamma$, including the contributions of different zeros at that height. Set $L_T=\log T/(2\pi)$ and $\Phi_I(u)=\int_a^b(r-|u|)_+\,dr$. Normalize pair sums by $TL_T$. The prime-frequency DPP selects one label per ordinate. Its unweighted two-point statistic with all true self-pairs restored is $M_T(I)$, and $\ell_T(I)$ is the expected loss from ordered pairs of distinct labels.

* `ProjectedDistinctSpacing.prime_expectedPairMass_eq_distinct` evaluates the second determinant for every signed finite ordinate weight. The true self-pair contribution tends to $(b^2-a^2)/2$. `ZeroDPPProjectionBridge.actual_integral_eq_restored_add_loss` identifies the full width-integrated triangle energy exactly with $M_T(I)+\ell_T(I)$.
* `ZeroDPPCollisionLoss.triangleLoss` charges every coincident pair of different labels. The loss is at least $(b^2-a^2)\sum_\gamma m_\gamma(m_\gamma-1)/(2TL_T)$. The marginal-vacancy budget is between the genuine expected loss and twice that loss. `density_one_of_triangleLoss` deduces density one of simple critical-line zeros from vanishing loss at a single positive interval, for every frequency sequence.
* `ZeroDPPTriangleVacancy.interval_pair_loss_le` bounds the loss with a square root involving the third moment of the full count and the total missing-label mass. `ZeroDPPVacancyDensity.prime_triangleLoss_tendsto_zero_iff` identifies vanishing at any fixed positive interval with density one of simple critical-line zeros, given `BoundedTranslatedThirdMoment` at its upper width. The same equivalence holds for the logarithmic kernel.
* `ProjectedDistinctSpacing.actual_prime_physical_jensen` applies Jensen to the actual omitted count. `prime_missing_density_penalty` integrates the quadratic penalty on $[k,k+1]$. For the normalized number of missing labels $d_T=(N(T)-\#\{\gamma\})/(TL_T)$, the penalty is at least $k^2 d_T^2-(k+1)d_T$. This bound only needs leading second-moment information at cofinal large widths to force $d_T\to0$ when the full count has its subquadratic upper envelope.
* `ZeroDPPProjectedCriterion.primeProjectedSineLimit_iff_positiveGapPCC` compares the projected sine limit for the actual prime dictionary with ordinary positive-gap PCC, using the explicitly typed large-width upper, short-window upper and translated third-moment providers. `MontgomeryPositiveGap.integrated_window_energy_of_sine_moment` passes from actual pointwise energy limits to rational width integrals by dominated convergence.
* `ZeroDPPDilation.triangleLoss_dilate_le` shows that dilating a fixed interval gives $\ell_T(nI)\ge n^2\ell_T(I)$ for every positive integer $n$. If the projected moment converges to the sine moment on each such interval, a full-count upper excess of $o_I(n^2)$ there suffices for $\ell_T(I)\to0$. `ZeroDPPDilation.positiveGapPCC_of_projected_dilation` needs only one suitable integer dilation for each interval and error tolerance. The height limit is taken at that fixed dilation. This direction uses the positivity of the pair omission probabilities and requires no third moment.

### Published analytic inputs and their scopes

[Arias de Reyna and Rodgers, Corollary 35](https://arxiv.org/html/2311.13441v2) bounds every fixed moment of the count over $[X,2X]$ with physical width $A/\log X$. For width $b/L_T$, on dyadic pieces with $X\le T$ one may dominate by $2\pi b/\log X$. Summing their lengths and handling bounded initial heights gives the third-moment provider for the clipped cutoff count. This argument includes multiplicities.

[Goldston, Lee, Schettler and Suriajaya, Propositions 1 and 2](https://arxiv.org/html/2503.15449v2) give the large-width upper for the actual count. Put $U=r/L_T$, first take the height limit with each dilated interval fixed, then let its dilation grow. The microscopic variance correction is $O(\log(2+r))$. Its integral over $nI$ is $O_I(n\log(2+n))$, which is $o_I(n^2)$. The one-sided short-window estimate for the reverse PCC deduction is the repository's `ShortWindowSecondMomentUpper`. These number-theoretic estimates enter the formal implications as hypotheses. The remaining arithmetic limit is the distinct-ordinate sine spacing law. It would establish ordinary PCC and density one of simple critical-line zeros.
