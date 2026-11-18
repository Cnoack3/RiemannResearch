# Montgomery horizontal Bessel theorem catalog

Date: November 10, 2026.
Starting revision: `29fa256722998cc6fa8b9b0f6682fd7788ffae85`.
Companion research ledger: [MontgomeryHorizontalBesselResearch20261110.md](MontgomeryHorizontalBesselResearch20261110.md).

There are 36 new theorem declarations and 8 definitions in four focused
modules, all under `RiemannResearch.Analysis`.
The analytic upper bounds are unconditional. The four convergence/transfer
results below retain explicit, unresolved asymptotic hypotheses.

| Module | Namespace | Main declaration | Scope and assumptions |
|---|---|---|---|
| `Analysis/MontgomeryResolventDifference.lean` | `MontgomeryResolventDifference` | `inverse_mixed_difference` | Exact four-term inverse difference; only nonzero denominator assumptions. |
| Same | Same | `differenceKernel_bound` | \(\left|\Delta_{a,b}K(id)\right|\le4|ab|w(d)\), for \(|a|,|b|\le1/2\); no zeros or density premise. |
| `Analysis/MontgomeryDifferenceGram.lean` | `MontgomeryDifferenceGram` | `difference_gram` | Complete signed Gram identity for exponential differences; arbitrary finite ordinates and coefficients, including repeated ordinates. |
| Same | Same | `pairFeature_integrable`, `weightedDifference_memLp` | Integrability and L2 membership are proved. |
| Same | Same | `difference_energy_le_of_rows` | Energy bounded by \(4D\sum_i|c_i|^2a_i^2\); explicit Cauchy row bound \(D\). |
| `Analysis/MontgomeryHorizontalBessel.lean` | `MontgomeryHorizontalBessel` | `shiftedDifferenceSignal_split` | Exact signed coefficient/feature decomposition, before estimation. |
| Same | Same | `shiftedDifference_energy_le` | General-frequency squared-coefficient perturbation bound, under a finite row bound. |
| Same | Same | `actual_shiftedDifferenceSignal` | Identification with the actual cosh correction, using actual reflection and every multiplicity. |
| Same | Same | `exists_defectIntegral_le_budget` | Actual unnormalized energy \(\le C\log(T+3)B_T(u)\), \(T\ge0\). Actual local zero counts discharge the row-bound hypothesis. |
| Same | Same | `exists_horizontalDefect_le_budget` | Actual normalized defect \(\mathcal H_T(\alpha)\le C B_T(\alpha\log T)/T\), \(T\ge9\), all real \(\alpha\). |
| Same | Same | `horizontalBudget_le_exponentialMoment` | \(B_T(u)\le(1+v^2)\sum_i\delta_i^2e^{2v|\delta_i|}\), for \(|u|\le v\). |
| Same | Same | `exists_horizontalDefect_le_exponentialMoment` | Uniform actual bound on \(|\alpha|\le A\); the full exponential weights remain. |
| `Analysis/MontgomeryHorizontalLimit.lean` | `MontgomeryHorizontalBessel` | `horizontalDefect_tendsto_zero` | **Conditional:** \(B_T(\alpha(T)\log T)/T\to0\). |
| Same | Same | `sqrt_horizontal_difference_tendsto_zero` | **Conditional:** same budget decay; compares raw/complex square roots. |
| Same | Same | `raw_limit_of_budget` | **Conditional:** budget decay and a nonnegative finite complex form-factor limit. |
| Same | Same | `raw_limit_of_exponentialMoment` | **Conditional:** eventually bounded frequencies, weighted moment decay, and a complex form-factor limit. |

## Horizontal energy and shrinking Montgomery frequencies

Write $E(T)$ for the total horizontal energy, $r(T)=(\log\log T)^2/\log T$,
and $u=\alpha\log T$. Every zero in the cutoff carries its analytic multiplicity.

| Lean declaration | Result |
|---|---|
| `horizontalEnergy_eq_reflected_pair_add` | A reflected off-line pair contributes exactly $2m(\rho)(\Re\rho-1/2)^2$, with the full sum over the remaining zeros. |
| `riemannHypothesis_iff_cofinal_horizontalEnergy_small` | RH is equivalent to arbitrarily small unnormalized $E(T)$ at arbitrarily large heights. |
| `horizontalEnergy_add_const_div_height_isBigO` | $(E(T)+c)/T=O(r(T))$ for every fixed real $c$. |
| `horizontalBudget_eq_coshMass` | $B_T(u)=E(T)+M_T(2u)-2M_T(u)$, where $M_T$ sums $\cosh(u(\beta-1/2))-1$. |
| `horizontalBudget_le_horizontalEnergy` | $B_T(u)\le(4\cosh u-3)E(T)$ at every height. |
| `horizontalBudget_le_of_strictTail` | If the two-sided tail is bounded by $M e^{-qt}$, then $B_T(u)\le 8M(1+u^2)/q^2$ for $|u|\le q/4$ and $q>0$. |
| `eventually_horizontalBudget_loglog_band` | Uniformly for $|u|\le \log T/(32\log\log T)$, one has $B_T(u)/T\ll(1+u^2)r(T)$. |
| `horizontalBudget_div_height_tendsto_zero_of_loglog`, `sqrt_formFactor_difference_tendsto_zero_of_loglog` | If $u(T)^2r(T)\to0$, then $B_T(u(T))/T\to0$ and the square-root form factors agree up to $o(1)$. Both implications are unconditional for these frequencies. |
| `eventually_sqrt_formFactor_difference_loglog_band` | Unconditionally, the absolute difference of the two square roots is $O(\sqrt{(1+u^2)r(T)})$ uniformly throughout $|u|\le \log T/(32\log\log T)$. |
| `sharpFormFactor_sub_main_eq_pair_remainder` | Exact normalization of the signed complex pair remainder with $x=T^\alpha$ and $D=T\log T/(2\pi)$, for $T>1$. |
| `sharpFormFactor_bound_of_bgstb`, `correctedComplexFormFactorEstimate_of_bgstb` | The first line of BGSTB (3.5) yields normalized error $O(T^{-2\alpha}+1/\sqrt{\log T})$ uniformly on $[0,1]$. This implies the existing estimate. Both declarations take the physical pair-sum estimate as a premise. |
| `transition_spike` | The normalized spike is exactly $e^{-c}$ at $\alpha_c=(\log\log T+c)/(2\log T)$ for $T>1$. |
| `sharp_transition_limit_of_corrected_complex_estimate`, `raw_transition_limit_of_corrected_complex_estimate` | With the normalized complex estimate, each statistic tends to $e^{-c}$ for fixed $c$. |
| `raw_transition_uniform_rate_of_corrected_complex_estimate` | With the same input, the raw statistic differs from $e^{-c}$ by $O_A((\log\log T)^2/\sqrt{\log T})$ uniformly for $|c|\le A$. |

[RH energy criterion](RH/HorizontalEnergyCriterion.lean) · [Unconditional transfer](Analysis/MontgomeryLoglogTransfer.lean) · [Transition and analytic hypothesis](Analysis/MontgomeryTransitionFrequency.lean) · [Corrected positive-cutoff estimate, v3, equation (3.5)](https://arxiv.org/html/2501.14545v3#S3.E5)

## Prime mean-square terms and critical-line proportions

Write $D=T\log T/(2\pi)$, $N=N(T)$ and $C(T)=\sum_\gamma H_T(\gamma)^2$, where $H_T(\gamma)$ counts every zero occurrence at ordinate $\gamma$. Write $S(T)$ for the count of simultaneously simple critical-line zeros. All three counts use $0<\gamma\le T$.

| Declaration | Result and assumptions |
|---|---|
| `log_mean_square_eq`, `log_mean_square_error_le` | For $T\ge2$ the logarithmic term $M_1$ has error at most $3T\log T/x^2$. The exact antiderivative retains both endpoints. |
| `log_phase_integral_parts`, `norm_log_phase_integral_le` | Exact signed integration by parts and the bound $2\log(T+2)/\log n$ for the individual frequency $n>1$. |
| `crossIntegral_eq_series`, `norm_crossIntegral_le` | The full $A_1\overline{A_2}$ cross integral has an absolutely convergent signed von Mangoldt expansion. Its modulus is at most $(2\log(T+2)/\log 2)\sum_{n\ge2}\Lambda(n)/n^{3/2}$ uniformly in $x>0$. |
| `twice_count_le_simpleCriticalCount_add_collision`, `density_one_of_collision_limit` | Unconditionally $2N\le S(T)+C(T)$. The ES1 limit $C(T)/D\to1$ implies $S(T)/N\to1$ and $N_0(T)/N\to1$. |
| `fejerFormFactor_eq_kernelEnergy`, `collision_div_main_le_fejerFormFactor` | The triangular integral of the raw form factor is exactly the normalized Cauchy-weighted sinc-squared sum. Every equal-ordinate pair contributes $1/D$. |
| `fejer_model_value`, `simpleCritical_proportion_of_fejer_limit` | The full Fourier model gives $1+1/(3R^2)$ at radius $R\ge1$. Any one fixed triangular limit $M$ gives every eventual lower proportion strictly below $2-M$. |
| `collision_limit_of_fejer_upper`, `density_one_of_rawFormFactorTestLimit` | One-sided triangular bounds arbitrarily close to one suffice for ES1. The raw compact-test Fourier law implies density one of simple critical-line zeros, without RH. |
| `physicalTriangle_eq_collision_add_positive_gaps`, `integral_sinc_sq_pi_Ioi` | The physical triangle is $R C(T)/D+2\int_0^R P_T(u)\,du$, where $P_T$ counts strictly positive unfolded gaps divided by $D$. The missing sine-kernel mass on the positive half-line is exactly $1/2$. |
| `shrinking_positive_gap_limit`, `density_one_of_positiveGapPCC` | The classical strict positive-gap PCC alone gives ES2 on every shrinking unfolded window. PCC together with the separate short-window second-moment upper bound gives ES1 and density one of simple critical-line zeros. |

A fixed Fourier test radius reaches frequencies of order one and higher. The audited transition frequency tends to zero and provides a different test. In the classical counting formulation the conjecture omits all equal ordinates. The short-window mean-square estimate recovers their total through the triangle identity. Goldston, Lee, Schettler and Suriajaya prove the required estimate without RH in Propositions 1 and 2 and deduce the density conclusion from PCC. [Primary paper](https://doi.org/10.1112/mtk.70127) · [Positive-gap proof](https://arxiv.org/html/2503.15449v2#S3)

[Logarithmic mean square](Analysis/MontgomeryLogMeanSquare.lean) · [Oscillatory integral](Analysis/MontgomeryLogPhaseIntegral.lean) · [Prime cross integral](Analysis/MontgomeryPrimeCrossIntegral.lean) · [Critical-line counts](Analysis/ActualZeroCollisionDensity.lean) · [Raw Fourier tests](Analysis/MontgomeryFejerDensity.lean) · [Strict positive gaps](Analysis/MontgomeryPositiveGapDensity.lean)

## Central Fourier mass and the analytic diagonal

The finite certificates and signed gap identity formalize Sections 3–5 of the
user-provided note `Montgomery_Pair_Correlation_Without_RH.md`.
The core estimate formalizes Section 2. Write $D=T\log(T)/(2\pi)$,
$C$ for the equal-ordinate count, and $A=\sum_\rho m(\rho)^2$ for the
analytic diagonal.

| Declaration | Result and assumptions |
|---|---|
| [`eventually_raw_central_peak_L1`](Analysis/MontgomeryCentralPeak.lean), `raw_central_test_tendsto_value` | Under `BGSTBPositiveCutoffEstimate`, the rescaled raw profile extended by zero has full-line L1 error $O(\log\log T/\log T)$ from $e^{-2|u|}$. The corresponding Fourier core contributes $f(0)$ to each continuous test. |
| [`density_one_of_fejer_outside_central_upper`](Analysis/MontgomeryCentralPeak.lean) | Under the BGSTB input, one-sided upper bounds on the part outside the core imply simple-critical density one. The full Fourier prediction would give the complementary Fejér value $1-1/R+1/(3R^2)$ for fixed $R\ge1$. |
| [`mul_fejerCentralContribution_eq_mass_sub_moment`](Analysis/MontgomeryFejerCoreUniform.lean), `eventually_fejer_central_error` | The exact core uses its first absolute Fourier moment. Under BGSTB, the approximation by $1/R$ has error $O(b_T/R)$, uniformly for $R\ge1$, with $b_T=\log\log T/\log T$. |
| [`eventually_outside_fejer_critical_line_iff`](Analysis/MontgomeryFejerCoreUniform.lean) | Under BGSTB, with the explicit resolving radius and at most one quarter of a pair of core error after multiplication by $D$, the unnormalized outside statistic with $D/R$ restored has a strict $3/2$ threshold for criticality. |
| [`eventually_positive_fourier_shoulder_mass_bound`](Analysis/MontgomeryFourierShoulder.lean), `positive_fourier_shoulder_mass_tendsto_zero` | Under BGSTB, the raw Fourier mass between $b_T$ and $(\log T)^{-1/2}$ is $O((1+(\log\log T)^2)/\sqrt{\log T})$ and tends to zero. Evenness gives the negative shoulder. |
| [`eventually_positive_fourier_band_mass_le`](Analysis/MontgomeryExtendedFourierShoulder.lean), `positive_extended_shoulder_mass_tendsto_zero`, `density_one_of_fejer_outside_extended_upper` | **Conditional research reduction.** BGSTB (3.5) and the repository's horizontal comparison give a cubic integrated error and negligible shoulder mass through $L^{-1/3}/(1+\log L)$. The exact decomposition and its uniform Fejér error allow the complementary upper test to start there. The internal BGSTB provider and the actual complementary bound remain open. |
| [`analyticPairCount_eq_sum_sq`](Analysis/ActualZeroAnalyticDiagonal.lean), `collision_eq_analytic_add_distinctZeroCollision` | Exact analytic diagonal and equal-ordinate decomposition. The distinct-zero term bounds the off-line occurrence count. |
| [`normalized_fejer_sub_analytic_eq`](Analysis/MontgomeryFejerCertificate.lean), `cofinal_fejer_critical_line_iff_RH` | The adjusted Fejér energy is the distinct-zero equal-height count plus the full nonnegative different-height remainder. The strict two-pair threshold along cofinal cutoffs is equivalent to Mathlib's RH and permits arbitrary critical-line multiplicities. |
| [`sq_mul_fejerNonzeroGapRemainder_eq`](Analysis/MontgomeryFejerResolution.lean), `normalized_fejer_sub_analytic_in_collision_unit_interval`, `eventually_resolving_fejer_gap_lt_two_iff_RH` | The exact oscillatory Fejér remainder is controlled by its Cauchy-weighted inverse-square gap budget $K_T$. Any radius $R\ge\sqrt{1+K_T}$ resolves the unnormalized distinct-zero equal-height count to within one pair. The explicit radius gives a single test per height equivalent to RH. |
| [`iteratedFejerTriangle_eq_of_eqOn`](Analysis/MontgomeryFejerPower.lean), `normalized_fejerPower_sub_analytic_eq`, `cofinal_prescribed_fejerPower_critical_line_iff_RH` | Iterated triangular convolution uses only the band of radius $4n/\delta$ and preserves the equal-ordinate atom. Nonzero phases at least $\delta$ from zero contribute at most $N(T)^2/4^n$. A prescribed logarithmic order recovers the distinct-zero collision count in its unit interval, and the cofinal strict two-pair test is equivalent to RH. |
| [`distinct_height_excess_bound`](Analysis/OrdinateCrowding.lean), `crowded_occurrence_excess_bound`, `crowded_height_excess_bound` | Finite inequalities for the number of distinct heights and the two forms of the high-occupancy count. |
| [`collision_div_main_eq_signed_gap_deficits`](Analysis/MontgomeryIntegratedGapDensity.lean), `density_one_of_integratedGapDeficits` | Exact normalized collision count equals the sine-hole triangle plus the signed moment and integrated gap deficits. An eventual upper bound on their sum at a common fixed width for each tolerance suffices for density one. |
| [`integral_sub_gapMeshSum_bounds`](Analysis/MontgomeryGapMesh.lean), `collision_div_main_eq_signed_mesh_deficits` | The exact signed identity replaces the gap integral with a uniform left-endpoint sum and retains the entire quadrature correction. For monotone $P_T$ the error lies between zero and $(R/n)(P_T(R)-P_T(0))$. |
| [`cofinal_sampled_gap_critical_line_iff_RH`](Analysis/MontgomeryGapMesh.lean) | At any fixed positive unfolded width, sufficiently fine finite sampling gives an absolute two-pair RH certificate after subtracting the analytic diagonal. The sine-model terms cancel in the summed statistic. |
| [`centeredSampledGapStatistic_sub_collision_eq`](Analysis/MontgomeryGapPrescribedMesh.lean), `abs_centeredSampledGapStatistic_sub_collision_le`, `cofinal_prescribed_sampled_gap_critical_line_iff_RH` | Centering the two endpoint rules gives an exact signed error and a two-sided bound. **Conditional research reduction:** `ShortWindowSecondMomentUpper` supplies a fixed width $B/2$ and the prescribed mesh $\lceil(B+1)D\rceil+1$ for the cofinal one-pair threshold. The moment remains open in Lean. |
| [`density_one_of_rational_positiveGap_lower`](Analysis/MontgomeryGapMesh.lean) | One-sided pointwise lower sine-model bounds at positive rational gaps suffice for density one when paired with `ShortWindowSecondMomentUpper`. The proof needs only finitely many samples for each tolerance and chosen width. |
| [`eventually_integral_positiveGapMass_lower_of_affine`](Analysis/MontgomeryGapTailDensity.lean), `collision_limit_of_largeGapAffineLower`, `density_one_of_largeGapAffineLower` | **Conditional research reduction.** An eventual one-sided affine lower bound $P_T(u)\ge u-1/2-\varepsilon$ at each sufficiently large fixed $u$, together with the GLSS moment at arbitrarily large fixed widths, yields density one. The short-gap interval costs at most $U^2/R$ in the normalized bound. The actual affine bound and the internal moment provider remain open. |
| [`occurrenceCollision_add_two_at_fresh_height`](Analysis/MontgomeryFinitePairPerturbation.lean), `eventually_formFactorWithTwoAtHeight_sub_bound` | Adding two occurrences at a fresh common height increases the ordered collision count by four. The normalized raw Fourier perturbation is $O(T^{-1})$ uniformly in both frequency and insertion height. |

## Open providers

| Obligation | Status |
|---|---|
| Lean proof of `BGSTBPositiveCutoffEstimate` for the actual complex pair sum | Open in Lean. The authors prove it unconditionally for $(0,T]$ in §3, equation (3.5) of v3, equation (3.3) of v1/v2. The zero-box and strong density hypotheses concern other results. |
| Explicit-formula pair-sum identification (3.4), uniform prime mean square $M_2$, and the explicit-formula remainder $A_3$ | Open components for an internal proof of BGSTB (3.5). |
| `ShortWindowSecondMomentUpper` for the actual cutoff | Open in Lean. The independent analytic input follows from the published GLSS short-interval moment and boundary estimates. |
| `RawFormFactorTestLimit` or cofinal one-sided Fejér upper tests | Open for the actual raw ordinates. |
| `PositiveGapPCC` | Open for strict positive gaps in the actual zero multiset. |
| One-sided positive rational gap lower bounds or common-width sampled deficit budget | Open for the actual zeros. Either form can be used with the indicated moment or signed companion bound. |
| Absolute Fejér or sampled-gap upper bound below two beyond the analytic diagonal at cofinal cutoffs | Open and equivalent to RH. The normalized density-one bounds leave this absolute scale unresolved. |
| Actual budget or weighted-moment decay on a fixed support window | Open |
| Complex or raw form-factor asymptotic above support one | Open |
| Complete normalized gamma remainder and growing homogeneous sampling transfer | Open |
| Transition-frequency concentration and complete weak PCC | Open |
| Montgomery pair correlation conjecture | Not proved |
| Riemann Hypothesis | Not proved |

The positive all-window budget criterion is strong enough to exclude every
off-line zero; the ledger explains why it is not a globally weaker replacement
for RH. No domain-specific hypothesis is silently discharged.
