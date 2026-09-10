# Theorem catalog

### Vanishing-damping quotient: checked components and conditional norm assembly (2026-09-10)

Source: the user-provided continuation “The vanishing-damping quotient norm is uniformly bounded,” equations (N1)–(N31), in the two-seed signed-tail handoff. This is a **partial formalization** of that argument. The unconditional uniform arithmetic norm theorem is not yet an established Lean result.

| Status | Module and declaration | Precise checked scope |
| --- | --- | --- |
| Established local declaration | `Analysis/AbelPrefixBound.lean`: `normalized_geometric_tsum_le_of_nonneg` | A nonnegative sequence with prefix sums at most `C N` has a summable geometric series and normalized Abel sum at most `C`. Exact finite summation retains its terminal term. |
| Established local declaration | `Analysis/AbelCoboundary.lean`: `orbit_average_fixed_add_coboundary` | Exact Abel identity for an invariant vector plus a coboundary, with every required series convergence hypothesis visible. |
| Established local declaration | `Analysis/AbelOrbitGrowth.lean`: `norm_orbit_average_coboundary_le_sqrt` | Physical orbit growth bounded by `C sqrt(n+1)` implies summability and the explicit bound `4 C sqrt(1-r)` for the averaged coboundary, when `1/2 ≤ r < 1`. |
| Established local declaration | `Analysis/AbelGramBound.lean`: `norm_average_sq_le` | Diagonal bound `D(j+1)` and an off-diagonal Gram majorant with prefix bound `A N` imply the full squared Abel norm bound `D+2A`. Vector convergence is derived; the exact recurrence includes every mixed term. |
| Established local declaration | `RH/DampedMobiusSeed.lean`: `dampedMobius_centered_seed_identity`, `dampedMobiusPrefix_at_zero` | Actual finite Möbius/floor/residue identities, exact compensation of any density term, and zero-damping cancellation. These do not assume or prove quantitative Mertens cancellation. |
| Established local declaration | `RH/DyadicRegularizedNorm.lean`: `mem_dyadicQuotientSubspace_iff`, `dyadicQuotientProjection_dilation_projection`, `regularizationZetaSeries_summable` | Genuine quotient projection in the actual weighted Hilbert space, fixed-adjoint characterization, exact `Q T_m Q = Q T_m`, quotient dilation bound, and positive-damping scalar Dirichlet-series convergence. |
| Established local declaration | `RH/DyadicQuotientAbel.lean`: `dyadicQuotientDilation_orbit`, `dyadicQuotientDilation_fixed_residue_two` | Actual induced integer-dilation semigroup and physical orbits; the mean vector `QR₂` is fixed. |
| Established local declaration | `RH/DyadicTailQuotient.lean`: `mem_dyadicPhysicalTail_iff`, `dyadicTailRegularizedFamily_eq_transfer`, `dyadicTailRegularizedSeriesSummable_of_base` | Constructs the actual tail spaces and quotient projections, proves their support/variational semantics and exact arithmetic transfer. Convergence of the base arithmetic series implies convergence of the concrete tail series. |
| Conditional research reduction | `RH/DyadicQuotientAbel.lean`: `dyadicStepAbelOrbit_norm_sq_le_of_gram` | The concrete step-orbit Abel bound follows from its actual diagonal/off-diagonal Gram data and their prefix bound. Those concrete analytic providers are not yet discharged. |
| Conditional research reduction | `RH/DyadicRegularizedNorm.lean`: `dyadicRegularizedNormBound_of_analytic_estimates` | For the concrete product-index Möbius regularization, projected-series summability, a uniform actual step-orbit bound, and the actual remainder estimate (N24) imply uniform base norm boundedness. All three domain-specific inputs remain explicit. |
| Conditional research reduction | `RH/DyadicTailQuotient.lean`: `dyadicTailRegularizedNormBound_of_base` | Base summability and base boundedness imply the full concrete `C d` bound with all original `X,d,ε` quantifiers. The base bound remains an explicit hypothesis; no arbitrary-projection or transfer-identity assumption remains. |

| Established local declaration | `RH/DyadicStepLogBound.lean`: `dyadicProjectedStep_odd_norm_sq_signed`, `dyadicProjectedStep_norm_sq_le_depth`, `dyadicProjectedStep_triadic_diagonal`, `dyadicStepAbelOrbit_series_summable` | Exact weighted boundary refinement and support orthogonality prove m ≤ 2^N ⇒ ‖QT_m1‖² ≤ 1+N/4, hence the concrete triadic diagonal bound D=3/2 and positive-damping step-series convergence. The negative adjacent-step difference energy is retained. Off-diagonal/prefix estimates remain Open. |
| Established local declaration | `RH/DyadicCriticalApproximation.lean`: `dyadicCriticalPacket_norm_sq_eq`, `dyadicCriticalPacket_error_norm_sq_le`, `dyadicCriticalPacket_tendsto` | Exact signed terminal energy; squared truncation error ≤ 2^(-N)‖f‖² and genuine norm convergence for every physical vector. Integer steps admit a scale-free dyadic-cutoff accuracy certificate. |
| Established local declaration | `RH/DyadicCenteredSeedRepair.lean`: `dyadicCenteredSeed_optimal_complementary_energy`, `finite_centered_dyadic_repair_error_sq` | Actual finite dyadic directions G_m=T_mR₂−R₂ have zero quotient; scalar optimization gives the exact physical complementary-energy gain. Finite signed corrections retain the complete i,j Gram form and produce actual finite two-seed legal lifts. Energy exhaustion remains Open. |
| Established local declaration | `RH/DyadicCriticalResolvent.lean`: `dyadicQuotientProjection_norm_sq_eq_criticalResolvent`, `dyadicQuotientProjection_inner_eq_criticalResolvent` | For every actual Hilbert vector, the convergent half-adjoint resolvent gives the exact quotient norm and every mixed Gram entry. No analytic provider is assumed. The specific boundary fold and uniform arithmetic estimates remain separate obligations. |
| Established local declaration | `RH/DyadicFiniteCriticalNorm.lean`: `dyadicQuotientProjection_norm_sq_of_support`, `dyadicQuotientProjection_inner_of_support` | Exact finite critical norm and mixed Gram formulas for actual physical vectors supported below a dyadic cutoff. Convergence of the kernel lift and vanishing of the terminal adjoint iterate are proved internally. This does not yet prove the full boundary fold or the uniform arithmetic estimates. |
| Established local declaration | `RH/DyadicStepMeanIdentity.lean`: `dyadicProjectedStep_sum_error_sq`, `dyadicStepFiniteAbelAverage_error_sq` | Exact signed centered Gram error, including the scalar mean defect; finite Abel truncation retains its terminal error. Infinite mean/variance identities require the actual vector series to be summable. |
| Conditional research reduction | `RH/DyadicTailRecovery.lean`: `dyadicTailProjectedTriadicClosure_eq_quotient_of_inner_limits` | Actual arithmetic summability and separating inner-product limits imply quotient density. Finite signed lifts have actual legal membership and zero head support. The inner-product limits remain Open; recovery itself uses checked closed-subspace duality. |
| Conditional research reduction | `RH/DyadicRegularizedGramAssembly.lean`: `dyadicRegularized_explicit_bounds_of_gram_and_error` | Actual off-diagonal/prefix data, arithmetic series convergence, and the actual remainder produce the same explicit constant for the base and every physical tail, retaining both convergence conclusions. The diagonal is now discharged internally with D=3/2; the remaining analytic data stay Open. |
| Established local declaration | `RH/DyadicTriadicComplementObstruction.lean`: `dyadicTriadic_complementary_energy_gap`, `dyadic_two_channel_lift_error_eq` | A positive full-space Mellin gap for the actual residue-3 seed forces positive complementary energy when quotient error is small. Exact two-channel error retains the complete signed mixed term. No zeta-zero or RH assumption. |

**Open formal providers:** the critical fold/martingale norm and its BV estimates; uniform quantitative Möbius cancellation and damping differentiation; construction and growth of the concrete seed potential; actual off-diagonal Gram and continued-fraction prefix estimates; convergence and exact identification of the projected arithmetic series; and the concrete (N24) remainder. These are missing Lean providers for the ordinary proof, not a claim that the statements are mathematically open. The concrete logarithmic diagonal is proved with D=3/2, and the damped step series converges unconditionally for positive damping. The complete operator critical norm now has a checked resolvent provider; the specific boundary fold and BV estimates remain Open. Actual weak/Mellin limits remain Open. Finite signed legal recovery and quotient density now have checked conditional providers from actual summability and scalar inner-product limits; no convex-combination algorithm is claimed.

The complete eight-module supporting check and nineteen project dependencies passed in job `job_H3BDnrCxPZVm2eNwx5awrKGwWOkal1rV` (`verified: true`, exit code 0; submitted-source SHA-256 `376022424baaf8952e72ca2f01a98601658cfdd52fdbb7cc51a5687087a389c0`). The audited endpoints use only `propext`, `Classical.choice`, and `Quot.sound`; these axiom reports do not discharge the conditional theorem's local hypotheses. The final repository checkpoint additionally validates the separated modules.

Detailed coverage and exact remaining inputs: [`RH/DyadicRegularizedNormFormalization20260910.md`](RH/DyadicRegularizedNormFormalization20260910.md). The six-module continuation is recorded in [`RH/DyadicRegularizedVerificationContinuation20260910.md`](RH/DyadicRegularizedVerificationContinuation20260910.md).

The subsequent exact-boundary/diagonal and centered-repair source check passed in `job_fz5g6EneRkvk0yBiMb1Wb3sSBt_Kat9z` (`verified: true`, exit code 0, 6.920 s; SHA-256 `def7a780ae7713d765372423c5df8c0fd3efde76391c9aa6b8a84ce72fc031b0`). The critical truncation check passed in `job_xfWXrn2br_HD9p8nj1gDWoEUYReptO1I` (`verified: true`, exit code 0, 2.918 s). Audited endpoints use only standard foundational axioms. The two norm-assembly theorem types no longer accept a diagonal-growth provider; the other substantive assumptions remain explicit. Neither unconditional (N2) nor RH is established.

### Single-conductor obstruction with a constructed nonzero signature (2026-09-09)

Source: the user-provided Nyman–Weil note, sections 10.3–10.4, especially equation (10.5). These are unconditional established results about the actual functions and Bochner integrals.

| Result | Declaration and precise scope |
| --- | --- |
| Compact smooth interpolation | `Analysis/CompactLaplaceInterpolation.lean`: `MeasureTheory.BilateralLaplace.centeredTransform_compactLaplaceSeed` constructs an actual smooth test v_s supported in [-2,2] with Mv_s(s)=1, for every complex s. Thus the required nonzero spectral signature is constructed, rather than assumed. |
| General single-conductor obstruction | `RH/NymanSingleConductorObstruction.lean`: `singleConductorCompletion_energy_lower_bound`. For any compact smooth potential u, smooth superexponential f, and actual equality L R_n u=f below Y, the actual difference has energy at least exp(Y)|M f(s)|² at every conductor-symbol zero s distinct from 1. Its L² membership and exact transform signature are derived. No zeta-zero or RH hypothesis is used. |
| Actual arithmetic-tail growth floor | `nymanCompletionTail_artificial_zero_linear_lower_bound`, `nymanCompletionTail_explicit_artificial_zero_lower_bound`: the concrete inverse-completion tails satisfy energy >= exp(a)|M(Lv)(s)|²(M+1). The latter theorem uses the literal frequencies s=1+2πik/log(n), k!=0. |
| Constructed failure of sublinear energy | `nymanCompletionTail_compactLaplaceSeed_linear_lower_bound` gives energy >= exp(-2)|s(s-1)|²(M+1) for the concrete interpolating seed. `exists_nymanCompletionTail_normalized_energy_not_tendsto_zero` proves that every n>=2 has a compact smooth seed for which energy/(M+1) does not converge to zero. The seed's nonzero signature is fully discharged. |
| Quantified divergence for a given signature | `nymanCompletionTail_energy_unbounded_of_artificial_signature` and `nymanCompletionTail_normalized_energy_not_tendsto_zero` give the corresponding general-seed consequences under an explicitly stated nonzero transform value. |

The complete isolated check succeeded in job `job_EdjW3qXuXoisnvZV2JTfeJ3O22Ak2yyF`, `verified: true`, exit code 0, 17.196 seconds. Submitted-source SHA-256: `f5596c65d61c1725df66ca9e2d8aa82c601c3a2de49341c33dded481906a3758`. It included the two new modules and their 28 dependency modules. Axiom audits for the interpolation, general completion obstruction, and constructed nonconvergence endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.

This establishes the single-conductor obstruction independently of RH. It does not establish the optimized mixed-conductor upper bound, a uniform analytic inverse for conductors 2 and 3, or RH.

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

## Two-seed approximation implies RH (9 September 2026)

The declarations below have namespace `RiemannResearch.RH.Pareto` and live in
`RH.ThresholdRiemannHypothesis`. They use the actual weighted Hilbert space,
actual zeta function, and all positive integer dilations. The converse
`RiemannHypothesis → hilbertOne ∈ hilbertLegalClosure {2, 3}` remains **Open**.

| Declaration | Established scope |
|---|---|
| `paretoMellin_zero_on_legalClosure_of_zeta` | A hypothetical zeta zero with Re(s)>1/2, s≠1 annihilates the entire closed legal space for any positive seeds. |
| `zeta_ne_zero_of_hilbertOne_mem_legalClosure` | Actual target membership excludes these zeros without an assumed NB bridge. |
| `riemannHypothesis_of_hilbertOne_mem_legalClosure` | For any positive seeds, actual target membership implies Mathlib's RH; reflection and boundary/trivial-zero issues are discharged by existing providers. |
| `riemannHypothesis_of_twoSeed_closure` | The complete 2,3 approximation-to-RH implication. This does not establish target membership or the reverse implication. |
| `legalClosure_distance_sq_lower_bound_of_zeta` | Full weighted squared distance is at least (2 Re(s)−1)/‖s‖² for every vector in the closed legal space at a hypothetical such zero. |
| `arithmeticZeroObstruction` | Discharges the previously open `ArithmeticZeroObstructionTarget`, including every finite two-seed legal vector. |


The converse now has the following proved supporting components:

| Declaration family | Module | Exact status |
|---|---|---|
| `hilbertTail_inner_scaling`, `hilbertTail_inner_pow_scaling`, `hilbertTail_inner_sub`, `hilbertTail_inner_sub_sq_le_tailEnergy`, `hilbertTailEnergy_tendsto_zero` | `RH.ThresholdJointAdjointTail` | Actual absolutely summable weighted tails, exact scaling from a fixed-adjoint equation, exact finite blocks, full tail-energy decompositions and vanishing energy. The local L² limit/rate and quantitative coordinate recovery remain Open. |
| `continuous_eq_const_of_two_irrational_periods`, `primeLogRatio_irrational`, `continuous_primeLog_periods_constant`, `continuous_twoSeed_log_periods_constant` | `RH.PrimeLogPeriodRigidity` | Unconditional dense-period rigidity for continuous profiles and its actual distinct-prime and two-seed logarithmic specializations. Constructing such a continuous profile from the adjoint-fixed Hilbert data remains Open. |
| `legalSeedSpan_positive_eq_residue_span`, `hilbertDilation_sub_mem_legalClosure`, `adjoint_sub_mem_full_orthogonal` | `RH.ThresholdHilbertCocycle` | Exact full-residue space identification and closed-Hilbert cocycle/orthogonality reduction, without RH or density hypotheses. |
| `adjoint_fixed_of_legal_orthogonal_of_full_density` | `RH.ThresholdHilbertCocycle` | **Conditional research reduction:** full positive-residue density is an explicit input. |
| `twoSeed_legalClosure_eq_top_of_full_density_of_joint_fixed_constants`, `hilbertOne_mem_twoSeed_of_full_density_of_joint_fixed_constants` | `RH.ThresholdTwoSeedConverse` | **Conditional research reduction:** full positive-residue density and two-seed adjoint rigidity are explicit inputs. Both still require actual providers before the RH-to-approximation converse can be claimed. |

See `RH/ThresholdEquivalenceProgress20260909.md` for the exact remaining
targets and the combined verification receipt.

## Gibbs contraction, legal wavelets, and arithmetic repair (9 September 2026)

Source: the chat research development and
`RH_Contracting_Evolution_and_Arithmetic_Repair_2026-09-08.md`, together with
the general component and distributed-repair notes. These declarations concern
the actual infinite Pareto Hilbert space, the actual signed legal arithmetic
generators, and full errors. They do not establish RH. See
`RH/ChatFormalizationCoverage20260909.md` for the claim-by-claim scope and open
formalization obligations.

Names in the analytic rows have prefix `RiemannResearch.RH.Pareto`.

| Declaration family | Modules | Established scope |
|---|---|---|
| `gibbsAction_pairing_symm`, `gibbs_dirichlet_identity`, `gibbs_conditional_loss_identity`, `gibbsAction_fixed_iff_constant` | `RH.ParetoGibbsOperator`, `ParetoGibbsEnergy`, `ParetoGibbsPositive` | Infinite kernel normalization, full weighted square summability, reversible positivity, exact energy losses, and constant fixed space |
| `hilbertGibbsContinuous`, `hilbertGibbsContinuous_isSelfAdjoint`, `hilbertGibbsIterate_tendsto` | `RH.ParetoGibbsHilbert`, `ParetoGibbsHilbertEnergy`, `ParetoGibbsConvergence` | Actual bounded positive self-adjoint operator and unconditional strong convergence of every iterate to the weighted mean |
| `tailBasis_inner`, `tailBasisSpan_closure`, `tailBasis_gibbs_inner` | `RH.ParetoGibbsTailBasis`, `ParetoGibbsTailMatrix`, `ParetoGibbsHankel` | Actual orthonormal basis for the mean-zero closure and exact infinite-operator matrix; these analytic basis vectors are not asserted to be legal arithmetic vectors |
| `gibbsSchurGamma_row_hasSum`, `gibbsComplementKernel_quadratic_le`, `paretoGibbsSharpGap` | `RH.ParetoGibbsSchur`, `ParetoGibbsSchurGamma`, `ParetoGibbsSchurEnergy`, `ParetoGibbsSpectralGap`; `Analysis.PositiveQuadraticNorm` | Exact Gamma row, uniform Schur estimate, and unconditional norm contraction by pi/4 on the whole mean-zero space |
| `gibbsSchur_truncation_defect_le`, `hilbertGibbs_meanZero_optimal_constant_iff`, `hilbertGibbsMeanZeroContinuous_norm` | `RH.ParetoGibbsGammaTruncation`, `ParetoGibbsGammaDefect`, `ParetoGibbsOptimality` | Explicit Gamma-weighted truncations have unbounded norms and bounded Rayleigh defects; the actual restricted operator norm is exactly pi/4. No complete spectral-set claim is inferred |
| `hilbertWaveletClosure_eq_legal`, `twoSeed_waveletClosure_eq_legal` | `RH.DilationWaveletAlgebra`, `DilationWaveletClosure` | Exact period cancellation, geometric infinite tail bounds, and equality of actual full wavelet and legal closed spaces |
| `binary_wavelet_hilbert_gram_bound`, `normalizedBinaryWavelet_adjacent_tendsto_zero`, `normalizedBinaryWavelet_no_uniformLowerRiesz` | `RH.BinaryWaveletPrimitive`, `BinaryWaveletNearbySupport`, `DilationWaveletBinaryNorm`, `DilationWaveletOffScale`, `DilationWaveletNearbyEnergy`, `DilationWaveletNoRiesz`; `Analysis.BoundedPrimitiveAbel`, `NormalizedPairObstruction` | Exact binary norm pi/(4m), full signed Abel Gram identity, off-scale and nearby-scale estimates, and failure of any positive uniform lower Riesz bound |
| `paretoMean_residue`, `paretoMean_dilationWaveletSequence`, `initialLegalMeanOne_mean` | `RH.ParetoResidueLogMean`, `GibbsLegalSeed` | General logarithmic means, binary geometric-tail constant, and an actual finite legal mean-one initial vector |
| `geometricTransform_residue_generator`, `paretoStep_energy_identity` | `RH.ParetoCyclotomicTransform`, `ParetoWaveletTransform`, `ParetoStepIsometry` | Actual scalar transforms of legal generators/wavelets and exact step-function integral isometry under weighted square summability |
| `hilbertGibbs_repair_energy`, `hilbertGibbs_repair_convergence`, `hilbertGibbs_legal_repair_iff_closure_unconditional` | `RH.ThresholdContractiveRepair`, `ParetoGibbsRepair`, `ParetoGibbsSpectralGap`; `Analysis.ContractiveRepair`, `MeanNormalization`, `ContractiveRepairClosure` | Exact mixed-energy identity; vanishing actual errors suffice without summability; existence of a legal repair orbit is equivalent to target membership in the legal closure. Existence itself remains open |
| `hilbertOne_mem_legalClosure_of_gibbs_invariance`, `riemannHypothesis_of_gibbs_invariance`, `riemannHypothesis_of_gibbs_repair` | `RH.GibbsArithmeticResearchTargets` | Conditional research reductions. Only legal Gibbs invariance/repair remains an unresolved input; the approximation-to-RH implication is supplied by `riemannHypothesis_of_twoSeed_closure`. |
| `RH.FiniteBoundaryRepair.smooth_finite_boundary_fullError_lower` | `RH.FiniteRepairTriangular`, `FiniteBoundaryRepairObstruction` | For N ordered balanced repair endpoints, the actual full-error floor is 1/[72((3/2)^N-1)^2], with genuine root-charge and slope hypotheses explicit |
| `RH.DistributedRepair.fullError_distributed_completion`, `RH.FiniteBalancedRepair.balancedFloor_mem_legalSeedSpan` | `RH.DistributedRepairCompletion`, `SmoothRepairAntichain`, `FiniteBalancedRepairSynthesis` | Every mixed/remainder/tail term is retained; explicit smooth divisibility antichains and actual finite legal synthesis under component balance |
| `RH.DivisorComponentJumpRow.componentCharge_eq_totient_jumps`, `smooth_seed_fullError_lower`, `smooth_jumpWeight` | `RH.ComponentJumpGram`, `DivisorComponentJumpRow`, `DivisorComponentNormBound`, `SmoothComponentClosedFloor`, `SmoothComponentJumpWeights` | Actual totient jump row and norm bound; full-error floor 2/[(A+4)(4B+9)] for every A,B>0 and complements coprime to 6; explicit interior and boundary weights |

**Open obligations:** construct finite legal mean-one Gibbs repairs with errors
tending to zero, and prove the RH-to-approximation converse. The forward
approximation-to-RH implication is now established. Other
unproved propositions are represented explicitly in
`GibbsArithmeticResearchTargets`, `ArithmeticMellinResearchTargets`,
`DilationWaveletAsymptoticTargets`, `GeometricDifferentialResearchTargets`, and
`ParetoGibbsSpectrumTarget`, `GeometricHilbertRealizationResearchTargets`, and
`ArithmeticFluxResearchTargets`. Defining such a `Prop` only records its statement;
it does not provide a proof. Complete spectrum, Mellin/Plancherel and zero-mode
bridges, sharp adjacent asymptotics, differential/Meixner identities, and the
remaining arithmetic network identifications are tracked in the coverage ledger.
Finite experiments are not used as hypotheses or extrapolated to convergence.


## Period-5040 gain, general component charges, and boundary-repair obstruction (8 September 2026)

These results concern actual signed two-seed generators and complete infinite
Pareto error. The exact finite certificates and obstruction identities use no RH
or numerical optimality premise. General matrix and distributed-repair research
is recorded separately; its uniform upper estimate remains open.

| Declaration family | Module | Established scope |
|---|---|---|
| `Analysis.lower_certificate_of_cross_mul`, `residue_lower_common_denominator` | `Analysis.LowerCertificateArithmetic` | Exact real bridges from signed integer lower certificates |
| `RH.TwoSeedThreshold.legalWitness5040_upper_certificate` | `RH.ThresholdSeedPowerCertificate5040` | Explicit rational witness; all 5040 residue caps and exact periodicity |
| `RH.TwoSeedThreshold.legalWitness5040_mem_legalSeedSpan`, `legalWitness5040_full_error_lt` | `RH.ThresholdSeedPowerInfinite5040` | Actual legal witness; summability and exact residue regrouping; full error <39/1000 |
| `RH.TwoSeedThreshold.conductor2520Generator_exhaustive`, `conductor2520Combination_full_error_gt` | `RH.ThresholdConductor2520DualLower` | All 68 legal generators covered and annihilated; every signed combination has full error >419/10000 |
| `RH.TwoSeedThreshold.legalWitness5040_uniform_improvement` | `RH.ThresholdSeedPowerGain` | Strict full-error gain >29/10000 over the entire period-2520 space; >149/9000 over every balanced single-boundary repair in the proved smooth-endpoint class |
| `RH.FiniteSeedComponentCharge.mobiusDifference_generator`, `componentFiniteError_exact` | `RH.FiniteSeedComponentCharge` | Actual endpoint divergence; arbitrary finite closed components; exact finite Riesz square remainder and full-error bound |
| `RH.seedEdge_dvd_component_iff`, `twoSeed_dvd_component_iff` | `RH.DivisorComponentArithmetic` | Divisor-component closure for legal edges in D*r when the complementary factor is coprime to the seed |
| `RH.divisor_moebius_signal_eq_totient_div`, `divisor_moebius_signal_pos` | `RH.DivisorComponentSignal` | Exact target charge phi(D)/D and its positivity for every D>0 |
| `RH.DivisorSeedComponentObstruction.divisorComponent_seedCombination_fullError_lower` | `RH.DivisorSeedComponentObstruction` | Explicit positive finite-norm error floor for fixed D>0, uniformly over all r coprime to 6 and all signed legal combinations in D*r |
| `RH.CoupledSeedComponentObstruction.conductor_seedCaps_four_two_coupled_fullError_lower`, `coupled_component_gram_completion` | `RH.CoupledSeedComponentObstruction` | Exact mixed-component completion; full error >=272/15927 when 32 and 27 both fail to divide the conductor |
| `RH.OneBoundaryRepair.adjacent_error_completion`, `smooth_single_boundary_fullError_lower` | `RH.OneBoundaryRepairObstruction` | Balanced actual Mobius-head floor repairs with one smooth root endpoint have full error >=1/18; all other endpoints are positive and do not divide the root endpoint; smoothness and summability discharged |

**Next research target:** jointly optimize the head and distributed component
repairs under exact charge balance, retaining every mixed and tail term. Numerical
tests favor permitting head error, but the tested sparse antichains do not beat the
established certificates. The period-15120 comparison is a useful next certificate target.
The closed-form seed-exponent bound and bounded-number repair extension are
now proved in the 9 September addition above. The full coupled-component network
and antichain convergence analysis remain research obligations. No convergence
to zero or RH is established here.

## Prime-seven gain and seed-power obstructions (8 September 2026)

The new rational witness certifies the jointly reoptimized enlargement from period
360 to 2520. Every old generator is retained; all signed coefficients and the full
infinite weighted error are included. No numerical-optimality or RH premise is used.

| Declaration family | Module | Exact scope |
|---|---|---|
| `Analysis.upper_certificate_of_cross_mul`, `residue_upper_common_denominator` | `Analysis.UpperCertificateArithmetic` | Generic denominator-clearing bridge and exact progression upper-weight formula |
| `RH.TwoSeedThreshold.conductor360Generator_exhaustive`, `conductor360Combination_full_error_gt` | `RH.ThresholdConductor360DualLower` | All 34 allowed endpoint pairs covered; every signed old combination has full error >27/625 |
| `RH.TwoSeedThreshold.legalWitness2520_upper_certificate` | `RH.ThresholdPrimeSevenCertificate2520` | Explicit rational witness, exact periodicity, all 2520 integer residue certificates, finite bound <421/10000 |
| `RH.TwoSeedThreshold.legalWitness2520_mem_legalSeedSpan`, `legalWitness2520_full_error_lt` | `RH.ThresholdPrimeSevenInfinite2520` | Actual legal span, summability, exact residue regrouping, and full infinite error <421/10000 |
| `RH.TwoSeedThreshold.legalWitness2520_uniform_improvement` | `RH.ThresholdPrimeSevenGain` | Strict improvement >11/10000 over every old period-360 combination; bounded current seed powers cannot halve the new witness error |
| `RH.PrimeDefectEnergy.finiteError_joint_completion`, `signed_seed_joint_forcedMass`, `conductor_omitting_seven_fullError_lower` | `RH.PrimeDefectEnergy` | Exact coupled signed prime-5/7 square completion; full coefficient-mass bounds; conductors omitting 7 have error at least 1/100 |
| `RH.SquarefreeConductorObstruction.conductor_seedValuations_fullError_lower`, `legalWitness360_beats_conductors_with_small_seedValuations` | `RH.SquarefreeConductorObstruction` | If 4 and 9 both fail to divide the conductor, every signed approximation has error at least 2/45; the old period-360 witness beats this entire infinite family |
| `RH.BoundedSeedConductorObstruction.conductor_seedCaps_three_two_fullError_lower` | `RH.BoundedSeedConductorObstruction` | If 16 and 27 both fail to divide the conductor, every signed approximation has error at least 2/95, independently of all other prime factors |

**Continuation completed above:** period 2520 to 5040 is certified, and the
general divisor-component functional now has a proved positive signal and exact
finite Riesz completion. The closed-form exponent bound is now proved in the
9 September addition; uniform residual capture remains a research obligation.
None of these results establishes RH.

## Signed seed constraints and certified finite gains (8 September 2026)

These are unconditional finite-space and full infinite-error results for the actual
seed-2/seed-3 generators and Pareto weights. They do not prove norm convergence or RH.
The prime-five enlargement retains arbitrary signed coefficients and the full weighted
error. The lower certificate checks all twelve period-dividing-36 generators;
an exhaustive-coverage theorem proves that every allowed seed/dilation pair
appears in this list.

| Declaration family | Module | Exact scope |
|---|---|---|
| `Analysis.periodic_square_error_bound` | `Analysis.PeriodicSquareBound` | A generic finite uniform bound for the squared error of a sequence with a positive period |
| `LinearAlgebra.weighted_error_dual_exact`, `weighted_error_lower_of_dual` | `LinearAlgebra.WeightedDualCertificate` | Generic exact weighted square identity and dual lower bound; positive weights and annihilation explicit |
| `RH.TwoSeedThreshold.legalWitness180_full_error_lt`, `legalWitness360_full_error_lt` | `RH.ThresholdPrimeFiveInfinite180`, `RH.ThresholdPrimeFiveInfinite360` | Explicit legal witnesses with full infinite squared error <47/1000 and <44/1000; summability, regrouping and tail enclosure proved |
| `RH.TwoSeedThreshold.conductor36Generator_exhaustive`, `conductor36Combination_full_error_gt` | `RH.ThresholdConductor36DualLower` | Every allowed conductor-36 generator appears among the twelve indexed generators; every indexed combination has full squared error >49/1000 |
| `RH.TwoSeedThreshold.legalWitness180_uniform_improvement`, `legalWitness360_uniform_improvement` | `RH.ThresholdPrimeFiveGain` | Strict full-error improvements exceeding 2/1000 and 5/1000 over every old combination |
| `RH.PositiveSeedCone.generator_defects_exact`, `finiteError_completion`, `positive_seed_cone_full_lower` | `RH.PositiveSeedCone` | Exact prime-five/seven defects; arbitrary nonnegative finite seed combinations have full error at least 37/1299, with summability discharged |
| `RH.PositiveSeedCone.signed_seed_primeFive_forcedMass`, `signed_seed_exists_negative_primeFive` | `RH.PositiveSeedCone` | Arbitrary signed finite combinations satisfy the prime-five square bound; error <1/52 forces a negative coefficient at dilation 5 |

The finite upper certificates live in `RH.ThresholdPrimeFiveCertificate180` and
`RH.ThresholdPrimeFiveCertificate360`. These use exact rational arithmetic, with no
numerical-optimality assumption. The positive-cone constant is sharp for the two-defect
halfspace relaxation; no attainment assertion for the actual positive cone is made.

**Open obligations:** the general arithmetic-component transport theorem, four-gcd
covariance and centered Abel tail estimate, quantitative Mellin lift obstruction, and
any scalable residual-capture estimate are research arguments or targets in the
accompanying note, not consequences claimed for this formalization.

**Completed finite target:** the jointly reoptimized enlargement from conductor
360 to 2520 is now certified above, retaining all old generators and the full error.
For asymptotic work, use cofinal periods such as `lcm(1,...,N)` so that every
positive integer dilation, including higher prime powers, eventually appears.

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

## Bounded exact interpolation and weighted CRT target (9 September 2026)

See [RH/ThresholdBoundedInterpolation.md](RH/ThresholdBoundedInterpolation.md) for the exact minimum-norm argument, capacity dichotomy, finite-head construction, all-component two-seed charge constraints, and weighted CRT Schur-complement target.

| Declaration family | Module | Exact scope / status |
|---|---|---|
| `Analysis.BoundedInterpolation.cauchySeq_of_bounded_exact_energy`, `exists_minimum_head`, `minimum_head_pythagoras`, `exists_exact_heads_tendsto_of_bounded` | `Analysis.BoundedInterpolation` | Established Hilbert-space support: actual closed-subspace projections, exact minimum-head completion, and strong convergence plus exact target error from an explicit uniform interpolation bound. |
| `Pareto.hilbertLegalClosure_of_bounded_exact_heads` | `RH.ThresholdBoundedInterpolation` | **Conditional research reduction:** uniformly bounded finite legal exact heads imply membership of the actual unit target in the genuine weighted legal closure. All positive integer dilations remain available. |

- **Open:** provide uniformly bounded full squared norms for finite legal exact interpolants, in particular for seeds {2, 3}.
- **Open:** prove that the weighted CRT Schur-complement tail energies remain uniformly bounded. The exact infinite-tail matrix assembly, its inverse, and attained minimization are now proved in `RH.ParetoExactHeadCRT`; the uniform bound is still missing.
- **Open:** assemble the RH criterion bridge in Lean. The cited classical full-residue criterion does not establish a two-seed converse.
- The finite/closed exact-head infimum equality and capacity dichotomy are proved in the research note; they are not asserted to be fully formalized by these declarations.

## Exact Pareto packets, arithmetic obstructions, and the remaining bound (9 September 2026)

See [RH/RHChatFormalization.md](RH/RHChatFormalization.md) and the preserved [research note](RH/RH_CRT_Packet_Research_2026-09-09.md). These are support results and concrete constructions, not a proof of RH.

| Declaration family | Modules | Exact scope / status |
|---|---|---|
| `ExactHeadCRT.tail_schur_completion`, `exists_inverse_tail_optimizer`, `mixed_uniform_defect` | `RH.ParetoExactHeadCRT` | Actual infinite tail weights, every mixed defect, positive Gram matrix, constructed inverse, and attained constrained minimum. |
| `nearbyDilationGram_exact`, `nearbyDilationGram_div_log_tendsto` | `RH.NearbyDilationGram`, `NearbyDilationAsymptotic`, `Analysis.PeriodicHarmonicMean` | Full infinite remainder retained; exact harmonic extraction and fixed-periodic logarithmic limit. |
| Residue gcd covariance, phi/theta identities, sharp jump completion | `RH.ResidueJumpCovariance`, `ResidueNearbyAsymptotic`, `OptimizedResiduePackets`, `OptimizedResidueHarmonic`, `OptimizedResidueIdentities`, `SmoothResidueJumpOptimality` | Exact arithmetic providers, including the sharp one-half fixed-seed coefficient. |
| Concrete Hilbert packets, dyadic substitution, logarithmic Gram/transfer limits | `RH.OptimizedResidueHilbert`, `OptimizedResidueSubstitution`, `OptimizedResidueAsymptotic`, `OptimizedCorrectionNormAsymptotic`, `OptimizedTransferAsymptotic` | Actual legal vectors, nonzero repair direction, exact vanishing remainder, closure equivalence, and full norm limits. |
| `optimizedPacketIterate_energy_telescope`, `optimizedPacketUniformBound_target_membership` | `RH.OptimizedPacketRecursion`, `ParetoPacketCoordinates`, `LinearAlgebra.OrthogonalSchurRepair` | Concrete all-N legal mean-one exact heads and complete signed energies. **Only the final membership implication assumes the open uniform bound.** |
| Complete Haar coordinates and sharp future transfer | `RH.ParetoHaarCoordinates`, `ParetoSchurTransfer`, `LinearAlgebra.SchurTransferSharpBound` | Actual isometry and reconstruction, arithmetic coefficients, causal recurrence, and attained sharp amplification. |
| Tail process identities and target-induced completeness | `RH.ParetoTailMartingale`, `ThresholdInterpolationCompleteness` | Exact covariance and mean-zero obstruction; target membership plus all integer dilations implies closure equals top. No Gaussian or independence claim. |
| Forced head charges and full arithmetic mixed energy | `RH.ExactHeadCharges`, `RoughComponentHead`, `RoughComponentExhaustion`, `ComponentHeadEnergy`, `RoughProfileCancellation` | Automatic finite component exhaustion, exact divisor inversion and profile partition, every ordered cross term, and the negative linear mixed-energy limit. |
| `fixed_prefix_norms_not_bounded` | `RH.FixedPrefixIncidence`, `SmoothHeadBoundaryFlux`, `SmoothPrefixFlow`, `SmoothPrefixDivergence` | Actual fixed original-generator prefix obstruction, with quantitative energy growth. |
| `roughDiagonalHead_div_tendsto_explicit`, `hasSum_squarefree_coprime_six` | `RH.RoughProfileBounds`, `RoughDiagonalLimit`, `RoughDiagonalEvaluation`, `NumberTheory.SquarefreeEulerSeries` | Actual dominated convergence and exact Euler-product evaluation give the full diagonal limit `6/(5*pi^2)`. |
| `arithmeticMellin_identity` | `RH.ParetoMellinFunctional`, `ParetoMellinDilation`, `ParetoMellinHolomorphic`, `ParetoResidueMellinArithmetic`, `ParetoResidueMellinContinuation`, `ArithmeticMellinIdentity` | Actual integral, continuity, dilation, Abel identity, holomorphic continuation, and finite coefficient linearity. |
| `meanOne_exactHead_tail_energy`, `finite_legal_seed_not_cyclic`, `finite_legal_seed_positive_distance_gap`, `finite_legal_seed_interpolation_unbounded` | `Analysis.AnalyticZeroPersistence`, `FiniteExponentialZeros`, `RH.ArithmeticMellinSymbolZeros`, `ParetoMellinHeadObstruction`, `FiniteSeedMellinObstruction` | Exact mean-one head/tail-error identity, nonreal arithmetic zeros, and genuine continuous Mellin separation; no unresolved identity or zero-existence providers. |

- **Open:** `Pareto.OptimizedPacketUniformBound` and the broader `UniformLegalExactHeadBound`. No proof of either is asserted.
- The forward formal bridge from two-seed closure membership to Mathlib's `RiemannHypothesis` is proved. The two-seed closure membership/uniform bound itself remains open.
- The exact Euler-product constant, automatic finite component exhaustion, and actual signed arithmetic cancellation have proved providers. Numerical experiments remain informal.

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

## RH chat: Pareto–Nyman, Green, and single-test tails (updated 9 September 2026)

Source: user-provided RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md and
the associated chat. Exact inventory, verification evidence, hypotheses, and
remaining obligations: RH/ChatFormalizationReport.md. The recorded original
publications added 39 and 41 public theorems; the latest continuation adds
40 more, alongside the additional upstream research cited below. The full
discussion remains incompletely formalized and RH remains unproved.

| Module | New scope and status |
|---|---|
| RH.ParetoNymanPointwise; RH.ParetoUniformLaw; RH.ParetoNymanNorm | Actual reciprocal-floor distribution, pointwise residue identity, full squared-error norm transfer and finiteness for finite positive-conductor combinations |
| RH.ParetoResidueMean | General residue mean log(n), actual packet mean vonMangoldt(q), prime-power and zero-mean specializations |
| RH.ParetoBinaryApproximation | Exact complete-Pareto binary quadratic and optimum 1-log(2) |
| RH.NymanInverseMobius | Actual mixed two/three synthesis forces the Möbius head; finite support and reciprocal cancellation A_M(1)=0 |
| RH.ParetoPacketGreenGram | Ramanujan increments and gcd formula; exact finite boundary term and full summable tail |
| Analysis.SubpowerTailObstruction | Two conditional obstructions for actual L² tails: subpower growth and eventual power bounds, retaining logarithmic support and fixed transform signature |
| RH.RiemannHypothesisStrip | Actual Mathlib RH iff all actual open-strip zeta zeros lie on the critical line |
| RH.SingleTestTailCriterion | Conditional theorem concluding actual RH; detector nonvanishing, tail L², support, cancellation and subpower growth remain explicit hypotheses |
| RH.ConductorBoundedReciprocal | 6 established declarations: actual symbol gap, reciprocal bound and exact convergent geometric series |
| Analysis.ConductorL2Inverse | 17 established theorems: actual Lebesgue L² translations, operator geometric inverse series, both inverse identities, norm bound n/(sqrt(n)-1) and bijectivity for n>1 |
| Analysis.ConductorL2Support | 9 established theorems: exact inverse values on full left blocks almost everywhere; a compact input has an inverse nonzero on positive-measure sets below every threshold |
| Analysis.CenteredTransformPlancherel | 4 established theorems: actual centered/Fourier convention, spectral integrability and full-line Plancherel with normalization 1/(2π), including smooth-superexponential functions |
| RH.ParetoApproximationRatio | 3 established declarations: exact bias/variance error and equivalence of two small-error properties in a scalar-closed bounded class; existence of approximations remains Open |
| RH.ParetoFiniteSchur | 20 established finite-control identities for the complete Pareto law, with explicit invertible Gram action; all-scale variance convergence remains Open |
| RH.ParetoLegalApproximationClosure | 6 established theorems: exact Hilbert norm/error identity, equivalence of legal closure with small error/noise ratio, prime-pair packet formulation, and actual RH from arbitrarily small legal noise/signal ratio using the proved Mellin bridge |
| Analysis.CountableLaplaceDetector | 10 established declarations: countable entire zeros, simultaneous real tilt, normalized compact bump, transform shift and smooth compact detection of a specified countable spectrum |
| RH.CountableTiltDetector | Established existence of a nonzero smooth compact pole-annihilating countable-spectrum detector; actual-zeta specialization is now supplied by RH.CountableZetaDetector; original whole-strip detector remains Open |
| RH.CountableZetaDetector | Standard actual-zeta zero countability and an unconditional smooth compact polar-annihilating detector for all nontrivial zeta zeros; no growth estimate asserted |
| RH.FixedZetaDetectorCriterion | 3 established theorems: properties of one fixed choice of the actual compact detector, and conditional RH/quantitative zero-free consequences. Detector existence is discharged; actual tail L², support, cancellation and growth remain explicit |
| RH.SingleZetaDetectorCriterion | Conditional research reduction to actual RH with detection only at actual strip zeros; an actual detector is supplied by RH.CountableZetaDetector. Tail L², support, cancellation and subpower growth remain explicit obligations for an arbitrary/mixed optimizer |
| RH.NymanConductorTailObstruction | Exact canonical-tail signature at conductor-multiplier zeros; linear energy floor and failure of subpower growth under a nonzero artificial-zero signature; for every fixed conductor, a genuine zeta-detecting compact potential with a positive linear tail floor is constructed |
| Analysis.ActualL2Norm; RH.ConductorDifferenceEnergy | Exact translation-difference squared-energy identity with its full remainder, reverse triangle lower bound, and actual conductor operator with strictly positive L² gap for n at least two |

The countable-spectrum smooth compact detector and its actual-zeta specialization
are established. The forward legal-approximation-to-RH implication is also
established; the RH-to-approximation converse remains Open here. The original
whole-strip infinite-convolution detector and the full classical
Nyman–Beurling equivalence remain unformalized in this development. Subpower growth and asymptotic
variance reduction for a suitable mixed family remain mathematically unproved.
The canonical one-conductor family is obstructed whenever its head has a
nonzero artificial-zero signature. A stronger universal finite-jet obstruction
for a fixed nonzero head is proved in prose in
[the conductor-tail audit](RH/NymanConductorTailObstruction.md), but its
derivative-signature and moment/projection steps remain Open in Lean.
The criterion does not identify the mixed optimizer with canonical tails.
The genuine centered Plancherel theorem does not by itself identify that
mixed family's actual transform factorization.


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
| TwoChannelCancellation.centered_energy; TwoChannelCancellation.correlation_identity; TwoChannelCancellation.correlation_fourth_power | LinearAlgebra.TwoChannelCancellation | Exact Hilbert variance/covariance identities; fourth-power cancellation under explicit centered-norm lower bounds |
| PairedAnnihilatorObstruction.no_exact_decomposition; PairedAnnihilatorObstruction.reciprocal_error_lower_bound | LinearAlgebra.PairedAnnihilatorObstruction | Conditional research reduction from explicitly quantified paired annihilators; actual arithmetic witness construction remains Open |
| summable_adjacent_arithmeticRepair_variance; summable_adjacent_arithmeticRepair_sq_norm | RH.ParetoAdjacentSummability | Unconditional full diagonal summability for every positive adjacent integer scale |
| inverseSmooth35_tsum; inverseSmooth35_shift_tsum | Analysis.Smooth35ReciprocalMass | Exact full reciprocal smooth-grid mass 15/8 and quadrant tails |
| arithmeticRepair_binary_variance_sqrt_telescope; summable_ordered_disjoint_arithmeticRepair_variance | RH.ParetoDisjointRepairSummability | Full variance bounded by 64 times the reciprocal-square-root potential drop; unconditional disjoint-interval summability |
| summable_smooth35SuccessorRepair_variance; smooth35SuccessorRepair_span_eq | RH.ParetoSmoothAdjacentSummability | Actual least-smooth replacement family has summable full variances and exactly the original algebraic span, without quantitative smooth gaps |
| exists_head_mean; mem_legal_iff_exists_budget | RH.FiniteTwoSeedHeadMean | Actual two-seed finite head and complete-mean interpolation, with algebraic budget exhaustion |
| residue_finset_coefficient; residueGramQuadratic_pos | RH.ParetoResidueGramStrict | Exact coefficient recovery, residue independence and strict positivity of the full infinite-tail Gram form |
| residue_constrained_minimum_identity; residue_constrained_minimum_strict | RH.ParetoConstrainedResidueMinimum | Exact constrained minimum and strictness under actual stationarity and constraint equations |
| budgetErrorInfimum_antitone; exact_approximation_iff_budget | RH.ParetoTwoSeedBudgetMinimum | Actual constrained budget infima and algebraic exhaustion; no vanishing-error limit asserted |
| paretoHeadMean_energy_identity; paretoHead_one_mean_zero_cost | RH.ParetoHeadMeanEnergy | Exact complete head/mean minimizer and nonnegative remainder; sharp constant-head cost |
| closedRepairProjection_tendsto_zero; infiniteRepairPivotSpan_closure; infiniteRepairPivot_summable_iff | RH.ParetoClosedRepairTails | Actual closed Hilbert tails, orthogonal pivots, completeness and strong convergence under the stated triangular hypotheses |
| infiniteRepairPivot_sharp_lower_at_anchor | RH.ParetoTailPivotEnergy | Full mean-zero pivot energy lower bound at the actual physical anchor, including sparse indexing |
| finiteRepairPivot_tendsto; finiteRepairPivot_energy_gap | RH.ParetoFinitePivotLimit | Finite pivots converge to actual infinite pivots with exact energy difference |
| originalRepairSeries_converges_iff | RH.ParetoReversePivotExpansion | Exact transformed-coefficient convergence criterion retaining the complete moving-boundary term |
| adjacentBinaryRepair_covariance; adjacentBinaryRepair_abel | RH.ParetoAdjacentRepairCalculus | Full signed covariance differences and Abel summation retaining terminal anchors |
| binaryDilation_combination_energy_le_cumulative_tail; adjacentBinaryRepair_combination_energy | RH.ParetoAdjacentKernelBounds | Exact minimum-kernel factorization and full signed Gram energy |
| CompressedMellin.cellDensity_eq; CompressedMellin.phase_difference_square | RH.ParetoCompressedMellinCosine | Exact actual cosine density and signed phase identities |
| CompressedMellin.cosineDeficit_summable; CompressedMellin.cosineMass_le_quadratic | RH.ParetoCompressedMellinSummability | Unconditional actual cosine-series convergence and full majorant |
| CompressedMellin.compressedMellinEnergy_eq; CompressedMellin.fullCosineIdentity | RH.ParetoCompressedMellinNorm | Exact complete complex-cell norm; supplies FullCosineIdentity without additional analytic hypotheses |
| CompressedMellin.actual_no_exact_decomposition; CompressedMellin.actual_reciprocal_error_obstruction | RH.ParetoMellinObstructionTargets | Conditional research reductions for actual seed closures. CosineMassAsymptotic, PhaseCenteredAnalyticProvider and ActualPairedMellinProvider remain Open |

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
