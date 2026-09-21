# Stringent conditions under failure of RH: Lean coverage

21 September 2026. Source baseline: `ed133e89c8f8b1df19ae075d301612bfb67c44ac`.

All 35 groups from the requested synthesis are mapped below. This update adds 17 modules, strengthens the existing joint obstruction, and supplies 49 new public proved declarations. It also records precise propositions for many outstanding claims. **It does not prove every statement in all 35 groups.** A definition of a proposition is not a proof, and no Open target is assumed as a project axiom.

The full historical source is preserved in [RH_NOT_RH_HISTORICAL_SOURCE_2026-09-21.md](RH_NOT_RH_HISTORICAL_SOURCE_2026-09-21.md). That source predates this Lean audit; its mathematical or historical verification language must be read using the status corrections here. The user's subsequent instruction explicitly authorized this Lean work.

## Status and verification

- **Established consequence:** a theorem with its exact stated hypotheses and a checked proof. A consequence of failure of RH does not prove that RH fails or that these joint constraints are inconsistent.
- **General theorem:** a checked geometric, analytic, or probability lemma. Any arithmetic specialization still needs all its hypotheses.
- **Conditional research reduction:** a checked implication requiring a named substantive analytic provider. Such a provider remains Open until a separate checked declaration proves it.
- **Open target:** a concrete proposition definition or an explicitly documented missing construction, with no proof asserted.

The main gain, weighted-vacancy, determinant-limit, and joint-obstruction axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`. This is separate from inspecting domain-specific hypotheses in theorem types. The final publication checkpoint audits the source and validates affected modules and reverse dependencies. No admitted proof, project axiom, or unsafe declaration is used.

## Principal additions

| Result | Exact scope | Module |
|---|---|---|
| Common obstruction | One actual zero, the same fixed projection and canonical certificate; sharp weighted-hole exponents, positive energy, exact-head tail product, reconstruction escape, exact gain sum and strict occupied-determinant separation | [RHFalseJointObstruction](./RHFalseJointObstruction.lean) |
| Exact gain budgets | Summable gains, exact infinite logarithmic budget, finite harmonic mass, exact capacity gain sum | [ResidualGainObstruction](./ResidualGainObstruction.lean) |
| Mean-one floor and repair | Variance at least E/(1-E); cofinally large repairs at every strict threshold below (1-q)sqrt(E/(1-E)); no bounded-repair assumption | [MeanOneResidualFloor](./MeanOneResidualFloor.lean), [ContractiveRepairFloor](../Analysis/ContractiveRepairFloor.lean) |
| Sharp vacancy threshold | One zero forces nonsummability of (n+1)^alpha times the actual site vacancy for every alpha >= 2 Re(rho)-1, including equality | [IntegerDPPPowerWeightedHoles](./IntegerDPPPowerWeightedHoles.lean) |
| Actual occupied determinant limit | Unconditional convergence and B >= p0(1+limitingVacancy); under not RH, B > p0 | [IntegerDPPDampedConvergence](./IntegerDPPDampedConvergence.lean) |
| Common Mellin constraints | The same limiting residual has value 1/rho at every applicable actual zero, while the projection has value zero | [ResidualMellinZeroConditions](./ResidualMellinZeroConditions.lean) |
| Hardy obstruction | A simple meromorphic pole excludes Hardy membership on every half-plane containing it; endpoint weighted-energy divergence remains Open | [ChebyshevZeroObstruction](./ChebyshevZeroObstruction.lean) |
| Source spectral mechanism | Positive limiting defect plus vanishing polarization implies persistent omitted mass and a divergent inverse first moment; arithmetic identification remains Open | [SourceSpectralObstruction](../LinearAlgebra/SourceSpectralObstruction.lean) |
| Weil and reflection | Weil implications retain both Open providers; reflection gives the correct disjunction of failed objectives; constrained window test sets are nested | [WeilFailureConditions](./WeilFailureConditions.lean), [ReflectionFailureConditions](./ReflectionFailureConditions.lean) |
| Classical supporting lemmas | Chebyshev damping monotonicity and exact transformed-zero Li geometry; classical oscillation, coefficient growth, Robin/Lagarias/Newman claims remain Open | [ClassicalArithmeticObstructions](./ClassicalArithmeticObstructions.lean), [LiCoefficientObstructions](./LiCoefficientObstructions.lean) |

## Open-target modules

- [CanonicalTailHistoricalTargets](./CanonicalTailHistoricalTargets.lean)
- [CanonicalSieveAbelTargets](./CanonicalSieveAbelTargets.lean)
- [ResidualEnergyHistoricalTargets](./ResidualEnergyHistoricalTargets.lean)
- [IntegerDPPHistoricalTargets](./IntegerDPPHistoricalTargets.lean)
- [ClassicalArithmeticObstructions](./ClassicalArithmeticObstructions.lean)
- [LiCoefficientObstructions](./LiCoefficientObstructions.lean)
- [DeBruijnNewmanObstructions](./DeBruijnNewmanObstructions.lean)
- [ResidualMellinZeroConditions](./ResidualMellinZeroConditions.lean)
- [ChebyshevZeroObstruction](./ChebyshevZeroObstruction.lean)
- [WeilFailureConditions](./WeilFailureConditions.lean)

Further gaps, including some family-specific covariance claims, higher Mellin Gram constructions, actual spectral-measure assembly, and several historical analytic proof packages, are recorded below without artificial opaque predicates claiming to formalize unspecified mathematics.

## Detailed coverage of all 35 groups

The following source-audit notes distinguish existing declarations, the new checked proof texts, and unresolved obligations. Their development-stage references to a candidate or draft identify the files integrated in this update; **Open always means unproved**. An unlocated theorem is a scoped formalization gap, not a mathematical refutation.

### Static coverage audit of stringent conditions 1–18

Inspected base: `ed133e89`, isolated workspace `ws_t_M8deMlkpyHkqmPbAaha5nt-x_V9Y45`.
This is a source/type audit, not a new build or historical verification claim.
All names below are existing declarations unless explicitly labelled candidate.
`CS` abbreviates `RiemannResearch.RH.Pareto.CoefficientStabilization`.
`TC` abbreviates `CS.TailCapacity`. Other short names are in
`RiemannResearch.RH.Pareto` unless their module indicates a generic namespace.

| Group | Checked existing source coverage | Sharper claims not yet supplied by inspected declarations |
|---|---|---|
| 1: global approximation gap | `CS.energy_tendsto`, `CS.energy_antitone`, `CS.energy_eq_limit_add` in `RH/MobiusCoefficientStabilization.lean`; `CS.not_RH_limitEnergy_pos` and `CS.residual_error_pairing` in `RH/ExactHeadResidualTail.lean`. Zero lower bound follows by specializing `legal_exact_head_residual_lower_bound` (`RH/ParetoExactHeadResidual.lean`) to N=0 and the actual closed projection. | Numerical ceiling E<0.0242446 not located as checked declaration. The exact arbitrary-legal Pythagorean split has generic projection ingredients, but should not claim the numeric certificate is newly verified. |
| 2: common first-site and constant residual | `CS.firstCoordinate_energy_identity`, `CS.firstCoordinate_energy_bounds`, `CS.firstCoordinate_nonneg`, `CS.projection_firstCoordinate_tendsto` in `RH/MobiusResidualFirstCoordinate.lean`; `CS.not_RH_first_coordinate_and_coefficient` in `RH/RHFalseTailConstraints.lean`. These give the exact stated r(1) bounds after multiplying by two. | The two-sided comparison `(1±1/√2)^2 E` for δ not found in inspected source. Need a separate projection-norm/dilation proof; it must not be claimed from r(1) bounds alone. |
| 3: mean-one variance floor | `not_RH_meanOne_variance_uniform_floor` in `RH/RHCriterionFailures.lean`; finite exact mean-normalized completion in `RH/ParetoGramMeanOptimizer.lean` (`normalizedProjection_variance`, `normalizedProjection_completion`, `normalizedProjection_minimizes`). Sharp Gibbs contraction provider `hilbertGibbs_meanZero_quadratic_le`, `paretoGibbsSharpGap` in `RH/ParetoGibbsSpectralGap.lean`. Candidate `RH/MeanOneResidualFloor.lean` proves exact lower bound E/(1-E) for every actual closed legal mean-one vector and E<1. | Equality of the infimum over **finite** legal vectors, explicit attainment/approximating mean normalization, and assembled conditional-variance floor `(1-π/4)E/(1-E)` are not proved by the candidate lower bound alone. |
| 4: bounded capacity/coercivity | `TC.tailCapacity_monotone`, `TC.tailCapacity_bounded_iff_exists_certificate` (`RH/ParetoTailCapacityDuality.lean`); `TC.tailCapacity_tendsto_canonical_energy` (`RH/CanonicalTailCapacityGeometry.lean`); `TC.not_RH_firstCoordinateTailGap_pos`, `TC.firstCoordinateTailGap_controls_all`, `TC.uniformTailCoercivity_iff_capacity_bounded` (`RH/FirstCoordinateTailGap.lean`). `TC.canonicalTailCertificate_norm_sq` gives exact `C=1/δ-2`. | Determinant-ratio formulas require the separate matrix-determinant implementation/normalization; not certified by these capacity statements alone. |
| 5: canonical certificate and strong limits | `TC.canonicalTailCertificate_isCertificate`, `TC.canonicalTailCertificate_norm_sq`, `TC.tailCertificate_energy_completion`, `TC.tailMinimum_increment` in `RH/ParetoTailCapacityDuality.lean`; `TC.tailMinimum_tendsto_canonical`, `TC.certificate_canonical_energy_split` in `RH/CanonicalTailCapacityGeometry.lean`. `tailCertificateAnnihilator_first` and `_orthogonal` in `RH/ResidueTailCertificateRegularity.lean`. | Covered at exact Hilbert/certificate level; no independent regularity assumption is required. The pointwise formula for z* is equivalent to its implemented `tailMap` definition. |
| 6: dilation orthogonality and annihilator mean | `TC.projectedPoint_orthogonal_zeroHead`, `TC.projectedPoint_inner_dilation` in `RH/CanonicalTailCapacityGeometry.lean`; scaled/unscaled conversion and exact norm scaling in `RH/TailCapacityDilationCorrection.lean` (`unscaledResidueDilation_norm_sq`). | The exact normalized F*=e1+z*/C statement and negative-mean interval for h were not located as declarations; normalization and quantitative mean bounds need actual derivations. |
| 7: primitive ℓ², non-ℓ¹, sqrt decay | `TC.not_RH_canonical_obstruction` (`RH/RHFalseTailConstraints.lean`) has same canonical certificate and simultaneous square summability / nonsummability; `anchoredSignedTail_square_tsum_le`, `signedTail_sqrt_mul_tendsto_zero` (`RH/ParetoPrimitiveRegularity.lean`). The constant-four bound is established. `anchoredSignedTail_energy_density` is used in that file, giving exact termwise weighted difference identity. | Dyadic block-mass assertions and the extra canonical pointwise bound with constant `1/(1-1/√2)` were not found. A global exact energy sum requires assembling the termwise identity with the Hilbert norm. |
| 8: both signs and partial-sum excursions | `TC.not_RH_canonical_both_signs`, `TC.not_RH_canonical_power_excursions`, `TC.not_RH_canonical_log_excursions` (`RH/RHFalseTailConstraints.lean`); `tailCertificate_not_summable_firstMoment` and `tailCertificate_both_signs_arbitrarily_far` (`RH/ResidueTailCertificateRegularity.lean`); `tailCertificate_not_summable_partialSum_div_square` (`RH/ResidueTailAdditiveCancellation.lean`). | **Separate** divergence of the positive and negative first moments is stronger than absolute divergence plus both signs infinitely often. It was not proved by the inspected declarations and must remain a gap. |
| 9: subexponential pointwise irregularity | `normalizedResidue_orthogonal_eq_zero_of_firstMoment` and first-moment/signed-tail rigidity are implemented. | No quantitative weak-L¹ density provider at every `θ<3/5` was located, hence the asserted exponential-logarithmic limsup cannot be marked checked here. Hilbert membership implies u(n)=o(n) independently, but the exact theorem was not located. |
| 10: noncommuting sieve/Abel limits | Exact finite boundary algebra in `RH/ParetoFiniteSieveBoundary.lean` (`pareto_finite_signed_sieve_boundary`, `LegalAnnihilator.finite_signed_sieve_boundary`); quantitative boundary kernels in `RH/ParetoSieveBoundaryNorm.lean`; explicit sieve-boundary energy divergence in `RH/ParetoSieveBoundaryGrowth.lean`. | The particular two iterated Abel/sieve limits K_{m,y}(t) in the prose are not implemented by these finite boundary theorems. Need their actual Abel-limit and growing-prime-product providers. |
| 11: exact-head energy barriers | `legal_exact_head_residual_lower_bound` (`RH/ParetoExactHeadResidual.lean`) proves the exact all-legal error lower bound `a(N+1)^a/|ρ|²`, with arbitrary closure members. `paretoMellin_exact_head_lower_bound` (`RH/ParetoMellinHeadObstruction.lean`) keeps the head and full oscillatory factor; `TwoSeedExactHeadEnergy.energy_exact_lower_of_zeta` (`RH/RHFalseTailConstraints.lean`) passes this to the actual infimum. `legal_exactHead_energy_tendsto_atTop_of_zeta` and subpower criterion in `RH/ParetoLegalHeadGrowth.lean`; actual monotone energy divergence in `RH/RHFalseTailConstraints.lean`. | The multiplicity improvement `N^a(log N)^(2m-2)` was not found as a checked provider; do not infer it solely from the simple-zero evaluation inequality. |
| 12: residual tail | `CS.residualTailEnergy_eq_weighted`, `CS.residualTailEnergy_tendsto_zero`, `CS.residual_tail_product_lower`, `CS.not_RH_exact_head_errors_tendsto_atTop` in `RH/ExactHeadResidualTail.lean` provide exact weighted tail, decay, product lower bound and divergence for every exact-head legal family. | The cofinal upper construction `Δ_N≤4N+1/(N+1)` and resulting `liminf N t_N≥E²/4` were not found. Positivity of each tail is a short additional consequence once finite exact-head existence is connected to this closedSpace; existing finite two-seed head existence is in `RH/TwoSeedExactHeadEnergy.lean`. |
| 13: mean-one exact heads | Exact complete tail identity `meanOne_exactHead_tail_energy` in `RH/ParetoMellinHeadObstruction.lean`; exact conditional dual head/tail obstructions in `RH/ConditionalMeanHeadObstruction.lean` and `RH/ConditionalMeanTailObstruction.lean`. | The sharper constant `a/|ρ-1|²`, conditional tail-variance exponent `2β`, and asserted covariance growth for actual Schur minimizers require additional centering and minimizer-normal-equation proofs; not located as declarations. |
| 14: finite total gains | Existing `not_RH_legalWalk_relativeGain_summable` (`RH/RHCriterionFailures.lean`) covers every legal walk, even nonexhaustive. `TC.not_RH_accumulated_capacity_gain` (`RH/RHFalseTailConstraints.lean`) gives exact accumulated capacity limit. Candidate `RH/ResidualGainObstruction.lean` supplies exact infinite logarithmic gain HasSum budget, tsum comparison, finite harmonic mass of scales with gain≥c/(n+1), and exact capacity gain HasSum. Root verified this candidate in an isolated batch. | The separate reciprocal-increment HasSum budget was not included. All projected/screened gains must be linked to the actual gain domination before transferring the summability result. |
| 15: quantitative recurrent repair | `not_RH_not_contractive_repair_orbit`, `not_RH_not_Gibbs_repair_orbit` (`RH/RHCriterionFailures.lean`) already rule out vanishing repair. Candidate `Analysis/ContractiveRepairFloor.lean` proves cofinal strict repair threshold by finite descent; root verified generic module. Candidate `RH/MeanOneResidualFloor.lean` specializes to actual closed legal space and sharp threshold `(1-q)√(E/(1-E))`, with separate positivity theorem from ¬RH. | The cofinal strict-threshold formulation is mathematically the claimed extended-real limsup lower bound; it does not assume bounded repairs. Do not introduce a real-valued `limsup` without stating boundedness conventions. |
| 16: stabilized wrong coefficients and reconstruction | `CS.coefficient_tendsto` (`RH/MobiusCoefficientStabilization.lean`); `CS.not_RH_cofinally_wrong_coefficients`, `CS.not_RH_defect_series_not_summable`, `CS.not_RH_defect_norms_not_summable` (`RH/MobiusResidualInfiniteDefects.lean`); `CS.defectPartialSum_norm_tendsto_of_not_rh`, `CS.defectPartialSum_norm_sq` (`RH/MobiusCoefficientDefect.lean`); `CS.defect_reconstruction_dual_bound_sq`, `CS.not_RH_defect_norms_tendsto_atTop` (`RH/MobiusResidualEscape.lean`). | Exact polynomial/multiplicity reconstruction lower constants, `Q_N=o(N log²N)`, the residual-tail product liminf with constant E²/2, and the separate `∑|b_d|/√d=∞` were not found. Note the implemented `coefficientDefect` uses the opposite sign from b_d in the prose; squared norms are unchanged. |
| 17: normalized escape | `CS.coordinatePartialSum_prefix_linear`, `CS.dualCoordinateProjection_tendsto`, `CS.coordinatePartialSum_dual_orthogonal` and reconstruction divergence in `RH/MobiusResidualEscape.lean` supply foundational identities. | Weak convergence of the normalized reconstruction, head-energy escape, nonuniform integrability, and the Cesàro-smoothed bounds are not themselves proved by those divergence declarations and were not found as exact statements. |
| 18: L¹–L² cost and Laguerre | `paretoMellin_l1_power_lower`, `mellinL1Exponent_pos`, `mellinL1Constant_pos` (`RH/ParetoL1MellinBound.lean`) give explicit exponent `(2β-1)/(1-β)` and positive constant. `legal_l1_power_barrier_of_zeta`, `hilbert_error_energy_le`, `not_RH_legal_l1_energy_tendsto_atTop` (`RH/RHFalseEnergyConsequences.lean`) connect to actual legal vectors. Actual Laguerre Parseval is proved in `RH/ActualLaguerreParseval.lean`. | The exponential variance lower bound from matching k Laguerre moments was not found and is not supplied merely by Parseval. Quantitative weak-norm density and rate-to-exponent endpoint details must be tracked separately. |

The unlocated statements above are **formalization gaps in this scoped audit**,
not mathematical refutations. Conversely, a general conditional lemma does not
establish its arithmetic premises. There is no claim that all 18 prose groups
are completely formalized after the proposed additions.

#### Added concrete Open-target index

These targets now encode most sharper statements above as actual Lean
propositions. Their names ending in `Target` do **not** assert proofs.

`RH/CanonicalTailHistoricalTargets.lean`:

- Group 2: `TC.PointConstantResidualComparisonTarget`.
- Group 6: `TC.CanonicalAnnihilatorMeanTarget`, `TC.CanonicalNormalizedDilationTarget`.
- Group 7: `TC.CanonicalPrimitivePointwiseTarget`, `TC.CanonicalPrimitiveDyadicTarget`, `TC.CanonicalPrimitiveEnergyTarget`.
- Group 8: `TC.CanonicalSeparateSignedMomentTarget`.
- Group 9: `CS.AnnihilatorSubexponentialExcursionTarget`, `CS.HilbertPhysicalSublinearTarget`.

`RH/CanonicalSieveAbelTargets.lean`:

- Group 10: `TC.CanonicalAbelSummabilityTarget`, `TC.CanonicalSieveAbelNoncommutationTarget`. These explicitly define the prime product, Euler density, damped primitive, and signed sieve remainder. The first target prevents relying on the default value of an undefined real series; the second gives both iterated-limit ingredients on the same actual certificate.

`RH/ResidualEnergyHistoricalTargets.lean`:

- Group 1: `CS.HistoricalResidualCeilingTarget`.
- Group 3: `CS.FiniteMeanOneVarianceInfimumTarget`, `CS.MeanOneConditionalVarianceFloorTarget`.
- Group 4: `CS.CapacityDeterminantRatioLimitsTarget`. Follow-up discovery found the **finite** identities already proved in `RH/IntegerDPPGramDeterminant.lean`: `IntegerDPP.fullGram_det_eq`, `IntegerDPP.gram_det_ratio_eq_vacancy`. The new target is only the stated nonzero limiting formula.
- Group 11: `CS.MultiplicityExactHeadLowerTarget`.
- Group 12: `CS.LinearExactHeadUpperWitnessTarget`, `CS.ResidualTailLinearFloorTarget`.
- Group 13: `CS.MeanOneExactHeadSharpZeroTarget`, `CS.ExactHeadTailBiasVarianceTarget`, `CS.MeanOneExactHeadTailVarianceTarget`.
- Group 14: `CS.ReciprocalProjectionGainBudgetTarget`.
- Group 16: `CS.ReconstructionTailProductTarget`, `CS.ReconstructionZeroPowerTarget`, `CS.ReconstructionMultiplicityTarget`, `CS.ReconstructionUpperRateTarget`, `CS.ReconstructionWeightedAbsoluteDivergenceTarget`.
- Group 17: `CS.NormalizedReconstructionEscapeTarget`, `CS.NormalizedReconstructionNotUniformlyIntegrableTarget`, `CS.ReconstructionCesaroTarget`.
- Group 18: `CS.LaguerreMatchingVarianceTarget`.

One statement cannot yet receive a faithful concrete target from the visible
prose alone: group 13's polynomial covariance growth for the **specified actual
Schur error minimizers**. The user-facing claim does not identify the finite
correction spaces, conductor budgets, or exact minimizing family. Defining an
arbitrary minimizer and assuming the covariance bound would conceal this
normalization gap. The exact all-vector head bias/variance identity and
mean-one variance obstructions are encoded, while that family-specific growth
assertion remains a documented Open specification/formalization obligation.

All root-repaired candidates must take precedence over local earlier drafts.
Root reported the substantive gain, generic repair, and arithmetic mean-one
modules passed aggregate isolated verification; publication/checkpoint status
is exclusively root's responsibility.


### Analytic-condition coverage for the 2026-09-21 stringent-condition response

Scope: preceding response groups 19, 20, and 28–32. Static source audit used
workspace base `ed133e89`. All candidate checking/publication is performed by
the root coordinator; this document does not certify a candidate merely
because its proof text has been written. Names below are actual inspected
declarations or new candidates, never presumed historical providers.

#### Group 19 — simultaneous Mellin zero and multiplicity constraints

- **New actual infinite-residual theorem:**
  `CoefficientStabilization.limitResidual_mellin_at_zero` proves
  `paretoMellin limitResidual rho = 1/rho` for every actual zero with
  `1/2 < rho.re`, `rho != 1`. The same fixed residual is used for all zeros.
- **New actual projection/residual theorem:**
  `limitProjection_and_residual_zero_constraints` proves zero projection
  Mellin value and nonzero residual value at the same zero.
- **Established finite jet mechanism:**
  `Analysis.ResidualZeroSensors.zeta_lower_derivatives_zero`,
  `zeta_residual_jet`, `residual_lower_jet`, and `full_zero_sample_energy`
  concern actual zeta multiplicities and finite arithmetic residual numerators.
  This is not automatically a derivative-through-infinite-closure theorem.
- **Open, precise target:** `ClosedSpaceMellinMultiplicityTarget` in
  `RH/ResidualMellinZeroConditions.lean` states vanishing of every legal
  closure jet through the actual multiplicity minus one and the exact
  `(-1)^j j! / rho^(j+1)` values of the actual limiting residual.
- **Open:** corresponding higher jets of the canonical tail certificate;
  real/complex compatible construction of the simultaneous evaluation map J;
  the joint pseudoinverse Loewner inequality with the actual Gram matrix.
  The finite target must lie in the range before interpreting a pseudoinverse
  as a constrained minimum. No zero-mode completeness has been established.

#### Group 20 — small-eigenvalue source mass

- **Established finite geometry:** `Analysis.CompressedProjectionModes`
  derives the modal Gram and synthesis formulas from actual compressed
  projection eigenvector equations. `LinearAlgebra.SourceSpectralMass`
  proves `omittedMass_bounds`, `half_mass_defect_bound`, and cutoff energy
  estimates; it explicitly does not prove an arithmetic decay estimate.
- **New general theorems** in `LinearAlgebra/SourceSpectralObstruction.lean`:
  `omittedMass_le_scaled_inverseSourceMoment`,
  `omittedMass_tendsto_defect`, and
  `inverseSourceMoment_tendsto_atTop_of_positive_defect`.
  These retain the actual finite spectral sums and prove: positive limiting
  projection error plus polarization tending to zero implies positive limiting
  omitted mass at every fixed cutoff and divergence of the inverse first moment.
  Eigenvalues are strictly positive when inverted, all source weights nonnegative.
- **Open arithmetic assembly:** instantiate those hypotheses with the full
  growing-head arithmetic compression; construct the actual spectral measures
  and prove weak convergence to `E delta_0 + (1-E) delta_1`.
- **Open:** all positive inverse powers, logarithmic inverse moment divergence,
  smallest-eigenvalue limit, and the full stable-cutoff vector limit to P1.
  The new generic theorem supplies a real mechanism, not these unproved identifications.

#### Group 28 — Chebyshev damping and full signed arithmetic energy

- **Established analytic ingredients:** `RH/ChebyshevMellin.lean` proves
  the actual Chebyshev integral identity on Re(s)>1;
  `RH/ChebyshevEnergyHardy.lean` proves actual finite weighted energy implies
  holomorphy and Hardy H2 of the integral transform.
- **Established meromorphic facts:** `ChebyshevMellinRH` proves
  `meromorphicError_order_at_zero` and `riemannHypothesis_iff_error_analytic`.
- **New actual consequences** in `RH/ChebyshevZeroObstruction.lean`:
  `meromorphicError_not_hardy_of_zero`,
  `off_line_zero_pole_and_all_hardy_obstructions`, and
  `not_RH_exists_chebyshev_pole_and_hardy_obstructions`.
  They prove a simple pole and failure of every Hardy half-plane containing
  that pole. They do not identify totalized divergent Bochner integrals with
  their continuation.
- **Open precise endpoint target:** `OffLineZeroDampedEnergyDivergenceTarget`
  states `not ErrorFiniteEnergy (1+epsilon)` for all
  `0<epsilon<=2*rho.re-1`, including equality. The definition uses genuine
  nonintegrability of `(psi(x)-x)^2 x^(-2-epsilon)`, rather than equating a
  real-valued totalized integral to infinity.
- **Established finite signed bookkeeping:** `PrimePowerCriticalEnergy`
  defines actual von Mangoldt jumps and proves `actual_integral_energy` with
  complete signed and terminal terms. Identification of its damped infinite
  limit with the asserted divergent energy, and failure of Cauchy convergence
  for the particular Hardy approximants, remain **Open**.
- **Open:** exact pole residue `-multiplicity/rho` (the order is established),
  and claimed critical accumulated-energy non-power bounds.

#### Group 29 — compact/critical Mellin rigidity

- **Established, no open provider:**
  `SpectralObstruction.compactFrequencyRigidity_proved` in
  `RH/CompactFrequencyRigidity.lean`: compact-frequency annihilation iff
  the zeta-weighted complex density vanishes almost everywhere.
- **Established:** `compactCriticalMixtureTriviality_proved` in
  `RH/CompactCriticalMixtureTriviality.lean`: no nonzero compact-frequency,
  finite-energy critical-line annihilator.
- **Established:** `finiteCriticalMixture_logEnergy_eq_gram`,
  `finiteCriticalMixture_logEnergy_tendsto`, and
  `finite_criticalMixture_coefficients_zero_of_summable` in
  `RH/FiniteCriticalMellinMixtureEnergy.lean` retain the full double Gram sum.
- **Established:** `criticalPurePointEnergyProvider_proved`,
  `criticalMixture_not_summable`, `nonzero_criticalMixture_not_summable` in
  `RH/CriticalMellinCountableEnergy.lean`. Their absolute control is explicitly
  `Summable (fun j => norm (criticalAmplitude a gamma j))`, not merely an
  unspecified conditional convergence assumption.
- **Open:** poles of the specific damped-Mobius candidate at shifted off-line
  zeros; asserted reflected-boundary convergence with failure of holomorphic
  membership. Existing `DampedMobiusFourierSymbol` establishes the actual
  absolutely convergent Fourier/Mobius identity, not these continuation claims.
- **Not claimed:** unrestricted conditionally convergent or unbounded-frequency
  mixtures are eliminated by the above theorems.

#### Groups 30–31 — completed Weil spectral growth and fixed smoothing

- **Established actual normalization:** `WeilEnergyNormalization` proves the
  full signed prime-power correlation-energy identity with the evaluated
  archimedean displacement constant. The arithmetic completed form is defined
  by `FixedWidthWeilDiscrepancy.completedWeilForm`.
- **Existing OPEN providers:** `TwoHatWeilIdentity h` and
  `FixedWidthLandauDetection h`. `PolynomialWeilCriterion` explicitly depends
  on these; the previous prose's stronger research-derived claims cannot be
  presented as already fully checked source theorems.
- **New proved conditional reductions** in `RH/WeilFailureConditions.lean`:
  `not_RH_twoHat_polynomial_lower_failure`,
  `not_RH_twoHat_energy_lower_failure`, and
  `not_RH_twoHat_provider_alternative`. They give arbitrarily late actual
  violations when providers are supplied, or the correct disjunction of
  provider failures when the lower bound is supplied.
- **New precise OPEN target:**
  `FixedWidthTwoSidedExponentialDetectionTarget h`, stating both signs of the
  claimed exponential excursions with explicit quantifiers for every
  `0<=c<rho.re-1/2` and every amplitude and starting point.
- **New exact definitions:** `weilMoment`, `WeilWindowTest`, `weilL2Energy`,
  `weilReferenceEnergy`, `weilWindowBottomValues`, `weilWindowTopValues`,
  `weilWindowBottom`, `weilWindowTop`, `zetaHorizontalDefect`.
  Tests are smooth, compactly supported inside `(-L/2,L/2)` and obey both
  exponential-moment constraints. The reference form retains the exact
  positive archimedean difference-energy integral.
- **New elementary geometry:** `WeilWindowTest.mono`,
  `weilWindowBottomValues_mono`, and `weilWindowTopValues_mono` prove support
  enlargement and nesting of the actual constrained Rayleigh sets.
- **New precise OPEN target:** `WeilWindowSpectralGrowthTarget`, including
  nonempty and bounded Rayleigh sets for every positive window; decreasing
  bottom and increasing top on positive windows; bottom tending to minus
  infinity, top tending to infinity; and the exact limsup exponent equality.
- **New precise OPEN target:** `WeilSobolevSemiboundFailureTarget` with
  `weilSobolevEnergy`, retaining all integer-order derivatives in the norm.
- **Open:** finite operator construction, identification with these Rayleigh
  definitions, exact signed Schur negative-direction statements, and the
  finite-matrix/layer-cake conclusions for their intended arithmetic tests.

#### Group 32 — older proof packages

- The two-hat provider-alternative theorem above formally preserves the rule
  that jointly sufficient hypotheses need not fail individually.
- Existing `ParetoReflectionConvergence.riemannHypothesis_of_legal_reflection_split_tendsto`
  is a checked conditional route: actual signed calibration and normalized
  reflection variance must not both tend to zero under not RH.
- New `not_RH_reflection_objective_alternative` in
  `RH/ReflectionFailureConditions.lean` records that exact disjunction on the
  actual sequences, retaining all legality, mean, period and reflection premises.
- The broad historical Pick/Herglotz, self-adjoint determinant, Selberg–Connes,
  uniform transport, prime-cover/Riesz, atom-reuse, and mixed-source packages
  do not all have concrete corresponding declarations in the audited sources.
  Their exact maps, analytic domains, normalization, convergence topology,
  and substantive provider theorems remain **Open**. A proposition parameter
  saying merely 'this package implies RH' would not formalize those analytics.
- In particular no actual Riesz-function exponent obstruction is promoted to
  a theorem here. `DilationWaveletNoRiesz` is about Riesz bases and does not
  discharge the classical Riesz-function claim.

#### Integration list

1. `RiemannResearch/RH/ChebyshevZeroObstruction.lean`
2. `RiemannResearch/RH/WeilFailureConditions.lean`
3. `RiemannResearch/LinearAlgebra/SourceSpectralObstruction.lean`
4. `RiemannResearch/RH/ResidualMellinZeroConditions.lean`
5. `RiemannResearch/RH/ReflectionFailureConditions.lean`

Export each module and record provider targets as Open in the catalogue.
No project axiom, sorry, admit, or unsafe declaration was added.


### Coverage audit: catalogue groups 21--27

Source audit performed on base ed133e89, actual RiemannResearch sources. New
proof drafts are verified only by the coordinating agent. No remote edits,
checks, diagnostics, builds, or checkpoints were submitted by this agent.

| Group | Existing actual-object coverage | New work | Genuinely remaining |
|---|---|---|---|
| 21: occupation limit below one | `IntegerDPPClosure.vacancy_tendsto`, `limitingVacancy_pos_of_not_RH`; `IntegerDPPKernel.integerKernel_tendsto`, `vacancy_eq_kernel_complement`; `IntegerDPPHazards.vacancy_eq_capacity`; `IntegerDPPMellinObstruction.mellinVacancyFloor_eq`, `_le_limitingVacancy`, `capacity_bound_of_zeta_zero` | No duplicate wrapper introduced. | Catalogue's stronger ratio bound q*≤1/(1+κρ), concrete seven-generator numerical lower certificate, and changing-residue qN convergence not established by inspected files. User subsequently set aside trigamma convergence; no new trigamma claim is made. |
| 22: each site's persistent vacancy | `IntegerDPPAllSiteObstruction.siteMellinVacancyFloor_eq`, `_pos`, `_le_limitingKernel_complement`, `_le_integerKernel_complement`, `exists_common_site_vacancy_floor_of_not_RH` | `IntegerDPPPowerWeightedHoles.site_mellin_numerator_power_lower`, `critical_weight_mul_site_floor_lower` retain the sharp β-dependent exponent. | A one-zero rank-one *hole-process coupling* and its singleton tail law are not supplied by the operator lower bound alone. Full asymptotic equivalence of the numerator and explicit singleton law remain open formalization. |
| 23: weighted vacancy divergence | `IntegerDPPWeightedHoles.weightedLimitingHole_not_summable_of_not_RH`, harmonic lower bound; `IntegerDPPWeightedWindow.riemannHypothesis_of_bounded_weighted_hole_windows` | Draft proves `power_weighted_holes_not_summable_of_zeta_zero` for every α≥2Re(s)−1, including equality, for the physical weight (n+1)^α. `exists_common_critical_hole_exponent_of_not_RH` chooses one actual zero simultaneously for all α. | Sharp polynomial finite-window rate WN≥cN^(2−2β), logarithmic endpoint asymptotic constants, products with exact-head energies, and joint probability formulations require further proofs. Non-summable weighted expectation is NOT an a.s. infinitely-many-holes theorem. |
| 24: at least two holes, global/conditional occupation | Actual finite/limiting laws: `IntegerDPPExistence`; actual finite-rank cardinality: `IntegerDPPCardinality.integerLaw_cardinality`; nested spatial coupling: `IntegerDPPSpatialCoupling`; never-entry marginals and weighted consequences: `IntegerDPPSpatialVacancy`; temporal hazard summability: `IntegerDPPMellinObstruction.hazard_summable_of_not_RH` | Concrete targets `AtLeastTwoHoles`, `PositiveFiniteHead`, `HeadOccupationPairExponent`, `ConditionalOccupationDecay`. | None of finite-rank cardinality, positive site vacancy, or first-site non-a.s.-occupation alone proves at least two limiting holes a.s. Conjugate-pair rank/coupling theorem, a.s. non-full limiting occupation, determinant head exponent, and surrounding-head conditional decay remain open formalization. |
| 25: exponentially damped hole Fredholm | `IntegerDPPFiniteDamping` proves actual finite symmetric **occupied** determinant identities; `IntegerDPPWindowGenerating` finite generating identities. | Actual `holePrefixDeterminant t m` and `holeDampedValue t` definitions, with `HolePrefixConvergence`, `HoleDampingZeroOne`, `HoleDampingPairExponent` explicit open propositions. | Infinite operator Fredholm identification, t→0 zero-one law, pair power upper bound, and all-rank domination are not provided by the existing fixed Pareto damping theorem. |
| 26: fixed Pareto occupied determinant | `IntegerDPPDampedMinimum` finite exact benchmark criterion; `IntegerDPPDampedLimit.dampedPrefix_lower` quantitative finite lower bound and `dampedPrefix_tendsto_benchmark_iff` | New `IntegerDPPDampedConvergence`: nonnegative/antitone actual determinant sequence, unconditional convergence `dampedPrefixDeterminant_tendsto`, quantitative `dampedPrefixLimit_lower`, and `benchmark_lt_dampedPrefixLimit_of_not_RH`. `weightedVacancyMass` and `OccupiedDampingLogComparison` supply the remaining concrete target. | The sharp μ≤log(B/p0)≤2μ bounds and pathwise positive weighted hole mass remain open formalization. The historical target uses the new actual `dampedPrefixLimit`, with no duplicate definition. |
| 27: profinite and sampling coexistence | `IntegerDPPArithmeticExclusion`: all finite common-conductor exclusion/weighted lift identities. `IntegerDPPLiftFactorization`, `IntegerDPPConditionalLifts`: finite lifting. `Probability/ConditionalIIDSampleMean` and `ConditionalIIDSampleRates`: general conditional iid theory. Deterministic positive legal-error floor is covered in the Hilbert-space group. | `InfiniteArithmeticProgressionOccupation`, actual residue-class event, and `ShrinkingClassNoncommutation` propositions. | Infinite occupation in every progression, profinite closure, iterated-limit failure, escaping representatives, and a fully connected DPP random-interpolation variance theorem remain open formalization. Generic sampling variance decay does not prove absence of arithmetic bias. |

All target definitions use actual kernels/laws/determinants. They are declarations
of propositions with no proof providers and no axioms. They must be catalogued
as **Open**, not as kernel-verified mathematical consequences merely because
their definitions compile. The substantive new power-weight proof invokes an
actual zeta zero (and obtains one from not RH in its endpoint); it does not
assume the desired weighted divergence.


### Classical conditions: groups 28, 33--35

Static audit at parent workspace base `ed133e89`. No Lean verification was
submitted by this sub-agent. New source below requires root's serialized
verification and publication before any verified claim is made.

#### Existing concrete providers

- `RH/ChebyshevMellin.lean`: actual `errorMellin`,
  `meromorphicError`, and `error_mellin_identity` for `1 < Re s`.
- `RH/ChebyshevMellinRH.lean`: `logDeriv_order_at_zero`,
  `analyticAt_meromorphicError_iff`, `meromorphicError_order_at_zero`, and
  `riemannHypothesis_iff_error_analytic`. Pole order is proved; the residue
  coefficient `-m/rho` is expressly outside that module's claimed scope.
- `RH/ChebyshevEnergyHardy.lean`: `ErrorFiniteEnergy`,
  `errorMellin_analyticAt_of_energy`, and `errorMellin_hardy_of_energy`.
  These use the actual Chebyshev error integral as a hypothesis.
- `Analysis/WeightedMellinEnergy.lean`: `finiteEnergy_mono`, exact transform,
  transform analyticity and energy estimate.
- `RH/DyadicFourierAnalyticTargets.lean`: existing concrete
  `Pareto.classicalMertensFunction`, reused rather than redefined. Its
  `ClassicalQuantitativeMertensBound` remains an open proposition.
- `RH/PrimePowerEnergyBounds.lean`: actual signed-energy identities and
  unconditional estimates for exponent `s > 2`; does not supply the
  off-line-zero divergence or the endpoint proof.

#### New file coverage

| Item | Precise target | Proof status and missing input |
|---|---|---|
| 28: every positive damping `epsilon <= 2 beta - 1` diverges | `ChebyshevMellin.OffLineZeroDampedEnergyDivergenceTarget` (in sibling `ChebyshevZeroObstruction.lean`) | Open. Need analytic continuation of the actual Mellin integral after clearing the zeta denominator; endpoint requires Hardy boundary-pole exclusion. |
| 28/33: residue `-m/rho` | `ChebyshevZeroResidueTarget` | Open coefficient proof; order `-1` already has a provider. |
| 33: Mertens, psi, theta, pi-li exceed every smaller power/log envelope on every tail | `ArithmeticEnvelopeFailureTarget` | Open. Actual functions and every constant, cutoff, logarithmic exponent are formalized. |
| 33: boundary square-energy divergence for both M and psi | `ArithmeticBoundaryEnergyDivergenceTarget` | Open, includes equality `c = beta`, and every cutoff `X > 1`. |
| 33: exact multiplicity lower excursions | `ArithmeticBoundaryExcursionTarget` | Open. Multiplicity is the actual `analyticOrderAt` and the Mertens constant uses actual `iteratedDeriv m riemannZeta rho`. |
| 34: Li two-sign exponential limsup | `LiTwoSignExponentialGrowthTarget` | Open. Actual regularized xi, derivative-defined coefficients, nearest transformed-zero radius and both root-limsups included. Need generating function, attained minimum, singularity argument and both-sign Pringsheim argument. |
| 34: arbitrarily late coefficients of both signs | `LiInfiniteBothSignsTarget` | Open. Separate consequence recorded explicitly. |
| 35: quantitative infinitely many Robin violations | `RobinQuantitativeViolationsTarget` | Open Robin theorem provider; actual divisor sum, Euler constant and all zero-dependent b supplied. |
| 35: infinitely many Lagarias violations | `LagariasInfiniteViolationsTarget` | Open transfer from quantitative Robin plus harmonic threshold estimates. |
| 35: positive Newman constant and nonreal zeros at all nonnegative subcritical times | `NewmanFailureRHPositiveTarget` | Open; actual heat kernel is defined. Its convergence, zero-time identification and precise finite threshold are separate mandatory open providers. |

#### New mathematical candidates, to verify

`ClassicalArithmeticObstructions.lean` proves the specialization of weighted
energy monotonicity to the actual Chebyshev error, propagation of an endpoint
failure to smaller damping.
These results do not discharge the divergence targets.

`LiCoefficientObstructions.lean` proves the exact algebraic identities

```
liZeroRadius rho = norm (rho - 1) / norm rho
liZeroRadius rho ^ 2 * norm rho ^ 2 = norm rho ^ 2 - (2 * rho.re - 1)
```

for nonzero rho, and `0 < liZeroRadius rho < 1` for an actual right-hand
zero. Thus the classical Li radius uses the same horizontal zero defect as
the projection and exact-head obstructions. It does not yet prove the
coefficient growth.

#### Important exact scope

1. A pole of `meromorphicError` and analyticity of `errorMellin` cannot be
   combined by silently extending their Re(s)>1 identity. That continuation
   is a separate mathematical step.
2. A real-valued Bochner integral is never set equal to infinity. The
   square-energy target states nonintegrability of the nonnegative density.
3. The endpoint `epsilon = 2 beta - 1` is explicitly present and cannot be
   replaced by a strict-open-half-plane argument.
4. Li's xi must be regularized at 1 *before* differentiating. Defining xi as
   the naive totalized `s*(s-1)*completedRiemannZeta(s)/2` has the wrong value
   at the differentiation point. The entire `completedRiemannZeta₀` formula
   avoids that issue.
5. The Newman formula uses ordinary infinite sums and integrals only as
   definitions. Their convergence is not inferred from Lean's totalization.
   Likewise the sInf-defined constant requires nonempty/bounded-below
   threshold data before it can be interpreted as the classical constant.

The new files contain no axioms, placeholders, or admitted proofs. The target
definitions are not theorem providers and must remain Open in the catalog.
