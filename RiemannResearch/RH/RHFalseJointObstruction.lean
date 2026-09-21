import RiemannResearch.RH.IntegerDPPWeightedHoles
import RiemannResearch.RH.RHFalseTailConstraints
import RiemannResearch.RH.RHCriterionFailures
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.MobiusResidualEscape
import RiemannResearch.RH.ResidualGainObstruction
import RiemannResearch.RH.IntegerDPPPowerWeightedHoles
import RiemannResearch.RH.IntegerDPPDampedConvergence

/-!
# Joint arithmetic obstruction under failure of RH

Source: user-requested synthesis of the RiemannResearch obstruction theorems,
2026-09-21. The proof assembles the actual Mellin zero, all-site arithmetic
projection bounds, exact two-seed head energy, and canonical residue-tail
certificate; it does not introduce an external RH criterion or density provider.

All conclusions follow under the sole assumption of the negation of Mathlib's
RiemannHypothesis. The selected zero is shared by the site bounds, head bound,
pole, and canonical-certificate Mellin identity. The certificate is the existing
canonical object, not a separately chosen witness for each constraint.

This is an established conditional consequence of failure of RH. The conjunction
has not been shown impossible and does not prove RH. It is not claimed to be a
maximal inventory of all project consequences or all mathematical RH criteria.
The 2026-09-21 stringent-condition extension retains the common projection:
positive limiting constant energy, vanishing residual tails with a uniform
product barrier, cofinally wrong stabilized coefficients, divergent actual
reconstruction norms, nonsummable absolute reconstruction norms, both
canonical excursion families, and simultaneous bounds for every actual zero.
See RiemannResearch/RH/NOT_RH_STRINGENT_CONDITIONS.md for all 35 requested groups and
the remaining formalization obligations; that ledger is not a proof.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization CoefficientStabilization.TailCapacity IntegerDPP

/-- A single zero forces the all-site and exact-head barriers, while the
same canonical certificate carries all residue constraints. -/
theorem not_RH_joint_arithmetic_obstruction (hRH : ¬ RiemannHypothesis) :
    (∃ s : ℂ, riemannZeta s = 0 ∧ (1 / 2 : ℝ) < s.re ∧ s.re < 1 ∧
      meromorphicOrderAt RiemannResearch.RH.ChebyshevMellin.meromorphicError s = -1 ∧
      (∀ n : ℕ, 0 < siteMellinVacancyFloor n s ∧
        siteMellinVacancyFloor n s ≤ 1 - limitingKernel n n ∧
        ∀ N : ℕ, siteMellinVacancyFloor n s ≤ 1 - integerKernel N n n) ∧
      (∀ N : ℕ,
        (N : ℝ) / ((N : ℝ) + 1) +
          ((2 * s.re - 1) * ((N : ℝ) + 1) ^ (2 * s.re - 1) / ‖s‖ ^ 2) *
            ‖1 - ((N : ℂ) + 1)^(-s)‖ ^ 2 ≤ TwoSeedExactHeadEnergy.energy N) ∧
      paretoMellin canonicalTailCertificate s =
        (-(‖canonicalTailCertificate‖ ^ 2) : ℝ) •
          paretoMellin (paretoPointHilbert 0) s ∧
      (∀ α : ℝ, 2 * s.re - 1 ≤ α →
        ¬ Summable (fun n : ℕ => ((n : ℝ) + 1) ^ α *
          (1 - limitingKernel n n)))) ∧
    IsResidueTailCertificate canonicalTailCertificate ∧
    Tendsto tailCapacity atTop (𝓝 (‖canonicalTailCertificate‖ ^ 2)) ∧
    (∀ z : ThresholdHilbert, IsResidueTailCertificate z →
      ‖z‖ ^ 2 = ‖canonicalTailCertificate‖ ^ 2 + ‖z - canonicalTailCertificate‖ ^ 2) ∧
    Summable (fun n =>
      anchoredSignedTail (hilbertSequence canonicalTailCertificate) n ^ 2) ∧
    ¬ Summable (anchoredSignedTail (hilbertSequence canonicalTailCertificate)) ∧
    ¬ Summable (fun n : ℕ =>
      |additivePartialSum (hilbertSequence canonicalTailCertificate) n| / (n : ℝ)^2) ∧
    (∀ N : ℕ,
      (∃ k, N ≤ k ∧ 2 ≤ k ∧ 0 < hilbertSequence canonicalTailCertificate k) ∧
      (∃ k, N ≤ k ∧ 2 ≤ k ∧ hilbertSequence canonicalTailCertificate k < 0)) ∧
    ¬ Summable weightedLimitingHole ∧
    (∃ p : ℝ, 0 < p ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      C * ((N : ℝ) + 1) ^ p < TwoSeedExactHeadEnergy.energy N) ∧
    ¬ RiemannResearch.RH.ConditionalMeanGram.UniformSignedSchurTarget ∧
    0 < limitEnergy ∧
    Tendsto CoefficientStabilization.energy atTop (𝓝 limitEnergy) ∧
    Tendsto residualTailEnergy atTop (𝓝 0) ∧
    (∀ N : ℕ, ∀ f : ThresholdHilbert, f ∈ closedSpace →
      (∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) →
      limitEnergy ^ 2 ≤ residualTailEnergy N * ‖hilbertOne - f‖ ^ 2) ∧
    (∀ N : ℕ, ∃ d : ℕ, N < d ∧ 1 < d ∧
      limitCoefficient d ≠ -(ArithmeticFunction.moebius d : ℝ)) ∧
    Tendsto (fun N => ‖coordinatePartialSum limitResidual N‖) atTop atTop ∧
    (¬ Summable (fun i : ℕ =>
      ‖coefficientCLM (i + 2) limitResidual • residueAtom i‖)) ∧
    (∀ η : ℝ, 0 < η → ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      C * (n : ℝ) ^ (1 - η) <
        |additivePartialSum (hilbertSequence canonicalTailCertificate) n|) ∧
    (∀ η : ℝ, 0 < η → ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      C * (n : ℝ) / Real.log (2 * (n : ℝ)) ^ (1 + η) <
        |additivePartialSum (hilbertSequence canonicalTailCertificate) n|) ∧
    (∀ s : ℂ, (1 / 2 : ℝ) < s.re → s ≠ 1 → riemannZeta s = 0 →
      ∀ n : ℕ, siteMellinVacancyFloor n s ≤ 1 - limitingKernel n n) ∧
    HasSum (fun n => -Real.log (1 - projectionRelativeGain n))
      (Real.log (CoefficientStabilization.energy 0 / limitEnergy)) ∧
    paretoProductBenchmark < dampedPrefixLimit := by
  obtain ⟨s, hz, hs, h1, hpole, _, hhead⟩ :=
    TwoSeedExactHeadEnergy.not_RH_zero_pole_and_energy hRH
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at h1
  have hr := not_RH_pointDualResidual_ne_zero hRH
  obtain ⟨hc, hcap, hsq, hnotsum, hpartial⟩ := not_RH_canonical_obstruction hRH
  refine ⟨⟨s, hz, hs, h1, hpole, ?_, hhead,
    canonicalTailCertificate_mellin_at_zero hr s hs hs1 hz,
    (fun α hα => power_weighted_holes_not_summable_of_zeta_zero s hs h1 hz α hα)⟩,
    hc, hcap, certificate_canonical_energy_split hr, hsq, hnotsum, hpartial,
    not_RH_canonical_both_signs hRH,
    weightedLimitingHole_not_summable_of_not_RH hRH,
    TwoSeedExactHeadEnergy.not_RH_eventual_subpower_failure hRH,
    RiemannResearch.RH.ConditionalMeanGram.not_RH_not_uniformSignedSchurTarget hRH,
    not_RH_limitEnergy_pos hRH, energy_tendsto, residualTailEnergy_tendsto_zero,
    (fun N f hf hh => residual_tail_product_lower N hf hh),
    not_RH_cofinally_wrong_coefficients hRH,
    not_RH_defect_norms_tendsto_atTop hRH,
    not_RH_defect_norms_not_summable hRH,
    not_RH_canonical_power_excursions hRH,
    not_RH_canonical_log_excursions hRH,
    (fun s hs h1 hz n =>
      siteMellinVacancyFloor_le_limitingKernel_complement s hs h1 hz n),
    not_RH_logarithmic_gain_hasSum hRH,
    benchmark_lt_dampedPrefixLimit_of_not_RH hRH⟩
  intro n
  exact ⟨siteMellinVacancyFloor_pos n s hs,
    siteMellinVacancyFloor_le_limitingKernel_complement s hs hs1 hz n,
    siteMellinVacancyFloor_le_integerKernel_complement s hs hs1 hz n⟩

end RiemannResearch.RH.Pareto
