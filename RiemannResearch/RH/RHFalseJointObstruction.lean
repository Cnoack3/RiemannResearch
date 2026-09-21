import RiemannResearch.RH.IntegerDPPWeightedHoles
import RiemannResearch.RH.RHFalseTailConstraints
import RiemannResearch.RH.RHCriterionFailures

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
          paretoMellin (paretoPointHilbert 0) s) ∧
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
    ¬ RiemannResearch.RH.ConditionalMeanGram.UniformSignedSchurTarget := by
  obtain ⟨s, hz, hs, h1, hpole, _, hhead⟩ :=
    TwoSeedExactHeadEnergy.not_RH_zero_pole_and_energy hRH
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at h1
  have hr := not_RH_pointDualResidual_ne_zero hRH
  obtain ⟨hc, hcap, hsq, hnotsum, hpartial⟩ := not_RH_canonical_obstruction hRH
  refine ⟨⟨s, hz, hs, h1, hpole, ?_, hhead,
    canonicalTailCertificate_mellin_at_zero hr s hs hs1 hz⟩,
    hc, hcap, certificate_canonical_energy_split hr, hsq, hnotsum, hpartial,
    not_RH_canonical_both_signs hRH,
    weightedLimitingHole_not_summable_of_not_RH hRH,
    TwoSeedExactHeadEnergy.not_RH_eventual_subpower_failure hRH,
    RiemannResearch.RH.ConditionalMeanGram.not_RH_not_uniformSignedSchurTarget hRH⟩
  intro n
  exact ⟨siteMellinVacancyFloor_pos n s hs,
    siteMellinVacancyFloor_le_limitingKernel_complement s hs hs1 hz n,
    siteMellinVacancyFloor_le_integerKernel_complement s hs hs1 hz n⟩

end RiemannResearch.RH.Pareto
