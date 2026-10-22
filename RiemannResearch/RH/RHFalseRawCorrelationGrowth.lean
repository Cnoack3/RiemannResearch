import RiemannResearch.RH.RawMobiusFiniteWindowCriterion
import RiemannResearch.RH.RawMobiusSignedGramEnergy
import RiemannResearch.RH.ParetoExactHeadResidual
import RiemannResearch.RH.RHFalseEnergyConsequences

/-!
# A common zero forces signed raw Gram growth and exact-head energy
Source: user-requested negated-RH synthesis, October 1, 2026.
The proof combines existing exact Mellin and signed raw Gram estimates.
Both orientations, every signed pair and the logarithmic boundary remain.
This is an unconditional consequence of a hypothetical zero, not its exclusion.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto

theorem rawMobiusOffDiagonal_lower_of_zeta_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    ∀ᶠ N : ℕ in atTop,
      (((2 * s.re - 1) / (4 * ‖s‖ ^ 2)) *
        ((N : ℝ) + 1) ^ (2 * s.re - 1) -
        48 * (∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ)) - 8) / 24 ≤
          rawMobiusOffDiagonalEnergy N := by
  filter_upwards [rawMobiusBudget_eventual_signed_sandwich,
    eventually_ge_atTop (3 : ℕ)] with N hbudget hN
  have hlower := rawMobiusSquareBudget_lower_of_zeta_zero N hN s hs hs1 hz
  have hupper := hbudget.2
  linarith

theorem not_RH_same_zero_signed_raw_and_head_obstruction
    (hRH : ¬ RiemannHypothesis) :
    ∃ s : ℂ, riemannZeta s = 0 ∧ (1 / 2 : ℝ) < s.re ∧ s.re < 1 ∧
      (∀ᶠ N : ℕ in atTop,
        (((2 * s.re - 1) / (4 * ‖s‖ ^ 2)) *
          ((N : ℝ) + 1) ^ (2 * s.re - 1) -
          48 * (∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ)) - 8) / 24 ≤
            rawMobiusOffDiagonalEnergy N) ∧
      (∀ N : ℕ, ∀ f : ThresholdHilbert,
        f ∈ CoefficientStabilization.closedSpace →
        (∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) →
        ((2 * s.re - 1) / ‖s‖ ^ 2) *
          ((N : ℝ) + 1) ^ (2 * s.re - 1) ≤ ‖hilbertOne - f‖ ^ 2) := by
  obtain ⟨s, hz, hs, hsupper⟩ := RiemannResearch.RH.exists_right_zero_of_not_RH hRH
  have hs1 : s ≠ 1 := by intro he; simp [he] at hsupper
  refine ⟨s, hz, hs, hsupper,
    rawMobiusOffDiagonal_lower_of_zeta_zero s hs hs1 hz, ?_⟩
  intro N f hf hhead
  exact legal_exact_head_residual_lower_bound {n : ℕ | 0 < n}
    (fun _ hn => hn) s hs hs1 hz
    (CoefficientStabilization.closedSpace_le_legalClosure hf) hhead

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection

theorem inverseSourceEnergy_power_lower_of_zeta_zero
    (n : ℕ) (hn : 2 ≤ n) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (((2 * s.re - 1) / (4 * ‖s‖ ^ 2)) *
      (((n + 1 : ℕ) : ℝ) + 1) ^ (2 * s.re - 1) -
      24 * energy 0 - 8) / 24 ≤ inverseSourceEnergy n := by
  have hlower := RiemannResearch.RH.Pareto.rawMobiusSquareBudget_lower_of_zeta_zero
    (n + 1) (by omega) s hs hs1 hz
  have hupper := RiemannResearch.RH.Pareto.rawMobiusSquareBudget_le_two_raw_norm_sq (n + 1)
  rw [← naturalResidual_eq_rawMobiusResidual n,
    naturalResidual_norm_sq_eq_energy_add] at hupper
  have he := energy_antitone (Nat.zero_le n)
  linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection
