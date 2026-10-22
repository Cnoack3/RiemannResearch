import RiemannResearch.RH.CRTLegalCoordinates

/-!
# A three-site obstruction to nonnegative residue approximants

Source: user-provided RH/DPP research question, 21 September 2026.
This excludes a positive-coefficient shortcut, not signed legal approximation.
The arithmetic separator and all constants are proved explicitly.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CRTBlock
open Pareto ArithmeticCumulative
open ArithmeticCumulative.CesaroResidue

theorem residueFraction_two_three_separator (d : ℕ) (hd : 2 ≤ d) :
    2 * residueFraction d 1 ≤
      residueFraction d 2 + 2 * residueFraction d 3 := by
  by_cases hd2 : d = 2
  · subst d
    norm_num [residueFraction]
  by_cases hd3 : d = 3
  · subst d
    norm_num [residueFraction]
  have h1 : 1 < d := by omega
  have h2 : 2 < d := by omega
  have h3 : 3 < d := by omega
  simp only [residueFraction, Nat.mod_eq_of_lt h1,
    Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]
  push_cast
  simp only [div_eq_mul_inv]
  have hi : 0 ≤ (d : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg d)
  nlinarith

theorem normalizedResidueSynthesis_two_three_separator
    (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) (hc : ∀ d ∈ s, 0 ≤ c d) :
    2 * normalizedResidueSynthesis s c 1 ≤
      normalizedResidueSynthesis s c 2 +
        2 * normalizedResidueSynthesis s c 3 := by
  have hp : ∀ d ∈ s,
      2 * (c d * residueFraction d 1) ≤
        c d * residueFraction d 2 + 2 * (c d * residueFraction d 3) := by
    intro d hd
    have hh := mul_le_mul_of_nonneg_left
      (residueFraction_two_three_separator d (hs d hd)) (hc d hd)
    nlinarith
  have hh := Finset.sum_le_sum hp
  simpa only [normalizedResidueSynthesis, Finset.sum_add_distrib,
    ← Finset.mul_sum] using hh

theorem two_three_energy_lower_bound {x y : ℝ} (h : 2 ≤ x + 2 * y) :
    (2 : ℝ) / 27 ≤ x ^ 2 / 6 + y ^ 2 / 12 := by
  have hp : 0 ≤ (x + 2 * y - 2) * (x + 2 * y + 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [sq_nonneg (4 * x - y)]

theorem normalizedResidueSynthesis_nonnegative_tail_lower_bound
    (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) (hc : ∀ d ∈ s, 0 ≤ c d)
    (hhead : normalizedResidueSynthesis s c 1 = 1) :
    (2 : ℝ) / 27 ≤
      (normalizedResidueSynthesis s c 2) ^ 2 / 6 +
        (normalizedResidueSynthesis s c 3) ^ 2 / 12 := by
  apply two_three_energy_lower_bound
  have hh := normalizedResidueSynthesis_two_three_separator s c hs hc
  rw [hhead] at hh
  linarith

theorem normalizedResidueSynthesis_nonnegative_occupation_cap
    (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) (hc : ∀ d ∈ s, 0 ≤ c d)
    (hhead : normalizedResidueSynthesis s c 1 = 1)
    (U : ℝ)
    (hU : (normalizedResidueSynthesis s c 2) ^ 2 / 6 +
      (normalizedResidueSynthesis s c 3) ^ 2 / 12 ≤ U) :
    ((1 : ℝ) / 2) / (1 / 2 + U) ≤ 27 / 31 := by
  have hb := normalizedResidueSynthesis_nonnegative_tail_lower_bound s c hs hc hhead
  have hden : 0 < (1 : ℝ) / 2 + U := by linarith
  apply (div_le_iff₀ hden).2
  linarith

end RiemannResearch.RH.CRTBlock
