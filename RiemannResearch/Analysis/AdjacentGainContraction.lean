import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Contraction forced by adjacent energy gains

Source: user-requested backwards RH verification, 13 October 2026.
These conditional deductions are independently formalized, without a novelty claim.
No missing arithmetic bound is asserted.
-/

namespace RiemannResearch.Analysis.AdjacentGainContraction

/-- Elementary contraction; no square-root optimization is needed. -/
theorem middle_contraction_of_adjacent_gains (a b c η : ℝ)
    (hη : 0 < η) (hb : 0 ≤ b) (hc : 0 ≤ c) (hba : b ≤ a)
    (hs : η * b ^ 2 ≤ 2 * (a - b) * (b - c)) :
    b ≤ (2 / (η + 2)) * a := by
  have hden : 0 < η + 2 := by linarith
  have hp : 0 ≤ (a - b) * c := mul_nonneg (sub_nonneg.mpr hba) hc
  have hmul : ((η + 2) * b) * b ≤ (2 * a) * b := by nlinarith
  by_cases hb0 : b = 0
  · subst b
    have ha : 0 ≤ a := hba
    positivity
  · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hlinear : (η + 2) * b ≤ 2 * a := (mul_le_mul_iff_left₀ hbp).mp hmul
    calc
      _ ≤ (2 * a) / (η + 2) := (le_div_iff₀ hden).mpr (by nlinarith)
      _ = _ := by ring

theorem contraction_factor_lt_one (η : ℝ) (hη : 0 < η) :
    0 < (2 : ℝ) / (η + 2) ∧ (2 : ℝ) / (η + 2) < 1 := by
  have hden : 0 < η + 2 := by linarith
  constructor
  · exact div_pos (by norm_num) hden
  · apply (div_lt_one hden).mpr
    linarith

end RiemannResearch.Analysis.AdjacentGainContraction
