import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- A quantitative continuity bound sufficient for prime summability.
The sharper logarithmic modulus can be retained in the original variance
estimate; this elementary consequence avoids a delicate monotonicity argument
when a logarithmic-power estimate for the gap is substituted. -/
theorem small_gap_log_modulus_le_sqrt (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    δ * (1 + Real.log δ⁻¹) ≤ 2 * Real.sqrt δ := by
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hs2 := Real.sq_sqrt hδ.le
  have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (inv_pos.mpr hδ))
  rw [Real.log_sqrt (inv_pos.mpr hδ).le, Real.sqrt_inv] at hlog
  have hsum : 1 + Real.log δ⁻¹ ≤ 2 / Real.sqrt δ - 1 := by
    simp only [div_eq_mul_inv] at hlog ⊢
    linarith
  have heq : δ * (2 / Real.sqrt δ - 1) = 2 * Real.sqrt δ - δ := by
    field_simp [ne_of_gt hs]
    nlinarith
  calc
    _ ≤ δ * (2 / Real.sqrt δ - 1) := mul_le_mul_of_nonneg_left hsum hδ.le
    _ = 2 * Real.sqrt δ - δ := heq
    _ ≤ 2 * Real.sqrt δ := by linarith

end
end RiemannResearch.RH.Pareto
