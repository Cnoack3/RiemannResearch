import Mathlib.Analysis.PSeries

/-!
# Summability of the logarithmic p-series

Source: user-provided
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Section 26.1, for the RH application requiring this majorant.
The classical proof strategy is Cauchy condensation, implemented using
`summable_condensed_iff_of_nonneg` and the p-series theorems from
`Mathlib.Analysis.PSeries`. No arithmetic research hypothesis is used.
-/

noncomputable section
namespace RiemannResearch.Analysis

/-- The standard logarithmic p-series, with log(2n) to avoid a special
positive coordinate at n=1. The n=0 term is zero. -/
theorem summable_log_power_majorant {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ =>
      1 / ((n : ℝ) * Real.log (2 * (n : ℝ)) ^ p)) := by
  let f : ℕ → ℝ := fun n => 1 / ((n : ℝ) * Real.log (2 * (n : ℝ)) ^ p)
  have hl (n : ℕ) : 0 ≤ Real.log (2 * (n : ℝ)) := by
    rcases n with _ | n
    · simp
    · apply Real.log_nonneg
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hf (n : ℕ) : 0 ≤ f n := by
    exact div_nonneg (by norm_num)
      (mul_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg (hl n) p))
  have hm : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm0 hmn
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    have hmR : 0 < (m : ℝ) := by linarith
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hnR : 0 < (n : ℝ) := lt_of_lt_of_le hmR hmnR
    have hlm : 0 < Real.log (2 * (m : ℝ)) := Real.log_pos (by linarith)
    have hln : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by linarith)
    have hlogs : Real.log (2 * (m : ℝ)) ≤ Real.log (2 * (n : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    have hpows : Real.log (2 * (m : ℝ)) ^ p ≤ Real.log (2 * (n : ℝ)) ^ p :=
      Real.rpow_le_rpow hlm.le hlogs (by linarith)
    have hden : (m : ℝ) * Real.log (2 * (m : ℝ)) ^ p ≤
        (n : ℝ) * Real.log (2 * (n : ℝ)) ^ p :=
      mul_le_mul hmnR hpows (Real.rpow_nonneg hlm.le p) hnR.le
    dsimp [f]
    apply (div_le_div_iff₀
      (mul_pos hnR (Real.rpow_pos_of_pos hln p))
      (mul_pos hmR (Real.rpow_pos_of_pos hlm p))).2
    simpa only [one_mul] using hden
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ p) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hp)
  have he (k : ℕ) : (2 : ℝ) ^ k * f (2 ^ k) =
      (Real.log 2 ^ p)⁻¹ * (1 / ((k : ℝ) + 1) ^ p) := by
    have hlog : Real.log (2 * ((2 ^ k : ℕ) : ℝ)) =
        ((k : ℝ) + 1) * Real.log 2 := by
      calc
        _ = Real.log ((2 : ℝ) ^ (k + 1)) := by
          congr 1
          simp only [Nat.cast_pow, Nat.cast_ofNat, pow_succ']
        _ = _ := by rw [Real.log_pow]; push_cast; ring
    have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
    have hk : ((k : ℝ) + 1) ^ p ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by positivity) p)
    have hlogp : Real.log 2 ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hl2 p)
    dsimp [f]
    rw [hlog, Real.mul_rpow (by positivity) hl2.le]
    push_cast
    field_simp [h2k, hk, hlogp]
    <;> ring
  apply (summable_condensed_iff_of_nonneg hf hm).mp
  apply (hs.mul_left ((Real.log 2 ^ p)⁻¹)).congr
  intro k
  exact (he k).symm

end RiemannResearch.Analysis
