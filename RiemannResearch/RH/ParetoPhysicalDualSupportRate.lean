import RiemannResearch.RH.ParetoPhysicalDualProjection
import RiemannResearch.Analysis.StretchedExponentialBounds

/-! The actual physical-dual error is O(log K / sqrt K), without RH.
Source: user-provided support-error formula and its proved logarithmic envelope. -/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

theorem physicalDualProjectionResidual_norm_le_log_sqrt (n : ℕ) (hn : 4 ≤ n) :
    ‖physicalDualProjectionResidual n‖ ≤
      2 * (Real.log (((n + 1 : ℕ) : ℝ) + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  have hK : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hL : 1 ≤ Real.log (((n + 1 : ℕ) : ℝ) + 1) :=
    RiemannResearch.Analysis.one_le_log_of_six_le (by exact_mod_cast (by omega : 6 ≤ n + 2))
  have hroot := Real.sq_sqrt hK.le
  have hroot0 := Real.sqrt_pos.mpr hK
  have hs :
      (2 * (Real.log (((n + 1 : ℕ) : ℝ) + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ))) ^ 2 =
        4 * Real.log (((n + 1 : ℕ) : ℝ) + 1) ^ 2 / ((n + 1 : ℕ) : ℝ) := by
    rw [mul_pow, div_pow, hroot]
    norm_num <;> ring
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (div_nonneg (by linarith) hroot0.le))).mp
  rw [hs]
  have hnum : 2 * Real.log (((n + 1 : ℕ) : ℝ) + 1) ^ 2 + 1 ≤
      4 * Real.log (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (((n + 1 : ℕ) : ℝ) + 1) - 1)]
  exact (physicalDualProjectionResidual_log_bound n).trans
    (div_le_div_of_nonneg_right hnum hK.le)

theorem physicalDualProjectionResidual_norm_isBigO :
    (fun n : ℕ => ‖physicalDualProjectionResidual n‖) =O[atTop]
      (fun n => Real.log (((n + 1 : ℕ) : ℝ) + 1) /
        Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop 4] with n hn
  have harg : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) (n + 1)]
  have hnonneg : 0 ≤ Real.log (((n + 1 : ℕ) : ℝ) + 1) /
      Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    div_nonneg (Real.log_nonneg harg) (Real.sqrt_nonneg _)
  simpa only [Real.norm_eq_abs, abs_norm, abs_of_nonneg hnonneg] using
    physicalDualProjectionResidual_norm_le_log_sqrt n hn

end RiemannResearch.RH.Pareto.CoefficientStabilization
