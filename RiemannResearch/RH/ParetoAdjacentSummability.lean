import RiemannResearch.RH.ParetoRepairSummability
import Mathlib.Analysis.PSeries

/-!
# Unconditional diagonal summability for adjacent integer repairs

Source: `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`, adjacent-scale
analysis. The variance here is the complete Pareto variance. No smooth-number
gap input is used. Diagonal summability is distinguished from convergence of
arbitrary linear combinations, which requires control of every covariance.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The exact previously proved logarithmic modulus at unit scale gap. -/
theorem adjacent_arithmeticRepair_variance_log_bound (n : ℕ) (hn : 0 < n) :
    paretoVariance (arithmeticRepair 2 n (n + 1)) ≤
      8 * (1 / (n : ℝ)^2) * (1 + Real.log (n : ℝ)) := by
  simpa using arithmeticRepair_binary_variance_log_bound n 1 (by omega) hn

/-- A convenient summable power bound, obtained from the full logarithmic modulus. -/
theorem adjacent_arithmeticRepair_variance_rpow_bound (n : ℕ) (hn : 0 < n) :
    paretoVariance (arithmeticRepair 2 n (n + 1)) ≤
      16 * (1 / (n : ℝ)^(3 / 2 : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (n : ℝ)^(3 / 2 : ℝ) = (n : ℝ) * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hnR, Real.rpow_one]
  have he : 16 * Real.sqrt ((1 : ℝ) / n) / n =
      16 * (1 / (n : ℝ)^(3 / 2 : ℝ)) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, hp]
    ring
  calc
    _ ≤ 16 * Real.sqrt ((1 : ℝ) / n) / n := by
      simpa using arithmeticRepair_binary_variance_sqrt_bound n 1 (by omega) hn
    _ = _ := he

/-- The entire adjacent integer family has summable individual variances.
The shift indexes exactly the positive integers and removes the degenerate scale zero. -/
theorem summable_adjacent_arithmeticRepair_variance :
    Summable (fun n : ℕ =>
      paretoVariance (arithmeticRepair 2 (n + 1) (n + 1 + 1))) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ)^(3 / 2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hs' := (hs.comp_injective Nat.succ_injective).mul_left (16 : ℝ)
  apply Summable.of_nonneg_of_le (fun _ => paretoVariance_nonneg _) _ hs'
  intro n
  simpa only [Function.comp_apply, Nat.succ_eq_add_one] using
    adjacent_arithmeticRepair_variance_rpow_bound (n + 1) (by omega)

/-- Since every adjacent repair has mean zero, diagonal variance summability
is precisely summability of the complete squared Pareto norms. -/
theorem summable_adjacent_arithmeticRepair_sq_norm :
    Summable (fun n : ℕ =>
      paretoInner (arithmeticRepair 2 (n + 1) (n + 1 + 1))
        (arithmeticRepair 2 (n + 1) (n + 1 + 1))) := by
  apply summable_adjacent_arithmeticRepair_variance.congr
  intro n
  simp only [paretoVariance,
    arithmeticRepair_mean_zero 2 (n + 1) (n + 1 + 1) (by omega) (by omega) (by omega),
    sub_zero]

end
end RiemannResearch.RH.Pareto
