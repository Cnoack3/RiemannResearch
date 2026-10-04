import RiemannResearch.RH.ActualPrimePowerErrorSummability
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The actual prime-power correction belongs to the Pareto energy space

This is an unconditional consumer of the actual MediumPNT and Costa-Pereira
providers established in ActualPrimePowerErrorSummability. At n=0 the formal
weight is zero. No arithmetic signed-energy bound is inferred from this result.
-/
noncomputable section
open Filter

namespace RiemannResearch.RH.ActualPrimePowerError

/-- The elementary cubic-root term has the required p-series energy decay. -/
theorem cubic_energy_identity {x : ℝ} (hx : 0 < x) :
    (x ^ ((1 : ℝ) / 3)) ^ 2 / x ^ 2 = 1 / x ^ ((4 : ℝ) / 3) := by
  have hp : (x ^ ((1 : ℝ) / 3)) ^ 2 * x ^ ((4 : ℝ) / 3) = x ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
    norm_num
  apply (div_eq_div_iff (by positivity : x ^ 2 ≠ 0)
    (by positivity : x ^ ((4 : ℝ) / 3) ≠ 0)).2
  simpa only [one_mul] using hp

/-- The complete actual square-root compensated prime-power error is square
summable under the Pareto weight. This is independent of RH. -/
theorem summable_error_energy :
    Summable (fun n : ℕ => error n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
  obtain ⟨A, hA, hbound⟩ := sqrt_psi_bound
  let D : ℝ := 2 * (Real.log 4 + 4)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlogsum : Summable (fun n : ℕ =>
      1 / ((n : ℝ) * Real.log (2 * (n : ℝ)) ^ (2 : ℕ))) := by
    simpa only [Real.rpow_two] using
      (RiemannResearch.Analysis.summable_log_power_majorant
        (p := (2 : ℝ)) (by norm_num))
  have hpowsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ ((4 : ℝ) / 3)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hmajor := (hlogsum.mul_left (2 * A ^ 2)).add
    (hpowsum.mul_left (2 * D ^ 2))
  apply hmajor.of_norm_bounded_eventually_nat
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hn0 : 0 < (n : ℝ) := by linarith
  have hL : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by nlinarith)
  have hr := rootRemainder_bounds (show 1 ≤ (n : ℝ) by linarith)
  have hrabs : |rootRemainder n| ≤ D * (n : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [abs_of_nonneg hr.1]
    exact hr.2
  have habs : |error n| ≤
      A * Real.sqrt n / Real.log (2 * (n : ℝ)) +
        D * (n : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [error_eq]
    exact (abs_add_le _ _).trans (add_le_add hn hrabs)
  have hapos : 0 ≤ A * Real.sqrt n / Real.log (2 * (n : ℝ)) := by positivity
  have hbpos : 0 ≤ D * (n : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hsq := mul_le_mul habs habs (abs_nonneg (error n)) (add_nonneg hapos hbpos)
  have hasq : (A * Real.sqrt n / Real.log (2 * (n : ℝ))) ^ 2 =
      A ^ 2 * (n : ℝ) / Real.log (2 * (n : ℝ)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hn0.le]
  have hesq : error n ^ 2 ≤
      2 * (A ^ 2 * (n : ℝ) / Real.log (2 * (n : ℝ)) ^ 2) +
        2 * D ^ 2 * ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
    have hsabs : |error n| * |error n| = error n ^ 2 := by
      rw [← pow_two, sq_abs]
    rw [hsabs] at hsq
    nlinarith [sq_nonneg
      (A * Real.sqrt n / Real.log (2 * (n : ℝ)) -
        D * (n : ℝ) ^ ((1 : ℝ) / 3))]
  have hnum0 : 0 ≤
      2 * (A ^ 2 * (n : ℝ) / Real.log (2 * (n : ℝ)) ^ 2) +
        2 * D ^ 2 * ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by positivity
  have hden : (n : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 1) := by nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ error n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))]
  calc
    _ ≤ (2 * (A ^ 2 * (n : ℝ) / Real.log (2 * (n : ℝ)) ^ 2) +
        2 * D ^ 2 * ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2) /
        ((n : ℝ) * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right hesq (by positivity)
    _ ≤ (2 * (A ^ 2 * (n : ℝ) / Real.log (2 * (n : ℝ)) ^ 2) +
        2 * D ^ 2 * ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2) / (n : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      exact mul_le_mul_of_nonneg_left hden hnum0
    _ = 2 * A ^ 2 * (1 / ((n : ℝ) * Real.log (2 * (n : ℝ)) ^ 2)) +
        2 * D ^ 2 * (1 / (n : ℝ) ^ ((4 : ℝ) / 3)) := by
      rw [add_div]
      have hcub := cubic_energy_identity hn0
      have hsplit :
          (2 * D ^ 2 * ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2) / (n : ℝ) ^ 2 =
          2 * D ^ 2 * (1 / (n : ℝ) ^ ((4 : ℝ) / 3)) := by
        calc
          _ = (2 * D ^ 2) *
            (((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 / (n : ℝ) ^ 2) := by ring
          _ = _ := by rw [hcub]
      rw [hsplit]
      congr 1
      field_simp [hn0.ne', hL.ne']
      <;> ring

end RiemannResearch.RH.ActualPrimePowerError
