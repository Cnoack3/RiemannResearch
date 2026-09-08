import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! A uniform logarithmic bound for the half-length harmonic sum used in the
hidden-noise moment estimates. Source: arithmetic-repair report, §6. -/

open scoped BigOperators
namespace RiemannResearch.Analysis

theorem half_harmonic_sub_log_abs_le_one (n : ℕ) (hn : 3 ≤ n) :
    |(∑ j ∈ Finset.range (n / 2), (1 : ℝ) / ((j + 1 : ℕ) : ℝ)) -
      Real.log n| ≤ 1 := by
  have hm : 0 < n / 2 := by omega
  have hcast : (harmonic (n / 2) : ℝ) =
      ∑ j ∈ Finset.range (n / 2), (1 : ℝ) / ((j + 1 : ℕ) : ℝ) := by
    simp [harmonic, one_div]
  rw [← hcast]
  have hlo := log_add_one_le_harmonic (n / 2)
  have hhi := harmonic_le_one_add_log (n / 2)
  have hloghi : Real.log (n / 2 : ℕ) ≤ Real.log n := by
    apply Real.log_le_log (by exact_mod_cast hm)
    exact_mod_cast (Nat.div_le_self n 2)
  have hloglo : Real.log n ≤ Real.log (2 * ((n / 2 + 1 : ℕ) : ℝ)) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show n ≤ 2 * (n / 2 + 1) by omega)
  rw [Real.log_mul (by norm_num) (by positivity)] at hloglo
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end RiemannResearch.Analysis
