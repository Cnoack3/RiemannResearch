import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conditional finite logarithmic residual barrier

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Section 7. The distance lower bound is an explicit domain-specific
hypothesis, not a formalized invocation of Burnol's theorem. The result
is the finite logarithmic budget; no logarithmic reconstruction upper
bound, asymptotic sharp constant, or RH assertion is proved here.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.LogarithmicResidualBarrier

def relativeGain (d : ℕ → ℝ) (j : ℕ) : ℝ := (d j - d (j+1)) / d j

theorem one_sub_relativeGain (d : ℕ → ℝ) (j : ℕ) (hj : d j ≠ 0) :
    1-relativeGain d j = d (j+1) / d j := by
  unfold relativeGain
  field_simp
  ring

theorem log_gain_telescope (d : ℕ → ℝ) (hd : ∀ j, 0 < d j) (N : ℕ) :
    (∑ j ∈ Finset.range N, -Real.log (1-relativeGain d j)) =
      Real.log (d 0 / d N) := by
  have hterm (j : ℕ) :
      -Real.log (1-relativeGain d j) = Real.log (d j)-Real.log (d (j+1)) := by
    rw [one_sub_relativeGain d j (ne_of_gt (hd j)),
      Real.log_div (ne_of_gt (hd (j+1))) (ne_of_gt (hd j))]
    ring
  simp_rw [hterm]
  rw [Finset.sum_range_sub', Real.log_div (ne_of_gt (hd 0)) (ne_of_gt (hd N))]

/-- Explicitly conditional on the classical-distance lower estimate at N.
It bounds the cumulative logarithmic gains, not reconstruction cost above. -/
theorem log_gain_budget_of_distance_lower (d : ℕ → ℝ) (hd : ∀ j, 0 < d j)
    (N : ℕ) (c : ℝ) (hc : 0 < c)
    (hlower : c / ((N : ℝ)+1) ≤ d N) :
    (∑ j ∈ Finset.range N, -Real.log (1-relativeGain d j)) ≤
      Real.log (d 0 / c) + Real.log ((N : ℝ)+1) := by
  rw [log_gain_telescope d hd]
  have hn : 0 < (N : ℝ)+1 := by positivity
  have hb : d 0 / d N ≤ (d 0 / c) * ((N : ℝ)+1) := by
    have hl := (div_le_iff₀ hn).mp hlower
    apply (div_le_iff₀ (hd N)).mpr
    apply (le_of_mul_le_mul_right ?_ hc)
    calc
      d 0 * c ≤ d 0 * (d N * ((N : ℝ)+1)) :=
        mul_le_mul_of_nonneg_left hl (hd 0).le
      _ = ((d 0 / c) * ((N : ℝ)+1) * d N) * c := by field_simp [ne_of_gt hc] <;> ring
  calc
    Real.log (d 0 / d N) ≤ Real.log ((d 0/c)*((N : ℝ)+1)) :=
      Real.log_le_log (div_pos (hd 0) (hd N)) hb
    _ = _ := Real.log_mul (ne_of_gt (div_pos (hd 0) hc)) (ne_of_gt hn)

end RiemannResearch.Analysis.LogarithmicResidualBarrier
