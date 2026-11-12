/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ParetoPeriodicAbelTail
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Complete tail bounds for Pareto and reciprocal-weighted moments

Source: Pareto-first research agenda, Priority 2, 11 November 2026.
These bounds include the entire infinite tail after N. They apply to
Gram products, sources, and signed residual products after supplying
their absolute bound. Periodic mean acceleration is available separately.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ParetoReciprocalTailCertificate
open ParetoPeriodicAbelTail

theorem weighted_tail_bound (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (ha : ∀ k, |a k| ≤ C) :
    |∑' k, a k * weight N k| ≤ C / ((N + 1 : ℕ) : ℝ) := by
  have hs := bounded_summable a N C ha
  calc
    _ ≤ ∑' k, |a k * weight N k| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' k, C * weight N k := by
      apply Summable.tsum_le_tsum _ hs.abs ((weight_summable N).mul_left C)
      intro k
      rw [abs_mul, abs_of_nonneg (weight_nonneg N k)]
      exact mul_le_mul_of_nonneg_right (ha k) (weight_nonneg N k)
    _ = _ := by rw [tsum_mul_left, weight_mass]; ring

theorem reciprocal_weighted_tail_bound (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ k, |a k| ≤ C) :
    |∑' k, (a k / ((k + N + 1 : ℕ) : ℝ)) * weight N k| ≤
      C / (((N + 1 : ℕ) : ℝ) ^ 2) := by
  have hb (k : ℕ) : |a k / ((k + N + 1 : ℕ) : ℝ)| ≤
      C / ((N + 1 : ℕ) : ℝ) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((k + N + 1 : ℕ) : ℝ))]
    apply div_le_div₀ hC (ha k) (by positivity)
    exact_mod_cast (show N + 1 ≤ k + N + 1 by omega)
  have h := weighted_tail_bound
    (fun k => a k / ((k + N + 1 : ℕ) : ℝ)) N
    (C / ((N + 1 : ℕ) : ℝ)) hb
  convert h using 1 <;> ring

/-- A rational head and an enclosing tail interval certify the complete signed moment. -/
theorem complete_moment_interval (head tail center radius : ℝ)
    (htail : |tail - center| ≤ radius) :
    head + center - radius ≤ head + tail ∧
      head + tail ≤ head + center + radius := by
  have h := abs_le.mp htail
  constructor <;> linarith

end RiemannResearch.Analysis.ParetoReciprocalTailCertificate
