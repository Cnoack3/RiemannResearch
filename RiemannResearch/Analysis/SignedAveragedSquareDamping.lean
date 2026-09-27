/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.SignedDiniBoundedSubsequence
import RiemannResearch.Analysis.LogPowerSummability

/-!
# Averaged squared-prefix estimates imply signed Dini control

Weighted Young's inequality (equivalently a Cauchy--Schwarz argument) transfers
summable square energy against a logarithmic harmonic weight to the linear Dini
condition. This is an average over cutoffs, not a pointwise prefix bound.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis

/-- General weighted square-to-linear summability. The inverse weight must
be summable; no monotonicity or pointwise envelope is required. -/
theorem summable_of_weighted_sq_and_inv
    (a t : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ht : ∀ n, 0 < t n)
    (hsq : Summable (fun n => (a n)^2 * t n))
    (hinv : Summable (fun n => 1 / t n)) : Summable a := by
  apply (hsq.add hinv).of_nonneg_of_le ha
  intro n
  have heq : ((a n)^2 * t n + 1 / t n) * t n =
      (a n * t n)^2 + 1 := by
    field_simp [(ht n).ne']
  have hy : a n * t n ≤ ((a n)^2 * t n + 1 / t n) * t n := by
    rw [heq]
    nlinarith [sq_nonneg (a n * t n - (1 / 2 : ℝ))]
  exact (mul_le_mul_iff_left₀ (ht n)).mp (by simpa only [mul_comm] using hy)

variable {E : Type*} [NormedAddCommGroup E]

/-- The complete signed norm is squared only after all arithmetic terms are
combined. Summable weighted square energy yields the averaged Dini condition. -/
theorem signedVector_dini_of_log_weighted_sq
    (u : ℕ → E) {ε q : ℝ} (hq : 1 < q)
    (henergy : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ)^(-2 * ε - 1) *
        Real.log (2 * ((n + 1 : ℕ) : ℝ))^q *
          ‖signedVectorPrefix u (n + 1)‖^2)) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ)^(-ε - 1) *
      ‖signedVectorPrefix u (n + 1)‖) := by
  apply summable_of_weighted_sq_and_inv _
    (fun n => ((n + 1 : ℕ) : ℝ) * Real.log (2 * ((n + 1 : ℕ) : ℝ))^q)
  · intro n
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (n + 1)) _) (norm_nonneg _)
  · intro n
    have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hL : 0 < Real.log (2 * ((n + 1 : ℕ) : ℝ)) := by
      apply Real.log_pos
      have hn0 := Nat.cast_nonneg (α := ℝ) n
      push_cast
      linarith
    exact mul_pos hx (Real.rpow_pos_of_pos hL q)
  · apply henergy.congr
    intro n
    have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hp : ((n + 1 : ℕ) : ℝ)^(-ε - 1) *
        ((n + 1 : ℕ) : ℝ)^(-ε - 1) * ((n + 1 : ℕ) : ℝ) =
        ((n + 1 : ℕ) : ℝ)^(-2 * ε - 1) := by
      calc
        _ = ((n + 1 : ℕ) : ℝ)^((-ε - 1) + (-ε - 1)) *
            ((n + 1 : ℕ) : ℝ)^(1 : ℝ) := by
          rw [Real.rpow_add hx, Real.rpow_one]
        _ = ((n + 1 : ℕ) : ℝ)^((-ε - 1) + (-ε - 1) + 1) :=
          (Real.rpow_add hx _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = (((n + 1 : ℕ) : ℝ)^(-ε - 1) *
            ((n + 1 : ℕ) : ℝ)^(-ε - 1) * ((n + 1 : ℕ) : ℝ)) *
          Real.log (2 * ((n + 1 : ℕ) : ℝ))^q *
            ‖signedVectorPrefix u (n + 1)‖^2 := by rw [hp]
      _ = _ := by ring
  · exact (summable_nat_add_iff 1).mpr (summable_log_power_majorant hq)

end RiemannResearch.Analysis
