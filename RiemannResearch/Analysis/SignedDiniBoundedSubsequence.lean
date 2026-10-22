/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.SignedPowerDampingAbel

/-!
# Averaged signed-prefix damping without a boundary hypothesis

A Dini sum of complete signed prefix norms forces the normalized Abel boundary
below one infinitely often. The exact finite Abel identity then bounds the
weighted vector sums along an unbounded subsequence. This does not assert full
natural-order convergence: isolated large boundary values remain possible.

Source: standard Abel summation and harmonic-series divergence; independently
assembled here for the arithmetic finite-energy application, with no novelty
claim.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis

/-- Harmonic divergence extracts small normalized values from a Dini sum.
No pointwise asymptotic bound or monotonicity of the prefix norms is assumed. -/
theorem frequently_power_normalized_le_one_of_dini
    (a : ℕ → ℝ) {ε : ℝ}
    (hdini : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ)^(-ε - 1) * a n)) :
    ∃ᶠ n : ℕ in atTop, ((n + 1 : ℕ) : ℝ)^(-ε) * a n ≤ 1 := by
  by_contra hnot
  have he : ∀ᶠ n : ℕ in atTop, 1 < ((n + 1 : ℕ) : ℝ)^(-ε) * a n := by
    filter_upwards [not_frequently.mp hnot] with n hn
    exact lt_of_not_ge hn
  have hh : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ)^(-1 : ℝ)) := by
    apply hdini.of_norm_bounded_eventually_nat
    filter_upwards [he] with n hn
    have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ)^(-1 : ℝ) *
          (((n + 1 : ℕ) : ℝ)^(-ε) * a n) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hn.le
          (Real.rpow_nonneg hx.le (-1 : ℝ))
      _ = ((n + 1 : ℕ) : ℝ)^(-ε - 1) * a n := by
        rw [← mul_assoc, ← Real.rpow_add hx]
        congr 2
        ring
  have hh0 : Summable (fun n : ℕ => (n : ℝ)^(-1 : ℝ)) :=
    (summable_nat_add_iff 1).mp hh
  have himpossible := Real.summable_nat_rpow.mp hh0
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Averaged cancellation alone gives bounded damped partial sums along an
unbounded subsequence. It does not require the Abel boundary to tend to zero. -/
theorem signedVector_power_damped_frequently_bounded_of_dini
    (u : ℕ → E) {ε : ℝ} (hε : 0 ≤ ε)
    (hdini : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ)^(-ε - 1) * ‖signedVectorPrefix u (n + 1)‖)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ᶠ N : ℕ in atTop,
      ‖∑ n ∈ Finset.range (N + 1), ((n + 1 : ℕ) : ℝ)^(-ε) • u n‖ ≤ B := by
  let v : ℕ → ℝ := fun n =>
    |((n + 1 : ℕ) : ℝ)^(-ε) - ((n + 2 : ℕ) : ℝ)^(-ε)| *
      ‖signedVectorPrefix u (n + 1)‖
  have hv (n : ℕ) : 0 ≤ v n := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hs : Summable v := by
    apply (hdini.mul_left ε).of_nonneg_of_le hv
    intro n
    have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hstep := abs_power_damping_step_le hε hx
    have hcast : (((n + 1 : ℕ) : ℝ) + 1) = ((n + 2 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hcast] at hstep
    simpa only [v, mul_assoc] using
      mul_le_mul_of_nonneg_right hstep (norm_nonneg (signedVectorPrefix u (n + 1)))
  refine ⟨1 + ∑' n, v n, add_nonneg (by norm_num) (tsum_nonneg hv), ?_⟩
  apply (frequently_power_normalized_le_one_of_dini
    (fun n => ‖signedVectorPrefix u (n + 1)‖) hdini).mono
  intro N hN
  rw [signedVector_power_weight_identity]
  calc
    _ ≤ ‖((N + 1 : ℕ) : ℝ)^(-ε) • signedVectorPrefix u (N + 1)‖ +
        ‖∑ n ∈ Finset.range N,
          (((n + 1 : ℕ) : ℝ)^(-ε) - ((n + 2 : ℕ) : ℝ)^(-ε)) •
            signedVectorPrefix u (n + 1)‖ := norm_add_le _ _
    _ ≤ 1 + ∑' n, v n := by
      apply add_le_add
      · simpa only [norm_smul,
          Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (N + 1)) _)] using hN
      · apply (norm_sum_le _ _).trans
        simp only [norm_smul, Real.norm_eq_abs]
        exact hs.sum_le_tsum (Finset.range N) (fun n _ => hv n)

end RiemannResearch.Analysis
