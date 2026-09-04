/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rank-one Schur elimination

Exact scalar and Cauchy--Schwarz forms of the rank-one high-mode elimination
used in the second `L = log 3` endpoint computation.

Source: Lemma 6.1 and its proof in the user-provided report
`rh_irreducible_targets_progress_2026-09-03`. The report supplies the proof
strategy. The explicit positivity hypotheses below include the positive
high-floor condition inherited from the surrounding operator reduction.
-/

namespace RiemannResearch.LinearAlgebra

/-- Exact one-dimensional completion of the square for a signed rank-one
perturbation. The coefficient `τ` may have either sign. -/
theorem rank_one_scalar_identity
    (δ τ c a r : ℝ) (hD : δ + τ * c ^ 2 ≠ 0) :
    δ * r ^ 2 + τ * (a + c * r) ^ 2 =
      (δ + τ * c ^ 2) *
          (r + τ * c * a / (δ + τ * c ^ 2)) ^ 2 +
        (τ * δ / (δ + τ * c ^ 2)) * a ^ 2 := by
  field_simp [hD]
  ring

/-- The effective rank-one term is a lower bound whenever the corrected
denominator is positive, including the negative-`τ` case. -/
theorem rank_one_scalar_lower_bound
    (δ τ c a r : ℝ) (hD : 0 < δ + τ * c ^ 2) :
    (τ * δ / (δ + τ * c ^ 2)) * a ^ 2 ≤
      δ * r ^ 2 + τ * (a + c * r) ^ 2 := by
  rw [rank_one_scalar_identity δ τ c a r (ne_of_gt hD)]
  exact le_add_of_nonneg_left
    (mul_nonneg (le_of_lt hD) (sq_nonneg _))

/-- Cauchy--Schwarz abstraction of high-mode rank-one elimination.

Here `C` represents the squared norm of the discarded polar vector, `s`
its pairing with the free high vector, and `r2` that vector's squared norm.
The hypothesis `s² ≤ C*r2` is precisely the Cauchy--Schwarz input. -/
theorem rank_one_elimination_lower_bound
    (δ τ C a s r2 : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < δ + τ * C)
    (hCS : s ^ 2 ≤ C * r2) :
    τ * δ / (δ + τ * C) * a ^ 2 ≤
      δ * r2 + τ * (a + s) ^ 2 := by
  rw [show τ * δ / (δ + τ * C) * a ^ 2 =
      (τ * δ * a ^ 2) / (δ + τ * C) by ring]
  apply (div_le_iff₀ hD).2
  have hrem : 0 ≤ r2 - s ^ 2 / C := by
    rw [sub_nonneg, div_le_iff₀ hC]
    simpa [mul_comm] using hCS
  have hnonneg :
      0 ≤ δ * (δ + τ * C) * (r2 - s ^ 2 / C) +
        (τ * C * a + (δ + τ * C) * s) ^ 2 / C := by
    exact add_nonneg
      (mul_nonneg (mul_nonneg (le_of_lt hδ) (le_of_lt hD)) hrem)
      (div_nonneg (sq_nonneg _) (le_of_lt hC))
  have hid :
      (δ + τ * C) * (δ * r2 + τ * (a + s) ^ 2) -
          τ * δ * a ^ 2 =
        δ * (δ + τ * C) * (r2 - s ^ 2 / C) +
          (τ * C * a + (δ + τ * C) * s) ^ 2 / C := by
    field_simp [ne_of_gt hC]
    ring
  rw [← hid] at hnonneg
  linarith

/-- The algebraic lower bound is attained at the rank-one normal-equation
values. This verifies that the effective coefficient is exact, not merely a
convenient underestimate. -/
theorem rank_one_elimination_attained
    (δ τ C a : ℝ) (hD : δ + τ * C ≠ 0) :
    δ * (τ ^ 2 * C * a ^ 2 / (δ + τ * C) ^ 2) +
        τ * (a - τ * C * a / (δ + τ * C)) ^ 2 =
      τ * δ / (δ + τ * C) * a ^ 2 := by
  field_simp [hD]
  ring

end RiemannResearch.LinearAlgebra

namespace RiemannResearch.LinearAlgebra

/-- Sharp rank-one high-mode lower bound. The denominator condition is
essential when `τ < 0`. This formalizes the Hilbert-space minimization used in
Lemma 6.1 of the supplied 3 September 2026 progress report. -/
theorem rankOne_highMode_lower_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (δ τ a : ℝ) (c r : H)
    (hδ : 0 < δ)
    (hden : 0 < δ + τ * ‖c‖ ^ 2) :
    (τ * δ * a ^ 2) / (δ + τ * ‖c‖ ^ 2) ≤
      δ * ‖r‖ ^ 2 + τ * (a + inner ℝ c r) ^ 2 := by
  by_cases hc : c = 0
  · subst c
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, add_zero, inner_zero_left] at hden ⊢
    rw [div_le_iff₀ hδ]
    have hnon : 0 ≤ δ ^ 2 * ‖r‖ ^ 2 :=
      mul_nonneg (sq_nonneg δ) (sq_nonneg ‖r‖)
    nlinarith
  · have hC : 0 < ‖c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
    have hcs :
        (inner ℝ c r) ^ 2 ≤ ‖c‖ ^ 2 * ‖r‖ ^ 2 := by
      simpa [pow_two, real_inner_self_eq_norm_sq] using
        (real_inner_mul_inner_self_le c r)
    have hgap :
        0 ≤ ‖c‖ ^ 2 * ‖r‖ ^ 2 - (inner ℝ c r) ^ 2 :=
      sub_nonneg.mpr hcs
    have hmain :
        0 ≤
          δ * (δ + τ * ‖c‖ ^ 2) *
              (‖c‖ ^ 2 * ‖r‖ ^ 2 - (inner ℝ c r) ^ 2) +
            ((δ + τ * ‖c‖ ^ 2) * inner ℝ c r +
              τ * ‖c‖ ^ 2 * a) ^ 2 := by
      exact add_nonneg
        (mul_nonneg
          (mul_nonneg (le_of_lt hδ) (le_of_lt hden)) hgap)
        (sq_nonneg _)
    have hid :
        ‖c‖ ^ 2 *
            ((δ * ‖r‖ ^ 2 + τ * (a + inner ℝ c r) ^ 2) *
                (δ + τ * ‖c‖ ^ 2) -
              τ * δ * a ^ 2) =
          δ * (δ + τ * ‖c‖ ^ 2) *
              (‖c‖ ^ 2 * ‖r‖ ^ 2 - (inner ℝ c r) ^ 2) +
            ((δ + τ * ‖c‖ ^ 2) * inner ℝ c r +
              τ * ‖c‖ ^ 2 * a) ^ 2 := by
      ring
    have hprod :
        0 ≤ ‖c‖ ^ 2 *
            ((δ * ‖r‖ ^ 2 + τ * (a + inner ℝ c r) ^ 2) *
                (δ + τ * ‖c‖ ^ 2) -
              τ * δ * a ^ 2) := by
      rw [hid]
      exact hmain
    have hdiff :
        0 ≤
          (δ * ‖r‖ ^ 2 + τ * (a + inner ℝ c r) ^ 2) *
              (δ + τ * ‖c‖ ^ 2) -
            τ * δ * a ^ 2 :=
      nonneg_of_mul_nonneg_right hprod hC
    rw [div_le_iff₀ hden]
    linarith

/-- The rank-one lower bound is attained at the explicit minimizer. -/
theorem rankOne_highMode_attains
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (δ τ a : ℝ) (c : H)
    (hden : δ + τ * ‖c‖ ^ 2 ≠ 0) :
    let r₀ := (-(τ * a / (δ + τ * ‖c‖ ^ 2))) • c
    δ * ‖r₀‖ ^ 2 + τ * (a + inner ℝ c r₀) ^ 2 =
      (τ * δ * a ^ 2) / (δ + τ * ‖c‖ ^ 2) := by
  dsimp
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- Explicit negative-pole specialization, `τ = -κ < 0`. -/
theorem rankOne_highMode_lower_bound_neg
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (δ κ a : ℝ) (c r : H)
    (hδ : 0 < δ)
    (_hκ : 0 < κ)
    (hden : 0 < δ - κ * ‖c‖ ^ 2) :
    (-κ * δ * a ^ 2) / (δ - κ * ‖c‖ ^ 2) ≤
      δ * ‖r‖ ^ 2 - κ * (a + inner ℝ c r) ^ 2 := by
  have hden' : 0 < δ + (-κ) * ‖c‖ ^ 2 := by
    simpa [sub_eq_add_neg] using hden
  simpa [sub_eq_add_neg] using
    (rankOne_highMode_lower_bound δ (-κ) a c r hδ hden')

end RiemannResearch.LinearAlgebra
